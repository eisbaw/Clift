"""Claude API integration for the proof engine.

Wires the extract -> prompt -> API call -> parse -> apply -> check pipeline
to the Anthropic Claude API. The LLM is UNTRUSTED: every suggested proof is
kernel-checked by Lean via `lake build`.

Usage (CLI):
    python -m CImporter.proof_engine.claude_api Examples/SwapProof.lean \\
        --project-dir . --dry-run

Usage (library):
    from CImporter.proof_engine.claude_api import prove_file
    results = prove_file("Examples/SwapProof.lean", project_dir=".", dry_run=True)
"""

import argparse
import json
import logging
import re
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional

from .extract_goals import extract_sorry_static, SorryGoal
from .build_prompt import build_prompt, ProofPrompt
from .apply_proof import (
    apply_and_check,
    extract_tactic_from_response,
    ProofResult,
)

logger = logging.getLogger(__name__)

# Default model for Claude API calls
DEFAULT_MODEL = "claude-sonnet-4-20250514"
DEFAULT_MAX_RETRIES = 3
DEFAULT_MAX_TOKENS = 4096


@dataclass
class APICallStats:
    """Track API usage for cost awareness."""
    calls_made: int = 0
    input_tokens: int = 0
    output_tokens: int = 0
    errors: int = 0
    start_time: float = 0.0
    model: str = ""

    def log_summary(self) -> str:
        elapsed = time.time() - self.start_time if self.start_time else 0
        return (
            f"API stats: {self.calls_made} calls, "
            f"{self.input_tokens} input tokens, "
            f"{self.output_tokens} output tokens, "
            f"{self.errors} errors, "
            f"{elapsed:.1f}s elapsed, "
            f"model={self.model}"
        )


def _call_claude_api(
    prompt: ProofPrompt,
    model: str = DEFAULT_MODEL,
    max_tokens: int = DEFAULT_MAX_TOKENS,
    stats: Optional[APICallStats] = None,
) -> str:
    """Call the Claude API with the given prompt. Returns the raw response text.

    TODO: Set ANTHROPIC_API_KEY environment variable before use.
    The anthropic SDK reads it automatically.

    Raises:
        ImportError: if `anthropic` package is not installed
        anthropic.APIError: on API failures (rate limit, auth, etc.)
    """
    try:
        import anthropic
    except ImportError:
        raise ImportError(
            "Install the anthropic SDK: pip install anthropic\n"
            "Then set ANTHROPIC_API_KEY in your environment."
        )

    client = anthropic.Anthropic()  # reads ANTHROPIC_API_KEY from env

    logger.info(f"Calling Claude API (model={model}, max_tokens={max_tokens})")
    logger.debug(f"System: {prompt.system_message[:200]}...")
    logger.debug(f"User: {prompt.user_message[:200]}...")

    try:
        response = client.messages.create(
            model=model,
            max_tokens=max_tokens,
            system=prompt.system_message,
            messages=[{"role": "user", "content": prompt.user_message}],
        )
    except Exception as e:
        if stats:
            stats.errors += 1
        logger.error(f"Claude API error: {e}")
        raise

    # Extract text from response
    text = ""
    for block in response.content:
        if hasattr(block, "text"):
            text += block.text

    # Track usage
    if stats and hasattr(response, "usage"):
        stats.calls_made += 1
        stats.input_tokens += response.usage.input_tokens
        stats.output_tokens += response.usage.output_tokens

    logger.info(f"Got response: {len(text)} chars")
    return text


def prove_sorry(
    goal: SorryGoal,
    project_dir: str,
    model: str = DEFAULT_MODEL,
    max_retries: int = DEFAULT_MAX_RETRIES,
    dry_run: bool = False,
    stats: Optional[APICallStats] = None,
    lake_cmd: str = "lake",
) -> ProofResult:
    """Attempt to prove a single sorry using the Claude API.

    Pipeline: goal -> prompt -> API call -> parse tactic -> apply -> lake build check.
    On failure, feeds the error back to Claude for retry (up to max_retries).

    Args:
        goal: The sorry location + context
        project_dir: Path to the lake project root
        model: Claude model to use
        max_retries: Max attempts per sorry
        dry_run: If True, print prompt but don't call API
        stats: API usage tracker
        lake_cmd: Command to invoke lake
    """
    error_feedback = None

    for attempt in range(1, max_retries + 1):
        logger.info(
            f"Attempt {attempt}/{max_retries} for "
            f"{goal.file}:{goal.line} ({goal.enclosing_name or 'unknown'})"
        )

        # Build prompt (includes error feedback on retries)
        prompt = build_prompt(goal, error_feedback=error_feedback)

        if dry_run:
            print(f"\n{'='*60}")
            print(f"DRY RUN: {goal.file}:{goal.line} ({goal.enclosing_name})")
            print(f"{'='*60}")
            print(f"\n--- System Message ---\n{prompt.system_message}")
            print(f"\n--- User Message ---\n{prompt.user_message}")
            return ProofResult(
                goal=goal, success=False, tactic="(dry run)", attempts=attempt
            )

        # Call Claude API
        try:
            response_text = _call_claude_api(prompt, model=model, stats=stats)
        except Exception as e:
            logger.error(f"API call failed: {e}")
            return ProofResult(
                goal=goal, success=False, tactic="", error=str(e), attempts=attempt
            )

        # Parse tactic from response
        tactic = extract_tactic_from_response(response_text)
        logger.info(f"Extracted tactic ({len(tactic)} chars): {tactic[:100]}...")

        # Apply and check with lake build
        result = apply_and_check(
            goal, tactic, project_dir, lake_cmd=lake_cmd
        )
        result.attempts = attempt

        if result.success:
            logger.info(f"Proof accepted by kernel on attempt {attempt}")
            return result

        # Failed: feed error back for retry
        error_feedback = result.error
        logger.warning(
            f"Attempt {attempt} failed: {result.error[:200] if result.error else 'unknown'}"
        )

    logger.error(
        f"All {max_retries} attempts failed for {goal.file}:{goal.line}"
    )
    return result


def prove_file(
    filepath: str,
    project_dir: str,
    model: str = DEFAULT_MODEL,
    max_retries: int = DEFAULT_MAX_RETRIES,
    dry_run: bool = False,
    lake_cmd: str = "lake",
) -> list[ProofResult]:
    """Process all sorry in a single .lean file.

    This is the --batch entry point. Extracts all sorry locations,
    then attempts to prove each one sequentially (since each proof
    changes the file and may affect subsequent line numbers).

    Returns list of ProofResult (one per sorry).
    """
    stats = APICallStats(start_time=time.time(), model=model)

    goals = extract_sorry_static(filepath)
    if not goals:
        logger.info(f"No sorry found in {filepath}")
        return []

    logger.info(f"Found {len(goals)} sorry in {filepath}")
    results = []

    for i, goal in enumerate(goals):
        logger.info(f"\n--- Processing sorry {i+1}/{len(goals)} ---")
        result = prove_sorry(
            goal,
            project_dir=project_dir,
            model=model,
            max_retries=max_retries,
            dry_run=dry_run,
            stats=stats,
            lake_cmd=lake_cmd,
        )
        results.append(result)

        if result.success and not dry_run:
            # Re-extract goals since line numbers shifted after file edit
            remaining = extract_sorry_static(filepath)
            logger.info(f"{len(remaining)} sorry remaining after success")

    # Summary
    successes = sum(1 for r in results if r.success)
    logger.info(f"\n{'='*60}")
    logger.info(f"Results: {successes}/{len(results)} sorry eliminated")
    logger.info(stats.log_summary())
    logger.info(f"{'='*60}")

    return results


def main():
    parser = argparse.ArgumentParser(
        description="Wire proof engine to Claude API for automated sorry elimination"
    )
    parser.add_argument(
        "file", nargs="?",
        help="Lean file to process (or use --batch for all sorry)"
    )
    parser.add_argument(
        "--project-dir", default=".",
        help="Path to lake project root (default: .)"
    )
    parser.add_argument(
        "--model", default=DEFAULT_MODEL,
        help=f"Claude model to use (default: {DEFAULT_MODEL})"
    )
    parser.add_argument(
        "--max-retries", type=int, default=DEFAULT_MAX_RETRIES,
        help=f"Max retry attempts per sorry (default: {DEFAULT_MAX_RETRIES})"
    )
    parser.add_argument(
        "--dry-run", action="store_true",
        help="Show prompts without calling API"
    )
    parser.add_argument(
        "--batch", action="store_true",
        help="Process all sorry in the file"
    )
    parser.add_argument(
        "--lake-cmd", default="lake",
        help="Command to invoke lake (default: lake)"
    )
    parser.add_argument(
        "-v", "--verbose", action="store_true",
        help="Enable debug logging"
    )
    parser.add_argument(
        "--output-json", type=str, default=None,
        help="Write results as JSON to this file"
    )

    args = parser.parse_args()

    level = logging.DEBUG if args.verbose else logging.INFO
    logging.basicConfig(
        level=level,
        format="%(asctime)s %(name)s %(levelname)s %(message)s",
    )

    if not args.file:
        parser.error("Provide a .lean file to process")

    filepath = str(Path(args.file).resolve())
    if not Path(filepath).exists():
        logger.error(f"File not found: {filepath}")
        sys.exit(1)

    results = prove_file(
        filepath=filepath,
        project_dir=args.project_dir,
        model=args.model,
        max_retries=args.max_retries,
        dry_run=args.dry_run,
        lake_cmd=args.lake_cmd,
    )

    # Output results
    if args.output_json:
        data = []
        for r in results:
            data.append({
                "file": r.goal.file,
                "line": r.goal.line,
                "enclosing": r.goal.enclosing_name,
                "success": r.success,
                "tactic": r.tactic,
                "error": r.error,
                "attempts": r.attempts,
            })
        Path(args.output_json).write_text(json.dumps(data, indent=2))
        logger.info(f"Results written to {args.output_json}")

    # Exit code: 0 if all succeeded, 1 if any failed
    successes = sum(1 for r in results if r.success)
    if successes == len(results) and results:
        sys.exit(0)
    else:
        sys.exit(1)


if __name__ == "__main__":
    main()
