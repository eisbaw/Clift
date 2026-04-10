"""Build LLM prompts from sorry goals.

Prompt construction is LLM-agnostic: the same prompt works for Claude, GPT,
DeepSeek-Prover, or any model that understands Lean 4 tactic proofs.

The prompt includes:
1. The goal state (what needs to be proven)
2. Available hypotheses
3. Surrounding code context (function definition, imports)
4. Similar proven lemmas from ProofIndex (few-shot examples)
5. Common patterns and hints (e.g., [local irreducible] for heap proofs)
"""

import json
import logging
from dataclasses import dataclass
from pathlib import Path
from typing import Optional

from .extract_goals import SorryGoal

logger = logging.getLogger(__name__)


# Known proof patterns for common goal shapes
PROOF_HINTS = {
    "validHoare": [
        "For validHoare goals, decompose with l1_vcg_finish or intro + manual steps.",
        "For guard+modify patterns, use L1_guard_modify_result.",
        "For sequential composition, find the intermediate state.",
    ],
    "L1corres": [
        "Use corres_auto for structural L1corres goals.",
        "For call-containing functions, ensure callee corres is available.",
    ],
    "heapPtrValid": [
        "Use heapUpdate_preserves_heapPtrValid for pointer validity after writes.",
        "Use [local irreducible] hVal heapUpdate for projection lemmas.",
    ],
    "hVal": [
        "Use hVal_heapUpdate_same for reading what was just written.",
        "Use hVal_heapUpdate_disjoint for reading a different location.",
        "Mark hVal/heapUpdate as [local irreducible] to prevent kernel deep recursion.",
    ],
    "UInt32": [
        "Use omega for UInt32/Nat arithmetic.",
        "UInt32.toNat for converting to natural numbers.",
    ],
}


@dataclass
class ProofPrompt:
    """A complete prompt for an LLM to generate a tactic proof."""
    goal: SorryGoal
    system_message: str
    user_message: str
    # Error feedback from a previous attempt (for retry)
    previous_error: Optional[str] = None


def build_prompt(goal: SorryGoal,
                 similar_proofs: list[dict] = None,
                 error_feedback: Optional[str] = None) -> ProofPrompt:
    """Build a complete prompt for an LLM to fill a sorry.

    Args:
        goal: The sorry goal to fill
        similar_proofs: List of {goal_pattern, proof_script} from ProofIndex
        error_feedback: Error message from a previous failed attempt (for retry)
    """
    if similar_proofs is None:
        similar_proofs = []

    system_msg = _build_system_message()
    user_msg = _build_user_message(goal, similar_proofs, error_feedback)

    return ProofPrompt(
        goal=goal,
        system_message=system_msg,
        user_message=user_msg,
        previous_error=error_feedback,
    )


def _build_system_message() -> str:
    return """You are a Lean 4 proof assistant. Your task is to replace `sorry` with a valid tactic proof.

Rules:
1. Output ONLY the tactic block (no explanation, no markdown fences unless asked)
2. The proof must type-check in Lean 4 (kernel-verified)
3. Use standard tactics: simp, omega, rfl, exact, apply, intro, constructor, cases, rw, unfold
4. For heap/pointer proofs, use [local irreducible] hVal heapUpdate patterns
5. For Hoare triples (validHoare), decompose with l1_vcg_finish or step-by-step
6. Keep proofs as simple as possible - prefer automation over manual steps
7. If a proof needs sorry, say so explicitly - never hide complexity

Format your response as:
```lean
<tactic proof here>
```"""


def _build_user_message(goal: SorryGoal,
                         similar_proofs: list[dict],
                         error_feedback: Optional[str]) -> str:
    parts = []

    # Goal location
    parts.append(f"## Goal to prove")
    parts.append(f"File: {goal.file}")
    parts.append(f"Line: {goal.line}")
    if goal.enclosing_name:
        parts.append(f"In: {goal.enclosing_name}")
    parts.append("")

    # Goal state (if available)
    if goal.goal_state:
        parts.append("## Goal state")
        parts.append("```")
        parts.append(goal.goal_state)
        parts.append("```")
        parts.append("")

    # Hypotheses
    if goal.hypotheses:
        parts.append("## Available hypotheses")
        for h in goal.hypotheses:
            parts.append(f"  {h}")
        parts.append("")

    # Surrounding context
    if goal.context_before:
        parts.append("## Code context (before sorry)")
        parts.append("```lean")
        parts.append(goal.context_before)
        parts.append("```")
        parts.append("")

    if goal.context_after:
        parts.append("## Code context (after sorry)")
        parts.append("```lean")
        parts.append(goal.context_after)
        parts.append("```")
        parts.append("")

    # Hints based on goal patterns
    hints = _get_hints(goal)
    if hints:
        parts.append("## Hints")
        for h in hints:
            parts.append(f"- {h}")
        parts.append("")

    # Similar proofs (few-shot)
    if similar_proofs:
        parts.append("## Similar proven lemmas (use as examples)")
        for sp in similar_proofs[:3]:  # Max 3 examples
            parts.append(f"Pattern: {sp.get('goal_pattern', 'unknown')}")
            parts.append(f"Proof: {sp.get('proof_script', 'sorry')}")
            parts.append("")

    # Error feedback (for retry)
    if error_feedback:
        parts.append("## Previous attempt failed with:")
        parts.append("```")
        parts.append(error_feedback)
        parts.append("```")
        parts.append("Please fix the proof based on this error.")
        parts.append("")

    parts.append("## Task")
    parts.append("Replace the `sorry` with a valid tactic proof. Output ONLY the tactic block.")

    return "\n".join(parts)


def _get_hints(goal: SorryGoal) -> list[str]:
    """Extract relevant hints based on keywords in the goal context."""
    hints = []
    context = (goal.context_before + " " + goal.context_after +
               " " + (goal.goal_state or ""))

    for keyword, keyword_hints in PROOF_HINTS.items():
        if keyword in context:
            hints.extend(keyword_hints)

    return hints[:5]  # Limit to 5 hints


if __name__ == "__main__":
    import sys
    logging.basicConfig(level=logging.INFO)

    if len(sys.argv) < 2:
        print("Usage: python build_prompt.py <goals.json>")
        sys.exit(1)

    goals_data = json.loads(Path(sys.argv[1]).read_text())
    for gd in goals_data:
        goal = SorryGoal(**gd)
        prompt = build_prompt(goal)
        print(f"=== {goal.file}:{goal.line} ===")
        print(prompt.user_message)
        print()
