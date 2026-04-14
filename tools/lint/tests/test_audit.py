"""Tests for tools/lint/audit.py — positive (detect known issues) + negative (clean code passes)."""
import subprocess
import json
import os
import tempfile
import sys

AUDIT = os.path.join(os.path.dirname(__file__), "..", "audit.py")
PROJECT_ROOT = os.path.join(os.path.dirname(__file__), "..", "..", "..")

def run_audit(*args):
    """Run audit.py and return (exit_code, stdout)."""
    result = subprocess.run(
        [sys.executable, AUDIT, *args],
        capture_output=True, text=True,
        cwd=PROJECT_ROOT
    )
    return result.returncode, result.stdout

def run_audit_json():
    """Run audit.py --json and return parsed dict."""
    code, out = run_audit("--json", "--skip-lake")
    return code, json.loads(out)


class TestAuditRuns:
    """Basic sanity: audit runs and produces output."""

    def test_runs_without_crash(self):
        code, out = run_audit("--skip-lake")
        assert "Clift Proof Integrity Audit" in out

    def test_json_output_valid(self):
        code, data = run_audit_json()
        assert "checks" in data
        assert isinstance(data["checks"], list)
        assert "has_fail" in data

    def test_json_has_core_checks(self):
        """With --skip-lake, sorry_axiom is skipped. Check the rest."""
        _, data = run_audit_json()
        check_names = [c["name"] for c in data["checks"]]
        expected = [
            "sorry_count", "hand_written_l1", "wrong_target",
            "tautological_weakening", "circular_specs", "custom_axioms",
            "native_decide", "csimp_smuggling",
            "implemented_by", "unsafe_defs", "vacuous_preconditions"
        ]
        for name in expected:
            assert name in check_names, f"Missing check: {name}"


class TestPositiveDetections:
    """These SHOULD be detected (known issues in codebase)."""

    def test_detects_hand_written_l1(self):
        _, data = run_audit_json()
        hw = next(c for c in data["checks"] if c["name"] == "hand_written_l1")
        assert hw["count"] >= 10, f"Expected >=10 hand-written L1 bodies, got {hw['count']}"
        assert hw["severity"] == "WARN"

    def test_detects_wrong_target(self):
        _, data = run_audit_json()
        wt = next(c for c in data["checks"] if c["name"] == "wrong_target")
        assert wt["count"] >= 2, f"Expected >=2 wrong targets, got {wt['count']}"
        assert "DmaBufferProof" in str(wt["details"])

    def test_detects_native_decide(self):
        _, data = run_audit_json()
        nd = next(c for c in data["checks"] if c["name"] == "native_decide")
        assert nd["count"] >= 3, f"Expected >=3 native_decide, got {nd['count']}"
        assert nd["severity"] == "WARN"

    def test_detects_sorry(self):
        _, data = run_audit_json()
        sc = next(c for c in data["checks"] if c["name"] == "sorry_count")
        assert sc["count"] >= 1, "Expected at least 1 sorry"

    def test_sorry_not_in_core_library(self):
        """Core library (Clift/) must be sorry-free."""
        _, data = run_audit_json()
        sc = next(c for c in data["checks"] if c["name"] == "sorry_count")
        # Check that no sorry is in Clift/
        clift_sorry = [d for d in sc.get("details", []) if d.startswith("Clift/")]
        assert len(clift_sorry) == 0, f"Sorry in core library: {clift_sorry}"


class TestNegativeDetections:
    """These should NOT be flagged (clean areas of codebase)."""

    def test_no_custom_axioms(self):
        _, data = run_audit_json()
        ca = next(c for c in data["checks"] if c["name"] == "custom_axioms")
        assert ca["count"] == 0
        assert ca["severity"] == "OK"

    def test_no_csimp(self):
        _, data = run_audit_json()
        cs = next(c for c in data["checks"] if c["name"] == "csimp_smuggling")
        assert cs["count"] == 0
        assert cs["severity"] == "OK"

    def test_no_implemented_by(self):
        _, data = run_audit_json()
        ib = next(c for c in data["checks"] if c["name"] == "implemented_by")
        assert ib["count"] == 0
        assert ib["severity"] == "OK"

    def test_no_unsafe(self):
        _, data = run_audit_json()
        ud = next(c for c in data["checks"] if c["name"] == "unsafe_defs")
        assert ud["count"] == 0
        assert ud["severity"] == "OK"

    def test_no_circular_specs(self):
        _, data = run_audit_json()
        cs = next(c for c in data["checks"] if c["name"] == "circular_specs")
        assert cs["count"] == 0
        assert cs["severity"] == "OK"

    def test_no_vacuous_preconditions(self):
        _, data = run_audit_json()
        vp = next(c for c in data["checks"] if c["name"] == "vacuous_preconditions")
        assert vp["count"] == 0
        assert vp["severity"] == "OK"

    def test_no_tautological_weakening(self):
        """After removing bogus proofs, no validHoare_weaken_trivial_post usage."""
        _, data = run_audit_json()
        tw = next(c for c in data["checks"] if c["name"] == "tautological_weakening")
        assert tw["count"] == 0, f"Expected 0 tautological weakening, got {tw['count']}"


class TestExitCodes:
    """Exit codes for CI integration."""

    def test_no_fail_means_exit_0(self):
        """If no FAIL severity, exit 0."""
        code, data = run_audit_json()
        fails = [c for c in data["checks"] if c["severity"] == "FAIL"]
        if len(fails) == 0:
            assert code == 0
        else:
            assert code == 1


if __name__ == "__main__":
    import pytest
    pytest.main([__file__, "-v"])
