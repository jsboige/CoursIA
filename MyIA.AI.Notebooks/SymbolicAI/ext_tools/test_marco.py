"""Regression tests for ext_tools/marco.py (MARCO MUS/MSS enumerator).

Pins the duplicate-clause hang bug: control variables were named after the
constraint's string representation (`Bool(str(constraint))`), so two clauses
with identical text (e.g. duplicate unit clauses, legal in DIMACS) collided
to a single Z3 control variable. This corrupted the Map solver's blocking
logic and sent `enumerate_sets` into an infinite loop on valid input.

The fix names control variables after the constraint INDEX (`Bool(f"__c{i}")`),
guaranteeing one distinct control variable per clause regardless of content.

These tests run marco.py as a subprocess with a hard timeout: the buggy
version hangs (timeout => fail), the fixed version terminates with correct
MUS/MSS output.
"""
import os
import re
import subprocess
import sys
import textwrap

HERE = os.path.dirname(os.path.abspath(__file__))
MARCO = os.path.join(HERE, "marco.py")
TIMEOUT_S = 30  # buggy version loops forever; 30s is generous for fixed version on these tiny CNFs


def _run_marco(cnf_text: str, *extra):
    """Write CNF to a temp file and run marco.py. Returns (rc, stdout)."""
    import tempfile

    cnf = tempfile.NamedTemporaryFile("w", suffix=".cnf", delete=False, encoding="utf-8")
    cnf.write(textwrap.dedent(cnf_text).lstrip())
    cnf.close()
    try:
        proc = subprocess.run(
            [sys.executable, MARCO, cnf.name, *extra],
            capture_output=True, text=True, timeout=TIMEOUT_S,
        )
        return proc.returncode, proc.stdout
    finally:
        os.unlink(cnf.name)


def _parse(output: str):
    """Return (mus_list, mss_list) parsed from marco verbose output."""
    mus, mss = [], []
    for line in output.splitlines():
        line = line.strip()
        if line.startswith("U "):
            mus.append(sorted(int(x) for x in re.findall(r"\d+", line)))
        elif line.startswith("S "):
            mss.append(sorted(int(x) for x in re.findall(r"\d+", line)))
    return sorted(mus), sorted(mss)


def test_simple_mus_and_mss():
    """(x1)(¬x1)(x2): MUS={0,1}, MSS={0,2} and {1,2}."""
    rc, out = _run_marco("""
        p cnf 2 3
        1 0
        -1 0
        2 0
    """, "-v")
    assert rc == 0, f"marco exited {rc}: {out}"
    mus, mss = _parse(out)
    assert mus == [[0, 1]], mus
    assert mss == [[0, 2], [1, 2]], mss


def test_two_independent_muses():
    """(x1)(¬x1)(x2)(¬x2): two MUSes {0,1},{2,3} and 4 MSS (one from each pair)."""
    rc, out = _run_marco("""
        p cnf 2 4
        1 0
        -1 0
        2 0
        -2 0
    """, "-v")
    assert rc == 0, f"marco exited {rc}: {out}"
    mus, mss = _parse(out)
    assert mus == [[0, 1], [2, 3]], mus
    assert len(mss) == 4, mss


def test_duplicate_clause_does_not_hang():
    """REGRESSION PIN: duplicate unit clause must terminate with DISTINCT MUSes.

    Buggy version: c0=(x1) and c1=(x1) share control var Bool("x1") ->
    infinite loop in enumerate_sets (timeout => subprocess.TimeoutExpired -> fail).

    Fixed version: distinct index-named control vars -> MUSes {0,2} and {1,2}
    (each duplicate paired with the negation c2=(¬x1) is independently minimal
    unsatisfiable).
    """
    rc, out = _run_marco("""
        p cnf 2 4
        1 0
        1 0
        -1 0
        2 0
    """, "-v")  # subprocess.run raises TimeoutExpired if it hangs -> test fails
    assert rc == 0, f"marco exited {rc}: {out}"
    mus, mss = _parse(out)
    # Both duplicates form their own minimal UNSAT subset with the negation.
    assert [0, 2] in mus and [1, 2] in mus, mus


def test_duplicate_disjunction_terminates():
    """Same collision class: duplicate non-unit clause (x1∨x2)."""
    rc, out = _run_marco("""
        p cnf 2 4
        1 2 0
        1 2 0
        -1 0
        -2 0
    """, "-v")
    assert rc == 0, f"marco exited {rc}: {out}"
    mus, _ = _parse(out)
    # {0,2,3} and {1,2,3}: each duplicate (x1∨x2) with (¬x1)(¬x2) is minimally UNSAT.
    assert [0, 2, 3] in mus and [1, 2, 3] in mus, mus


def test_mus_only_flag():
    """--mus-only enumerates only MUS lines."""
    rc, out = _run_marco("""
        p cnf 2 3
        1 0
        -1 0
        2 0
    """, "--mus-only", "-v")
    assert rc == 0
    mus, mss = _parse(out)
    assert mus == [[0, 1]], mus
    assert mss == [], mss


def test_mss_only_flag():
    """--mss-only enumerates only MSS lines."""
    rc, out = _run_marco("""
        p cnf 2 3
        1 0
        -1 0
        2 0
    """, "--mss-only", "-v")
    assert rc == 0
    mus, mss = _parse(out)
    assert mus == [], mus
    assert mss == [[0, 2], [1, 2]], mss
