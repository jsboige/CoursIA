"""Regression tests for LeanRunner._run_wsl (issue #17612).

The previous implementation piped user code into the Lean 4 `repl` binary,
which does NOT load `Init.Prelude` automatically — every Nat literal
failed with `Unknown identifier 'OfNat'` / `Unknown identifier 'Nat'`
followed by a parser cascade (`unexpected token '+' / '*'`), and even
`theorem t : True := trivial` did not resolve.

Fix: switch the WSL backend to `lean --json file.lean` against a lake
project (default `~/lean-projects/notebook_context`), wrapping the
user code with `import Init.Prelude`. These tests cover:

1. Successful theorem verification (Nat literal case from #17612)
2. Failed theorem (sorry / wrong proof)
3. Successful #check with Nat literal
4. User-provided `import Init.Prelude` is not duplicated
5. JSON stdout is parsed line-by-line (multiple messages)
"""

import json
import sys
from pathlib import Path
from unittest.mock import patch, MagicMock

import pytest

LEAN_DIR = Path(__file__).resolve().parents[2]
if str(LEAN_DIR) not in sys.path:
    sys.path.insert(0, str(LEAN_DIR))

from lean_runner import LeanRunner, Backend, LeanResult  # noqa: E402


def _completed(stdout: str = "", stderr: str = "", returncode: int = 0):
    """Helper to build a CompletedProcess for mocking subprocess.run."""
    import subprocess as _subprocess
    return _subprocess.CompletedProcess(
        args=["wsl"], returncode=returncode, stdout=stdout, stderr=stderr
    )


def _make_runner_with_wsl():
    """Construct a LeanRunner pinned to the WSL backend without running
    the WSL availability check (which would slow unit tests)."""
    runner = LeanRunner.__new__(LeanRunner)
    runner.timeout = 30
    runner.backend = Backend.WSL
    runner.wsl_project_dir = "~/lean-projects/notebook_context"
    runner._temp_dir = None
    runner._wsl_kernel = None
    runner._leandojo_repo = None
    return runner


def _bash_commands(mock_run):
    """Return the list of bash -c command strings passed to subprocess.run.

    `_run_wsl` makes 3 calls: (1) `echo ${TMPDIR}`, (2) the lean heredoc,
    (3) `rm -f <tmpfile>`. We return all of them so callers can inspect
    the heredoc specifically.
    """
    cmds = []
    for call in mock_run.call_args_list:
        args = call.args if hasattr(call, "args") else call[0]
        if args and isinstance(args[0], list) and "bash" in args[0]:
            cmds.append(args[0][-1])
    return cmds


def test_17612_nat_literal_theorem_verifies_via_wsl():
    """Issue #17612 founder case: a Nat literal theorem must verify
    through the WSL backend. Before the fix, this returned
    `success=False` with `unexpected token '+'; expected ':='`."""
    runner = _make_runner_with_wsl()
    # What `lean --json` emits for a successful #check of a theorem
    # whose body uses Nat literals and `rfl`.
    stdout = (
        '{"severity":"information","data":"test_verification '
        '(n : Nat) : n + 0 = n","pos":{"line":6,"column":0}}\n'
    )
    with patch("lean_runner.subprocess.run", return_value=_completed(stdout=stdout)) as mock_run:
        result = runner.run("theorem test_verification (n : Nat) : n + 0 = n := by\n  rfl")

    assert isinstance(result, LeanResult)
    assert result.success is True
    assert result.backend == "wsl"
    assert "n + 0 = n" in result.output
    assert result.errors == ""
    # The heredoc must include `import Init.Prelude` and the wrapped
    # theorem. Inspect the bash commands to find it.
    bash_cmds = _bash_commands(mock_run)
    lean_cmd = next((c for c in bash_cmds if "lean --json" in c), "")
    assert "import Init.Prelude" in lean_cmd
    assert "theorem test_verification" in lean_cmd


def test_run_wsl_sorry_is_treated_as_failure():
    """A proof that uses `sorry` must be flagged as a failure."""
    runner = _make_runner_with_wsl()
    stdout = (
        '{"severity":"warning","kind":"hasSorry","data":"declaration '
        'uses `sorry`","pos":{"line":3,"column":8}}\n'
    )
    with patch("lean_runner.subprocess.run", return_value=_completed(stdout=stdout)):
        result = runner.run("theorem t : True := by sorry")

    assert result.success is False
    assert "sorry" in result.errors.lower()


def test_run_wsl_unknown_identifier_reported_as_error():
    """A reference to an undefined identifier must surface as an error."""
    runner = _make_runner_with_wsl()
    stdout = (
        '{"severity":"error","data":"Unknown identifier `triv`",'
        '"pos":{"line":1,"column":20}}\n'
    )
    with patch("lean_runner.subprocess.run", return_value=_completed(stdout=stdout)):
        result = runner.run("theorem t : True := triv")

    assert result.success is False
    assert "Unknown identifier" in result.errors


def test_run_wsl_user_import_init_prelude_not_duplicated():
    """If the user already wrote `import Init.Prelude`, the wrapper
    must not produce a duplicate line — Lean would still accept it but
    the duplicate inflates the diff and obscures the user code."""
    runner = _make_runner_with_wsl()
    stdout = '{"severity":"information","data":"ok","pos":{"line":1,"column":0}}\n'
    with patch("lean_runner.subprocess.run", return_value=_completed(stdout=stdout)) as mock_run:
        runner.run("import Init.Prelude\n\ntheorem t : True := trivial")

    bash_cmds = _bash_commands(mock_run)
    lean_cmd = next((c for c in bash_cmds if "lean --json" in c), "")
    # Exactly one `import Init.Prelude` line in the heredoc payload.
    prelude_count = lean_cmd.count("import Init.Prelude")
    assert prelude_count == 1


def test_run_wsl_multiple_json_messages_parsed_line_by_line():
    """`lean --json` emits one JSON object per line. The parser must
    iterate over each line and not only the first."""
    runner = _make_runner_with_wsl()
    stdout = "\n".join([
        '{"severity":"information","data":"first line","pos":{"line":1,"column":0}}',
        '{"severity":"information","data":"second line","pos":{"line":2,"column":0}}',
        '{"severity":"warning","data":"some warning","pos":{"line":3,"column":0}}',
    ])
    with patch("lean_runner.subprocess.run", return_value=_completed(stdout=stdout)):
        result = runner.run("theorem t : True := trivial")

    assert result.success is True
    assert "first line" in result.output
    assert "second line" in result.output
    assert "some warning" in result.output


def test_run_wsl_timeout_on_lean_call_returns_failure():
    """A Lean subprocess that exceeds `self.timeout` must yield a
    failure LeanResult, not raise. The TMPDIR probe and the cleanup
    `rm -f` calls must NOT trigger the timeout (we mock them to
    succeed) — only the lean call itself times out.
    """
    import subprocess
    runner = _make_runner_with_wsl()
    runner.timeout = 1

    real_run = subprocess.run
    calls = {"n": 0}

    def fake_run(*args, **kwargs):
        calls["n"] += 1
        if calls["n"] == 2:
            # The second call is the lean heredoc — timeout there.
            raise subprocess.TimeoutExpired(cmd=["wsl"], timeout=1)
        return real_run(*args, **kwargs) if False else _completed()

    with patch("lean_runner.subprocess.run", side_effect=fake_run):
        result = runner.run("theorem t : True := trivial")

    assert result.success is False
    assert "Timeout" in result.errors
    assert result.exit_code == -1


def test_run_wsl_handles_non_json_garbage_lines():
    """If `lean --json` ever emits a non-JSON line (warnings on stderr
    that bled through, etc.), the parser must not crash and should
    surface the text as informational output."""
    runner = _make_runner_with_wsl()
    stdout = (
        "warning: ignored (something)\n"
        '{"severity":"information","data":"ok","pos":{"line":1,"column":0}}\n'
    )
    with patch("lean_runner.subprocess.run", return_value=_completed(stdout=stdout)):
        result = runner.run("theorem t : True := trivial")

    assert result.success is True
    assert "warning: ignored" in result.output
    assert "ok" in result.output


def test_run_wsl_heredoc_delimiter_is_per_invocation_random():
    """Two back-to-back invocations must produce two different heredoc
    delimiters — and the WSL subprocess command must contain neither the
    static `LEANRUNNER_EOF` marker nor any other delimiter that could
    be hit by an attacker-controlled notebook line (NanoClaw review
    #17621 finding #1)."""
    runner = _make_runner_with_wsl()

    captured = []

    def fake_run(*args, **kwargs):
        a = args[0] if args else kwargs.get("args")
        captured.append(a)
        # The first wsl invocation per `_run_wsl` is the TMPDIR probe;
        # return `/tmp` so the file path looks right.
        if isinstance(a, list) and a and a[0] == "wsl" and len(a) >= 7 and "echo ${TMPDIR:-/tmp}" in a[-1]:
            return _completed(stdout="/tmp\n")
        return _completed(
            stdout='{"severity":"information","data":"ok","pos":{"line":1,"column":0}}\n'
        )

    with patch("lean_runner.subprocess.run", side_effect=fake_run):
        runner.run("theorem t : True := trivial")
        runner.run("theorem t : True := trivial")

    # Two invocations → two heredoc commands (each `cat > ... <<'EOM' ... EOM`).
    # The heredoc body is the last positional arg of `subprocess.run`.
    bash_cmds = [
        a[-1] for a in captured
        if isinstance(a, list) and a and a[0] == "wsl"
        and len(a) >= 7 and "cat > " in a[-1]
    ]
    assert len(bash_cmds) >= 2, (
        f"expected ≥2 heredoc commands, got {len(bash_cmds)}: {captured}"
    )
    # The static marker must be gone.
    assert all("LEANRUNNER_EOF" not in cmd for cmd in bash_cmds), (
        f"static marker leaked: {bash_cmds}"
    )
    # Every invocation carries a per-call marker, and they differ.
    import re
    markers = []
    for cmd in bash_cmds:
        markers.extend(re.findall(r"LEANRUNNER_EOM_[0-9a-f]{8}", cmd))
    assert len(markers) >= 2, f"expected ≥2 EOM markers, got {markers}"
    # The same marker appears twice within one invocation (open + close
    # heredoc line), so check uniqueness of DISTINCT markers across all
    # invocations — and that there is at least one per invocation.
    distinct_markers = set(markers)
    assert len(distinct_markers) >= 2, (
        f"expected ≥2 distinct EOM markers across invocations, got {distinct_markers}"
    )
    # Per invocation, the marker is the same on both the open and close
    # heredoc line (this is the whole point of the hardening: the
    # attacker cannot split the heredoc because the marker is fixed).
    for cmd in bash_cmds:
        cmd_markers = re.findall(r"LEANRUNNER_EOM_[0-9a-f]{8}", cmd)
        assert len(cmd_markers) == 2, (
            f"expected exactly 2 occurrences of the marker per cmd "
            f"(open + close), got {len(cmd_markers)}: {cmd_markers}"
        )
        assert cmd_markers[0] == cmd_markers[1], (
            f"open/close markers differ within a single invocation: "
            f"{cmd_markers}"
        )


def test_run_wsl_heredoc_delimiter_collision_is_refused():
    """If the randomly-generated delimiter happens to occur as a line in
    the wrapped code (astronomically unlikely but checked), the runner
    must refuse with a failure LeanResult rather than letting the heredoc
    close prematurely and execute the remainder as raw bash in WSL."""
    import lean_runner
    runner = _make_runner_with_wsl()

    real_uuid = lean_runner.uuid.uuid4
    seq = iter(["0123abcd"] * 100)  # force a deterministic collision marker

    def fake_uuid4():
        return type("U", (), {"hex": property(lambda self: next(seq))})()

    # Patch uuid so we can force the marker into the user code.
    monkey_marker = "LEANRUNNER_EOM_0123abcd"
    user_code = f"-- prelude\n{monkey_marker}\n#eval 1 + 1\n"

    with patch.object(lean_runner.uuid, "uuid4", side_effect=lambda: type(
        "U", (), {"hex": property(lambda self: "0123abcd")}
    )()):
        with patch("lean_runner.subprocess.run", return_value=_completed()):
            result = runner.run(user_code)

    assert result.success is False
    assert "Heredoc delimiter collision" in result.errors
    assert result.exit_code == -1


def test_check_wsl_available_does_not_require_repl():
    """`_check_wsl_available` must accept a WSL where only `lean`
    is installed (the WSL backend no longer uses `repl` since #17612).
    It must NOT shell out to `which repl` and treat its absence as a
    failure (NanoClaw review #17621 finding #2)."""
    import lean_runner
    runner = _make_runner_with_wsl()
    seen_cmds = []

    def fake_run(*args, **kwargs):
        cmd_str = args[0] if args else kwargs.get("args")
        if isinstance(cmd_str, list) and cmd_str and cmd_str[0] == "wsl":
            seen_cmds.append(cmd_str[-1])
        return _completed(stdout="/home/user/.elan/bin/lean\n")

    with patch("lean_runner.subprocess.run", side_effect=fake_run):
        ok = runner._check_wsl_available()

    assert ok is True
    # The shell command must not mention `repl`.
    assert all("repl" not in c for c in seen_cmds), (
        f"_check_wsl_available still probes for `repl`: {seen_cmds}"
    )
