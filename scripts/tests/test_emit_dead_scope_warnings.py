"""Tests for `scripts/ci/emit_dead_scope_warnings.py` (#13129).

The helper is the advisory-side bridge between `check_lane_claim.py`'s
`caller_empty_scope` and the GitHub Actions `::warning::` annotation
channel. The tests cover:
  - paths extraction from a PR body with a [CLAIMED] marker
  - paths extraction from a body with NO marker (no-ops)
  - the lane extractor (delegates to `grain_tag.extract_lane`)
  - end-to-end: a body with one dead and one live glob produces ONE annotation
  - end-to-end: a body whose every glob matches -> zero annotations
  - the proximity suggestion is a SEPARATE channel (stderr WARN from
    `check_lane_claim.py`'s `_lint_claim_events`, not this helper's stdout)
  - the lane-claim-guard workflow YAML stays structurally valid after the
    helper is wired in (regression pin for the heredoc/inline-python3 trap)
"""
from __future__ import annotations

import importlib.util
import json
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
SCRIPTS_CI = ROOT / "scripts" / "ci"
SCRIPTS = ROOT / "scripts"


def _load_helper():
    """Import `emit_dead_scope_warnings` as a module (no package install)."""
    spec = importlib.util.spec_from_file_location(
        "emit_dead_scope_warnings",
        SCRIPTS_CI / "emit_dead_scope_warnings.py",
    )
    assert spec and spec.loader
    mod = importlib.util.module_from_spec(spec)
    sys.path.insert(0, str(SCRIPTS))  # for grain_tag, check_lane_claim
    spec.loader.exec_module(mod)
    return mod


HELPER = _load_helper()


def test_extract_lane_reads_grain_tag_in_body():
    body = (
        "Grain: MED/tooling — lane myia-po-2024:CoursIA-2 — "
        "prev: MED/guard #13248\n\n"
        "Some prose.\n"
    )
    assert HELPER._extract_lane(body) == "myia-po-2024:CoursIA-2"


def test_extract_lane_empty_when_no_grain_tag():
    assert HELPER._extract_lane("Nothing here.") == ""


def test_extract_paths_in_body_parses_marker_clause():
    body = (
        "Some intro.\n"
        "[CLAIMED] lane myia-po-2024:CoursIA-2 -- "
        "paths: scripts/check_lane_claim.py, scripts/grain_tag.py\n\n"
        "Closing prose."
    )
    assert HELPER._extract_paths_in_body(body) == [
        "scripts/check_lane_claim.py",
        "scripts/grain_tag.py",
    ]


def test_extract_paths_in_body_empty_when_no_clause():
    assert HELPER._extract_paths_in_body("Just prose, no claim.") == []


def test_extract_paths_in_body_dedupes():
    body = "[CLAIMED] lane x -- paths: a.py, b.py, a.py"
    assert HELPER._extract_paths_in_body(body) == ["a.py", "b.py"]


def test_main_emits_one_warning_per_dead_glob(tmp_path, capsys):
    """End-to-end -- a body with one dead glob + one live glob yields ONE
    `::warning::` line. Live globs are intentionally silent (the channel
    is for hints, not noise)."""
    body_file = tmp_path / "body.txt"
    body_file.write_text(
        "Grain: MED/tooling — lane myia-po-2024:CoursIA-2 — "
        "prev: MED/guard #13248\n\n"
        "[CLAIMED] lane myia-po-2024:CoursIA-2 -- paths: "
        "scripts/notexist_typo.py, scripts/check_lane_claim.py\n",
        encoding="utf-8",
    )
    rc = HELPER.main(["--body-file", str(body_file)])
    assert rc == 0
    captured = capsys.readouterr()
    lines = [ln for ln in captured.out.splitlines() if ln.startswith("::warning")]
    assert len(lines) == 1
    assert "scripts/notexist_typo.py" in lines[0]
    assert "Dead scope glob (#13129)" in lines[0]


def test_main_no_warnings_when_all_globs_live(tmp_path, capsys):
    """Negative control -- a body whose every glob matches a tracked file
    produces ZERO annotations. Selectivity pin: the helper is a hint
    channel, not a no-op rewriter of every PR.

    #13486 : the JSON line is ALWAYS emitted (even when no suggestion
    fires), so the assertion pins ZERO annotations AND a JSON line whose
    suggestions list is empty.
    """
    body_file = tmp_path / "body.txt"
    body_file.write_text(
        "Grain: MED/tooling — lane myia-po-2024:CoursIA-2\n\n"
        "[CLAIMED] lane myia-po-2024:CoursIA-2 -- paths: "
        "scripts/check_lane_claim.py, scripts/grain_tag.py\n",
        encoding="utf-8",
    )
    rc = HELPER.main(["--body-file", str(body_file)])
    assert rc == 0
    captured = capsys.readouterr()
    annotation_lines = [
        ln for ln in captured.out.splitlines() if ln.startswith("::")
    ]
    assert annotation_lines == []
    json_lines = [
        ln for ln in captured.out.splitlines()
        if ln.startswith("{") and "dead_scope_suggestions" in ln
    ]
    assert len(json_lines) == 1
    assert json.loads(json_lines[0]) == {"dead_scope_suggestions": []}


def test_main_no_warnings_when_no_paths_clause(tmp_path, capsys):
    body_file = tmp_path / "body.txt"
    body_file.write_text(
        "Grain: MED/tooling — lane myia-po-2024:CoursIA-2\n\n"
        "Just prose, no claim marker.\n",
        encoding="utf-8",
    )
    rc = HELPER.main(["--body-file", str(body_file)])
    assert rc == 0
    # #13486 : no paths clause -> no scope to check -> no JSON emitted.
    assert capsys.readouterr().out.strip() == ""


def test_main_no_warnings_when_no_lane(tmp_path, capsys):
    body_file = tmp_path / "body.txt"
    body_file.write_text(
        "[CLAIMED] lane x -- paths: scripts/notexist.py\n",
        encoding="utf-8",
    )
    rc = HELPER.main(["--body-file", str(body_file)])
    assert rc == 0
    # #13486 : no declared lane -> nothing to anchor -> no JSON emitted.
    assert capsys.readouterr().out.strip() == ""


def test_missing_comma_tokens_returns_space_joined_paths():
    """#13129 motif B -- glob with whitespace and 2+ path-shaped tokens.

    Acceptance #13486 témoin : un glob espace-fusionne (`a.py b.py`) doit
    retourner la liste des tokens path-shaped (`['a.py', 'b.py']`).
    """
    assert HELPER._missing_comma_tokens("a.py b.py") == ["a.py", "b.py"]
    assert HELPER._missing_comma_tokens("scripts/check_lane_claim.py scripts/grain_tag.py") == [
        "scripts/check_lane_claim.py",
        "scripts/grain_tag.py",
    ]
    assert HELPER._missing_comma_tokens("docs/foo.md docs/bar.md docs/baz.md") == [
        "docs/foo.md",
        "docs/bar.md",
        "docs/baz.md",
    ]


def test_missing_comma_tokens_silent_on_healthy_globs():
    """#13129 motif B -- healthy glob must NOT trip the suggestion.

    Acceptance #13486 témoin : un glob sain (path without whitespace, or
    single token with whitespace but no path-shaped neighbor) doit
    retourner None -- silence.
    """
    # Single path, no whitespace: never a missing-comma candidate.
    assert HELPER._missing_comma_tokens("scripts/check_lane_claim.py") is None
    # Single token with surrounding whitespace-only: not a missing-comma
    # because only ONE path-shaped token, not two.
    assert HELPER._missing_comma_tokens("a.py not-a-path") is None
    # Empty / no whitespace: never.
    assert HELPER._missing_comma_tokens("") is None
    assert HELPER._missing_comma_tokens("scripts/check_lane_claim.py") is None


def test_missing_comma_tokens_silent_on_future_files():
    """#13129 motif B -- a glob that LOOKS like a future file (motif C) must
    NOT trip the missing-comma heuristic. Heuristic fires only on
    whitespace + 2+ path-shaped tokens -- a single 'to-create.py' is silent.

    Acceptance #13486 témoin : FUTUR (fichier a creer) -> silence. The
    test pins the heuristic: a future file is one token (no whitespace).
    """
    # Single future file: no whitespace, no missing-comma signal.
    assert HELPER._missing_comma_tokens("scripts/not_yet_created.py") is None
    # Single future dir: no whitespace.
    assert HELPER._missing_comma_tokens("scripts/new_module/") is None
    # Two tokens but only one path-shaped: not enough for the heuristic.
    assert HELPER._missing_comma_tokens("scripts/future.py just prose") is None


def test_main_emits_notice_for_missing_comma_glob(tmp_path, capsys):
    """End-to-end -- a body with a missing-comma glob yields ONE
    `::notice::` annotation (motif B, #13129) AND a structured
    `dead_scope_suggestions` JSON line with `hint=missing_comma` and the
    tokens list.

    Acceptance #13486 témoin : glob espace-fusionne -> hint virgule.
    Acceptance #13486 (3) : champ JSON expose + consomme.
    """
    body_file = tmp_path / "body.txt"
    body_file.write_text(
        "Grain: MED/tooling — lane myia-po-2024:CoursIA-2\n\n"
        "[CLAIMED] lane myia-po-2024:CoursIA-2 -- "
        "paths: scripts/check_lane_claim.py scripts/grain_tag.py\n",
        encoding="utf-8",
    )
    rc = HELPER.main(["--body-file", str(body_file)])
    assert rc == 0
    captured = capsys.readouterr()
    lines = [ln for ln in captured.out.splitlines() if ln.startswith("::")]
    # Exactly one notice (no warning -- the deadness is EXPLAINED by the typo).
    notices = [ln for ln in lines if ln.startswith("::notice")]
    warnings = [ln for ln in lines if ln.startswith("::warning")]
    assert len(notices) == 1, lines
    assert len(warnings) == 0, lines
    assert "Missing comma" in notices[0]
    assert "scripts/check_lane_claim.py" in notices[0]
    assert "scripts/grain_tag.py" in notices[0]

    # JSON line consumable by lane scripts.
    json_lines = [
        ln for ln in captured.out.splitlines()
        if ln.startswith("{") and "dead_scope_suggestions" in ln
    ]
    assert len(json_lines) == 1
    payload = json.loads(json_lines[0])
    assert "dead_scope_suggestions" in payload
    suggestions = payload["dead_scope_suggestions"]
    assert len(suggestions) == 1
    s = suggestions[0]
    assert s["hint"] == "missing_comma"
    assert "scripts/check_lane_claim.py" in s["tokens"]
    assert "scripts/grain_tag.py" in s["tokens"]


def test_main_emits_empty_suggestions_when_no_dead_globs(tmp_path, capsys):
    """#13486 (3) -- the JSON key is ALWAYS present in stdout, even when no
    suggestion fires. Consumers can rely on the key being there (cheap
    parser), not on its non-emptiness."""
    body_file = tmp_path / "body.txt"
    body_file.write_text(
        "Grain: MED/tooling — lane myia-po-2024:CoursIA-2\n\n"
        "[CLAIMED] lane myia-po-2024:CoursIA-2 -- "
        "paths: scripts/check_lane_claim.py, scripts/grain_tag.py\n",
        encoding="utf-8",
    )
    rc = HELPER.main(["--body-file", str(body_file)])
    assert rc == 0
    captured = capsys.readouterr()
    json_lines = [
        ln for ln in captured.out.splitlines()
        if ln.startswith("{") and "dead_scope_suggestions" in ln
    ]
    assert len(json_lines) == 1
    payload = json.loads(json_lines[0])
    assert payload == {"dead_scope_suggestions": []}


def test_missing_comma_heuristic_negative_control():
    """#13486 (4) -- faux négatif : muter la detection doit faire echouer
    le temoin. We hard-pin the heuristic: if someone WEAKENS the regex
    (e.g. drops `lean` from the tracked extensions) the test catches it.

    The regex `_PATHLIKE_TOKEN_RE` MUST treat a path ending in `.lean`
    as path-shaped. Mute the assertion to fail if `.lean` is dropped.
    """
    regex = HELPER._PATHLIKE_TOKEN_RE
    assert regex.match("MyIA.AI.Notebooks/GameTheory/game_theory_lean/Foo.lean"), (
        "_PATHLIKE_TOKEN_RE must recognize .lean as a tracked-file extension; "
        "if you dropped it from the alternation, motif B detection on Lean "
        "files (#13486) silently degrades."
    )


def test_lane_claim_guard_workflow_yaml_remains_valid():
    """Regression pin -- the YAML literal must parse cleanly after the
    helper is wired in. The c.579 first attempt broke the YAML by putting
    a multi-line `python3 -c "..."` in a YAML scalar; the helper extraction
    avoids that trap. Pin stays green for the foreseeable future.

    #13384 : la surface live est le step advisory lane-claim
    d'always-on-guards.yml (fusion des cinq gardes always-on) ;
    lane-claim-guard.yml est dormant mais reste verifie -- sa copie de
    reference ne doit pas diverger.
    """
    import yaml  # type: ignore

    for wf_name in ("always-on-guards.yml", "lane-claim-guard.yml"):
        wf = ROOT / ".github" / "workflows" / wf_name
        data = yaml.safe_load(wf.read_text(encoding="utf-8"))
        assert "jobs" in data, wf_name
        if wf_name == "lane-claim-guard.yml":
            assert "check-lane-claim-advisory" in data["jobs"]
            # The advisory job's `run:` block must mention the helper by path.
            advisory_run = "\n".join(
                step.get("run", "") for step in
                data["jobs"]["check-lane-claim-advisory"]["steps"]
            )
            assert "emit_dead_scope_warnings.py" in advisory_run
        else:
            # L'umbrella porte le run block porte verbatim : le helper doit
            # y figurer dans le step advisory lane-claim.
            umbrella_run = "\n".join(
                step.get("run", "") for job in data["jobs"].values()
                for step in job.get("steps", [])
            )
            assert "emit_dead_scope_warnings.py" in umbrella_run, (
                "always-on-guards.yml ne mentionne plus "
                "emit_dead_scope_warnings.py : le wiring #13129 des globs "
                "morts a ete perdu dans la fusion #13384"
            )
