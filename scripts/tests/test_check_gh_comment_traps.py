"""Offline tests for the gh posting-trap detector (#16866 member 1, #17326 member 2).

Member 1 positives are the REAL trapped bodies measured in #16866 (redacted to
their path shapes); member 2 positive is the #17270 payload shape with the real
body escaped inside the JSON envelope. Negatives cover @mentions, real bodies
with paths inside prose, fenced JSON snippets in prose (the structural
predicate must require the WHOLE body to be the object), and both members on
PR bodies.
"""
from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "ci" / "check_gh_comment_traps.py"

spec = importlib.util.spec_from_file_location("check_gh_comment_traps", SCRIPT)
mod = importlib.util.module_from_spec(spec)
sys.modules["check_gh_comment_traps"] = mod
spec.loader.exec_module(mod)


# --- positives: the three measured occurrences (#16866) ---
def test_trap_linux_tmp_path():
    assert mod.classify_body("@/tmp/a16766.md")


def test_trap_windows_backslash_path():
    assert mod.classify_body("@C:\\Users\\jsboi\\AppData\\Local\\Temp/a16766.md")


def test_trap_windows_path_newline_padded():
    assert mod.classify_body("@C:\\Users\\jsboi\\AppData\\Local\\Temp/a16723.md\n")


# --- negatives: look-alikes that must NOT flag ---
def test_mention_is_not_a_trap():
    assert not mod.classify_body("@clusterManager-Myia peux-tu relire la PR ?")


def test_real_body_mentioning_a_path_in_prose():
    assert not mod.classify_body(
        "Verifie dans scripts/ci/check_umbrella_freshness.py avant de conclure."
    )


def test_at_path_inside_longer_body():
    assert not mod.classify_body(
        "Le fichier @/tmp/report.md contient le detail complet de la mesure, "
        "voir la section 3 pour le verdict par cellule."
    )


def test_long_path_body_above_floor():
    # > 100 chars: not the silent-failure shape (a real file body that posted)
    long_path = "@" + "/".join(f"d{i}" for i in range(40)) + "/body.md"
    assert len(long_path) >= 100
    assert not mod.classify_body(long_path)


def test_empty_body():
    assert not mod.classify_body("")
    assert not mod.classify_body(None)


# --- scan wiring ---
def test_scan_reports_id_user_and_url():
    comments = [
        {"id": 1, "body": "[CLAIMED] legit", "user": {"login": "a"}, "html_url": "u1"},
        {"id": 2, "body": "@/tmp/x.md", "user": {"login": "b"}, "html_url": "u2"},
    ]
    trapped = mod.scan(comments)
    assert len(trapped) == 1
    assert trapped[0]["id"] == 2
    assert trapped[0]["user"] == "b"
    assert trapped[0]["url"] == "u2"
    assert trapped[0]["kind"] == "literal-path"


# --- member 2: the whole payload JSON published as the body (#17326, #17270) ---

def _payload_body() -> str:
    # The #17270 shape: long, plausible, and the real body is ESCAPED inside
    # the "body" value of the JSON envelope -- no published line is a body line.
    import json
    return json.dumps({
        "title": "feat(ci,#17097): mesure stable de la couverture proof-integrity",
        "body": "Grain: MED/guard -- lane myia-po-2023:CoursIA-2 -- prev: MED/docs #17228\n\n## Resume\n\n...",
    })


def test_payload_body_is_trapped_and_inner_extracted():
    inner = mod.classify_payload_body(_payload_body())
    assert inner is not None
    assert inner.startswith("Grain: MED/guard -- lane myia-po-2023:CoursIA-2")


def test_scan_flags_payload_comment_with_inner_first_line():
    comments = [
        {"id": 7, "body": _payload_body(), "user": {"login": "c"}, "html_url": "u7"},
    ]
    trapped = mod.scan(comments)
    assert len(trapped) == 1
    assert trapped[0]["kind"] == "json-payload"
    assert trapped[0]["inner_first_line"].startswith("Grain: MED/guard")
    assert trapped[0]["inner_len"] > 50  # a real body, not a stub (instance: 3695)


# --- member 2 negatives: a body that merely CONTAINS JSON is not the trap ---
def test_fenced_json_snippet_in_prose_is_not_the_trap():
    body = (
        "Diagnostic : le corps publie etait\n\n```json\n"
        '{"body": "Grain: ..."}\n'
        "```\n\nmais le corps source etait correct."
    )
    assert mod.classify_payload_body(body) is None


def test_json_without_string_body_key_is_not_the_trap():
    assert mod.classify_payload_body('{"title": "x", "body": null}') is None
    assert mod.classify_payload_body('{"title": "x"}') is None


def test_json_array_or_scalar_is_not_the_trap():
    assert mod.classify_payload_body('["body", "title"]') is None
    assert mod.classify_payload_body('42') is None


def test_plain_body_and_empty_stay_clean():
    assert mod.classify_payload_body("Grain: MED/guard -- a perfectly normal body") is None
    assert mod.classify_payload_body("") is None
    assert mod.classify_payload_body(None) is None


# --- PR body scan: both members, keyed by number ---
def test_scan_prs_flags_payload_body():
    prs = [
        {"number": 17270, "title": "t", "body": _payload_body(), "html_url": "p1"},
        {"number": 1, "title": "healthy", "body": "Grain: MED/guard -- ok", "html_url": "p2"},
    ]
    trapped = mod.scan_prs(prs)
    assert len(trapped) == 1
    assert trapped[0]["number"] == 17270
    assert trapped[0]["kind"] == "json-payload"
    assert trapped[0]["inner_first_line"].startswith("Grain:")


def test_scan_prs_flags_literal_path_body():
    # gh pr create -b @f.md lands the same literal-path member on a PR body
    prs = [{"number": 5, "title": "t", "body": "@/tmp/body.md", "html_url": "p"}]
    trapped = mod.scan_prs(prs)
    assert len(trapped) == 1
    assert trapped[0]["kind"] == "literal-path"
