"""Offline tests for the `gh -f body=@file` trap detector (#16866).

The three positive fixtures are the REAL trapped bodies measured in #16866
(redacted to their path shapes); negatives cover @mentions, real bodies with
paths inside prose, and long path-like bodies above the length floor.
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
