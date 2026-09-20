"""Tests for check_local_path_waivers.py (#16780).

The POSITIVE CONTROL is the exact body of the #16670 incident comment
(since deleted by the user): a sweep that does not cover its own positive
control measures nothing (issue note). Everything here runs offline --
classify_body is pure by design.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from check_local_path_waivers import LONE_PATH_RE, PROFILE_PATH_RE, classify_body

# Verbatim from issue #16780 (the comment itself is gone from GitHub).
INCIDENT_BODY_16670 = "@C:\\Users\\jsboi\\AppData\\Local\\Temp/a16670.md"


def test_positive_control_16670_replayed():
    """The incident body trips BOTH rules -- without this, green means nothing."""
    assert classify_body(INCIDENT_BODY_16670) == ["LONE_PATH", "PROFILE_PATH"]


def test_lone_windows_path_without_at():
    assert classify_body(r"D:\Dev\CoursIA\body.md") == ["LONE_PATH"]


def test_lone_windows_path_outside_users():
    body = r"C:\Temp\pr_body.md"
    assert classify_body(body) == ["LONE_PATH"]


def test_lone_unix_path():
    assert classify_body("/tmp/a16780.md") == ["LONE_PATH"]


def test_lone_home_path():
    assert classify_body("~/.config/gh/body.md") == ["LONE_PATH"]


def test_profile_path_inside_prose():
    """Containment rule: a profile path buried in a normal body is flagged too."""
    body = (
        "Re-execut localement, log complet dans "
        r"C:\Users\MYIA\AppData\Local\Temp\run.log -- verdict EXEC_PROVED."
    )
    assert classify_body(body) == ["PROFILE_PATH"]


def test_normal_body_clean():
    body = (
        "[DONE] cycle -- PR #16844 livree, 26/26 cellules executees, "
        "0 erreur. Residuel: rerun DWELL."
    )
    assert classify_body(body) == []


def test_correct_body_file_usage_clean():
    """Documenting the CORRECT command must not trip either rule."""
    body = 'gh pr comment 12 --body-file "$TEMP/body.md"  # @file reste litteral avec --body'
    assert classify_body(body) == []


def test_https_url_not_a_path():
    assert classify_body("https://github.com/jsboige/CoursIA/pull/16670") == []


def test_url_host_users_not_flagged():
    """https://.../Users/... is a URL path, not a Windows profile segment."""
    assert classify_body("see https://example.com/Users/foo") == []


def test_empty_and_whitespace_clean():
    assert classify_body("") == []
    assert classify_body("   \n  ") == []


def test_regexes_directly():
    assert LONE_PATH_RE.match(INCIDENT_BODY_16670)
    assert PROFILE_PATH_RE.search(INCIDENT_BODY_16670)
    assert not LONE_PATH_RE.match("not a path, a sentence")
