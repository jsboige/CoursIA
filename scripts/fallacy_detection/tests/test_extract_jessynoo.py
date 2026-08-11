#!/usr/bin/env python3
"""Tests pour ``scripts/fallacy_detection/extract_jessynoo_fallacy.py`` — Phase 1
livrable 3 de l'EPIC #10355 (extraction + anonymisation du corpus r/fallacy
depuis un Reddit Data Export).

Hermetique : stdlib only. Synthetise un .zip de Data Export dans tmp_path avec
des commentaires/posts fallacy ET non-fallacy + des mentions u/ de tiers, puis
verifie le filtrage, l'anonymisation stable, et la suppression des colonnes PII.
"""

import csv
import io
import sys
import zipfile
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
SCRIPTS_DIR = HERE.parent.parent  # scripts/
sys.path.insert(0, str(SCRIPTS_DIR))

from fallacy_detection.extract_jessynoo_fallacy import (  # noqa: E402
    OUT_FIELDS,
    U_MENTION_RE,
    anonymize_text,
    build_user_index,
    extract,
    main,
)


# ---------------------------------------------------------------------------
# Helpers — synthetic Reddit Data Export .zip
# ---------------------------------------------------------------------------

COMMENT_HEADER = "id,permalink,date,ip,subreddit,gildings,gildings_silver,gildings_supergold,link,parent,body,media"
POST_HEADER = "id,permalink,date,ip,subreddit,gildings,title,url,body"


def _csv(header, rows):
    """Build a CSV string from a header + list of row-lists."""
    out = io.StringIO()
    w = csv.writer(out, lineterminator="\n")
    w.writerow(header.split(","))
    for r in rows:
        w.writerow(r)
    return out.getvalue()


def _write_dump(tmp_path, comment_rows, post_rows):
    """Write a synthetic Data Export .zip with comments.csv + posts.csv."""
    zpath = tmp_path / "export.zip"
    with zipfile.ZipFile(zpath, "w") as z:
        z.writestr("comments.csv", _csv(COMMENT_HEADER, comment_rows))
        z.writestr("posts.csv", _csv(POST_HEADER, post_rows))
    return zpath


# ---------------------------------------------------------------------------
# build_user_index — collect third-party names, deterministic
# ---------------------------------------------------------------------------

def test_build_user_index_collects_names():
    rows = [
        {"body": "thanks u/ralph-j and u/onctech", "title": ""},
        {"body": "see u/SMGB_NeonYoshi here", "title": "u/gd2shoe wrote"},
    ]
    names = build_user_index(rows)
    assert names == {"ralph-j", "onctech", "SMGB_NeonYoshi", "gd2shoe"}


def test_build_user_index_ignores_short_mentions():
    # u/ab (2 chars) below the 3-char floor -> ignored (avoids URL fragments).
    rows = [{"body": "see u/ab and u/realuser", "title": ""}]
    assert build_user_index(rows) == {"realuser"}


# ---------------------------------------------------------------------------
# anonymize_text — stable replacement, owner kept
# ---------------------------------------------------------------------------

def test_anonymize_text_replaces_third_party():
    mapping = {"ralph-j": "[USER_1]", "onctech": "[USER_2]"}
    out = anonymize_text("thanks u/ralph-j and u/onctech", mapping)
    assert out == "thanks u/[USER_1] and u/[USER_2]"


def test_anonymize_text_keeps_unmapped_verbatim():
    mapping = {"ralph-j": "[USER_1]"}
    out = anonymize_text("u/ralph-j and u/someone_else", mapping)
    assert out == "u/[USER_1] and u/someone_else"


def test_anonymize_text_none_safe():
    assert anonymize_text(None, {}) is None
    assert anonymize_text("", {}) == ""


# ---------------------------------------------------------------------------
# extract — full pipeline (filter + anonymize + PII drop)
# ---------------------------------------------------------------------------

def test_extract_filters_fallacy_only(tmp_path):
    z = _write_dump(
        tmp_path,
        comment_rows=[
            ["c1", "https://reddit.com/r/fallacy/x", "2020-01-01 00:00:00 UTC",
             "1.2.3.4", "fallacy", "0", "0", "0", "l", "", "body1", ""],
            ["c2", "https://reddit.com/r/france/x", "2020-01-02 00:00:00 UTC",
             "1.2.3.4", "france", "0", "0", "0", "l", "", "body2", ""],
        ],
        post_rows=[],
    )
    rows, n = extract(str(z), tmp_path / "out.csv")
    assert len(rows) == 1
    assert rows[0]["id"] == "c1"
    assert rows[0]["kind"] == "comment"
    assert n == 0  # no u/ mentions


def test_extract_drops_pii_columns(tmp_path):
    z = _write_dump(
        tmp_path,
        comment_rows=[
            ["c1", "https://reddit.com/r/fallacy/x", "2020-01-01 00:00:00 UTC",
             "10.0.0.1", "fallacy", "1", "0", "0", "link1", "par", "body", "med"],
        ],
        post_rows=[],
    )
    rows, _ = extract(str(z), tmp_path / "out.csv")
    assert "ip" not in rows[0]
    assert "permalink" not in rows[0]
    assert "link" not in rows[0]
    assert "gildings" not in rows[0]
    # Schema est exactement OUT_FIELDS.
    assert set(rows[0].keys()) == set(OUT_FIELDS)


def test_extract_anonymizes_third_party_keeps_owner(tmp_path):
    z = _write_dump(
        tmp_path,
        comment_rows=[
            ["c1", "p", "2020-01-01 00:00:00 UTC", "", "fallacy",
             "0", "0", "0", "", "", "citing u/ralph-j and u/Jessynoo", ""],
        ],
        post_rows=[],
    )
    rows, n = extract(str(z), tmp_path / "out.csv", owner_handle="Jessynoo")
    assert n == 1  # ralph-j anonymized, Jessynoo kept
    assert "u/[USER_1]" in rows[0]["body"]
    assert "u/Jessynoo" in rows[0]["body"]  # owner self-attribution preserved
    assert "ralph-j" not in rows[0]["body"]


def test_extract_handles_posts_with_title_url(tmp_path):
    z = _write_dump(
        tmp_path,
        comment_rows=[],
        post_rows=[
            ["p1", "p", "2020-01-01 00:00:00 UTC", "", "fallacy",
             "0", "My post u/onctech", "https://example.com", "post body"],
        ],
    )
    rows, n = extract(str(z), tmp_path / "out.csv")
    assert len(rows) == 1
    assert rows[0]["kind"] == "post"
    assert rows[0]["title"] == "My post u/[USER_1]"
    assert rows[0]["url"] == "https://example.com"
    assert rows[0]["body"] == "post body"
    assert n == 1


def test_extract_anonymization_deterministic_across_runs(tmp_path):
    z = _write_dump(
        tmp_path,
        comment_rows=[
            ["c1", "p", "2020", "", "fallacy", "0", "0", "0", "", "",
             "u/zebra and u/apple", ""],
        ],
        post_rows=[],
    )
    r1, _ = extract(str(z), tmp_path / "o1.csv")
    r2, _ = extract(str(z), tmp_path / "o2.csv")
    # Sorted mapping => apple=[USER_1], zebra=[USER_2], stable across runs.
    assert r1[0]["body"] == r2[0]["body"]
    assert r1[0]["body"] == "u/[USER_2] and u/[USER_1]"


def test_extract_no_fallacy_returns_empty(tmp_path):
    z = _write_dump(
        tmp_path,
        comment_rows=[["c1", "p", "2020", "", "france", "0", "0", "0", "", "", "b", ""]],
        post_rows=[],
    )
    rows, n = extract(str(z), tmp_path / "out.csv")
    assert rows == []
    assert n == 0


# ---------------------------------------------------------------------------
# main — exit codes + env-gated path
# ---------------------------------------------------------------------------

def test_main_missing_env_returns_2(tmp_path, monkeypatch):
    monkeypatch.delenv("JESSYNOO_DUMP_PATH", raising=False)
    rc = main(["--out", str(tmp_path / "o.csv")])
    assert rc == 2


def test_main_missing_dump_returns_2(tmp_path, monkeypatch):
    monkeypatch.setenv("JESSYNOO_DUMP_PATH", str(tmp_path / "nonexistent.zip"))
    rc = main(["--out", str(tmp_path / "o.csv")])
    assert rc == 2


def test_main_no_fallacy_returns_1(tmp_path, monkeypatch):
    z = _write_dump(
        tmp_path,
        comment_rows=[["c1", "p", "2020", "", "france", "0", "0", "0", "", "", "b", ""]],
        post_rows=[],
    )
    monkeypatch.setenv("JESSYNOO_DUMP_PATH", str(z))
    rc = main(["--out", str(tmp_path / "o.csv")])
    assert rc == 1


def test_main_writes_anonymized_csv(tmp_path, monkeypatch):
    z = _write_dump(
        tmp_path,
        comment_rows=[
            ["c1", "p", "2020-01-01 00:00:00 UTC", "9.9.9.9", "fallacy",
             "0", "0", "0", "", "", "thanks u/ralph-j", ""],
        ],
        post_rows=[],
    )
    monkeypatch.setenv("JESSYNOO_DUMP_PATH", str(z))
    out = tmp_path / "o.csv"
    rc = main(["--out", str(out)])
    assert rc == 0
    with out.open(encoding="utf-8") as fh:
        rows = list(csv.DictReader(fh))
    assert len(rows) == 1
    assert rows[0]["body"] == "thanks u/[USER_1]"
    assert "ralph-j" not in out.read_text(encoding="utf-8")  # no raw name in file
    assert "ip" not in rows[0]
