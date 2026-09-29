"""Unicode path regressions for the PR perimeter guard (#16871)."""

from __future__ import annotations

import os
import sys
from types import SimpleNamespace

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import check_pr_perimeter as perimeter  # noqa: E402


ACCENTED_PATH = (
    "MyIA.AI.Notebooks/GenAI/SemanticKernel/"
    "Créateur de mail personnalisé.ipynb"
)
ASCII_PATH = "MyIA.AI.Notebooks/GenAI/FineTuning/FT-00c.ipynb"


def test_decode_nul_paths_preserves_unicode() -> None:
    raw = (ASCII_PATH + "\0" + ACCENTED_PATH + "\0").encode("utf-8")

    assert perimeter._decode_nul_paths(raw) == {ASCII_PATH, ACCENTED_PATH}


def test_classify_carried_uses_nul_output_for_unicode(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    files = [{"path": ASCII_PATH}, {"path": ACCENTED_PATH}]
    raw = (ASCII_PATH + "\0" + ACCENTED_PATH + "\0").encode("utf-8")
    calls: list[list[str]] = []

    monkeypatch.setattr(
        perimeter, "_resolve_base_pair", lambda _pr: ("head-sha", "origin/main")
    )
    monkeypatch.setattr(perimeter, "_base_age_hours", lambda *_args: 10)

    def fake_run(args: list[str], **_kwargs: object) -> SimpleNamespace:
        calls.append(args)
        return SimpleNamespace(returncode=0, stdout=raw, stderr=b"")

    monkeypatch.setattr(perimeter.subprocess, "run", fake_run)

    result = perimeter._classify_carried(16864, files)

    assert result.propres == files
    assert result.charries == []
    assert calls == [[
        "git", "diff", "--name-only", "-z", "origin/main", "head-sha", "--",
        ASCII_PATH, ACCENTED_PATH,
    ]]


def test_classify_carried_invalid_utf8_keeps_full_perimeter(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    files = [{"path": ASCII_PATH}, {"path": ACCENTED_PATH}]

    monkeypatch.setattr(
        perimeter, "_resolve_base_pair", lambda _pr: ("head-sha", "origin/main")
    )
    monkeypatch.setattr(
        perimeter.subprocess,
        "run",
        lambda *_args, **_kwargs: SimpleNamespace(
            returncode=0, stdout=b"valid.py\0\xff\0", stderr=b""
        ),
    )

    result = perimeter._classify_carried(16864, files)

    assert result.propres == files
    assert result.charries == []
    assert result.base_age_hours is None
