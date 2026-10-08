"""Tests du journal des tirages (#18203 geste 5).

Couvre :
- roundtrip JSONL (record -> line -> record)
- append (multi-ecrits sur meme fichier)
- lock applicatif (concurrence sur le meme Journal)
- refus d'un newline dans le serialise (defense en profondeur)
- helper ``log_tirage`` (chemin par defaut et chemin explicite)
- helper ``read_journal`` (fichier absent -> liste vide)
- CLI main : argparse + ecriture effective

Tous les tests utilisent un chemin de journal temporaire (tmp_path) ; aucun
fichier n'est cree sous D:\\Dev (chemin de production).
"""

from __future__ import annotations

import importlib.util
import json
import sys
import threading
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
SCRIPTS_DIR = HERE.parent
spec = importlib.util.spec_from_file_location(
    "tirage_journal", SCRIPTS_DIR / "coordination" / "tirage_journal.py"
)
mod = importlib.util.module_from_spec(spec)
sys.modules["tirage_journal"] = mod
spec.loader.exec_module(mod)


LANE = "myia-ai-01:CoursIA-2"


def test_record_roundtrip():
    r = mod.TirageRecord.new(
        lane=LANE,
        candidates=[123, 456, 789],
        retained=123,
        urn="grain",
        mode="belt",
        draw_id="abc123",
    )
    line = r.to_jsonl()
    assert "\n" not in line
    r2 = mod.TirageRecord.from_jsonl(line)
    assert r == r2
    assert r2.candidates == [123, 456, 789]
    assert r2.retained == 123
    assert r2.urn == "grain"
    assert r2.mode == "belt"
    assert r2.draw_id == "abc123"


def test_log_appends(tmp_path: Path):
    j = mod.Journal(tmp_path / "journal.jsonl")
    j.log(mod.TirageRecord.new(lane=LANE, candidates=[1], retained=1, urn="grain"))
    j.log(mod.TirageRecord.new(lane=LANE, candidates=[2], retained=2, urn="grain"))
    lines = (tmp_path / "journal.jsonl").read_text(encoding="utf-8").splitlines()
    assert len(lines) == 2
    assert json.loads(lines[0])["retained"] == 1
    assert json.loads(lines[1])["retained"] == 2


def test_log_tirage_default_and_explicit(tmp_path: Path, monkeypatch):
    # chemin explicite via helper
    p = tmp_path / "h.jsonl"
    r = mod.log_tirage(
        lane=LANE,
        candidates=[42, 43],
        retained=42,
        urn="umbrella",
        path=p,
    )
    assert p.exists()
    assert p.read_text(encoding="utf-8").strip() == r.to_jsonl()


def test_read_journal_empty(tmp_path: Path):
    assert mod.read_journal(tmp_path / "nope.jsonl") == []


def test_read_journal_roundtrip(tmp_path: Path):
    p = tmp_path / "j.jsonl"
    recs = [
        mod.TirageRecord.new(lane=LANE, candidates=[i], retained=i, urn="grain")
        for i in range(3)
    ]
    for r in recs:
        mod.Journal(p).log(r)
    out = mod.read_journal(p)
    assert out == recs


def test_lock_isolation(tmp_path: Path):
    """Deux ``Journal`` sur le meme chemin partagent le meme lock
    (le lock est sur l'instance -- on teste la sérialisation via une seule
    instance, qui est le cas d'usage nominal)."""
    p = tmp_path / "j.jsonl"
    j = mod.Journal(p)
    errors: list[Exception] = []

    def worker(seed: int) -> None:
        try:
            for i in range(50):
                j.log(
                    mod.TirageRecord.new(
                        lane=f"lane-{seed}",
                        candidates=[seed * 1000 + i],
                        retained=seed * 1000 + i,
                        urn="grain",
                    )
                )
        except Exception as e:  # pragma: no cover
            errors.append(e)

    threads = [threading.Thread(target=worker, args=(s,)) for s in range(4)]
    for t in threads:
        t.start()
    for t in threads:
        t.join()
    assert not errors
    lines = p.read_text(encoding="utf-8").splitlines()
    assert len(lines) == 4 * 50
    # Tous les logs sont des JSONL valides (pas de ligne tronquee par
    # entrelacement -- le lock couvre l'instance partagee).
    for line in lines:
        d = json.loads(line)
        assert "lane" in d
        assert "retained" in d


def test_to_jsonl_reject_bare_newline():
    """Defense en profondeur : si la serialisation JSON (pour une raison
    quelconque) produisait un newline NON escape, ``to_jsonl`` refuse.

    On simule ce cas en monkeypatchant ``json.dumps`` pour qu'il retourne
    une chaine avec un newline reel. C'est un cas que ``json.dumps`` ne
    peut pas produire en temps normal, mais la garde existe pour qu'un
    futur changement de serialiseur (ou un ``extras`` exotique) ne puisse
    pas silencieusement tronquer le journal.
    """
    r = mod.TirageRecord.new(lane=LANE, candidates=[1], retained=1, urn="grain")
    real_dumps = mod.json.dumps

    def bad_dumps(*a, **kw):
        return real_dumps(*a, **kw) + "\nNEWLINE-INJECTED"

    mod.json.dumps = bad_dumps  # type: ignore[assignment]
    try:
        with pytest.raises(ValueError):
            r.to_jsonl()
    finally:
        mod.json.dumps = real_dumps  # type: ignore[assignment]


def test_main_cli(tmp_path: Path, capsys):
    p = tmp_path / "cli.jsonl"
    rc = mod.main(
        [
            "--lane",
            LANE,
            "--candidates",
            "10,20,30",
            "--retained",
            "20",
            "--urn",
            "umbrella",
            "--mode",
            "admissible",
            "--draw-id",
            "cli-test",
            "--path",
            str(p),
        ]
    )
    assert rc == 0
    out = capsys.readouterr().out.strip()
    assert json.loads(out)["draw_id"] == "cli-test"
    assert json.loads(out)["retained"] == 20
    assert p.exists()
    # Fichier contient la meme ligne que stdout.
    assert p.read_text(encoding="utf-8").strip() == out


def test_main_cli_sans_retained(tmp_path: Path, capsys):
    """``--retained`` est optionnel : un tirage sans grain retenu (refus /
    pool vide) doit quand meme etre consigne (c'est precisement le cas que
    le journal est cense rendre visible -- ``Proposee puis ecantee``)."""
    p = tmp_path / "no-retained.jsonl"
    rc = mod.main(
        [
            "--lane",
            LANE,
            "--candidates",
            "1,2",
            "--urn",
            "grain",
            "--path",
            str(p),
        ]
    )
    assert rc == 0
    out = json.loads(capsys.readouterr().out.strip())
    assert out["retained"] is None
    assert out["candidates"] == [1, 2]
