"""Tests du journal des tirages (#18203 geste 5).

Couvre :
- roundtrip JSONL (record -> line -> record)
- append (multi-ecrits sur meme fichier)
- concurrence : plusieurs **instances** puis plusieurs **processus** sur le
  meme fichier, avec des records au-dela de 4096 octets -- N lignes JSONL
  completes, ni perdues ni entrelacees
- helper ``log_tirage`` (chemin par defaut et chemin explicite, voie verrouillee)
- resolution du chemin par defaut (``TIRAGE_JOURNAL_PATH`` puis state dir)
- refus d'un newline dans le serialise (defense en profondeur)
- helper ``read_journal`` (fichier absent -> liste vide)
- CLI main : argparse + ecriture effective

Tous les tests ecrivent sous ``tmp_path`` ; aucun fichier n'est cree sous le
state dir reel de la machine ni sous le clone.
"""

from __future__ import annotations

import importlib.util
import json
import subprocess
import sys
import threading
import textwrap
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
SCRIPTS_DIR = HERE.parent
MODULE_PATH = SCRIPTS_DIR / "coordination" / "tirage_journal.py"

spec = importlib.util.spec_from_file_location("tirage_journal", MODULE_PATH)
mod = importlib.util.module_from_spec(spec)
sys.modules["tirage_journal"] = mod
spec.loader.exec_module(mod)


LANE = "myia-ai-01:CoursIA-2"

# Un record qui depasse PIPE_BUF (4096 o) : c'est la taille a partir de
# laquelle l'atomicite d'un append en mode texte n'est plus garantie. Elle
# sert de jeu de donnees aux tests de concurrence, parce que c'est
# precisement la ou le verrou d'instance cede.
BIG_CANDIDATES = list(range(100_000, 101_200))


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


def test_big_record_exceeds_pipe_buf():
    """Le jeu de donnees des tests de concurrence depasse reellement 4096 o."""
    r = mod.TirageRecord.new(
        lane=LANE, candidates=BIG_CANDIDATES, retained=100_000, urn="grain"
    )
    assert len(r.to_jsonl().encode("utf-8")) > 4096


def test_log_appends(tmp_path: Path):
    j = mod.Journal(tmp_path / "journal.jsonl")
    j.log(mod.TirageRecord.new(lane=LANE, candidates=[1], retained=1, urn="grain"))
    j.log(mod.TirageRecord.new(lane=LANE, candidates=[2], retained=2, urn="grain"))
    lines = (tmp_path / "journal.jsonl").read_text(encoding="utf-8").splitlines()
    assert len(lines) == 2
    assert json.loads(lines[0])["retained"] == 1
    assert json.loads(lines[1])["retained"] == 2


def test_log_uses_file_lock(tmp_path: Path):
    """``Journal.log`` passe bien par un verrou fichier compagnon.

    Sans cela le test de concurrence multiprocessus ne pourrait pas passer ;
    ce test verrouille la *voie* (fichier compagnon cree, distinct du journal).
    """
    p = tmp_path / "j.jsonl"
    j = mod.Journal(p)
    assert j.lock_path == Path(str(p) + ".lock")
    assert j.lock_path != p
    j.log(mod.TirageRecord.new(lane=LANE, candidates=[1], retained=1, urn="grain"))
    assert j.lock_path.exists()


def test_log_tirage_explicit_path(tmp_path: Path):
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
    # Le helper emprunte la meme voie verrouillee que Journal.log.
    assert Path(str(p) + ".lock").exists()


def test_log_tirage_default_path_from_env(tmp_path: Path, monkeypatch):
    """Le chemin par defaut est resolu a l'appel, pas fige a l'import."""
    p = tmp_path / "env.jsonl"
    monkeypatch.setenv("TIRAGE_JOURNAL_PATH", str(p))
    r = mod.log_tirage(lane=LANE, candidates=[7], retained=7, urn="grain")
    assert p.exists()
    assert mod.read_journal()[-1] == r


def test_default_journal_path_resolution(tmp_path: Path, monkeypatch):
    """``TIRAGE_JOURNAL_PATH`` prime ; sinon le journal vit sous le state dir."""
    monkeypatch.setenv("TIRAGE_JOURNAL_PATH", str(tmp_path / "override.jsonl"))
    assert mod.default_journal_path() == tmp_path / "override.jsonl"

    monkeypatch.delenv("TIRAGE_JOURNAL_PATH")
    monkeypatch.setenv("LOCALAPPDATA", str(tmp_path))
    monkeypatch.delenv("XDG_STATE_HOME", raising=False)
    assert mod.default_journal_path() == (
        tmp_path / "CoursIA" / "tirage_journal" / "journal.jsonl"
    )

    # POSIX : LOCALAPPDATA absent, XDG_STATE_HOME prend le relais.
    monkeypatch.delenv("LOCALAPPDATA")
    monkeypatch.setenv("XDG_STATE_HOME", str(tmp_path / "state"))
    assert mod.default_journal_path() == (
        tmp_path / "state" / "CoursIA" / "tirage_journal" / "journal.jsonl"
    )


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


def test_concurrent_instances_same_file(tmp_path: Path):
    """Plusieurs ``Journal`` -- un par thread -- sur le meme chemin.

    Chaque thread construit **sa propre instance** : c'est le cas que le
    journal doit couvrir, et celui qu'un verrou d'instance ne couvre pas.
    """
    p = tmp_path / "j.jsonl"
    errors: list[Exception] = []
    n_threads, n_each = 4, 25

    def worker(seed: int) -> None:
        try:
            j = mod.Journal(p)  # une instance par thread
            for i in range(n_each):
                j.log(
                    mod.TirageRecord.new(
                        lane=f"lane-{seed}",
                        candidates=[seed * 1000 + i],
                        retained=seed * 1000 + i,
                        urn="grain",
                        draw_id=f"{seed}-{i}",
                    )
                )
        except Exception as e:  # pragma: no cover
            errors.append(e)

    threads = [threading.Thread(target=worker, args=(s,)) for s in range(n_threads)]
    for t in threads:
        t.start()
    for t in threads:
        t.join()
    assert not errors

    lines = p.read_text(encoding="utf-8").splitlines()
    assert len(lines) == n_threads * n_each
    seen = [json.loads(line)["draw_id"] for line in lines]
    assert sorted(seen) == sorted(
        f"{s}-{i}" for s in range(n_threads) for i in range(n_each)
    )


WORKER_SRC = textwrap.dedent(
    """
    \"\"\"Ecrit n records (candidats nombreux -> ligne > 4096 o) dans le journal.\"\"\"
    import importlib.util
    import sys
    from pathlib import Path

    module_path, journal_path, tag, n_each, n_candidates = sys.argv[1:6]

    spec = importlib.util.spec_from_file_location("tirage_journal", module_path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules["tirage_journal"] = mod
    spec.loader.exec_module(mod)

    cands = list(range(100_000, 100_000 + int(n_candidates)))
    for i in range(int(n_each)):
        mod.log_tirage(
            lane="proc-" + tag,
            candidates=cands,
            retained=int(tag) * 1000 + i,
            urn="grain",
            draw_id=tag + "-" + str(i),
            path=journal_path,
        )
    """
)


def test_concurrent_processes_same_file(tmp_path: Path):
    """Plusieurs **processus** sur le meme fichier, records > 4096 octets.

    C'est le cas que le module annonce couvrir (« plusieurs lanes en
    parallele ») et que seul un verrou fichier du systeme peut tenir : les
    processus ne partagent aucun objet Python. Verifie N lignes JSONL
    completes -- ni perdues, ni entrelacees.
    """
    p = tmp_path / "j.jsonl"
    worker = tmp_path / "worker.py"
    worker.write_text(WORKER_SRC, encoding="utf-8")

    n_procs, n_each, n_candidates = 5, 12, len(BIG_CANDIDATES)
    procs = [
        subprocess.Popen(
            [
                sys.executable,
                str(worker),
                str(MODULE_PATH),
                str(p),
                str(tag),
                str(n_each),
                str(n_candidates),
            ],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        for tag in range(n_procs)
    ]
    for proc in procs:
        out, err = proc.communicate(timeout=180)
        assert proc.returncode == 0, err.decode("utf-8", "replace")

    lines = p.read_text(encoding="utf-8").splitlines()
    assert len(lines) == n_procs * n_each, "records perdus ou entrelaces"

    # Aucune ligne n'est tronquee : chacune est un JSON complet dont les
    # candidats sont tous la.
    ids: list[str] = []
    for line in lines:
        d = json.loads(line)  # leve si la ligne est coupee
        assert len(d["candidates"]) == n_candidates
        ids.append(d["draw_id"])
    assert len(set(ids)) == n_procs * n_each, "draw_id duplique ou absent"
    assert sorted(ids) == sorted(
        f"{tag}-{i}" for tag in range(n_procs) for i in range(n_each)
    )

    # Le jeu de donnees depassait bien PIPE_BUF : sans verrou fichier, ce test
    # serait celui ou l'entrelacement se produit.
    assert max(len(line.encode("utf-8")) for line in lines) > 4096


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
