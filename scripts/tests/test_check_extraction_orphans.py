"""Tests de la garde extraction-orphelins (#13902).

Chaque test monte un depot jouet en tmp_path, y rejoue un scenario
suppression/deplacement, et confronte le verdict de l'organe. Les scenarios
sont les formes mesurees sur l'incident fondateur (#27119) : lien same-dir
pendouillant, cle de baseline repo-relative, lien relatif ../, deplacement
solidaire exempt de faux positif, artefact derive exclu.
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))
import check_extraction_orphans as mod  # noqa: E402


def _git(repo: Path, *args: str) -> None:
    r = subprocess.run(
        ["git", "-C", str(repo), *args],
        capture_output=True, text=True, encoding="utf-8",
    )
    assert r.returncode == 0, f"git {args}: {r.stderr}"


def _commit_all(repo: Path, msg: str) -> None:
    _git(repo, "add", "-A")
    _git(repo, "-c", "user.email=t@t.t", "-c", "user.name=t", "commit", "-m", msg)


def _run(repo: Path, monkeypatch, head: str = "HEAD") -> tuple[int, dict]:
    monkeypatch.setattr(mod, "REPO_ROOT", str(repo))
    import io
    import contextlib
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        rc = mod.main(["--base", "HEAD~1", "--head", head, "--json"])
    return rc, json.loads(buf.getvalue())


def test_lien_same_dir_orphelin(tmp_path, monkeypatch):
    """Deplacement d'un carnet, voisin non deplace qui pointe dessus."""
    repo = tmp_path / "r1"
    repo.mkdir()
    _git(repo, "init", "-q")
    (repo / "serie").mkdir()
    (repo / "serie" / "A-Python.ipynb").write_text('{"cells": []}', encoding="utf-8")
    (repo / "serie" / "B-Python.ipynb").write_text(
        '[suite](A-Python.ipynb) et voici la suite', encoding="utf-8")
    _commit_all(repo, "base")
    (repo / "serie" / "sous").mkdir()
    _git(repo, "mv", "serie/A-Python.ipynb", "serie/sous/A-Python.ipynb")
    _commit_all(repo, "move")
    rc, out = _run(repo, monkeypatch)
    assert rc == 1
    hits = [f for f in out["findings"] if f["consumer"].endswith("B-Python.ipynb")]
    assert hits and "basename" in hits[0]["form"]


def test_cle_baseline_repo_relative(tmp_path, monkeypatch):
    """Cle JSON pleine longueur vers le chemin retire (baseline)."""
    repo = tmp_path / "r2"
    repo.mkdir()
    _git(repo, "init", "-q")
    (repo / "nb").mkdir()
    (repo / "nb" / "X.ipynb").write_text("{}", encoding="utf-8")
    (repo / "tools").mkdir()
    (repo / "tools" / "baseline.json").write_text(
        '{"MyIA/nb/X.ipynb": 3}', encoding="utf-8")
    _commit_all(repo, "base")
    (repo / "nb" / "X.ipynb").unlink()
    _commit_all(repo, "drop")
    rc, out = _run(repo, monkeypatch)
    assert rc == 1
    hits = [f for f in out["findings"] if f["consumer"].endswith("baseline.json")]
    assert hits and "path" in hits[0]["form"]


def test_lien_relatif_parent(tmp_path, monkeypatch):
    """Lien ../chemin vers un fichier retire d'un autre dossier."""
    repo = tmp_path / "r3"
    repo.mkdir()
    _git(repo, "init", "-q")
    (repo / "a").mkdir()
    (repo / "b").mkdir()
    (repo / "a" / "cible.md").write_text("x", encoding="utf-8")
    (repo / "b" / "page.md").write_text("[voir](../a/cible.md)", encoding="utf-8")
    _commit_all(repo, "base")
    (repo / "a" / "cible.md").unlink()
    _commit_all(repo, "drop")
    rc, out = _run(repo, monkeypatch)
    assert rc == 1
    hits = [f for f in out["findings"] if f["consumer"].endswith("page.md")]
    assert hits


def test_deplacement_solaire_exempt(tmp_path, monkeypatch):
    """Voisin deplace AVEC la cible : son lien same-dir resolve, pas d'orphelin."""
    repo = tmp_path / "r4"
    repo.mkdir()
    _git(repo, "init", "-q")
    (repo / "serie").mkdir()
    (repo / "serie" / "A.ipynb").write_text("{}", encoding="utf-8")
    (repo / "serie" / "B.ipynb").write_text("[suite](A.ipynb)", encoding="utf-8")
    _commit_all(repo, "base")
    (repo / "serie" / "new").mkdir()
    (repo / "serie" / "A.ipynb").rename(repo / "serie" / "new" / "A.ipynb")
    (repo / "serie" / "B.ipynb").rename(repo / "serie" / "new" / "B.ipynb")
    _commit_all(repo, "move both")
    rc, out = _run(repo, monkeypatch)
    assert rc == 0, out["findings"]


def test_derives_exclus(tmp_path, monkeypatch):
    """Catalogue genere et traductions ne comptent pas comme consommateurs."""
    repo = tmp_path / "r5"
    repo.mkdir()
    _git(repo, "init", "-q")
    (repo / "nb").mkdir()
    (repo / "nb" / "X.ipynb").write_text("{}", encoding="utf-8")
    (repo / "COURSE_CATALOG.generated.md").write_text(
        "- [X](nb/X.ipynb)", encoding="utf-8")
    (repo / "translations").mkdir()
    (repo / "translations" / "gen.csv").write_text("nb/X.ipynb,ok", encoding="utf-8")
    _commit_all(repo, "base")
    (repo / "nb" / "X.ipynb").unlink()
    _commit_all(repo, "drop")
    rc, out = _run(repo, monkeypatch)
    assert rc == 0, out["findings"]


def test_aucune_suppression_verte(tmp_path, monkeypatch):
    """Une PR qui ne retire rien est verte par construction (borne au diff)."""
    repo = tmp_path / "r6"
    repo.mkdir()
    _git(repo, "init", "-q")
    (repo / "a.md").write_text("x", encoding="utf-8")
    _commit_all(repo, "base")
    (repo / "b.md").write_text("y", encoding="utf-8")
    _commit_all(repo, "add")
    rc, out = _run(repo, monkeypatch)
    assert rc == 0 and out["removed"] == []


def test_deja_repare_nouveau_chemin_non_signale(tmp_path, monkeypatch):
    """Consommateur CORRIGE qui porte le nouveau chemin (le basename y est
    suffixe) : la couverture par occurrence ne doit pas le re-signaler.

    Forme mesuree sur #27119 tete reparee : pedagogy_density_baseline.json
    et le README Actuariat portent GameTheory-17-MultiAgent-RL/<basename>.
    """
    repo = tmp_path / "r7"
    repo.mkdir()
    _git(repo, "init", "-q")
    (repo / "serie").mkdir()
    (repo / "tools").mkdir()
    (repo / "serie" / "A.ipynb").write_text("{}", encoding="utf-8")
    (repo / "tools" / "base.json").write_text('{"serie/A.ipynb": 1}', encoding="utf-8")
    (repo / "other").mkdir()
    (repo / "other" / "page.md").write_text(
        "[a](../serie/new/A.ipynb) et cle new/serie", encoding="utf-8")
    _commit_all(repo, "base")
    (repo / "serie" / "new").mkdir()
    _git(repo, "mv", "serie/A.ipynb", "serie/new/A.ipynb")
    (repo / "tools" / "base.json").write_text(
        '{"serie/new/A.ipynb": 1}', encoding="utf-8")
    _commit_all(repo, "move + liens realignes")
    rc, out = _run(repo, monkeypatch)
    assert rc == 0, out["findings"]


def test_mention_prose_non_signalee(tmp_path, monkeypatch):
    """Un bare basename dans la prose est un NOM, pas une reference : seule
    une CIBLE de lien `](basename)` compte pour la forme basename. Le fichier
    porte un lien valide vers le nouveau chemin ET une mention de nom -- rc 0
    (classe des mentions de nom mesuree sur #27119 tete reparee : README
    consommateurs du lake, material-map)."""
    repo = tmp_path / "r8"
    repo.mkdir()
    _git(repo, "init", "-q")
    (repo / "serie").mkdir()
    (repo / "serie" / "A.ipynb").write_text("{}", encoding="utf-8")
    (repo / "other").mkdir()
    (repo / "other" / "page.md").write_text(
        "[a](../serie/new/A.ipynb) et le carnet A.ipynb", encoding="utf-8")
    _commit_all(repo, "base")
    (repo / "serie" / "new").mkdir()
    _git(repo, "mv", "serie/A.ipynb", "serie/new/A.ipynb")
    _commit_all(repo, "move")
    rc, out = _run(repo, monkeypatch)
    assert rc == 0, out["findings"]


def test_historique_non_signale(tmp_path, monkeypatch):
    """Un rename-ledger et un snapshot de PRs fermees portent les anciens
    chemins PAR NATURE (registre d'historique) : ils ne sont pas des
    consommateurs vivants et ne doivent pas etre signales. Un consommateur
    vivant (baseline) sur le meme chemin reste signale dans la meme PR."""
    repo = tmp_path / "r9"
    repo.mkdir()
    _git(repo, "init", "-q")
    (repo / "serie").mkdir()
    (repo / "serie" / "A.ipynb").write_text("{}", encoding="utf-8")
    (repo / "tools").mkdir()
    (repo / "tools" / "base.json").write_text('{"serie/A.ipynb": 1}', encoding="utf-8")
    (repo / "docs").mkdir()
    (repo / "docs" / "reference").mkdir()
    (repo / "docs" / "reference" / "rename-ledger.tsv").write_text(
        "serie/A.ipynb\tserie/old-A.ipynb\t2026-01-01\tlane", encoding="utf-8")
    (repo / "scripts").mkdir()
    (repo / "scripts" / "ci" / "tests" / "fixtures").mkdir(parents=True)
    (repo / "scripts" / "ci" / "tests" / "fixtures" /
     "list_closed_unmerged_prs_snapshot.json").write_text(
        '{"x": {"files": [{"path": "serie/A.ipynb"}]}}', encoding="utf-8")
    _commit_all(repo, "base")
    (repo / "serie" / "new").mkdir()
    _git(repo, "mv", "serie/A.ipynb", "serie/new/A.ipynb")
    _commit_all(repo, "move")
    rc, out = _run(repo, monkeypatch)
    # seul le consommateur vivant (base.json) est signale ; ledger + snapshot non
    consumers = {f["consumer"] for f in out["findings"]}
    assert any(c.endswith("base.json") for c in consumers), out["findings"]
    assert not any("rename-ledger" in c for c in consumers), out["findings"]
    assert not any("snapshot" in c for c in consumers), out["findings"]


def test_self_test_zero_echec():
    assert mod.self_test() == 0
