"""Regression #25090 -- scan_diff doit ignorer les diffs EOL-purs.

Un diff EOL-pur (renormalisation CRLF -> LF d'un fichier existant, contenu
identique) reecrit chaque ligne du fichier : sans ``--ignore-cr-at-eol``, git
rend toutes ces lignes comme ajoutees et le garde prose-counts juge des
compteurs PRE-EXISTANTS comme s'ils venaient d'etre ecrits (instance mesuree :
#24774, 544 compteurs en faux positif sur 60 fichiers de docs/).

Deux garanties, toutes deux requises :

1. un commit qui ne fait QUE renormaliser les fins de ligne ne produit
   **aucun** finding ;
2. une vraie ligne ajoutee portant un compteur reste flaguee -- sinon la
   vacuite du cas 1 ne prouverait que l'aveuglement du scan, pas le drapeau.

Le fixture force ``core.autocrlf=false`` : avec la conversion activee, git
normaliserait le CRLF a l'indexation et le commit de renormalisation ne
produirait aucun diff meme SANS le correctif -- le test serait vert par
accident et ne discriminerait rien.
"""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
NOTEBOOK_TOOLS = HERE.parent / "notebook_tools"
sys.path.insert(0, str(NOTEBOOK_TOOLS))
from check_prose_quantitative_claims import _resolve_classes, scan_diff  # noqa: E402

# Ligne portant deux compteurs de la classe artifact (mesure #25090 : les
# compteurs en fausse attribution sur #24774 etaient des comptes de fichiers).
DOC = "Rapport de sweep : le module traite 42 fichiers et 17 dossiers.\n"
# Vraie addition pour le controle positif : comptes differents, meme classe.
DOC2 = "Deuxieme passe : 43 fichiers et 18 dossiers supplementaires.\n"


def _git(*args: str, cwd: Path) -> None:
    subprocess.run(
        ["git", *args], cwd=cwd, check=True, capture_output=True, text=True,
        encoding="utf-8", errors="replace",
    )


@pytest.fixture()
def eol_repo(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> tuple[Path, Path]:
    """Repo minimal avec un fichier .md CRLF commite une premiere fois."""
    monkeypatch.chdir(tmp_path)
    _git("init", "-q", ".", cwd=tmp_path)
    _git("config", "user.email", "test@example.invalid", cwd=tmp_path)
    _git("config", "user.name", "Regression Test", cwd=tmp_path)
    # Sans ceci, git normalise le CRLF a l'indexation et le test ne
    # discrimine pas le correctif (cf docstring module).
    _git("config", "core.autocrlf", "false", cwd=tmp_path)
    p = tmp_path / "doc.md"
    p.write_bytes(DOC.replace("\n", "\r\n").encode("utf-8"))
    _git("add", "doc.md", cwd=tmp_path)
    _git("commit", "-q", "-m", "crlf: contenu initial", cwd=tmp_path)
    return tmp_path, p


def test_pure_eol_renormalization_produces_no_finding(
    eol_repo: tuple[Path, Path],
) -> None:
    """Commit 2 = meme contenu, LF : le garde ne voit rien."""
    tmp_path, p = eol_repo
    p.write_bytes(DOC.encode("utf-8"))
    _git("add", "doc.md", cwd=tmp_path)
    _git("commit", "-q", "-m", "lf: renormalisation EOL-pure", cwd=tmp_path)
    classes, _ = _resolve_classes("all")
    assert scan_diff("HEAD~1..HEAD", classes) == []


def test_real_addition_with_counter_still_flagged(
    eol_repo: tuple[Path, Path],
) -> None:
    """Controle positif : une vraie ligne ajoutee reste vue par le garde."""
    tmp_path, p = eol_repo
    with p.open("ab") as f:
        f.write(DOC2.encode("utf-8"))
    _git("add", "doc.md", cwd=tmp_path)
    _git("commit", "-q", "-m", "ajout reel d'un compteur", cwd=tmp_path)
    classes, _ = _resolve_classes("all")
    findings = scan_diff("HEAD~1..HEAD", classes)
    assert findings, "le garde doit toujours voir une vraie ligne ajoutee"
    snippets = " ".join(snippet for _loc, _cls, snippet in findings)
    assert "43 fichiers" in snippets
