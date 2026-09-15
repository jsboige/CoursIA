"""Tests for check_twin_parity -- pression de fork (`_repo_root` sans fork, repli EAGAIN).

Why this exists
---------------
`check_twin_parity.py` est mort en CI a `_repo_root()`, ligne 627, sur un
`BlockingIOError: [Errno 11]` -- `EAGAIN` au `fork`. Le numero de ligne designe
OU l'echec a atterri, pas le coupable : `_repo_root()` est appele depuis `main`
AVANT toute boucle par paire, donc le processus n'avait quasiment rien forke
lui-meme. La pression qui epuise la table de processus lui est EXTERIEURE (les
organes co-tenants d'un job `Always-on guards -- N organes, 1 checkout`), et
aucun comptage de processus n'a ete fait sur le runner : c'est une lecture de
l'ordre d'appel, pas une mesure d'attribution.

Les deux garde-fous ci-dessous sont donc bornes a ce qui est etabli :

1. `_repo_root()` ne forke plus. `git rev-parse --show-toplevel` n'est qu'une
   remontee de parents jusqu'a un `.git` -- le test le prouve en faisant ECHOUER
   `subprocess.run` : si la fonction forke encore, elle echoue. C'est le seul
   point ou l'on sait que le fork mourait, et un organe qui demarre est un
   organe qui peut rapporter.
2. `_run_git` retente `EAGAIN` de facon BORNEE. La contrepartie est aussi
   testee (controle positif) : une `OSError` d'une autre nature ne doit PAS etre
   retentee. Sans ce controle, un `except OSError` trop large avalerait une
   panne reelle en trois essais silencieux -- le remede deviendrait pire que le
   mal.

Ce qui n'est PAS teste, volontairement : que `_run_git` reduise la pression de
fork. Il ne la reduit pas sur les 6 autres sites -- il rend seulement l'echec
transitoire surmontable. Reduire le fan-out (157 paires x N forks, un
`git cat-file --batch` en flux) est un troisieme axe, explicitement laisse hors
de ce correctif.
"""
from __future__ import annotations

import errno
import os
import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import check_twin_parity as ctp  # noqa: E402

REPO = Path(__file__).resolve().parents[3]


def _meme_chemin(a: Path, b: Path) -> bool:
    """Egalite de chemins robuste (separateurs et casse Windows)."""
    return os.path.normcase(str(a)) == os.path.normcase(str(b))


# --------------------------------------------------------------------------
# 1. `_repo_root` ne forke plus
# --------------------------------------------------------------------------

def test_repo_root_ne_fork_pas(monkeypatch):
    """Le fork doit avoir disparu : `subprocess.run` qui leve = echec du test.

    Le repertoire est choisi IMBRIQUE dans le depot : une remontee de parents
    doit le trouver, ce qu'un simple `Path.cwd()` ne ferait pas.
    """
    def interdit(*_args, **_kwargs):
        raise AssertionError("_repo_root() a forke (subprocess.run appele)")

    monkeypatch.setattr(subprocess, "run", interdit)
    monkeypatch.chdir(REPO / "scripts" / "notebook_tools" / "tests")

    assert _meme_chemin(ctp._repo_root(), REPO)


def test_repo_root_sans_fork_depuis_un_sous_dossier_profond(monkeypatch):
    """Meme garantie depuis un dossier profond, et sur un `.git` FILE (worktree)."""
    def interdit(*_args, **_kwargs):
        raise AssertionError("_repo_root() a forke (subprocess.run appele)")

    monkeypatch.setattr(subprocess, "run", interdit)
    monkeypatch.chdir(REPO / "MyIA.AI.Notebooks")

    racine = ctp._repo_root()
    assert _meme_chemin(racine, REPO)
    # Le `.git` detecte est bien celui du depot (dossier ou fichier de worktree).
    assert (racine / ".git").exists()


def test_repo_root_equivaut_a_git_rev_parse(monkeypatch):
    """Equivalence avec le `git rev-parse --show-toplevel` qu'elle remplace.

    C'est la preuve que la remontee est FIDELE, pas seulement rapide : si les
    deux divergent un jour, ce test tombe avant que le reste du registre ne
    derive sur une racine fausse.
    """
    monkeypatch.chdir(REPO)
    attendu = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
    assert attendu.returncode == 0, "premisse : le depot de test est bien un depot git"

    assert _meme_chemin(ctp._repo_root(), Path(attendu.stdout.strip()))


def test_repo_root_repli_sur_git_quand_aucun_git(monkeypatch, tmp_path):
    """Hors de tout depot, l'ancien comportement (fork unique) est preserve.

    La premisse est asserte : si un `.git` trainait dans un parent de `tmp_path`,
    le repli ne serait jamais atteint et le test passerait pour la mauvaise
    raison.
    """
    assert not any((p / ".git").exists() for p in (tmp_path, *tmp_path.parents)), \
        "premisse : tmp_path ne doit etre sous aucun depot"

    appels: list[list[str]] = []
    racine_factice = "C:/faux/depot"

    def faux_run(args, **_kwargs):
        appels.append(list(args))
        return subprocess.CompletedProcess(args, 0, stdout=racine_factice + "\n", stderr="")

    monkeypatch.setattr(subprocess, "run", faux_run)
    monkeypatch.chdir(tmp_path)

    assert _meme_chemin(ctp._repo_root(), Path(racine_factice))
    assert len(appels) == 1
    assert appels[0] == ["git", "rev-parse", "--show-toplevel"]


def test_repo_root_repli_signale_l_absence_de_depot(monkeypatch, tmp_path):
    """Hors depot, un git en echec donne toujours le meme SystemExit."""
    def faux_run(args, **_kwargs):
        return subprocess.CompletedProcess(args, 128, stdout="", stderr="fatal: not a git repository")

    monkeypatch.setattr(subprocess, "run", faux_run)
    monkeypatch.chdir(tmp_path)

    with pytest.raises(SystemExit, match="pas un depot git"):
        ctp._repo_root()


# --------------------------------------------------------------------------
# 2. `_run_git` : repli borne sur EAGAIN
# --------------------------------------------------------------------------

def _eagain() -> BlockingIOError:
    return BlockingIOError(errno.EAGAIN, "Resource temporarily unavailable")


def test_run_git_retente_sur_eagain(monkeypatch):
    """EAGAIN est temporaire : les 2 premiers forks echouent, le 3e passe."""
    appels = {"n": 0}
    sentinelle = subprocess.CompletedProcess(["git"], 0, stdout="ok\n", stderr="")

    def faux_run(args, **_kwargs):
        appels["n"] += 1
        if appels["n"] < 3:
            raise _eagain()
        return sentinelle

    monkeypatch.setattr(subprocess, "run", faux_run)
    monkeypatch.setattr(ctp.time, "sleep", lambda _s: None)

    assert ctp._run_git(["git", "status"]) is sentinelle
    assert appels["n"] == 3


def test_run_git_ne_retente_pas_une_autre_erreur(monkeypatch):
    """CONTROLE POSITIF -- une panne reelle ne doit pas etre avalee.

    Sans ce test, un `except OSError` trop large transformerait une erreur
    permanente (git absent, `ENOENT`) en trois essais silencieux : le remede
    serait pire que le mal. Ici l'exception doit remonter AU PREMIER appel.
    """
    appels = {"n": 0}

    def faux_run(_args, **_kwargs):
        appels["n"] += 1
        raise FileNotFoundError(errno.ENOENT, "No such file or directory: 'git'")

    monkeypatch.setattr(subprocess, "run", faux_run)
    monkeypatch.setattr(ctp.time, "sleep", lambda _s: None)

    with pytest.raises(FileNotFoundError):
        ctp._run_git(["git", "status"])
    assert appels["n"] == 1, "une erreur non-EAGAIN ne doit pas etre retentee"


@pytest.mark.parametrize("errno_erreur", [errno.EACCES, errno.ENOMEM, errno.EINVAL])
def test_run_git_ne_retente_pas_les_autres_errno(monkeypatch, errno_erreur):
    """Le repli est etroit : seuls EAGAIN/EWOULDBLOCK declenchent une tentative."""
    appels = {"n": 0}

    def faux_run(_args, **_kwargs):
        appels["n"] += 1
        raise OSError(errno_erreur, os.strerror(errno_erreur))

    monkeypatch.setattr(subprocess, "run", faux_run)
    monkeypatch.setattr(ctp.time, "sleep", lambda _s: None)

    with pytest.raises(OSError):
        ctp._run_git(["git", "status"])
    assert appels["n"] == 1


def test_run_git_epuise_les_tentatives_puis_remonte(monkeypatch):
    """La borne est reelle : apres `_EAGAIN_ATTEMPTS` essais, l'erreur remonte."""
    appels = {"n": 0}

    def faux_run(_args, **_kwargs):
        appels["n"] += 1
        raise _eagain()

    monkeypatch.setattr(subprocess, "run", faux_run)
    monkeypatch.setattr(ctp.time, "sleep", lambda _s: None)

    with pytest.raises(BlockingIOError):
        ctp._run_git(["git", "status"])
    assert appels["n"] == ctp._EAGAIN_ATTEMPTS


def test_run_git_backoff_borne(monkeypatch):
    """Le repli ne dort pas indefiniment : attentes courtes, nombre connu."""
    dors = []
    appels = {"n": 0}

    def faux_run(args, **_kwargs):
        appels["n"] += 1
        if appels["n"] < ctp._EAGAIN_ATTEMPTS:
            raise _eagain()
        return subprocess.CompletedProcess(args, 0, stdout="", stderr="")

    monkeypatch.setattr(subprocess, "run", faux_run)
    monkeypatch.setattr(ctp.time, "sleep", lambda s: dors.append(s))

    ctp._run_git(["git", "status"])

    assert dors == list(ctp._EAGAIN_BACKOFF)
    assert sum(dors) <= 1.0, "le repli doit rester borne en temps"


def test_run_git_transmet_le_mode_texte(monkeypatch):
    """`text=False` (site `git show`, binaire) ne doit pas recevoir d'encodage."""
    vus = []

    def faux_run(args, **kwargs):
        vus.append(kwargs)
        return subprocess.CompletedProcess(args, 0, stdout=b"", stderr=b"")

    monkeypatch.setattr(subprocess, "run", faux_run)

    ctp._run_git(["git", "show", "HEAD:x"], cwd=".", text=False)
    ctp._run_git(["git", "status"], cwd=".")

    assert "encoding" not in vus[0] and "errors" not in vus[0]
    assert vus[0]["text"] is False
    assert vus[1]["encoding"] == "utf-8" and vus[1]["errors"] == "replace"
    assert vus[1]["text"] is True
