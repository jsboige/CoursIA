"""Tests de `fork_retry` -- la reprise bornee sur EAGAIN, et sa portee exacte.

Why this exists
---------------
Un correctif de reprise est, vu de l'exterieur, indiscernable d'un avaleur
d'erreurs : les deux font disparaitre des exceptions. Ce qui les separe est le
CONTROLE POSITIF -- la preuve qu'une erreur qui n'est pas de la pression de fork
remonte AU PREMIER APPEL, sans reprise et sans attente. C'est la moitie de ce
fichier, et c'est la moitie qui compte.

L'autre moitie tient a la mutualisation elle-meme. Extraire une primitive
partagee par cinq gardes fait courir un risque precis : uniformiser en passant ce
qui etait deliberement different. Deux choses etaient deliberement differentes et
doivent le rester --

1. la FORME de l'appel (un garde lit de l'utf-8, un autre du binaire, un autre
   passe un `env` ou un `cwd`) : `run_with_fork_retry` transmet les `kwargs`
   verbatim, et `test_kwargs_transmis_verbatim` l'epingle ;
2. la POLITIQUE D'EPUISEMENT (fail-closed pour `check_slot_reservation`,
   fail-open pour `check_source_output_ratchet`) : les deux derniers tests
   l'epinglent garde par garde, parce que c'est precisement ce qu'un refactor
   distrait harmoniserait.

Ce qui n'est PAS teste, volontairement : que la reprise reduise la pression de
fork. Elle ne la reduit pas -- elle rend l'echec transitoire surmontable. Le
fan-out reste le meme, et le reduire est un axe distinct (#16111).
"""
from __future__ import annotations

import errno
import os
import subprocess
import sys

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import check_slot_reservation as csr  # noqa: E402
import check_source_output_ratchet as csor  # noqa: E402
import fork_retry  # noqa: E402


def _eagain() -> BlockingIOError:
    return BlockingIOError(errno.EAGAIN, "Resource temporarily unavailable")


@pytest.fixture(autouse=True)
def _pas_d_attente_reelle(monkeypatch):
    """Les tests mesurent le backoff, ils ne le subissent pas."""
    monkeypatch.setattr(fork_retry.time, "sleep", lambda _s: None)


# --------------------------------------------------------------------------
# 1. La reprise
# --------------------------------------------------------------------------

def test_retente_sur_eagain(monkeypatch):
    """EAGAIN est temporaire : les 2 premiers spawns echouent, le 3e passe."""
    appels = {"n": 0}
    sentinelle = subprocess.CompletedProcess(["git"], 0, stdout="ok\n", stderr="")

    def faux_run(_args, **_kwargs):
        appels["n"] += 1
        if appels["n"] < 3:
            raise _eagain()
        return sentinelle

    monkeypatch.setattr(subprocess, "run", faux_run)

    assert fork_retry.run_with_fork_retry(["git", "status"]) is sentinelle
    assert appels["n"] == 3


def test_retente_sur_ewouldblock(monkeypatch):
    """`EWOULDBLOCK` alias `EAGAIN` sous Linux, mais pas partout : couvrir les deux."""
    appels = {"n": 0}

    def faux_run(args, **_kwargs):
        appels["n"] += 1
        if appels["n"] < 2:
            raise OSError(errno.EWOULDBLOCK, "Operation would block")
        return subprocess.CompletedProcess(args, 0, stdout="", stderr="")

    monkeypatch.setattr(subprocess, "run", faux_run)

    fork_retry.run_with_fork_retry(["git", "status"])
    assert appels["n"] == 2


def test_epuisement_remonte_la_derniere_erreur(monkeypatch):
    """La borne est reelle : apres `ATTEMPTS` essais, l'erreur remonte."""
    appels = {"n": 0}

    def faux_run(_args, **_kwargs):
        appels["n"] += 1
        raise _eagain()

    monkeypatch.setattr(subprocess, "run", faux_run)

    with pytest.raises(BlockingIOError):
        fork_retry.run_with_fork_retry(["git", "status"])
    assert appels["n"] == fork_retry.ATTEMPTS


# --------------------------------------------------------------------------
# 2. Controle positif -- le filtre est etroit
# --------------------------------------------------------------------------

def test_controle_positif_une_panne_reelle_n_est_pas_retentee(monkeypatch):
    """Sans ce test, la reprise serait indiscernable d'un avaleur d'erreurs.

    Une panne permanente -- git absent, `ENOENT` -- doit remonter AU PREMIER
    appel : la retenter trois fois en silence rendrait le remede pire que le mal.
    """
    appels = {"n": 0}

    def faux_run(_args, **_kwargs):
        appels["n"] += 1
        raise FileNotFoundError(errno.ENOENT, "No such file or directory: 'git'")

    monkeypatch.setattr(subprocess, "run", faux_run)

    with pytest.raises(FileNotFoundError):
        fork_retry.run_with_fork_retry(["git", "status"])
    assert appels["n"] == 1, "une erreur non-EAGAIN ne doit pas etre retentee"


@pytest.mark.parametrize("errno_erreur", [errno.EACCES, errno.ENOMEM, errno.EINVAL])
def test_les_autres_errno_ne_sont_pas_retentes(monkeypatch, errno_erreur):
    """`ENOMEM` est le voisin dangereux : lui aussi vient de la charge, et lui
    n'est pas transitoire. Le filtre ne doit pas glisser jusqu'a lui."""
    appels = {"n": 0}

    def faux_run(_args, **_kwargs):
        appels["n"] += 1
        raise OSError(errno_erreur, os.strerror(errno_erreur))

    monkeypatch.setattr(subprocess, "run", faux_run)

    with pytest.raises(OSError):
        fork_retry.run_with_fork_retry(["git", "status"])
    assert appels["n"] == 1


def test_is_fork_pressure_ne_repond_qu_aux_oserror():
    assert fork_retry.is_fork_pressure(_eagain())
    assert not fork_retry.is_fork_pressure(OSError(errno.ENOENT, "absent"))
    assert not fork_retry.is_fork_pressure(ValueError("pas une OSError"))


# --------------------------------------------------------------------------
# 3. Le repli reste borne en temps
# --------------------------------------------------------------------------

def test_backoff_borne(monkeypatch):
    dors: list[float] = []
    appels = {"n": 0}

    def faux_run(args, **_kwargs):
        appels["n"] += 1
        if appels["n"] < fork_retry.ATTEMPTS:
            raise _eagain()
        return subprocess.CompletedProcess(args, 0, stdout="", stderr="")

    monkeypatch.setattr(subprocess, "run", faux_run)
    monkeypatch.setattr(fork_retry.time, "sleep", lambda s: dors.append(s))

    fork_retry.run_with_fork_retry(["git", "status"])

    assert dors == list(fork_retry.BACKOFF)
    assert sum(dors) <= 1.0, "le repli doit rester borne en temps"


def test_un_backoff_par_reprise():
    """Invariant d'indexation : `BACKOFF[tentative - 1]` ne doit jamais deborder."""
    assert len(fork_retry.BACKOFF) >= fork_retry.ATTEMPTS - 1


# --------------------------------------------------------------------------
# 4. La mutualisation n'impose aucune forme d'appel
# --------------------------------------------------------------------------

def test_kwargs_transmis_verbatim(monkeypatch):
    """Le module ne prend position ni sur le mode texte, ni sur `env`/`cwd`/`check`.

    C'est la condition pour qu'un garde binaire et un garde utf-8 partagent la
    meme porte sans changement de comportement.
    """
    vus: list[dict] = []

    def faux_run(args, **kwargs):
        vus.append(kwargs)
        return subprocess.CompletedProcess(args, 0, stdout=b"", stderr=b"")

    monkeypatch.setattr(subprocess, "run", faux_run)

    fork_retry.run_with_fork_retry(["git", "show", "HEAD:x"], capture_output=True, text=False)
    fork_retry.run_with_fork_retry(
        ["git", "status"], cwd=".", capture_output=True,
        encoding="utf-8", errors="replace", check=False, env={"A": "1"},
    )

    assert vus[0] == {"capture_output": True, "text": False}
    assert vus[1] == {
        "cwd": ".", "capture_output": True, "encoding": "utf-8",
        "errors": "replace", "check": False, "env": {"A": "1"},
    }


# --------------------------------------------------------------------------
# 5. Chaque garde CONSERVE sa politique d'epuisement
# --------------------------------------------------------------------------

def test_slot_reservation_retente_puis_reste_fail_closed(monkeypatch):
    """`check_slot_reservation` laisse remonter : un instrument muet ne vote pas."""
    appels = {"n": 0}

    def faux_run(args, **_kwargs):
        appels["n"] += 1
        if appels["n"] < 3:
            raise _eagain()
        return subprocess.CompletedProcess(args, 0, stdout="a.ipynb\n", stderr="")

    monkeypatch.setattr(subprocess, "run", faux_run)
    assert csr._git(["status"]) == "a.ipynb\n"
    assert appels["n"] == 3

    appels["n"] = 0

    def toujours_eagain(_args, **_kwargs):
        appels["n"] += 1
        raise _eagain()

    monkeypatch.setattr(subprocess, "run", toujours_eagain)
    with pytest.raises(OSError):
        csr._git(["status"])
    assert appels["n"] == fork_retry.ATTEMPTS


def test_source_output_ratchet_retente_puis_reste_fail_open(monkeypatch):
    """`check_source_output_ratchet` rend `None` -- politique preexistante, #16164.

    Ce test ne l'approuve pas, il l'EPINGLE : mutualiser la reprise ne doit pas
    la changer au passage. L'arbitrage fail-open/fail-closed appartient a #16164.
    """
    appels = {"n": 0}

    def faux_run(args, **_kwargs):
        appels["n"] += 1
        if appels["n"] < 3:
            raise _eagain()
        return subprocess.CompletedProcess(args, 0, stdout="ok\n", stderr="")

    monkeypatch.setattr(subprocess, "run", faux_run)
    assert csor.git("status") == "ok\n"
    assert appels["n"] == 3

    appels["n"] = 0

    def toujours_eagain(_args, **_kwargs):
        appels["n"] += 1
        raise _eagain()

    monkeypatch.setattr(subprocess, "run", toujours_eagain)
    assert csor.git("status") is None
    assert appels["n"] == fork_retry.ATTEMPTS


def test_les_deux_gardes_ne_retentent_pas_une_panne_reelle(monkeypatch):
    """Controle positif au niveau des gardes, pas seulement de la primitive."""
    appels = {"n": 0}

    def faux_run(_args, **_kwargs):
        appels["n"] += 1
        raise FileNotFoundError(errno.ENOENT, "No such file or directory: 'git'")

    monkeypatch.setattr(subprocess, "run", faux_run)

    with pytest.raises(FileNotFoundError):
        csr._git(["status"])
    assert appels["n"] == 1

    appels["n"] = 0
    # Fail-open : le ratchet avale l'`OSError` comme avant -- mais UNE SEULE fois.
    assert csor.git("status") is None
    assert appels["n"] == 1
