#!/usr/bin/env python3
"""Tests du verrou de lecture unique du cache du tapis rapide (#22630).

Le cache de lecture est partage par machine (`%LOCALAPPDATA%/CoursIA/tapis_rapide/`).
Avant ce verrou, deux lanes qui tiraient au meme instant lisaient chacune le
reseau : le credit gh etait paye deux fois pour le meme contenu.

Les etats verifies ici :
- un cache frais ne coute **aucun** appel ;
- le second tirage relit le cache que le premier vient d'ecrire : **aucun**
  appel reseau de plus ;
- le verrou est **relache** apres la lecture ;
- un delai de verrou **ne bloque pas** le tirage : la lecture part au reseau
  (l'attente est **bornee** a 120 s, pas nulle -- « jamais bloquant » veut
  dire « jamais empeche », pas « jamais attend ») ;
- un cache frais mais de **structure incorrecte** ne fait pas echouer le
  tirage : la lecture repart au reseau ;
- un verrou qui ne peut pas etre **cree** (permissions, disque plein) ne
  bloque pas non plus ;
- le cache **desactive** (`cache_s=0`) ne prend **pas** le verrou ;
- une erreur venue de la **lecture reseau** elle-meme n'est pas rejouee.

Aucun test ne touche le reseau ni le vrai depot : chaque lecture recoit un faux
`run(argv, timeout)`, et la sentinelle `forbid_shell_escape` refuse tout processus.
Les tests d'attente **simulent** l'entrelacement (monkeypatch du verrou) : ils
demontrent le comportement du code face a un cache rafraichi pendant
l'attente, pas une concurrence reelle.

Run: python -m pytest scripts/tests/test_gh_bulk_single_flight.py
"""
from __future__ import annotations

import json
import sys
import time
from contextlib import contextmanager
from dataclasses import asdict
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from coordination import gh_bulk, gh_cache, gh_snapshot  # noqa: E402

pytestmark = pytest.mark.usefixtures("forbid_shell_escape")


def _run_faux(appels: list[list[str]]):
    """Un `run` qui repond aux trois lectures sans toucher le reseau."""
    def run(argv: list[str], timeout: int) -> str:
        appels.append(argv)
        if argv[0] == "git":
            if "--format=%ct" in argv:  # pointe d'origin/main : fraiche
                return str(int(time.time()))
            return ""  # `git log` des citations : aucun commit
        if "issues" in " ".join(argv):  # pagination GraphQL
            return json.dumps({"data": {"repository": {"issues": {
                "pageInfo": {"hasNextPage": False, "endCursor": None}, "nodes": []}}}})
        return json.dumps([])  # PRs ouvertes
    return run


def _ecrire_cache(dossier: Path, jours: int = 45, epoch: float | None = None) -> Path:
    """Un cache valide, ecrit comme le fait `_lire_reseau`."""
    dossier.mkdir(parents=True, exist_ok=True)
    chemin = dossier / f"lecture-{jours}j.json"
    lecture = gh_bulk.Lecture(issues=[], prs=[], citations={}, lu_a="2026-11-14T10:00:00Z",
                              appels=4, secondes=1.0)
    chemin.write_text(json.dumps({**asdict(lecture),
                                  "_epoch": time.time() if epoch is None else epoch}),
                      encoding="utf-8")
    return chemin


# --- un cache frais ne coute aucun appel ---------------------------------------

def test_un_cache_frais_ne_coute_aucun_appel(tmp_path):
    _ecrire_cache(tmp_path)
    appels: list[list[str]] = []
    lecture = gh_bulk.lire_tout(tmp_path, cache_s=300, run=_run_faux(appels), jours=45,
                                dossier_cache=tmp_path)
    assert appels == []
    assert lecture.depuis_cache is True


# --- le second tirage relit le cache du premier --------------------------------

def test_le_second_tirage_ne_paye_plus_d_appel(tmp_path):
    appels: list[list[str]] = []
    run = _run_faux(appels)
    premiere = gh_bulk.lire_tout(tmp_path, cache_s=300, run=run, jours=45, dossier_cache=tmp_path)
    calls_apres_premiere = len(appels)
    assert calls_apres_premiere > 0  # la premiere lecture a bien lu le reseau
    assert premiere.depuis_cache is False

    seconde = gh_bulk.lire_tout(tmp_path, cache_s=300, run=run, jours=45, dossier_cache=tmp_path)
    assert len(appels) == calls_apres_premiere  # aucun appel de plus
    assert seconde.depuis_cache is True


# --- le verrou est relache -----------------------------------------------------

def test_le_verrou_est_relache_apres_la_lecture(tmp_path):
    appels: list[list[str]] = []
    gh_bulk.lire_tout(tmp_path, cache_s=300, run=_run_faux(appels), jours=45,
                      dossier_cache=tmp_path)
    assert not (tmp_path / "refresh.lock").exists()


# --- le second tirage lit le cache ecrit par le premier pendant l'attente ------

def test_un_attendant_retrouve_le_cache_sans_appel_reseau(tmp_path, monkeypatch):
    """Le cas du single-flight : le cache est ecrit PENDANT l'attente du verrou.

    Le verrou est **simule** (monkeypatch) : le test demonstre le
    comportement du code face a un cache rafraichi pendant l'attente, il ne
    demontre pas une concurrence reelle.
    """
    dossier = tmp_path
    _ecrire_cache(dossier, epoch=time.time() - 10_000)  # cache perime

    ecrit_pendant_l_attente = {"fait": False}
    vrai_lock = gh_snapshot.lock_directory

    def lock_qui_ecrit(directory, timeout=120.0):
        """Le verrou tient le temps d'ecrire le cache, comme l'autre lane."""
        with vrai_lock(directory, timeout):
            ecrit_pendant_l_attente["fait"] = True
            _ecrire_cache(directory)  # le cache est rafraichi par la lane qui tient
            yield directory / "refresh.lock"
    lock_qui_ecrit = contextmanager(lock_qui_ecrit)

    monkeypatch.setattr(gh_snapshot, "lock_directory", lock_qui_ecrit)
    appels: list[list[str]] = []
    lecture = gh_bulk.lire_tout(dossier, cache_s=300, run=_run_faux(appels), jours=45,
                                dossier_cache=dossier)
    assert ecrit_pendant_l_attente["fait"] is True
    assert appels == []  # l'attendant n'a paye aucun appel reseau
    assert lecture.depuis_cache is True


# --- un delai de verrou ne bloque jamais un tirage ------------------------------

def test_un_delai_de_verrou_retchute_sur_le_reseau(tmp_path, monkeypatch):
    """Le verrou n'est jamais bloquant : au delai, la lecture se fait sans lui."""
    @contextmanager
    def lock_qui_expire(directory, timeout=120.0):
        raise gh_snapshot.SnapshotLockTimeout("verrou non obtenu")
        yield  # pragma: no cover - jamais atteint

    monkeypatch.setattr(gh_snapshot, "lock_directory", lock_qui_expire)
    appels: list[list[str]] = []
    lecture = gh_bulk.lire_tout(tmp_path, cache_s=300, run=_run_faux(appels), jours=45,
                                dossier_cache=tmp_path)
    assert len(appels) > 0  # la lecture est partie au reseau
    assert lecture.depuis_cache is False


def test_le_delai_de_verrou_ne_remonte_pas_a_l_appelant(tmp_path, monkeypatch):
    @contextmanager
    def lock_qui_expire(directory, timeout=120.0):
        raise gh_snapshot.SnapshotLockTimeout("verrou non obtenu")
        yield  # pragma: no cover - jamais atteint

    monkeypatch.setattr(gh_snapshot, "lock_directory", lock_qui_expire)
    appels: list[list[str]] = []
    # pas d'exception : `SnapshotLockTimeout` est traduit en `TimeoutVerrou`
    gh_bulk.lire_tout(tmp_path, cache_s=300, run=_run_faux(appels), jours=45,
                      dossier_cache=tmp_path)
    assert gh_cache.TimeoutVerrou is not gh_snapshot.SnapshotLockTimeout


# --- un cache frais mais mal forme ne fait pas echouer le tirage --------------

def test_un_cache_de_structure_invalide_replique_sur_le_reseau(tmp_path):
    """Un cache frais mais de structure incorrecte part au reseau.

    Le defaut : la deserialisation avait ete sortie du `try`, et un cache
    `{"_epoch": <maintenant>}` (sans les champs attendus) leveait une
    `KeyError` hors de tout traitement -- le tirage echouait au lieu de
    relire le reseau.
    """
    chemin = tmp_path / "lecture-45j.json"
    chemin.write_text(json.dumps({"_epoch": time.time()}), encoding="utf-8")
    appels: list[list[str]] = []
    lecture = gh_bulk.lire_tout(tmp_path, cache_s=300, run=_run_faux(appels), jours=45,
                                dossier_cache=tmp_path)
    assert len(appels) > 0  # la lecture est partie au reseau
    assert lecture.depuis_cache is False
    # le cache invalide a ete remplace par un cache valide
    relu = json.loads(chemin.read_text(encoding="utf-8"))
    assert "citations" in relu


# --- un verrou non creable ne bloque pas le tirage -----------------------------

def test_un_verrou_impossible_creer_replique_sur_le_reseau(tmp_path, monkeypatch):
    """Permissions ou disque plein : le tirage part au reseau, sans exception."""
    @contextmanager
    def lock_qui_echoue(directory, timeout=120.0):
        raise OSError("permission denied")
        yield  # pragma: no cover - jamais atteint

    monkeypatch.setattr(gh_snapshot, "lock_directory", lock_qui_echoue)
    appels: list[list[str]] = []
    lecture = gh_bulk.lire_tout(tmp_path, cache_s=300, run=_run_faux(appels), jours=45,
                                dossier_cache=tmp_path)
    assert len(appels) > 0
    assert lecture.depuis_cache is False


def test_le_cache_desactive_ne_prend_pas_le_verrou(tmp_path, monkeypatch):
    """`cache_s=0` : rien a relire, donc rien a verrouiller."""
    prises = {"n": 0}
    vrai_lock = gh_snapshot.lock_directory

    def lock_compte(directory, timeout=120.0):
        prises["n"] += 1
        return vrai_lock(directory, timeout)

    monkeypatch.setattr(gh_snapshot, "lock_directory", lock_compte)
    appels: list[list[str]] = []
    lecture = gh_bulk.lire_tout(tmp_path, cache_s=0, run=_run_faux(appels), jours=45,
                                dossier_cache=tmp_path)
    assert prises["n"] == 0
    assert len(appels) > 0
    assert lecture.depuis_cache is False


def test_une_erreur_de_lecture_reseau_n_est_pas_rejouee(tmp_path, monkeypatch):
    """L'erreur de la lecture reseau elle-meme n'est pas rejouee.

    Le repli sur erreur de verrou ne doit pas transformer une panne reseau
    en double lecture (le credit gh est compte).
    """
    @contextmanager
    def lock_qui_echoue(directory, timeout=120.0):
        raise OSError("disque plein")
        yield  # pragma: no cover - jamais atteint

    monkeypatch.setattr(gh_snapshot, "lock_directory", lock_qui_echoue)
    appels: list[list[str]] = []

    def run_qui_echoue(argv: list[str], timeout: int) -> str:
        appels.append(argv)
        raise OSError("reseau indisponible")

    with pytest.raises(gh_bulk.LectureIncomplete):
        gh_bulk.lire_tout(tmp_path, cache_s=300, run=run_qui_echoue, jours=45,
                          dossier_cache=tmp_path)
    lectures = [argv for argv in appels if "issues" in " ".join(argv)]
    assert len(lectures) == 1  # une seule tentative de lecture, pas deux
