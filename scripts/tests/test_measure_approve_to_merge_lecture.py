"""Tests de la couche de lecture de la mesure APPROVE -> merge (#25510).

La mesure elle-meme est testee dans `test_measure_approve_to_merge.py`. Ce
module teste ce qui la porte : une lecture tombee en route ne doit pas
produire un releve.

- une erreur transitoire du serveur (5xx) est retentee comme une limite
  secondaire (403, 429) : le 26/11, un 502 au milieu d'un releve l'a fait
  tomber entier ;
- un quota primaire epuise n'est pas retente a l'aveugle : la lecture rend
  `QuotaEpuise` des la premiere reponse, avec l'instant de reinitialisation
  quand l'en-tete le donne ;
- `main` le rend en refus lisible (code 3), sans ecrire de JSON partiel.

`urlopen` est remplace : aucun test n'emet de requete.
"""

from __future__ import annotations

import sys
import urllib.error
from datetime import datetime, timezone
from pathlib import Path

CI_DIR = Path(__file__).resolve().parents[1] / "ci"
sys.path.insert(0, str(CI_DIR))

import measure_approve_to_merge as m  # noqa: E402

class _Reponse:
    """Reponse minimale : `urlopen` rend un contexte dont `read()` donne le corps."""

    def __init__(self, corps: bytes):
        self._corps = corps

    def read(self) -> bytes:
        return self._corps

    def __enter__(self):
        return self

    def __exit__(self, *_args):
        return False


def _erreur_http(code: int, entetes: dict | None = None) -> urllib.error.HTTPError:
    return urllib.error.HTTPError("https://api.github.com/x", code, "erreur",
                                  entetes or {}, None)


def _brancher_urlopen(monkeypatch, repondre):
    """Remplace `urlopen` par `repondre(numero_de_l_appel)` et retire les pauses."""
    appels: list[int] = []

    def faux_urlopen(_requete, timeout=0):
        appels.append(timeout)
        return repondre(len(appels))

    monkeypatch.setattr(m.urllib.request, "urlopen", faux_urlopen)
    monkeypatch.setattr(m.time, "sleep", lambda _secondes: None)
    return appels


def test_api_reessaie_une_erreur_transitoire_du_serveur(monkeypatch):
    def repondre(appel: int):
        if appel == 1:
            raise _erreur_http(502)  # mesure du 26/11 11:39Z : le releve est tombe
        return _Reponse(b'{"ok": true}')

    appels = _brancher_urlopen(monkeypatch, repondre)
    assert m.api("/x") == {"ok": True}
    assert len(appels) == 2


def test_api_abandonne_apres_le_derni_essai(monkeypatch):
    def repondre(_appel: int):
        raise _erreur_http(503)

    appels = _brancher_urlopen(monkeypatch, repondre)
    levee = None
    try:
        m.api("/x", essais=3)
    except urllib.error.HTTPError as exc:
        levee = exc
    assert len(appels) == 3
    assert levee is not None and levee.code == 503


def test_api_quota_epuise_arrete_des_la_premiere_reponse(monkeypatch):
    def repondre(_appel: int):
        raise _erreur_http(403, {"X-RateLimit-Remaining": "0",
                                 "X-RateLimit-Reset": "1795693932"})

    appels = _brancher_urlopen(monkeypatch, repondre)
    levee = None
    try:
        m.api("/x")
    except m.QuotaEpuise as exc:
        levee = exc
    # Le quota se reinitialise des minutes plus tard : retenter ne sert a rien.
    assert len(appels) == 1
    assert levee is not None
    assert levee.reinitialisation == datetime.fromtimestamp(1795693932, tz=timezone.utc)


def test_api_quota_epuise_sans_instant_reste_lisible(monkeypatch):
    def repondre(_appel: int):
        raise _erreur_http(403, {"X-RateLimit-Remaining": "0"})

    _brancher_urlopen(monkeypatch, repondre)
    levee = None
    try:
        m.api("/x")
    except m.QuotaEpuise as exc:
        levee = exc
    assert levee is not None and levee.reinitialisation is None


def test_api_403_de_limite_secondaire_est_reesayee(monkeypatch):
    def repondre(appel: int):
        if appel == 1:
            # Le quota primaire n'est pas epuise : c'est une limite secondaire.
            raise _erreur_http(403, {"X-RateLimit-Remaining": "41", "Retry-After": "2"})
        return _Reponse(b"[]")

    appels = _brancher_urlopen(monkeypatch, repondre)
    assert m.api("/x") == []
    assert len(appels) == 2


def test_main_quota_epuise_rend_3_et_n_ecrit_rien(monkeypatch, tmp_path, capsys):
    def faux_mesurer(*_args, **_kwargs):
        raise m.QuotaEpuise(datetime(2026, 11, 26, 11, 52, 12, tzinfo=timezone.utc))

    monkeypatch.setattr(m, "mesurer", faux_mesurer)
    sortie = tmp_path / "a2m.json"
    code = m.main(["--depuis", "2026-11-25T00:00:00Z", "--json", "--out", str(sortie)])
    flux = capsys.readouterr()
    assert code == 3
    assert flux.out == ""
    assert not sortie.exists()
    assert ("quota GitHub epuise : reinitialisation a 2026-11-26T11:52:12Z ;"
            " aucun releve produit, relancer apres cet instant") in flux.err


def test_main_quota_epuise_sans_instant_rend_3(monkeypatch, capsys):
    def faux_mesurer(*_args, **_kwargs):
        raise m.QuotaEpuise(None)

    monkeypatch.setattr(m, "mesurer", faux_mesurer)
    assert m.main(["--depuis", "2026-11-25T00:00:00Z"]) == 3
    assert "reinitialisation a -" in capsys.readouterr().err
