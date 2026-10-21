"""Regression #19643 (residu) : aucun appel `gh` de l'organe B.0 n'est sans borne.

Le 2026-10-09, sur `origin/main`, `scripts/check_unaddressed_nits.py` ne
contenait aucune occurrence de `timeout` : ses 11 sites d'appel passent par
`gh_json`, qui lancait `subprocess.run` sans borne. Un `gh` qui ralentit
(secondary rate limit) bloquait donc la lecture du merge-gate B.0 sans
jamais rendre de verdict.

Remede : `gh_json` porte une borne par appel (`GH_CALL_TIMEOUT_S`). Une
expiration n'est JAMAIS avalee :

- `_gh_fetch_issue` ne met pas `None` en cache sur expiration (le `None`
  signifie « numero qui n'est pas une issue », pas « gh n'a pas repondu ») ;
- `improper_dismissals` ne rend pas `set()` sur expiration (un ensemble vide
  lirait la reserve d'un tiers comme levee : rc=0 faux) ;
- `main()` transforme l'expiration en « NON MESURE » sur stderr et rend 1
  (non-CLEAN, fail-closed).

Les appels `gh` sont remplaces par des fausses fonctions : aucun reseau.
"""
import importlib.util
import subprocess
import sys
from pathlib import Path

import pytest

SCRIPT = Path(__file__).resolve().parents[1] / "check_unaddressed_nits.py"
spec = importlib.util.spec_from_file_location("check_unaddressed_nits_19643", SCRIPT)
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)


def _expiration(argv, **kwargs):
    """Remplace `subprocess.run` : simule un `gh` qui depasse sa borne."""
    raise subprocess.TimeoutExpired(cmd=argv, timeout=kwargs.get("timeout", 0))


def test_gh_json_porte_une_borne_par_appel(monkeypatch):
    # La borne est passee a subprocess.run : sans elle, un gh bloque reste
    # sans borne (l'etat de origin/main avant #19643-residu).
    appels = {}

    def faux_run(argv, **kwargs):
        appels.update(kwargs)
        return subprocess.CompletedProcess(argv, 0, stdout="{}", stderr="")

    monkeypatch.setattr(subprocess, "run", faux_run)
    assert mod.gh_json(["api", "repos/jsboige/CoursIA/pulls/1/reviews"]) == {}
    assert "timeout" in appels, "gh_json doit passer timeout= a subprocess.run"
    assert appels["timeout"] == mod.GH_CALL_TIMEOUT_S
    assert 0 < mod.GH_CALL_TIMEOUT_S <= 120


def test_improper_dismissals_propage_l_expiration(monkeypatch):
    # Avant le correctif : l'expiration tombait dans `except Exception` et
    # rendait set(), donc une dismissal d'un tiers etait lue comme levee.
    monkeypatch.setattr(subprocess, "run", _expiration)
    with pytest.raises(subprocess.TimeoutExpired):
        mod.improper_dismissals(1)


def test_gh_fetch_issue_ne_cache_pas_none_sur_expiration(monkeypatch):
    # Avant le correctif : l'expiration donnait None, mis en cache pour ce
    # numero (« pas une issue »), donc une levee par issue etait refusee a
    # tort pour le reste du processus.
    cache = {}
    monkeypatch.setattr(mod, "_ISSUE_INFO_CACHE", cache)
    monkeypatch.setattr(subprocess, "run", _expiration)
    with pytest.raises(subprocess.TimeoutExpired):
        mod._gh_fetch_issue(999991)
    assert 999991 not in cache


def test_gh_fetch_issue_404_reste_none_et_cache(monkeypatch):
    # Controle positif : un echec franc (404, numero qui n'est pas une issue)
    # garde son sens d'origine, None mis en cache (#13725).
    cache = {}
    monkeypatch.setattr(mod, "_ISSUE_INFO_CACHE", cache)

    def not_found(argv, **kwargs):
        raise subprocess.CalledProcessError(1, argv)

    monkeypatch.setattr(subprocess, "run", not_found)
    assert mod._gh_fetch_issue(999992) is None
    assert cache == {999992: None}


def test_main_rend_non_mesure_sur_expiration(monkeypatch, capsys):
    # Avant le correctif : l'expiration remontait nue jusqu'a main() (traceback,
    # aucun verdict). Apres : « NON MESURE » sur stderr et rc=1, jamais rc=0.
    monkeypatch.setattr(mod.gh_identity, "pin_gh_token", lambda: "")
    monkeypatch.setattr(subprocess, "run", _expiration)
    monkeypatch.setattr(sys, "argv", ["check_unaddressed_nits.py", "123"])
    assert mod.main() == 1
    assert "NON MESURE" in capsys.readouterr().err
