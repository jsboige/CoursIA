#!/usr/bin/env python3
"""Le tapis voit-il les parapluies GELES par un veto user ? (#25082)

Le constat (11/11, action de `myia-ai-01`) : `frozen_campaigns.py` declare
`FROZEN_UMBRELLAS = {"11601": "17040"}`, mais le tapis ne lisait PAS cette
definition -- il ne lisait que des marqueurs `[FROZEN]` poses a la main dans
un corps ou un fil. Un parapluie defini comme gele pouvait donc etre servi
tant que la main posee avait oublie : la densification repartait sous #11601,
et ses PRs etaient refusees ensuite au merge (le gel etait la, mais plus
tard).

Ce que ces tests verrouillent :

  1. **chaque cle de `FROZEN_UMBRELLAS` est vue gelee par le tapis**, sans
     aucun acces reseau -- la garantie demandee ;
  2. le tapis **ecarte** un parapluie gele par veto (le filtre bon marche
     des marqueurs de cloture) ;
  3. la cause du gel **nomme le veto**, et dit comment il se leve ;
  4. une issue qui n'est pas dans la definition **n'est pas gelee** par elle.

La lecture ne doit pas passer par le reseau : un test qui sort sur le
reseau verifie l'etat de GitHub, pas le code.
"""

import importlib.util
import pathlib
import sys

import pytest

SCRIPTS = pathlib.Path(__file__).resolve().parent.parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))
if str(SCRIPTS / "coordination") not in sys.path:
    sys.path.insert(0, str(SCRIPTS / "coordination"))

import frozen_campaigns  # noqa: E402

_spec = importlib.util.spec_from_file_location(
    "pick_idle_grain_local", SCRIPTS / "pick_idle_grain.py")
pig = importlib.util.module_from_spec(_spec)
sys.modules["pick_idle_grain_local"] = pig
_spec.loader.exec_module(pig)


@pytest.fixture
def pas_de_reseau(monkeypatch):
    """Toute sortie reseau fait echouer le test.

    La lecture du gel d'un parapluie doit se faire sur la definition
    partagee, pas sur le fil : un test qui interroge GitHub verifie
    l'etat de GitHub."""
    def _boom(*args, **kwargs):
        raise AssertionError("la lecture du gel ne doit pas sortir sur le reseau")

    monkeypatch.setattr(pig, "_issue_comments", _boom)
    monkeypatch.setattr(pig, "_issue_body", _boom)


def test_la_definition_partagee_est_lue_par_le_tapis():
    """Le tapis importe la definition PARTAGEE : deux organes qui ne
    lisent pas la meme chose derivent, et c'est exactement le defaut
    qu'on corrige."""
    assert pig.frozen_campaigns is not None
    assert pig.frozen_campaigns is frozen_campaigns
    assert frozen_campaigns.FROZEN_UMBRELLAS, (
        "la definition des parapluies geles est vide : le test ne prouve "
        "plus rien")


def test_le_tapis_voit_gele_chaque_cle_de_frozen_umbrellas(pas_de_reseau):
    """LA garantie demandee : chaque cle de la definition est vue gelee par
    le tapis, sans acces reseau."""
    for key, veto in frozen_campaigns.FROZEN_UMBRELLAS.items():
        gel = pig.has_frozen_marker(int(key))
        assert gel is not None and gel is not False, (
            f"#{key} n'est pas vu gele par le tapis")
        assert str(veto) in gel, (
            f"#{key} : la source du gel ne nomme pas le veto ({gel!r})")


def test_le_tapis_ecarte_un_parapluie_gele_par_veto(pas_de_reseau):
    """Le filtre bon marche (marqueurs de cloture) ecarte aussi un
    parapluie gele par un veto : le gel est un veto transversal, pas une
    particularite de l'urne `grain`."""
    for key in frozen_campaigns.FROZEN_UMBRELLAS:
        assert pig.has_recent_delivery_marker(int(key)) is True


def test_la_cause_du_gel_nomme_le_veto_et_son_degel(pas_de_reseau):
    """La cause dit WHY, et dit comment le gel se leve : un gel de veto
    user ne se leve pas par un `[UNFROZEN]` de lane."""
    key, veto = next(iter(frozen_campaigns.FROZEN_UMBRELLAS.items()))
    gel = pig.has_frozen_marker(int(key))
    cause = pig.gel_cause_text(gel)
    assert cause is not None
    assert str(veto) in cause
    assert "FROZEN_UMBRELLAS" in cause


def test_une_issue_hors_definition_n_est_pas_gelee_par_le_veto(monkeypatch):
    """Controle negatif : la definition ne gele que ses cles."""
    monkeypatch.setattr(pig, "_issue_comments", lambda n: (None, None))
    monkeypatch.setattr(pig, "_issue_body", lambda n: None)
    gel = pig.has_frozen_marker(999999999)
    assert gel is None or gel is False
    assert not (isinstance(gel, str) and gel.startswith("veto #"))
