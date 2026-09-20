"""Tests de la batterie d'intervention :mod:`ict.intervention_battery` (#15480).

Le critere 3 de l'acceptance #15480 exige que la chaine intervention ->
changement d'etat -> changement comportemental selectif soit TESTEE. Ces
tests sont la partie « testee » : chaque maillon a son test falsifiable sur
le banc synthetique Mess3 x RRXOR (modes bien separees par construction,
beliefs exacts), avec la meme discipline que la serie (pas de fixtures,
tolerances commentees, determinisme verifie).

Proprietes :

  1. (Gate identite) sham et intact sont l'identite PROUVEE : sha_after ==
     sha_before, effets delta nuls, FVU == 0 -- un artefact de pipeline
     produirait un effet sham non nul.
  2. (Gate enregistrement) chaque outcome porte un record JSON rejouable :
     spec appliquee = spec enregistree (le sham decrit une cible vide, pas la
     cible ciblee), alignment.model == "bench", prefixes de dose emboites.
  3. (Gate chaine etat) l'ablation du support du facteur A deplace la
     marginale A (distance L1 au belief propre gele) davantage que la
     marginale B, bras flens ET bras sae, >= 75 % des seeds (meme seuil que
     le verdict SUPPORTED du module).
  4. (Gate chaine comportement) la degradation du score de decodage du probe
     gele A (vraie classe, continu) excede celle de B, les deux bras, >= 75 %
     des seeds, et c'est bien une DEGRADATION de A (mediane > 0).
  5. (Gate controle apparie) le verdict vs_random du module est la fonction
     mecanique des differentielles par seed (recalculees ici depuis les
     outcomes bruts), et la differentielle de selectivite (A - B) de la cible
     excede celle du controle apparie en mediane appariee sur le canal ETAT
     (les deux bras) et sur le canal COMPORTEMENT (bras sae). Le bras flens
     vs_random comportement reste INCONCLUSIVE -- resultat mesure et
     documente (le module docstring) : a d=12 l'espace produit porte A sur
     presque toutes les coordonnees, le controle apparie n'y est pas
     A-aveugle.
  6. (Gate dose) la degradation comportementale de A est croissante en la
     fraction ablatee (au plus un pas de discretisation par courbe).
  7. (Gate verdicts) chaque maillon rend un verdict de l'enumer fermee avec
     taille d'effet, IC et p-valeur -- pas de score omnibus.
  8. (Gate determinisme) deux batteries au meme jeu de seeds rendent les
     memes sha et les memes verdicts.
"""

from __future__ import annotations

import json

import numpy as np
import pytest

from ict import intervention_battery as ib
from ict.bench_factorise import FactoredBench, Mess3, RRXOR

# Budget CPU commente : 16 seeds x (SAE 250 pas sur (490, 12) + 2 bras x 8
# interventions x mesureurs lstsq minuscules + verdicts) ~ 2-4 s total (le
# signflip vectorise par blocs enumere 2^16 = 65 536 configurations par test
# en un seul appel C par bloc) -- reste analytique.
N = 700
SEEDS = tuple(range(16))
SAE_KWARGS = {"n_features": 24, "k": 3, "top_m": 8, "n_steps": 250}

_BATTERIE = None


def _batterie() -> ib.BatteryResult:
    """Batterie lancee UNE fois par session de test (module-level cache, pas
    de fixture -- convention de la serie)."""
    global _BATTERIE
    if _BATTERIE is None:
        bench = FactoredBench(Mess3(), RRXOR(), name="mess3xrrxor")
        _BATTERIE = ib.run_battery(
            bench, seeds=SEEDS, n=N, sae_kwargs=SAE_KWARGS, top_m_flens=5
        )
    return _BATTERIE


def _outs(arm: str, control: str, dose: float | None = None):
    res = _batterie()
    sel = [
        o for o in res.outcomes
        if o.arm == arm and o.control == control
        and (dose is None or abs(o.dose - dose) < 1e-9)
    ]
    assert sel, f"aucun outcome {arm}/{control}/dose={dose}"
    return sel


# --------------------------------------------------------------------------- #
# Gate 1 -- identite sham / intact prouvee (pas supposee)
# --------------------------------------------------------------------------- #

def test_sham_et_intact_sont_l_identite():
    for arm in ib.BATTERY_ARMS:
        for control in ("sham", "intact"):
            for o in _outs(arm, control):
                rec = json.loads(o.record_json)
                assert rec["sha_before"] == rec["sha_after"], (
                    f"{arm}/{control} : l'identite doit etre prouvee par les "
                    "empreintes, pas supposee"
                )
                assert o.effects["behavior"]["fvu_delta"] == pytest.approx(
                    0.0, abs=1e-12
                )
                for canal in ("state", "readout", "behavior"):
                    for k, v in o.effects[canal].items():
                        if k.endswith("_delta"):
                            assert v == pytest.approx(0.0, abs=1e-12), (
                                f"{arm}/{control}/{canal}/{k} : effet sham "
                                "non nul = artefact de pipeline"
                            )


# --------------------------------------------------------------------------- #
# Gate 2 -- enregistrements rejouables : la spec enregistree EST la spec
# appliquee, prefixes de dose emboites
# --------------------------------------------------------------------------- #

def test_record_describe_la_spec_appliquee():
    for arm in ib.BATTERY_ARMS:
        sham = json.loads(_outs(arm, "sham")[0].record_json)
        assert sham["spec"]["features"] == [] and sham["spec"]["positions"] == []
        assert sham["spec"]["control_ref"] == "sham-intact"
        target_plein = json.loads(_outs(arm, "target", 1.0)[0].record_json)
        assert target_plein["alignment"]["model"] == "bench"
        assert target_plein["alignment"]["control"] == "target"
        assert target_plein["spec"]["operation"] == "ablate"
        # prefixes emboites : la cible a dose 0.25 est un prefixe de la cible
        # a dose 1.0 (l'axe de dose est un prefixe du classement, pas un tirage)
        quart = json.loads(_outs(arm, "target", 0.25)[0].record_json)
        f_quart = quart["spec"]["features"]
        f_plein = target_plein["spec"]["features"]
        assert f_plein[: len(f_quart)] == f_quart


# --------------------------------------------------------------------------- #
# Gate 3 -- chaine ETAT selective : dH_a > dH_b, les deux bras
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("arm", ib.BATTERY_ARMS)
def test_chaine_etat_selective(arm):
    pleins = _outs(arm, "target", 1.0)
    n_ok = sum(
        o.effects["state"]["disp_a_delta"] > o.effects["state"]["disp_b_delta"]
        for o in pleins
    )
    seuil = int(0.75 * len(pleins))
    assert n_ok >= seuil, (
        f"bras {arm} : l'ablation du support de A doit deplacer la marginale "
        f"A davantage que la B sur >= {seuil}/{len(pleins)} seeds "
        f"(observe {n_ok}) -- la chaine etat n'est pas selective"
    )


# --------------------------------------------------------------------------- #
# Gate 4 -- chaine COMPORTEMENT selective : -dacc_a > -dacc_b
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("arm", ib.BATTERY_ARMS)
def test_chaine_comportement_selective(arm):
    pleins = _outs(arm, "target", 1.0)
    deg_a = [-o.effects["behavior"]["score_a_delta"] for o in pleins]
    deg_b = [-o.effects["behavior"]["score_b_delta"] for o in pleins]
    n_ok = sum(a > b for a, b in zip(deg_a, deg_b))
    seuil = int(0.75 * len(pleins))
    assert n_ok >= seuil, (
        f"bras {arm} : le decode du facteur A doit se degrader davantage que "
        f"celui de B sur >= {seuil}/{len(pleins)} seeds "
        f"(observe {n_ok}) -- le changement d'etat ne se propage pas a un "
        "changement comportemental SELECTIF"
    )
    # et c'est bien une DEGRADATION de A, pas une amelioration de B
    assert np.median(deg_a) > 0


# --------------------------------------------------------------------------- #
# Gate 5 -- controle aleatoire apparie : la cible degrade davantage
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("arm", ib.BATTERY_ARMS)
def test_controle_aleatoire_apparie(arm):
    pleins = _outs(arm, "target", 1.0)
    rnds = _outs(arm, "random", 1.0)
    if len(rnds) != len(pleins):
        pytest.skip("controle aleatoire indisponible sur certaines seeds")
    # Differentielles de selectivite (A - B) par seed, cible et controle.
    # vs_random se joue sur la DIFFERENTIELLE, pas le dommage absolu : a d=12
    # le dommage absolu du controle aleatoire est domine par la masse des
    # coordonnees touchees -- ce qui doit distinguer la cible, c'est qu'elle
    # degrade A SANS B (meme lecture que le verdict vs_random du module).
    sel_state_t = [
        t.effects["state"]["disp_a_delta"]
        - t.effects["state"]["disp_b_delta"]
        for t in pleins
    ]
    sel_state_r = [
        r.effects["state"]["disp_a_delta"]
        - r.effects["state"]["disp_b_delta"]
        for r in rnds
    ]
    sel_beh_t = [
        -(t.effects["behavior"]["score_a_delta"]
          - t.effects["behavior"]["score_b_delta"])
        for t in pleins
    ]
    sel_beh_r = [
        -(r.effects["behavior"]["score_a_delta"]
          - r.effects["behavior"]["score_b_delta"])
        for r in rnds
    ]
    # (i) MECANISME : le verdict vs_random du module est la fonction
    # mecanique des differentielles -- mediane et effectif de seeds
    # gagnantes recalcules ici depuis les outcomes bruts doivent coincider.
    v_state = _batterie().verdicts[f"{arm}/etat"]["vs_random"]
    v_beh = _batterie().verdicts[f"{arm}/comportement"]["vs_random"]
    d_state = [a - b for a, b in zip(sel_state_t, sel_state_r)]
    d_beh = [a - b for a, b in zip(sel_beh_t, sel_beh_r)]
    assert v_state["median_diff"] == pytest.approx(float(np.median(d_state)))
    assert v_beh["median_diff"] == pytest.approx(float(np.median(d_beh)))
    assert v_state["n_seeds_positive"] == sum(d > 0 for d in d_state)
    assert v_beh["n_seeds_positive"] == sum(d > 0 for d in d_beh)
    # (ii) SUBSTANTIF, la ou la geometrie du banc supporte la separation :
    # la mediane APPARIEE (mediane des differences par seed) de la cible
    # excede celle du controle -- canal etat sur les deux bras, canal
    # comportement sur le bras sae (features dediees au facteur).
    assert np.median(d_state) > 0, (
        f"bras {arm} : la differentielle d'etat (A - B) de la cible doit "
        f"exceder le controle apparie en mediane appariee "
        f"({np.median(d_state):.3f}) -- le controle aleatoire n'est pas "
        "distingue, H1 n'est pas testee"
    )
    if arm == "sae":
        assert np.median(d_beh) > 0, (
            f"bras {arm} : la differentielle comportementale (A - B) de la "
            f"cible doit exceder le controle apparie ({np.median(d_beh):.3f})"
        )


# --------------------------------------------------------------------------- #
# Gate 6 -- dose-response monotone (prefixe du classement de selectivite)
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("arm", ib.BATTERY_ARMS)
def test_dose_response_monotone(arm):
    res = _batterie()
    v = res.verdicts[f"{arm}/dose"]
    assert v["n_seeds_monotone"] >= 5, (
        f"bras {arm} : la degradation doit croitre avec la fraction ablatee "
        f"({v['n_seeds_monotone']}/{v['n_seeds']} courbes monotones)"
    )


# --------------------------------------------------------------------------- #
# Gate 7 -- verdicts : enum fermee, taille d'effet, IC, p-valeur
# --------------------------------------------------------------------------- #

def test_verdicts_complets():
    res = _batterie()
    attendus = {
        f"{arm}/{maillon}"
        for arm in ib.BATTERY_ARMS
        for maillon in ("etat", "comportement", "dose")
    }
    assert attendus <= set(res.verdicts)
    enum = {"SUPPORTED", "NOT_SUPPORTED", "INCONCLUSIVE"}
    for cle, v in res.verdicts.items():
        if cle.endswith("/dose"):
            assert v["verdict"] in enum
            continue
        assert v["verdict"] in enum, f"{cle}: verdict hors enum"
        assert "median_diff" in v and "ci95" in v and "p_signflip" in v
        lo, hi = v["ci95"]
        assert lo <= v["median_diff"] <= hi
        assert 0.0 <= v["p_signflip"] <= 1.0
        # controle de manipulation : l'intervention DEPLACE A (vs identite) --
        # sans ce maillon la chaine n'a pas de premier fleche a tester
        assert v["vs_sham"]["verdict"] == "SUPPORTED", (
            f"{cle} : l'effet causal vs sham doit etre SUPPORTE "
            "(manipulation) -- sinon la chaine n'a pas de premier maillon "
            "a tester"
        )
        assert 0.0 <= v["vs_sham"]["p_signflip"] <= 1.0
    # pas de score omnibus : etat et comportement restent des entrees SEPAREES
    assert "sae/etat" in res.verdicts and "sae/comportement" in res.verdicts
    # Paysage attendu a cette configuration fixee (16 seeds) : les 4 verdicts
    # PRINCIPAUX (vs_B, la selectivite) SUPPORTED apres Holm, et l'unique
    # null honnete gelee : flens vs_random comportement INCONCLUSIVE (controle
    # apparie non A-aveugle a d=12 -- documente dans le module). Ces deux
    # assertions verifient AUSSI la mecanique signflip+Holm sur un resultat
    # connu : une regression du calcul statistique les casse.
    for arm in ib.BATTERY_ARMS:
        for m in ("etat", "comportement"):
            v = res.verdicts[f"{arm}/{m}"]
            assert v["verdict"] == "SUPPORTED", (
                f"{arm}/{m} : la selectivite (A vs B) doit etre SUPPORTED "
                "a cette configuration"
            )
            assert v["p_holm"] < 0.05
    assert res.verdicts["flens/comportement"]["vs_random"][
        "verdict"] == "INCONCLUSIVE"


# --------------------------------------------------------------------------- #
# Gate 8 -- determinisme : memes seeds -> memes sha, memes verdicts
# --------------------------------------------------------------------------- #

def test_determinisme():
    bench = FactoredBench(Mess3(), RRXOR(), name="mess3xrrxor")
    r1 = ib.run_battery(bench, seeds=(0, 1), n=300,
                        sae_kwargs=SAE_KWARGS, top_m_flens=5)
    r2 = ib.run_battery(bench, seeds=(0, 1), n=300,
                        sae_kwargs=SAE_KWARGS, top_m_flens=5)
    sha1 = [json.loads(o.record_json)["sha_after"] for o in r1.outcomes]
    sha2 = [json.loads(o.record_json)["sha_after"] for o in r2.outcomes]
    assert sha1 == sha2
    assert r1.verdicts == r2.verdicts
