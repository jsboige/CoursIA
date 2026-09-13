"""Tests du banc causal case 5bis (#15798).

Ce qui est épinglé, par coût d'erreur décroissant :

1. **L'état porté est EMPIRIQUE** (leçon mesurée seed 0 : patcher la
   signature agrégée écrit des zéros sur des zéros) — les features cibles
   sont l'union des actifs du donneur À SA fenêtre.
2. **λ=0 est l'identité PAR LA MÊME VOIE** (sham du moteur) et λ=1 porte
   l'argmax du donneur sur bras synthétiques séparables.
3. **Chaque branche de la table de verdict scellée** (FALSIFIED /
   INCONCLUSIF-rupture-générique / INCONCLUSIF-contrôle-manquant /
   CONFIRMED) — testée isolément sur PairResults synthétiques.
4. **L'ordre anti-HARKing** et le contrôle aléatoire jamais dégradé
   silencieusement (indisponibilité ENREGISTRÉE).
"""
from __future__ import annotations

import json

import numpy as np
import pytest

from ict import attention_schema_causal as ac
from ict import causal_engine as ce

D_SYN = 4096
CTX = ["ctx"] * 20


def _entry(tokens, feat_block, base=5, top=10, scale=1.0):
    """Entrée synthétique : positions de contexte -> feature `base` faible,
    positions de clause -> `feat_block..feat_block+top-1`. ``scale`` amplifie
    les valeurs de clause (le donneur de test doit DOMINER les features
    propres du receveur, qui persistent hors cible -- sémantique patch)."""
    T = len(tokens)
    ids = np.zeros((T, 2), dtype=np.int32)
    vals = np.zeros((T, 2), dtype=np.float16)
    for t in range(T):
        if tokens[t] == "ctx":
            ids[t] = [base, base + 1]
            vals[t] = [0.5, 0.3]
        else:
            # ids TOUJOURS distincts (un doublon ferait gagner le last-write
            # de densify et fabriquerait des égalités d'argmax artificielles)
            ids[t] = [feat_block, feat_block + 1 + (t % (top - 1))]
            vals[t] = [4.0 * scale, 2.0 * scale]
    return {"ids": ids, "vals": vals, "tokens": np.array(tokens)}


def _syn_traces(seed: int = 0) -> dict:
    """3 bras case-5-like : contextes partagés, clauses disjointes."""
    prompts = {}
    for name, clause, block, scale in (
        ("attn_self", ["A"] * 8, 1000, 1.0),
        ("attn_other", ["B"] * 9, 2000, 1.0),
        ("obj_chaise", ["C"] * 7, 3000, 2.0),
        ("calib_obj1", ["N1"] * 8, 4000, 2.0),
        ("calib_obj2", ["N2"] * 8, 4016, 2.0),
    ):
        for i in range(3):
            prompts[(name, i)] = _entry(CTX + clause, block, scale=scale)
    return {"meta": {"d_sae": D_SYN, "layer": 12, "seed": seed,
                     "model": "synthetic", "k": 2},
            "prompts": prompts}


def _dense(traces, name, i):
    d = ac._densify_entry(traces, name, i)
    return d


# --- 1. fenêtre : divergence + suffixe ---------------------------------------

def test_find_divergence_first_differing_token():
    assert ac.find_divergence(["a", "b", "c"], ["a", "b", "d"]) == 2
    assert ac.find_divergence(["a", "b"], ["a", "b", "c", "d"]) == 2  # préfixe


def test_suffix_window_last_k_positions():
    ta = CTX + ["A"] * 8            # T=28, clause 8
    tb = CTX + ["B"] * 11           # T=31, clause 11
    pos_a, pos_b, k = ac.suffix_window(ta, tb)
    assert k == 8
    assert list(pos_a) == list(range(20, 28))
    assert list(pos_b) == list(range(23, 31))


def test_suffix_window_identical_prompts_degenerate_raises():
    with pytest.raises(ValueError, match="fenêtre vide"):
        ac.suffix_window(["a", "b"], ["a", "b"])


# --- 2. cible empirique + patch ----------------------------------------------

def test_donor_features_are_the_empirical_window_state():
    tr = _syn_traces()
    d_b = _dense(tr, "attn_other", 0)
    pos_a, pos_b, _k = ac.suffix_window(
        [str(t) for t in tr["prompts"][("attn_self", 0)]["tokens"]],
        [str(t) for t in tr["prompts"][("attn_other", 0)]["tokens"]])
    feats = ac.donor_features(d_b["dense"], pos_b)
    # La fenêtre du donneur active exactement son bloc empirique 2000..2008
    # (top-1 constant 2000 + un t%10 par position) -- PAS la signature
    # agrégée, PAS les features de contexte : l'état réel de la fenêtre.
    assert feats and set(feats) <= set(range(2000, 2010))
    assert 2000 in feats and len(feats) == 9


def test_patch_lam_zero_is_identity_same_code_path():
    tr = _syn_traces()
    d_a = _dense(tr, "attn_self", 0)
    d_b = _dense(tr, "attn_other", 0)
    pos_a, pos_b, _k = ac.suffix_window(d_a["tokens"], d_b["tokens"])
    feats = ac.donor_features(d_b["dense"], pos_b)
    out = ac.patch_window(d_a["dense"], d_b["dense"], pos_a, pos_b, feats, 0.0)
    assert np.array_equal(out, d_a["dense"])   # sham : identité, même voie


def test_patch_lam_one_carries_donor_argmax():
    tr = _syn_traces()
    d_a = _dense(tr, "attn_self", 0)
    d_b = _dense(tr, "obj_chaise", 0)
    pos_a, pos_b, _k = ac.suffix_window(d_a["tokens"], d_b["tokens"])
    feats = ac.donor_features(d_b["dense"], pos_b)
    out = ac.patch_window(d_a["dense"], d_b["dense"], pos_a, pos_b, feats, 1.0)
    am_out = np.argmax(out[pos_a, :], axis=1)
    am_donor = np.argmax(d_b["dense"][pos_b, :], axis=1)
    assert np.all(am_out == am_donor)          # l'état du donneur est porté


def test_flip_curve_monotone_on_separable_arms():
    tr = _syn_traces()
    d_a = _dense(tr, "attn_self", 0)
    d_b = _dense(tr, "obj_chaise", 0)
    pos_a, pos_b, _k = ac.suffix_window(d_a["tokens"], d_b["tokens"])
    from ict.sae_traces import mean_activation_by_set
    means = mean_activation_by_set(tr)
    sig_obj = np.argsort(means["obj_chaise"])[::-1][:ac.K_FEATURES]
    curve = ac.flip_curve(d_a["dense"], d_b["dense"], pos_a, pos_b, sig_obj)
    doses = sorted(d for d in curve if d > 0)
    vals = [curve[d] for d in doses]
    assert curve[0.0] == 0.0
    assert all(b >= a for a, b in zip(vals, vals[1:])), (doses, vals)
    assert curve[1.0] > 0.5                     # bascule massive sur bras séparables


def test_composition_empty_window_raises():
    with pytest.raises(ValueError, match="fenêtre vide"):
        ac.composition(np.zeros((0, 4), dtype=np.float32), np.arange(3))


# --- 3. null neutre + verdicts ----------------------------------------------

def _null(eps: float = 0.1) -> dict:
    return {"epsilon_flip": eps, "sigma_null": 0.05, "scale_intact_median": 1.0}


def _pair(flip1: float, rand=np.nan, mono=True, seed=0) -> ac.PairResult:
    doses = (0.25, 0.5, 0.75, 1.0)
    vals = [flip1 * d for d in doses]
    return ac.PairResult(
        arm="attn_self", donor="attn_other", seed=seed, context=0,
        divergence=20, window_k=8, n_target_features=10,
        flip_by_dose={0.0: 0.0, **{d: v for d, v in zip(doses, vals)}},
        flip_random_control=rand,
        damage={"target_rel": 0.1, "off_target_rel": 0.0,
                "selectivity_ratio": 100.0} if not mono else
               {"target_rel": 0.1, "off_target_rel": 0.0, "selectivity_ratio": 100.0})


def test_axis_verdict_falsified_when_flip_below_eps():
    res = [_pair(flip1=0.05, seed=s) for s in (0, 1, 7, 42, 99)]
    axes = ac.axis_verdicts(res, _null(eps=0.1))
    assert axes["attn_self<-attn_other"]["etat"] == "FALSIFIED"


def test_axis_verdict_confirmed_when_flip_passes_controls_clean():
    res = [_pair(flip1=0.4, rand=0.0, seed=s) for s in (0, 1, 7, 42, 99)]
    axes = ac.axis_verdicts(res, _null(eps=0.1))
    a = axes["attn_self<-attn_other"]
    assert a["etat"] == "CONFIRMED"
    assert a["comportement"] == "NOT_MEASURABLE_FROZEN"


def test_axis_verdict_inconclusive_when_random_control_missing():
    res = [_pair(flip1=0.4, rand=np.nan, seed=s) for s in (0, 1, 7, 42, 99)]
    axes = ac.axis_verdicts(res, _null(eps=0.1))
    assert axes["attn_self<-attn_other"]["etat"] == "INCONCLUSIF"


def test_axis_verdict_inconclusive_when_random_control_flips_too():
    res = [_pair(flip1=0.4, rand=0.4, seed=s) for s in (0, 1, 7, 42, 99)]
    axes = ac.axis_verdicts(res, _null(eps=0.1))
    assert axes["attn_self<-attn_other"]["etat"] == "INCONCLUSIF"


def test_axis_verdict_needs_four_seeds_above_eps():
    flips = {0: 0.4, 1: 0.4, 7: 0.4, 42: 0.05, 99: 0.05}
    res = [_pair(flip1=v, rand=0.0, seed=s) for s, v in flips.items()]
    axes = ac.axis_verdicts(res, _null(eps=0.1))
    assert axes["attn_self<-attn_other"]["etat"] == "FALSIFIED"


def test_random_control_unavailable_is_recorded_never_silent(tmp_path, monkeypatch):
    """Corpus dénudé : aucune candidate appariée -> NaN ENREGISTRÉ + damage
    porte 'UNAVAILABLE' -- le verdict en tient compte (INCONCLUSIF si flips)."""
    tr_main = {s: _syn_traces(s) for s in (0, 1, 7)}
    tr_calib = {s: _syn_traces(s) for s in (0, 1, 7)}

    def _boom(*a, **k):
        raise ValueError("aucune candidate appariée")

    monkeypatch.setattr(ce, "random_target_matched", _boom)
    res = ac.run_main_arms(tr_main, tr_calib)
    assert res, "au moins une paire"
    assert all(np.isnan(r.flip_random_control) for r in res)
    assert all(r.damage.get("random_control") == "UNAVAILABLE" for r in res)


# --- 4. run complet + anti-HARKing -------------------------------------------

def test_run_analysis_serializable_with_labels():
    SEEDS5 = (0, 1, 7, 42, 99)
    tr_main = {s: _syn_traces(s) for s in SEEDS5}
    tr_calib = {s: _syn_traces(s) for s in SEEDS5}
    out = ac.run_analysis(_null(eps=0.1), tr_main, tr_calib)
    blob = json.dumps(out, ensure_ascii=False)      # sérialisable
    assert "case5bis_attention_schema_causal" in blob
    for key in ("axes", "diagnostic_posthoc_non_scelle",
                "bras_supplementaires_non_scelles", "limits"):
        assert key in out
    for axe in out["axes"].values():
        assert axe["comportement"] == "NOT_MEASURABLE_FROZEN"
    # CONTRÔLE POSITIF du pipeline : bras séparables + contrôles aléatoires
    # DISPONIBLES sur corpus synthétique -> la machinerie DOIT confirmer.
    # (Sur les traces réelles, le même code rend FALSIFIED : la bascule
    # scellée ne dépasse pas eps -- cf results json.)
    assert out["axes"]["attn_self<-obj_chaise"]["etat"] == "CONFIRMED"


def test_neutral_null_formula_and_three_seed_floor():
    calib = {}
    for s, drift in zip((0, 1, 7), (0.0, 0.0, 0.2)):
        tr = _syn_traces(s)
        # Le donneur neutre N2 et le receveur N1 partagent la structure du
        # contexte ; la bascule est nulle par construction (mêmes features),
        # on injecte la dérive via une graine au feat_block décalé.
        if drift:
            tr["prompts"][("calib_obj2", 0)] = _entry(
                CTX + ["N2"] * 8, 4016 + int(drift * 100))
        calib[s] = tr
    null = ac.neutral_null(calib)
    assert null["n_graines"] == 3
    assert null["sigma_null"] >= 0.0
    assert null["formula"].startswith("epsilon_flip = 0.5")


def test_cli_run_refuses_without_frozen_null(tmp_path):
    """Anti-HARKing opérationnel : le fichier de null gelé est EXIGÉ."""
    import subprocess, sys
    tr = _syn_traces(0)
    npz = tmp_path / "t.npz"
    np.savez(npz)
    proc = subprocess.run(
        [sys.executable, "-m", "ict.attention_schema_causal", "run",
         "--main", str(npz), str(npz), str(npz), str(npz), str(npz),
         "--calib", str(npz), str(npz), str(npz), str(npz), str(npz),
         "--null", str(tmp_path / "absent.json"),
         "--out", str(tmp_path / "o.json")],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
        cwd=str(__file__.rsplit("ict", 1)[0]))
    assert proc.returncode != 0
    assert "absent.json" in proc.stderr or "No such file" in proc.stderr
