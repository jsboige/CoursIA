"""Tests du banc case 19 — le mot « using » de RPT-1 (#8182, Butlin et al. 2023).

Les seuils viennent du pré-enregistrement scellé dans
``docs/ict/butlin-indicators-pre-enregistrement.md`` : bandes collapse 0.50,
inertie 0.01, fenêtre d'accuracy lésée [0.10, 0.35], graines test
(0, 1, 7, 42, 99), calibration sur graines disjointes (11/22/33).

Les tests ne mesurent pas de conscience : ils pincent la structure du jouet
(la tâche exige la mémoire, les trois architectures sont comportementalement
indiscernables, l'implémentation Real/Twin est indiscernable — l.780-782 du
papier), les verdicts structurels S1/S2, CHAQUE branche de la sonde causale,
le sham et le contrat de verdict — jamais les valeurs numériques du run
principal (déterministes par construction, vérifiées une fois dans le JSON de
résultats).
"""

from __future__ import annotations

import json
from pathlib import Path

import numpy as np

from ict.butlin_indicators import (
    ACC_LESION_THEORETICAL,
    ARCHITECTURES,
    BAND_COLLAPSE,
    K_SYMBOLS,
    SEEDS_CALIB,
    T_STEPS,
    _sample_sequences,
    _shift,
    calibrate,
    causal_probe,
    forward_puppet,
    forward_real,
    forward_twin,
    has_cycle,
    has_shared_weight_chain,
    run_protocol,
)

# Le JSON committé : sortie de run_protocol() (CLI ``--json``), CRLF à la
# livraison -- json.loads accepte les deux fins de ligne.
RESULTS_JSON = Path(__file__).resolve().parents[1] / "results" / "butlin_indicators_results.json"


def test_shift_inserts_head_and_shifts():
    """L'opération de mémoire insère en tête et décale — jamais un écrasement."""
    m = np.eye(K_SYMBOLS)[[1, 2, 3]]        # 3 positions occupées
    x = np.eye(K_SYMBOLS)[4]
    out = _shift(m, x)
    assert int(np.argmax(out[0])) == 4       # tête = nouveau symbole
    assert int(np.argmax(out[1])) == 1       # décalage d'une position
    assert int(np.argmax(out[2])) == 2


def test_task_requires_memory():
    """Le dernier symbole seul ne résout pas : un répondeur naïf échoue."""
    seqs, targets = _sample_sequences(0, 200)
    naive = np.array([int(np.argmax(seq[-1])) for seq in seqs])
    acc = float(np.mean(naive == targets))
    assert acc < 0.35    # au niveau du hasard (1/8 = 0.125), pas plus


def test_baselines_perfect():
    """Les trois architectures résolvent la tâche : le comportement ne
    discrimine pas (P1)."""
    seqs, targets = _sample_sequences(0, 200)
    for fwd in (forward_real, forward_twin, forward_puppet):
        assert float(np.mean([fwd(seqs[i]) == targets[i]
                              for i in range(len(seqs))])) == 1.0


def test_real_twin_predictions_indistinguishable():
    """Real et Twin sont indiscernables en sortie (le papier, l.780-782 :
    « implemented indistinguishably ») — la distinction vit dans le graphe."""
    seqs, _ = _sample_sequences(7, 100)
    for seq in seqs:
        assert forward_real(seq) == forward_twin(seq)


def test_lesion_loop_collapses_real_but_not_puppet():
    """La MÊME lésion (report coupé) : collapse sur Real, inertie exacte sur
    Puppet — le décor n'alimente pas la réponse."""
    seqs, targets = _sample_sequences(0, 300)
    acc_real = float(np.mean([forward_real(seqs[i], lesion="loop") == targets[i]
                              for i in range(len(seqs))]))
    assert acc_real < 0.35                       # collapse (analytique ≈ 0.234)
    preds = [forward_puppet(seqs[i], lesion="loop") for i in range(len(seqs))]
    preds_base = [forward_puppet(seqs[i]) for i in range(len(seqs))]
    assert preds == preds_base                   # inertie EXACTE


def test_lesion_selector_makes_puppet_constant():
    """Le porteur du Puppet est l'indexation single-shot : lésée, la réponse
    est constante."""
    seqs, _ = _sample_sequences(0, 100)
    preds = [forward_puppet(seqs[i], lesion="selector") for i in range(len(seqs))]
    assert set(preds) == {0}


def test_lesion_chain_collapses_twin():
    """Le report coupé dans la chaîne déroulée collapse le Twin."""
    seqs, targets = _sample_sequences(0, 300)
    acc = float(np.mean([forward_twin(seqs[i], lesion="chain") == targets[i]
                         for i in range(len(seqs))]))
    assert acc < 0.35


def test_sham_is_exact_identity_on_all_three():
    """La lésion du monitor (télémesure) est sans effet sur la sortie des
    trois architectures — sham dormant par construction (cf case 16)."""
    seqs, _ = _sample_sequences(1, 100)
    for fwd in (forward_real, forward_twin, forward_puppet):
        for seq in seqs:
            assert fwd(seq, lesion="monitor") == fwd(seq)


def test_s1_cycle_verdicts():
    """S1 (cycle) : présent sur Real et Puppet (le décor suffit au faux
    positif), absent sur Twin (faux négatif du mimique) — exact 1/3."""
    s1 = {n: has_cycle(a["nodes"], a["edges"]) for n, a in ARCHITECTURES.items()}
    assert s1 == {"real": True, "twin": False, "puppet": True}
    truth = {n: a["truth"] for n, a in ARCHITECTURES.items()}
    assert sum(s1[n] == truth[n] for n in truth) == 1


def test_s2_verdicts_still_blind_to_puppet():
    """S2 (cycle ou chaîne partagée) : guérit le faux négatif Twin, reste
    aveugle au faux positif Puppet — exact 2/3."""
    s2 = {n: (has_cycle(a["nodes"], a["edges"])
              or has_shared_weight_chain(a["nodes"], a["edges"], a["weights"]))
          for n, a in ARCHITECTURES.items()}
    assert s2 == {"real": True, "twin": True, "puppet": True}
    truth = {n: a["truth"] for n, a in ARCHITECTURES.items()}
    assert sum(s2[n] == truth[n] for n in truth) == 2


def test_shared_weight_chain_per_architecture():
    """Le prédicat de chaîne seul : vrai sur la chaîne déroulée du Twin
    (arêtes h_{t-1} -> h_t, même ensemble de poids), faux sur Real et Puppet
    (un seul nœud ``shift``, sa seule arête est une boucle, relevant de S1)."""
    chain = {n: has_shared_weight_chain(a["nodes"], a["edges"], a["weights"])
             for n, a in ARCHITECTURES.items()}
    assert chain == {"real": False, "twin": True, "puppet": False}


def test_shared_weight_chain_requires_an_edge_and_shared_weights():
    """Le prédicat exige une arête directe entre deux nœuds distincts ``shift``
    de MÊME ensemble de poids. Deux nœuds ``shift`` disjoints ne suffisent pas
    (le compteur d'origine rendait vrai ici) ; deux nœuds reliés mais de poids
    distincts ne suffisent pas non plus."""
    disjoint_nodes = {"in": "input", "a": "shift", "b": "shift", "out": "output"}
    disjoint_edges = [("in", "a"), ("a", "out"), ("in", "b"), ("b", "out")]
    shared = {"a": "W", "b": "W"}
    assert has_shared_weight_chain(disjoint_nodes, disjoint_edges, shared) is False
    # Arête directe, poids partagés : chaîne réelle.
    assert has_shared_weight_chain(disjoint_nodes, disjoint_edges + [("a", "b")],
                                   shared) is True
    # Arête directe, poids distincts : pas une chaîne à poids partagés.
    assert has_shared_weight_chain(disjoint_nodes, disjoint_edges + [("a", "b")],
                                   {"a": "W1", "b": "W2"}) is False
    # Une boucle n'est pas une chaîne (c'est S1).
    assert has_shared_weight_chain(disjoint_nodes, [("a", "a")], shared) is False


def test_causal_probe_identifies_carriers():
    """La sonde causale : porteurs {loop, chain, selector}, verdicts
    {oui, oui, non} — exact 3/3 ; Δ(sham) exactement nul."""
    seqs, targets = _sample_sequences(0, 300)
    probe = {n: causal_probe(a, seqs, targets) for n, a in ARCHITECTURES.items()}
    assert probe["real"]["carrier"] == "loop"
    assert probe["twin"]["carrier"] == "chain"
    assert probe["puppet"]["carrier"] == "selector"
    assert probe["real"]["verdict"] is True
    assert probe["twin"]["verdict"] is True
    assert probe["puppet"]["verdict"] is False
    assert probe["real"]["deltas"]["loop"] >= BAND_COLLAPSE
    assert probe["puppet"]["deltas"]["selector"] >= BAND_COLLAPSE
    assert probe["puppet"]["deltas"]["loop"] == 0.0
    for n in ARCHITECTURES:
        assert probe[n]["deltas"]["monitor"] == 0.0


def test_calibrate_bands_ok():
    """La calibration sur graines disjointes confirme les valeurs
    analytiques (baselines parfaites, collapse, fenêtre lésée, sham nul)."""
    cal = calibrate()
    assert cal["bands_ok"] is True
    assert all(SEEDS_CALIB[i] not in (0, 1, 7, 42, 99) for i in range(len(SEEDS_CALIB)))


def test_protocol_verdict_supported():
    """Contrat de verdict : SUPPORTED, P1/P4 tenues, P2/P3 échouent (les
    procédures structurelles se trompent sur ces témoins)."""
    out = run_protocol()
    assert out["verdict"] == "SUPPORTED"
    assert out["p1_baseline_perfect"] is True
    assert out["p4_causal_exact"] is True
    assert out["p2_s1_fails"] is True
    assert out["p3_s2_fails"] is True
    assert out["sham_max_abs_delta"] == 0.0
    assert out["structural"]["s1_exact"] == 1
    assert out["structural"]["s2_exact"] == 2
    assert all(c == 3 for c in out["c_exact_by_seed"])
    assert T_STEPS == 8


def test_calibration_values_cited_by_pr():
    """Rejeu de la calibration sur graines 11/22/33 : les accuracies lésées
    citées dans le body de la PR (0.228 / 0.232 / 0.248), la fenêtre et la
    valeur théorique 0.234375 (1/8 + 7/8 · 1/8)."""
    cal = calibrate()
    assert cal["seeds"] == [11, 22, 33]
    assert [r["acc_lesion_real"] for r in cal["by_seed"]] == [0.228, 0.232, 0.248]
    assert [r["delta_real"] for r in cal["by_seed"]] == [0.772, 0.768, 0.752]
    assert cal["acc_lesion_window"] == [0.10, 0.35]
    assert cal["acc_lesion_theoretical"] == ACC_LESION_THEORETICAL == 0.234375
    assert cal["bands_ok"] is True


def test_artifact_carries_replayable_calibration():
    """Le JSON committé porte le bloc ``calibration`` ; le rejouer depuis les
    graines seules redonne exactement ce bloc (types JSON, arrondis à 6 décimales)."""
    artifact = json.loads(RESULTS_JSON.read_text(encoding="utf-8"))
    assert artifact["calibration"] == calibrate()


def test_artifact_is_run_protocol_output():
    """Le JSON committé est égal (après parsing) à la sortie de run_protocol() :
    il se régénère par ``--json``, aucune valeur n'est éditée à la main."""
    artifact = json.loads(RESULTS_JSON.read_text(encoding="utf-8"))
    assert artifact == run_protocol()