"""Tests du module :mod:`ict.slens` (Epic #15475, grain #15481).

Couvre les acceptances du POC S-Lens vérifiables sans GPU :

  1. (Gate oracle) les deux bancs produisent une ground truth EXACTE : le
     generateur est confronte a l'oracle independant, jamais l'inverse ;
     un token d'offset hors bornes est refuse nommement.
  2. (Gate distribution) la distribution ground-truth des positions est
     exacte (somme 1, support = positions atteignables).
  3. (Gate appariement) les paires contre-factuelles partagent le bloc de
     valeurs, different d'offset, et leurs cibles viennent de l'oracle.
  4. (Gate probe) le ridge closed-form recupere un encodage lineaire connu,
     le shuffle retombe au plancher, et les metriques sont held-out.
  5. (Gate self-location) un encodage lineaire synthetique de la position est
     detecte par tete ; du bruit ne l'est pas ; le split est partage.
  6. (Gate causal) le verdict de location separe effet apparie / sham /
     cible aleatoire / dommage global.
  7. (Gate promotion) PROMOTE exige les deux bancs ET le verdict causal ;
     instabilite multi-seeds ou absence de signal rend INCONCLUSIVE ;
     un seul banc rend SPECIALIZED_ONLY.
  8. (Gate contrat) le manifeste porte la note de statut POC et n'est pas
     confondu avec un manifeste valide du contrat v1.

Pattern herite de ``test_causal_engine.py`` (bootstrap sys.path module-level,
fixtures synthetiques deterministes, tolerances commentees).
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent.parent))

from ict import slens  # noqa: E402
from ict import trace_contract  # noqa: E402


CFG = slens.CopyOffsetConfig(seq_values=8, n_symbols=10)
VCFG = slens.VarBindingConfig(n_pairs=4, n_vars=6, n_vals=6)


# --------------------------------------------------------------------------- #
# 1. Oracles
# --------------------------------------------------------------------------- #

def test_oracle_confirms_generator_copy_offset():
    rng = np.random.default_rng(0)
    batch = slens.generate_copy_offset(rng, 512, CFG)
    val, pos = slens.oracle_copy_offset(batch["tokens"], CFG)
    assert np.array_equal(val, batch["target_value"])
    assert np.array_equal(pos, batch["target_pos"])
    # l'offset est bien dans le contenu, pas dans la position du token
    assert np.array_equal(batch["tokens"][:, CFG.seq_values] - CFG.n_symbols + 1,
                          batch["offset"])


def test_oracle_confirms_generator_variable_binding():
    rng = np.random.default_rng(1)
    batch = slens.generate_variable_binding(rng, 512, VCFG)
    val, pos = slens.oracle_variable_binding(batch["tokens"], VCFG)
    assert np.array_equal(val, batch["target_value"])
    assert np.array_equal(pos, batch["target_pos"])


def test_offset_token_out_of_bounds_is_named():
    tokens = np.zeros((1, CFG.n_tokens), dtype=np.int64)
    tokens[0, CFG.seq_values] = CFG.n_symbols + CFG.seq_values + 3  # offset > L
    with pytest.raises(ValueError, match="offset hors bornes"):
        slens.oracle_copy_offset(tokens, CFG)


def test_generator_rejects_bad_config():
    with pytest.raises(ValueError, match="bornes d'offset"):
        slens.CopyOffsetConfig(seq_values=4, min_offset=5)
    with pytest.raises(ValueError, match="exceder n_vars"):
        slens.VarBindingConfig(n_pairs=5, n_vars=3)
    with pytest.raises(ValueError, match="strictement positif"):
        slens.generate_copy_offset(np.random.default_rng(0), 0, CFG)


# --------------------------------------------------------------------------- #
# 2. Distribution ground-truth exacte
# --------------------------------------------------------------------------- #

def test_exact_position_distribution_full_block():
    dist = slens.exact_position_distribution(CFG)
    assert dist.shape == (CFG.seq_values,)
    assert dist.sum() == pytest.approx(1.0)
    assert np.allclose(dist, 1.0 / CFG.seq_values)


def test_exact_position_distribution_partial_bounds():
    cfg = slens.CopyOffsetConfig(seq_values=6, min_offset=2, max_offset=4)
    dist = slens.exact_position_distribution(cfg)
    support = np.flatnonzero(dist > 0)
    # offsets 2..4 -> positions 6-2=4, 3, 2
    assert set(support.tolist()) == {2, 3, 4}
    assert dist.sum() == pytest.approx(1.0)


# --------------------------------------------------------------------------- #
# 3. Paires contre-factuelles
# --------------------------------------------------------------------------- #

def test_paired_by_offset_shares_context_and_differs():
    rng = np.random.default_rng(7)
    pairs = slens.paired_by_offset(CFG, rng, 256)
    assert not np.any(pairs["offset_a"] == pairs["offset_b"])
    # meme bloc de valeurs a gauche du token d'offset
    L = CFG.seq_values
    assert np.array_equal(pairs["tokens_a"][:, :L], pairs["tokens_b"][:, :L])
    assert np.array_equal(pairs["tokens_a"][:, L + 1:],
                          pairs["tokens_b"][:, L + 1:])
    # les cibles du donneur viennent de l'oracle, pas du generateur
    val_b, pos_b = slens.oracle_copy_offset(pairs["tokens_b"], CFG)
    assert np.array_equal(val_b, pairs["target_value_b"])
    assert np.array_equal(pos_b, pairs["target_pos_b"])


def test_paired_by_query_shares_context_and_switches_reference():
    rng = np.random.default_rng(8)
    pairs = slens.paired_by_query(VCFG, rng, 256)
    # tout le contexte de liaisons est partage ; seule la variable interrogee change
    assert np.array_equal(pairs["tokens_a"][:, :-1], pairs["tokens_b"][:, :-1])
    assert not np.any(pairs["tokens_a"][:, -1] == pairs["tokens_b"][:, -1])
    val_b, pos_b = slens.oracle_variable_binding(pairs["tokens_b"], VCFG)
    assert np.array_equal(val_b, pairs["target_value_b"])
    assert np.array_equal(pos_b, pairs["target_pos_b"])
    # les deux cibles diffèrent : meme contexte, reference differente
    assert not np.array_equal(pairs["target_value_a"], pairs["target_value_b"])


# --------------------------------------------------------------------------- #
# 4. Probe ridge et metriques held-out
# --------------------------------------------------------------------------- #

def test_ridge_recovers_known_linear_map():
    rng = np.random.default_rng(3)
    x = rng.normal(size=(400, 6))
    w_true = rng.normal(size=(6, 1))
    y = x @ w_true + 0.1
    w = slens.ridge_probe(x[:300], y[:300], alpha=1e-8)
    pred = np.concatenate([x[300:], np.ones((100, 1))], axis=1) @ w
    assert np.allclose(pred, y[300:], atol=1e-4)
    m = slens.probe_metrics(x[300:], y[300:, 0], w)
    assert m["r2"] > 0.999
    assert m["n_test"] == 100


def test_probe_metrics_exact_hit_on_separable_classes():
    rng = np.random.default_rng(4)
    n_per = 40
    centres = np.eye(4) * 5.0
    x = np.concatenate([c + rng.normal(scale=0.1, size=(n_per, 4)) for c in centres])
    y = np.repeat(np.arange(4), n_per)
    onehot = np.eye(4)[y]
    # split par permutation : les 4 classes doivent etre vues a l'entrainement,
    # sinon l'exactitude held-out mesure l'absence de classe, pas le probe.
    order = rng.permutation(x.shape[0])
    tr, te = order[:120], order[120:]
    w = slens.ridge_probe(x[tr], onehot[tr], alpha=1e-6)
    assert set(y[tr].tolist()) == {0, 1, 2, 3}
    m = slens.probe_metrics(x[te], y[te], w)
    assert m["exact_hit"] == pytest.approx(1.0)


def test_shuffle_control_falls_to_floor():
    rng = np.random.default_rng(5)
    x = rng.normal(size=(300, 8))
    y = rng.integers(0, 5, size=300)
    scores = slens.shuffle_control_scores(x, y, y, rng=rng)
    # appariement detruit : l'exactitude held-out reste au plancher (1/5 = 0.2)
    assert scores["value_exact"] < 0.45
    assert scores["position_exact"] < 0.45


# --------------------------------------------------------------------------- #
# 5. Self-location par tete
# --------------------------------------------------------------------------- #

def test_self_location_reads_values_on_a_sparse_label_space():
    """Un vocabulaire de valeurs qui ne commence pas a 0 reste lisible.

    Recoder les classes en indices compacts pour la regression puis passer les
    ids BRUTS a la metrique rendait ``value_exact`` nul par construction des que
    le premier id observe n'est pas 0 — le cas du banc binding, dont les valeurs
    vivent dans ``n_vars..n_vars+n_vals-1`` (defaut corrige : la cible passee a
    la metrique est la meme recodee que la regression).
    """
    rng = np.random.default_rng(21)
    n, n_pos, n_val, shift = 600, 8, 6, 5
    positions = rng.integers(0, n_pos, size=n)
    values = shift + rng.integers(0, n_val, size=n)      # ids 5..10, pas 0..5
    acts = np.concatenate(
        [np.eye(n_pos)[positions] + rng.normal(scale=0.05, size=(n, n_pos)),
         np.eye(n_val)[values - shift] + rng.normal(scale=0.05, size=(n, n_val))],
        axis=1,
    )
    rows = slens.self_location_table({"L0": acts}, positions, values=values,
                                     alpha=1e-6, n_labels=n_pos)
    assert rows[0]["value_exact"] > 0.9
    assert rows[0]["value_classes"] == n_val
    # memes probes sur le meme recodage, appariement detruit : le plancher doit
    # rester au niveau du hasard — sinon c'est le recodage qui produit le score.
    floor = slens.shuffle_control_scores(
        acts, positions, values, rng=np.random.default_rng(2), alpha=1e-6)
    assert floor["value_exact"] < 0.45


def test_self_location_detects_linear_position_code_and_rejects_noise():
    rng = np.random.default_rng(11)
    n, n_pos, d = 600, 8, 12
    positions = rng.integers(0, n_pos, size=n)
    values = rng.integers(0, 6, size=n)
    # tete informative : la position est lineairement lisible (one-hot bruite)
    informative = np.eye(n_pos)[positions] + rng.normal(scale=0.05, size=(n, n_pos))
    # tete informative aussi pour la valeur (bloc separe)
    informative = np.concatenate(
        [informative, np.eye(6)[values] + rng.normal(scale=0.05, size=(n, 6))], axis=1
    )
    noise = rng.normal(size=(n, d))
    rows = slens.self_location_table(
        {"L0H0": informative, "L0H1": noise}, positions, values=values,
        alpha=1e-6, n_labels=n_pos,
    )
    by_unit = {r["unit"]: r for r in rows}
    assert by_unit["L0H0"]["position_exact"] > 0.9
    assert by_unit["L0H0"]["value_exact"] > 0.9
    assert by_unit["L0H1"]["position_exact"] < 0.5
    # le split est partage : meme n_test pour toutes les unites
    assert by_unit["L0H0"]["position_rmse"] >= 0.0


def test_self_location_rejects_misaligned_lengths():
    rng = np.random.default_rng(12)
    positions = rng.integers(0, 4, size=50)
    with pytest.raises(ValueError, match="exemples != 50"):
        slens.self_location_table({"L0H0": rng.normal(size=(49, 4))}, positions)


def test_copy_success_by_position_reports_nan_when_absent():
    predicted = np.array([1, 2, 3])
    target_value = np.array([1, 0, 3])
    target_pos = np.array([0, 0, 2])
    acc = slens.copy_success_by_position(predicted, target_value, target_pos, 4)
    assert acc[0] == pytest.approx(0.5)
    assert acc[2] == pytest.approx(1.0)
    assert np.isnan(acc[1])


# --------------------------------------------------------------------------- #
# 6. Verdict causal
# --------------------------------------------------------------------------- #

def test_location_causal_verdict_follows_only_paired_effect():
    damage_ok = {"off_target_rel": 0.01, "target_rel": 0.5, "selectivity_ratio": 50.0}
    good = slens.location_causal_verdict(0.8, 0.2, 0.15, damage_ok)
    assert good["verdict"] == "causal"
    # effet present mais sham non separe -> non discrimine
    undisc = slens.location_causal_verdict(0.7, 0.6, 0.1, damage_ok)
    assert undisc["verdict"] == "undiscriminated"
    # dommage global : meme un effet fort ne suffit pas
    damaged = slens.location_causal_verdict(
        0.9, 0.1, 0.1, {"off_target_rel": 0.4, "target_rel": 0.9,
                        "selectivity_ratio": 2.2}
    )
    assert damaged["verdict"] == "global_damage"
    none = slens.location_causal_verdict(0.2, 0.15, 0.1, damage_ok)
    assert none["verdict"] == "no_effect"


def test_causal_verdict_does_not_label_an_absent_effect_as_global_damage():
    """Un dommage global presuppose un effet mesure.

    Une intervention qui ne deplace PAS la prediction mais abime le modele est
    un resultat NEGATIF : l'etiqueter ``global_damage`` affirmait un effet que
    la mesure n'avait pas vu. Le dommage reste reporte comme champ separe.
    """
    damaged = {"off_target_rel": 0.33, "target_rel": 0.31, "selectivity_ratio": 0.94}
    v = slens.location_causal_verdict(0.074, 0.195, 0.062, damaged)
    assert v["verdict"] == "no_effect"
    assert v["selectivity_ok"] is False         # le dommage n'est pas tu
    assert v["off_target_rel"] == pytest.approx(0.33)
    # un effet FORT assorti du meme dommage reste etiquete global_damage :
    # c'est le cas que le label decrit.
    assert slens.location_causal_verdict(
        0.9, 0.1, 0.1, damaged)["verdict"] == "global_damage"


# --------------------------------------------------------------------------- #
# 7. Gate de promotion
# --------------------------------------------------------------------------- #

def _evidence(**over):
    base = dict(
        position_exact=0.8, position_exact_shuffle=0.3, value_exact=0.7,
        copy_accuracy=0.9, causal_verdict="causal",
        second_task_position_exact=0.7, second_task_shuffle=0.3,
        second_task_causal="causal", seeds_stable=True,
    )
    base.update(over)
    return slens.PromotionEvidence(**base)


def test_promotion_requires_both_tasks_and_causal_leg():
    assert slens.promotion_verdict(_evidence()) == "PROMOTE"
    # un seul banc -> demonstrateur specialise
    assert slens.promotion_verdict(
        _evidence(second_task_position_exact=float("nan"),
                  second_task_shuffle=float("nan"))
    ) == "SPECIALIZED_ONLY"
    # pas de jambe causale -> specialise
    assert slens.promotion_verdict(
        _evidence(causal_verdict="undiscriminated")
    ) == "SPECIALIZED_ONLY"
    # instabilite multi-seeds -> inconclusif
    assert slens.promotion_verdict(_evidence(seeds_stable=False)) == "INCONCLUSIVE"
    # pas de signal au-dessus du shuffle -> inconclusif
    assert slens.promotion_verdict(
        _evidence(position_exact=0.35, position_exact_shuffle=0.30)
    ) == "INCONCLUSIVE"


# --------------------------------------------------------------------------- #
# 8. Manifeste POC
# --------------------------------------------------------------------------- #

def test_manifest_is_marked_poc_and_not_contract_valid():
    man = slens.slens_manifest(
        task="copy_offset", arch="rope", run="r0", seed=0, layer=1,
        d_model=64, n_heads=4, n_layers=2, n_test=256, prompt_set="poc",
    )
    assert man["instrument"] == "slens_poc"
    assert man["contract_note"].startswith("POC #15481")
    # honnetete du statut : le contrat v1 ne connait pas slens
    assert "slens" not in trace_contract.INSTRUMENTS
    with pytest.raises(trace_contract.TraceContractError):
        trace_contract.validate_manifest(man)


# --------------------------------------------------------------------------- #
# 9. Agregation multi-runs (charge un npz de run, agrege en preuves de gate)
# --------------------------------------------------------------------------- #

def _synthetic_run(tmp_path, *, task: str, arch: str, seed: int,
                   n: int = 600, n_pos: int = 14, n_val: int = 6,
                   bits: int = 64) -> dict:
    """Ecrit un npz de run factice (meme forme que ``scripts/slens_poc.py``).

    L'unite ``L0H0`` porte la position et la valeur en one-hot bruite : c'est
    le cas ou le probe DOIT se detacher de son plancher.
    """
    rng = np.random.default_rng(seed)
    positions = rng.integers(0, n_pos, size=n)
    values = rng.integers(0, n_val, size=n)
    unit = np.concatenate(
        [np.eye(n_pos)[positions] + rng.normal(scale=0.05, size=(n, n_pos)),
         np.eye(n_val)[values] + rng.normal(scale=0.05, size=(n, n_val))],
        axis=1,
    )
    stats = {
        "follow_donor": 0.8, "sham": 0.2, "random_target": 0.15,
        "off_target_rel": 0.01, "target_rel": 0.5, "selectivity_ratio": 50.0,
    }
    meta = slens.slens_manifest(
        task=task, arch=arch, run=f"{task}-{arch}-s{seed}", seed=seed, layer=0,
        d_model=bits, n_heads=1, n_layers=1, n_test=n, prompt_set="poc",
    )
    path = tmp_path / f"slens_{task}_{arch}_s{seed}.npz"
    np.savez(
        path,
        L0H0_q=unit.astype(np.float32),
        L0_q=rng.normal(size=(n, bits)).astype(np.float32),
        target_pos=positions, target_value=values,
        tokens=np.zeros((n, n_pos), dtype=np.int64),
        predictions_accuracy=np.float64(1.0),
        __meta__=np.array(json.dumps(meta)),
        patch_stats=np.array(json.dumps(stats)),
    )
    return slens.load_run(path)


def test_load_run_separates_manifest_from_arrays(tmp_path):
    run = _synthetic_run(tmp_path, task="copy_offset", arch="rope", seed=0)
    # le manifeste et le patch_stats sont relus, pas laisses en tableaux opaques
    assert run["meta"]["task"] == "copy_offset"
    assert run["meta"]["instrument"] == "slens_poc"
    assert isinstance(run["arrays"]["patch_stats"], dict)
    assert "__meta__" not in run["arrays"]


def test_run_metrics_selects_informative_unit_and_reads_causal(tmp_path):
    """Chemin d'integration complet : npz -> load_run -> run_metrics."""
    run = _synthetic_run(tmp_path, task="copy_offset", arch="rope", seed=3)
    m = slens.run_metrics(run)
    assert m["best_unit"] == "L0H0"
    assert m["position_exact"] > 0.9
    # le plancher shuffle est mesure, pas suppose nul
    assert m["position_exact_shuffle"] < m["position_exact"]
    assert m["causal"]["verdict"] == "causal"
    assert (m["task"], m["arch"], m["seed"]) == ("copy_offset", "rope", 3)


def _seq_metrics(position_exacts, shuffle_floor=0.10, causal="causal"):
    """Remplace ``run_metrics`` par une suite de localisations imposees.

    L'agregation est de la logique pure : la tester a travers le pipeline de
    probe la rendrait dependante du bruit d'echantillonnage du ridge, ce qui
    mesurerait autre chose que la regle de decision. Les runs sont consommes
    dans l'ordre, comme dans ``evidence_from_runs``.
    """
    it = iter(position_exacts)

    def fake(run, **_):
        return {
            "task": run["meta"]["task"],
            "arch": run["meta"].get("arch", "x"),
            "seed": 0, "table": [],
            "best_unit": "L0H0",
            "position_exact": next(it),
            "position_exact_shuffle": shuffle_floor,
            "value_exact": 0.8, "value_exact_shuffle": 0.1,
            "copy_accuracy": 1.0, "causal": {"verdict": causal},
            "patch_stats": {},
        }
    return fake


def _run(task: str, arch: str = "rope") -> dict:
    return {"meta": {"task": task, "arch": arch}, "arrays": {}}


def test_evidence_from_runs_requires_every_seed_above_its_floor(monkeypatch):
    monkeypatch.setattr(slens, "run_metrics", _seq_metrics([0.9] * 4 + [0.85] * 2))
    runs = [_run("copy_offset")] * 4 + [_run("variable_binding")] * 2
    ev, rows = slens.evidence_from_runs(runs)
    assert len(rows) == 6
    assert ev.seeds_stable is True
    assert ev.causal_verdict == "causal"
    assert ev.notes == []
    assert slens.promotion_verdict(ev) == "PROMOTE"

    # Une seed ou le signal est absent casse la generalisation : une moyenne
    # qui tient grace aux autres seeds n'est pas une preuve multi-seeds.
    monkeypatch.setattr(
        slens, "run_metrics", _seq_metrics([0.9, 0.9, 0.05, 0.9])
    )
    ev2, _ = slens.evidence_from_runs([_run("copy_offset")] * 4)
    assert ev2.seeds_stable is False
    assert slens.promotion_verdict(ev2) == "INCONCLUSIVE"


def test_evidence_from_runs_without_secondary_stays_specialized(monkeypatch):
    monkeypatch.setattr(slens, "run_metrics", _seq_metrics([0.9] * 2))
    ev, _ = slens.evidence_from_runs([_run("copy_offset")] * 2)
    assert np.isnan(ev.second_task_position_exact)
    assert ev.notes and "banc secondaire absent" in ev.notes[0]
    # le gate ne peut pas conclure PROMOTE sur un seul banc
    assert slens.promotion_verdict(ev) == "SPECIALIZED_ONLY"


def test_evidence_from_runs_notes_a_secondary_stuck_at_its_floor(monkeypatch):
    monkeypatch.setattr(
        slens, "run_metrics", _seq_metrics([0.9, 0.9, 0.09, 0.09])
    )
    ev, _ = slens.evidence_from_runs(
        [_run("copy_offset")] * 2 + [_run("variable_binding")] * 2
    )
    assert any("plancher shuffle" in n for n in ev.notes)
    assert slens.promotion_verdict(ev) == "SPECIALIZED_ONLY"


def test_evidence_from_runs_rejects_a_set_without_primary_bench(monkeypatch):
    # un jeu qui ne contient que le banc secondaire n'est pas agregreable :
    # le gate de promotion se juge d'abord sur le banc primaire.
    monkeypatch.setattr(slens, "run_metrics", _seq_metrics([0.9]))
    with pytest.raises(ValueError, match="aucun run pour le banc primaire"):
        slens.evidence_from_runs([_run("variable_binding")])


def test_evidence_from_runs_excludes_the_ablation_from_the_stability_test(monkeypatch):
    """La stabilite multi-graines porte sur l'architecture de reference.

    Un run d'ablation (autre regime de position) a une localisation differente
    par construction : le meler aux graines ferait passer une heterogeneite
    d'architecture pour une instabilite de graine, et le gate conclurait
    INCONCLUSIVE sur un resultat stable.
    """
    # 4 graines de reference parfaitement stables, puis l'ablation tres basse
    monkeypatch.setattr(
        slens, "run_metrics", _seq_metrics([0.9, 0.9, 0.9, 0.9, 0.10])
    )
    runs = [_run("copy_offset", "rope")] * 4 + [_run("copy_offset", "none")]
    ev, rows = slens.evidence_from_runs(runs)
    assert len(rows) == 5
    assert ev.reference_arch == "rope"
    assert ev.seeds_stable is True
    assert any("ablation" in n for n in ev.notes)
    # un seul banc -> demonstrateur specialise, jamais PROMOTE ici
    assert slens.promotion_verdict(ev) == "SPECIALIZED_ONLY"


def test_evidence_from_runs_refuses_an_absent_reference_architecture(monkeypatch):
    monkeypatch.setattr(slens, "run_metrics", _seq_metrics([0.9] * 2))
    with pytest.raises(ValueError, match="architecture de reference"):
        slens.evidence_from_runs([_run("copy_offset", "none")] * 2)
