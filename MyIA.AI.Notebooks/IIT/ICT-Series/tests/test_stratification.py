"""Tests de la stratification inter-tailles ICT-25a (#17740, volet 1).

Ce que ces tests protegent, dans l'ordre du module :

1. **La dispersion est publiee** -- une ligne de taille porte la valeur par
   graine, le min, le max et l'ecart-type, pas seulement une moyenne.
2. **L'appariement ne se fait pas au hasard** -- deux bras dont les jeux de
   graines different levent au lieu de comparer deux moyennes.
3. **Aucune agregation entre tailles** -- la sortie n'expose pas de total, et
   le dit ; c'est l'effet mesure qui serait efface.
4. **Le crossover est localise par un changement de signe consistant**, et une
   taille dont les graines se contredisent est declaree ``mixed`` au lieu
   d'etre lissee.
5. **Aucun verdict de significativite sous 4 graines** (batterie ML du depot),
   et le seuil atteint est declare *necessaire, non suffisant* -- la
   conjonction edge >= 2 sigma et Diebold-Mariano n'est pas evaluee ici.
6. **Une taille declaree sans artefact sort en ``provisional``** avec sa raison.
7. **Les nombres publies par la matrice sont reproduits** -- le controle de
   falsifiabilite porte sur les artefacts reels committes dans ``runs/``, qui
   portent quatre graines (0/1/7/42) depuis #17724 et couvrent 32B.
8. **Un artefact malforme ne fausse pas la mesure** -- un artefact sans clef
   ``steps`` ne casse pas la couverture, et une graine dupliquee leve au lieu
   de s'ecraser en silence sous l'appariement.

numpy non requis : statistiques standard + pytest, CPU uniquement.
"""

from __future__ import annotations

import json

import pytest

from ict.stratification import (
    DEFAULT_RUNS_DIR,
    DECLARED_SIZES,
    CLAIMED_SIZES,
    MIN_SEEDS_FOR_SIGNIFICANCE,
    PUBLISHED_HACK_LATE_SLOPE,
    StratificationError,
    control_published,
    coverage,
    load_runs,
    locate_crossover,
    paired_delta,
    plateaus,
    seed_map,
    size_row,
    stratify,
)

LATE = "hack_late"


def write_artifact(runs_dir, arm, size, per_seed, steps=120):
    """Ecrit un artefact minimal au format des runs committes."""
    runs_dir.mkdir(parents=True, exist_ok=True)
    model = f"Qwen/Qwen2.5-{size}-Instruct"
    seeds = [
        {"arm": arm, "model": model, "seed": seed, "steps": steps, "n_records": 240, LATE: value}
        for seed, value in sorted(per_seed.items())
    ]
    path = runs_dir / f"ict25a_{arm}_{size}.json"
    path.write_text(
        json.dumps({"model": model, "arm": arm, "steps": steps, "seeds": seeds}),
        encoding="utf-8",
    )
    return path


def build(tmp_path, arms_by_size):
    """``arms_by_size`` : {taille: {bras: {graine: valeur}}}."""
    for size, arms in arms_by_size.items():
        for arm, per_seed in arms.items():
            write_artifact(tmp_path, arm, size, per_seed)
    return tmp_path


# --- 1. dispersion ----------------------------------------------------------


def test_size_row_carries_dispersion_and_per_seed(tmp_path):
    runs_dir = build(tmp_path, {"7B": {"N": {0: 0.4, 1: 0.5, 42: 0.6}}})
    row = size_row(load_runs(runs_dir), LATE, "7B")
    arm = row["arms"]["N"]
    assert arm["n_seeds"] == 3
    assert arm["per_seed"] == {"0": 0.4, "1": 0.5, "42": 0.6}
    assert arm["mean"] == pytest.approx(0.5)
    assert arm["min"] == 0.4 and arm["max"] == 0.6
    assert arm["range"] == pytest.approx(0.2)
    assert arm["stdev"] == pytest.approx(0.1)


def test_size_row_rejects_a_missing_metric(tmp_path):
    runs_dir = build(tmp_path, {"7B": {"N": {0: 0.4}}})
    with pytest.raises(StratificationError, match="sans la grandeur"):
        size_row(load_runs(runs_dir), "reward_late", "7B")


# --- 2. appariement ---------------------------------------------------------


def test_paired_delta_refuses_unpaired_seed_sets(tmp_path):
    runs_dir = build(
        tmp_path,
        {"7B": {"N": {0: 0.4, 1: 0.5, 42: 0.6}, "Np": {0: 0.5, 7: 0.6, 42: 0.7}}},
    )
    with pytest.raises(StratificationError, match="non appariees"):
        paired_delta(load_runs(runs_dir), LATE, "7B")


def test_seed_map_refuses_a_duplicated_seed(tmp_path):
    """Une graine dupliquee s'ecraserait en silence et tromperait le refus n°2.

    Sans ce garde, un artefact de 4 enregistrements pour 3 graines rend un jeu
    de graines d'apparence coherente : l'appariement ``Np - N`` comparerait
    alors une graine a elle-meme sans que rien ne le signale.
    """
    path = write_artifact(tmp_path, "N", "7B", {0: 0.4, 1: 0.5, 42: 0.6})
    artifact = json.loads(path.read_text(encoding="utf-8"))
    artifact["seeds"].append(dict(artifact["seeds"][0]))
    with pytest.raises(StratificationError, match="dupliquee"):
        seed_map(artifact, LATE)


def test_paired_delta_is_per_seed_and_reports_signs(tmp_path):
    runs_dir = build(
        tmp_path,
        {"7B": {"N": {0: 0.40, 1: 0.40, 42: 0.40}, "Np": {0: 0.45, 1: 0.50, 42: 0.55}}},
    )
    delta = paired_delta(load_runs(runs_dir), LATE, "7B")
    assert delta["per_seed"] == {"0": pytest.approx(0.05), "1": pytest.approx(0.10), "42": pytest.approx(0.15)}
    assert delta["signs"] == ["+", "+", "+"]
    assert delta["sign_consistent"] is True
    assert delta["sign"] == "+"


def test_paired_delta_requires_both_arms(tmp_path):
    runs_dir = build(tmp_path, {"7B": {"N": {0: 0.4}}})
    with pytest.raises(StratificationError, match="deux bras"):
        paired_delta(load_runs(runs_dir), LATE, "7B")


# --- 3. pas d'agregation ----------------------------------------------------


def test_stratify_does_not_aggregate_across_sizes(tmp_path):
    runs_dir = build(
        tmp_path,
        {
            "1.5B": {"N": {0: 0.2, 1: 0.2, 42: 0.2}},
            "7B": {"N": {0: 0.4, 1: 0.4, 42: 0.4}},
            "14B": {"N": {0: 0.9, 1: 0.9, 42: 0.9}},
        },
    )
    report = stratify(runs_dir)
    assert set(report["sizes"]) == set(DECLARED_SIZES)
    assert report["aggregation"].startswith("aucune")
    for forbidden in ("overall", "mean", "total", "all_sizes"):
        assert forbidden not in report["sizes"]
    assert set(report["sizes"]) & set(CLAIMED_SIZES)


# --- 4. crossover -----------------------------------------------------------


def test_crossover_is_located_at_the_sign_flip(tmp_path):
    runs_dir = build(
        tmp_path,
        {
            "1.5B": {"N": {0: 0.20, 1: 0.20, 42: 0.20}, "Np": {0: 0.25, 1: 0.25, 42: 0.25}},
            "7B": {"N": {0: 0.40, 1: 0.40, 42: 0.40}, "Np": {0: 0.50, 1: 0.50, 42: 0.50}},
            "14B": {"N": {0: 0.90, 1: 0.90, 42: 0.90}, "Np": {0: 0.80, 1: 0.80, 42: 0.80}},
        },
    )
    crossover = stratify(runs_dir)["crossover"]
    assert crossover["crossover"]["between"] == ["7B", "14B"]
    assert crossover["signed_sizes"] == {"1.5B": "+", "7B": "+", "14B": "-"}
    assert crossover["mixed_sizes"] == []


def test_mixed_sign_size_is_not_lissed_into_a_crossover():
    deltas = {
        "1.5B": {"sign": "mixed"},
        "7B": {"sign": "+"},
        "14B": {"sign": "-"},
    }
    crossover = locate_crossover(deltas)
    assert crossover["mixed_sizes"] == ["1.5B"]
    assert crossover["crossover"]["between"] == ["7B", "14B"]


def test_no_crossover_when_signs_agree():
    deltas = {size: {"sign": "+"} for size in CLAIMED_SIZES}
    crossover = locate_crossover(deltas)
    assert crossover["crossover"] is None
    assert "aucun changement de signe" in crossover["verdict"]


# --- 5. significativite -----------------------------------------------------


def test_no_significance_claim_below_four_seeds(tmp_path):
    runs_dir = build(
        tmp_path,
        {"7B": {"N": {0: 0.4, 1: 0.5, 42: 0.6}, "Np": {0: 0.5, 1: 0.6, 42: 0.7}}},
    )
    significance = stratify(runs_dir)["significance"]
    assert significance["claim"] is False
    assert significance["seeds_observed"] == [3]
    assert significance["threshold"] == MIN_SEEDS_FOR_SIGNIFICANCE
    assert "sous le seuil" in significance["reason"]


def test_significance_claim_is_reachable_at_the_threshold(tmp_path):
    """Le seuil atteint est declare necessaire, pas suffisant.

    Les artefacts reels portent 4 graines depuis #17724 : le booleen passe a
    ``True``. La sortie doit dire dans le meme mouvement que la conjonction
    (edge >= 2 sigma ET Diebold-Mariano) n'est pas evaluee ici -- sinon le
    champ se lirait comme un verdict de significativite.
    """
    seeds = {seed: 0.4 for seed in range(4)}
    runs_dir = build(tmp_path, {"7B": {"N": dict(seeds), "Np": dict(seeds)}})
    significance = stratify(runs_dir)["significance"]
    assert significance["claim"] is True
    assert significance["seeds_observed"] == [4]
    assert "necessaire, non suffisant" in significance["reason"]
    assert "Diebold-Mariano" in significance["reason"]


# --- 6. provisional ---------------------------------------------------------


def test_provisional_size_carries_a_reason_and_no_verdict(tmp_path):
    runs_dir = build(tmp_path, {"7B": {"N": {0: 0.4, 1: 0.5, 42: 0.6}}})
    report = stratify(runs_dir)
    for size in ("1.5B", "14B", "32B"):
        entry = report["sizes"][size]
        assert entry["status"] == "provisional"
        assert set(entry) == {"status", "reason"}
        assert entry["reason"]
        # la raison nomme la taille concernee : elle reste localisable quand la
        # couverture bouge (32B a cesse d'etre provisional au palier #17724)
        assert size in entry["reason"]


def test_plateaus_report_disjoint_intervals(tmp_path):
    disjoint_dir = build(
        tmp_path / "disjoint",
        {
            "1.5B": {"N": {0: 0.20, 1: 0.22, 42: 0.23}},
            "7B": {"N": {0: 0.41, 1: 0.44, 42: 0.47}},
            "14B": {"N": {0: 0.93, 1: 0.94, 42: 0.95}},
        },
    )
    overlapping_dir = build(
        tmp_path / "overlapping",
        {
            "1.5B": {"N": {0: 0.20, 1: 0.45, 42: 0.23}},
            "7B": {"N": {0: 0.41, 1: 0.44, 42: 0.47}},
            "14B": {"N": {0: 0.93, 1: 0.94, 42: 0.95}},
        },
    )
    assert plateaus(load_runs(disjoint_dir), LATE)["disjoint"] is True
    assert plateaus(load_runs(overlapping_dir), LATE)["disjoint"] is False


# --- 7. controle de falsifiabilite sur les artefacts reels ------------------


def test_real_artifacts_are_present_and_carry_four_seeds():
    """Documente la couverture reelle : 2 bras x 4 tailles, 4 graines chacune.

    Le palier 32B (#17724) a porte les artefacts de trois a quatre graines en
    ajoutant la graine 7, et ajoute la tranche 32B : la couverture reelle est
    ce que ce test fige, pour qu'une campagne qui bouge se voie ici.
    """
    runs = load_runs(DEFAULT_RUNS_DIR)
    assert sorted(runs) == [
        ("N", "1.5B"),
        ("N", "14B"),
        ("N", "32B"),
        ("N", "7B"),
        ("Np", "1.5B"),
        ("Np", "14B"),
        ("Np", "32B"),
        ("Np", "7B"),
    ]
    seeds = {tuple(sorted(seed_map["seed"] for seed_map in artifact["seeds"])) for artifact in runs.values()}
    assert seeds == {(0, 1, 7, 42)}


def test_real_32b_is_measured_not_provisional():
    """32B est mesure depuis #17724 : il ne sort plus en ``provisional``.

    Tant que ses artefacts n'etaient pas sur ``main``, la taille sortait en
    ``provisional`` avec sa raison. Le test fige la bascule -- et la raison,
    elle, nomme toujours la taille, donc la meme assertion reste vraie pour
    une tranche encore absente.
    """
    sizes = stratify(DEFAULT_RUNS_DIR)["sizes"]
    assert sizes["32B"]["status"] == "measured"
    assert sizes["32B"]["delta_np_minus_n"][LATE]["sign"] == "-"


def test_published_matrix_numbers_are_reproduced():
    """Les nombres publies par la matrice se recalculent depuis `runs/`.

    C'est le controle qui rend la claim falsifiable : si un run est regenere et
    que la pente ou l'ecart derive, ce test echoue et la matrice doit etre
    mise a jour.
    """
    report = control_published(DEFAULT_RUNS_DIR)
    assert report["status"] == "MATCH", report["drifted"]
    assert len(report["rows"]) == 2 * len(CLAIMED_SIZES)


def test_published_slope_matches_the_committed_artifacts():
    runs = load_runs(DEFAULT_RUNS_DIR)
    for size, published in PUBLISHED_HACK_LATE_SLOPE.items():
        computed = size_row(runs, LATE, size)["arms"]["N"]["mean"]
        assert computed == pytest.approx(published, abs=5e-4), size


# --- 8. artefact malforme ---------------------------------------------------


def test_coverage_survives_an_artifact_without_steps(tmp_path):
    """Le tri des ``steps`` filtre les clefs absentes, comme celui des modeles.

    Sans le filtre, un artefact sans clef ``steps`` mettait ``None`` dans
    l'ensemble et ``sorted`` levait un ``TypeError`` : la couverture tombait sur
    un artefact malforme au lieu de rapporter ce qu'elle couvre.
    """
    runs_dir = build(tmp_path, {"7B": {"N": {0: 0.4}, "Np": {0: 0.5}}})
    stripped = runs_dir / "ict25a_Np_7B.json"
    artifact = json.loads(stripped.read_text(encoding="utf-8"))
    del artifact["steps"]
    stripped.write_text(json.dumps(artifact), encoding="utf-8")
    report = coverage(load_runs(runs_dir))
    assert report["count"] == 2
    assert report["steps"] == [120]
