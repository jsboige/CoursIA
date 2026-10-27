# Tests du pont Probas -> Lean (#22374) : conversion exacte du contrat,
# valeurs miroir, controles (gain nul exact, gain strict, rejets explicites,
# signal impossible, table corrompue) et acceptation par le kernel Lean.
#
# Le kernel est la seule autorite qui re-evalue valueNoisy* independamment du
# miroir Python : les tests de rejeu comparent le pont aux sorties mesurees
# du banc committees dans comparison.json, dans les tolerances du contrat.

import copy
import json
import sys
from fractions import Fraction
from pathlib import Path

import pytest

VOI = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(VOI))
import lean_bridge  # noqa: E402
from lean_bridge import (  # noqa: E402
    TOLERANCE_UTILITY_ABS, VoIContractError, compare_with_bench, emit_lean_check,
    lean_toolchain_available, lean_values, load_problem, run_lean_check,
    to_lean_problem, validate_problem)


def spec_of(name):
    return load_problem(VOI / "problems" / name)


def bench_outputs():
    return json.loads((VOI / "comparison.json").read_text(encoding="utf-8"))["problems"]


# --- 1. Table independante : gain EXACTEMENT nul -----------------------------

def test_independent_table_exact_zero_gain():
    spec = spec_of("forage-non-informatif.json")
    vals = lean_values(spec)
    scaled = vals["_scaled"]
    assert scaled["no_info"] == scaled["signal"], (
        "la table independante doit avoir des valeurs identiques, pas proches")
    assert vals["evsi_brute"] == 0, f"gain brut non nul : {vals['evsi_brute']}"
    tab = to_lean_problem(spec)
    assert tab["p"] == [[3, 3], [7, 7]], f"poids joints inattendus : {tab['p']}"


# --- 2. Table informative : gain STRICT --------------------------------------

def test_informative_strict_gain():
    spec = spec_of("forage-petrolier.json")
    vals = lean_values(spec)
    scaled = vals["_scaled"]
    assert scaled["no_info"] < scaled["signal"], "le test informatif doit apporter"
    assert scaled["signal"] <= scaled["perfect"], "signal > parfaite : impossible"
    assert Fraction(0) < vals["evsi_nette"] < vals["evpi"]


# --- 3. Poids invalides : rejet EXPLICITE ------------------------------------

def _corrupt(base, mutate):
    spec = copy.deepcopy(spec_of(base))
    mutate(spec)
    return spec


@pytest.mark.parametrize("label,mutate", [
    ("prior negatif", lambda s: s["priors"].__setitem__("petrole", -0.3)),
    ("priors ne somment pas a 1", lambda s: s["priors"].__setitem__("petrole", 0.2)),
    ("colonne de vraisemblance != 1",
     lambda s: s["likelihood"]["positif"].__setitem__("petrole", 0.95)),
    ("vraisemblance negative",
     lambda s: (s["likelihood"]["positif"].__setitem__("petrole", 1.2),
                s["likelihood"]["negatif"].__setitem__("petrole", -0.2))),
    ("utilitaire non entier",
     lambda s: s["utilities"]["forer"].__setitem__("petrole", 1500000.5)),
    ("action sans utilitaire", lambda s: s["utilities"].pop("vendre")),
])
def test_invalid_weights_rejected(label, mutate):
    spec = _corrupt("forage-petrolier.json", mutate)
    with pytest.raises(VoIContractError):
        validate_problem(spec)
    with pytest.raises(VoIContractError):
        to_lean_problem(spec)


def test_valid_contract_accepted():
    for name in ("forage-petrolier.json", "forage-non-informatif.json"):
        assert validate_problem(spec_of(name)) is True


# --- 4. Signal impossible : contribution NULLE -------------------------------

def test_impossible_signal_null_contribution():
    # contrat valide (chaque colonne d'etat somme a 1) mais le signal
    # "positif" a une masse nulle dans TOUS les etats : sa contribution
    # doit etre exactement nulle, comme le theoreme Lean valueNoisySignal_
    # zero_mass_cell le garantit pour l'organe.
    spec = _corrupt("forage-petrolier.json",
                    lambda s: (s["likelihood"].__setitem__(
                        "positif", {"petrole": 0.0, "pas_petrole": 0.0}),
                        s["likelihood"].__setitem__(
                            "negatif", {"petrole": 1.0, "pas_petrole": 1.0})))
    validate_problem(spec)
    tab = to_lean_problem(spec)
    assert tab["p"][0][0] == 0 and tab["p"][1][0] == 0, "masse du signal impossible"

    trimmed = copy.deepcopy(spec)
    trimmed["signals"] = ["negatif"]
    trimmed["likelihood"] = {"negatif": spec["likelihood"]["negatif"]}
    trimmed["problem"] = "forage-petrolier-signal-impossible"

    full = lean_values(spec)["_scaled"]
    cut = lean_values(trimmed)["_scaled"]
    assert full["signal"] == cut["signal"], (
        "un signal de masse nulle doit contribuer exactement 0")


# --- 5. Table corrompue : divergence signalee ou rejet -----------------------

def test_corrupted_table_divergence_not_smoothed():
    # corruption SEMANTIQUE qui reste valide au contrat : la vraisemblance
    # informative devient 0.8/0.2 (colonnes toujours a 1). Les valeurs
    # doivent diverger des references du banc, au-dela de la tolerance,
    # et la divergence doit etre RAPPORTEE (jamais lissee).
    bench = bench_outputs()["forage-petrolier"]["outputs"]["infer_net"]
    spec = _corrupt("forage-petrolier.json",
                    lambda s: (s["likelihood"]["positif"].__setitem__("petrole", 0.8),
                               s["likelihood"]["negatif"].__setitem__("petrole", 0.2)))
    validate_problem(spec)
    rows, agree = compare_with_bench(lean_values(spec), bench)
    assert not agree, "une table corrompue doit diverger des references, pas s'y arrondir"
    verdicts = {r[0]: r[3] for r in rows}
    assert verdicts["evsi_brute"] == "DESACCORD"
    gap = abs(float(lean_values(spec)["evsi_brute"]) - float(bench["evsi_brute"]))
    assert gap > TOLERANCE_UTILITY_ABS, f"ecart {gap:.0f} sous la tolerance : non signale"


def test_corrupted_table_hard_rejection():
    spec = _corrupt("forage-petrolier.json",
                    lambda s: s["likelihood"]["positif"].__setitem__("petrole", 0.91))
    with pytest.raises(VoIContractError):
        lean_values(spec)


# --- 6. Acceptation par le kernel Lean ---------------------------------------

needs_lean = pytest.mark.skipif(
    not lean_toolchain_available(),
    reason="toolchain Lean absente sur cette machine (lake/lean_exec) : "
           "verification kernel non executable ici, jamais blanchie")


@needs_lean
@pytest.mark.parametrize("name", ["forage-petrolier", "forage-non-informatif"])
def test_kernel_acceptance(name):
    """Le fichier emis est DECIDE par le kernel (theoremes sans sorry)."""
    out = run_lean_check(spec_of(f"{name}.json"), caller="pytest-lean-bridge")
    assert out["rc"] == 0 and out["kernel"] == "decide"


def test_emitted_file_is_clean(tmp_path):
    check = emit_lean_check(spec_of("forage-petrolier.json"), tmp_path / "check.lean")
    text = check.read_text(encoding="utf-8")
    assert "native_decide" not in text and "sorry" not in text
    assert text.lstrip().startswith("import Bayesian.InformationNoisy")
    assert "theorem pb_valueNoisySignal : valueNoisySignal pb = 45300000 := by decide" in text
    assert "theorem pb_strict_gain" in text
    assert "pb_zero_gain" not in text, "controle negatif emis sur un probleme informatif"


# --- 7. Rejeu du banc : ecart dans les tolerances du contrat -----------------

@pytest.mark.parametrize("name", ["forage-petrolier", "forage-non-informatif"])
@pytest.mark.parametrize("engine", ["infer_net", "pymc"])
def test_bench_replay_within_tolerance(name, engine):
    bench = bench_outputs()[name]["outputs"][engine]
    rows, agree = compare_with_bench(lean_values(spec_of(f"{name}.json")), bench)
    assert agree, f"desaccord lean vs {engine} : {rows}"


# --- 8. Artefact committee : la colonne lean y figure et s'accorde ----------

@pytest.mark.parametrize("name", ["forage-petrolier", "forage-non-informatif"])
def test_committed_comparison_carries_lean_column(name):
    entry = bench_outputs()[name]
    assert entry["lean_agree"] is True, entry["lean_comparisons"]
    assert entry["lean_controls_ok"] is True
    assert entry["kernel"]["rc"] == 0
    assert entry["outputs"]["lean"]["engine"] == "lean"
    for engine in ("infer_net", "pymc"):
        assert entry["lean_comparisons"][engine]["agree"] is True

