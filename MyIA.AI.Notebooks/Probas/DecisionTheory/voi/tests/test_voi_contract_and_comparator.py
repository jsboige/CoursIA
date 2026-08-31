# Tests VoI cross-engine (tranche 3/3 #13569) : validite du contrat JSON,
# logique du comparateur (accord ET desaccord), controls sur valeurs mesurees,
# execution reelle PyMC sur les deux problemes.

import json
import subprocess
import sys
from pathlib import Path

import pytest

VOI = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(VOI))
from run_comparison import TOLERANCE, check_controls, compare_problem  # noqa: E402

PROBLEMS = sorted((VOI / "problems").glob("*.json"))


def load(name):
    return json.loads((VOI / "problems" / name).read_text(encoding="utf-8"))


@pytest.mark.parametrize("path", PROBLEMS, ids=lambda p: p.stem)
def test_contract_valid(path):
    spec = json.loads(path.read_text(encoding="utf-8"))
    assert len(spec["states"]) == 2 and len(spec["signals"]) == 2
    assert abs(sum(spec["priors"].values()) - 1.0) < 1e-9
    for state in spec["states"]:
        col = sum(spec["likelihood"][sig][state] for sig in spec["signals"])
        assert abs(col - 1.0) < 1e-9, f"likelihood({state}) ne somme pas a 1"
    assert spec["test_cost"] > 0
    for action in spec["actions"]:
        assert set(spec["utilities"][action]) == set(spec["states"])


def _infer_net_output_stub(**over):
    out = {
        "eu_no_info": 200000.0, "action_no_info": "vendre",
        "evpi": 390000.0, "evsi_brute": 253000.0, "evsi_nette": 193000.0,
        "decision": "observer",
        "signal_marginals": {"positif": 0.41, "negatif": 0.59},
        "posteriors": {
            "positif": {"petrole": 0.6585365853658537, "pas_petrole": 0.3414634146341463},
            "negatif": {"petrole": 0.05084745762711864, "pas_petrole": 0.9491525423728814},
        },
    }
    out.update(over)
    return out


def test_comparator_agreement_within_tolerance():
    a = _infer_net_output_stub()
    b = _infer_net_output_stub(evsi_brute=252796.0, evsi_nette=192796.0)
    rows, agree = compare_problem("x", a, b)
    assert agree
    assert all(r[3] == "accord" for r in rows)


def test_comparator_flags_divergence_beyond_tolerance():
    a = _infer_net_output_stub()
    b = _infer_net_output_stub(evsi_nette=a["evsi_nette"] + TOLERANCE["utility_abs"] + 1)
    _, agree = compare_problem("x", a, b)
    assert not agree, "une divergence > tolerance doit etre signalee, jamais lissee"


def test_comparator_flags_decision_disagreement():
    a = _infer_net_output_stub()
    b = _infer_net_output_stub(decision="agir_sans_test")
    _, agree = compare_problem("x", a, b)
    assert not agree


def test_control_discriminant_on_measured_values():
    ok = check_controls("forage-petrolier", _infer_net_output_stub())
    assert all(c[1] for c in ok)
    bad = check_controls("forage-petrolier", _infer_net_output_stub(evsi_nette=0.0))
    assert not all(c[1] for c in bad)


def test_control_negative_on_measured_values():
    ok = check_controls("forage-non-informatif", _infer_net_output_stub(evsi_brute=0.0))
    assert all(c[1] for c in ok)
    bad = check_controls("forage-non-informatif", _infer_net_output_stub(evsi_brute=50000.0))
    assert not all(c[1] for c in bad)


@pytest.mark.parametrize("name,expect_decision", [
    ("forage-petrolier.json", "observer"),
    ("forage-non-informatif.json", "agir_sans_test"),
])
def test_pymc_adapter_real_execution(tmp_path, name, expect_decision):
    out_path = tmp_path / "out.json"
    proc = subprocess.run(
        [sys.executable, str(VOI / "pymc_voi.py"), str(VOI / "problems" / name),
         str(out_path), "50000"],
        capture_output=True, text=True, encoding="utf-8", errors="replace")
    assert proc.returncode == 0, proc.stderr
    out = json.loads(out_path.read_text(encoding="utf-8"))
    spec = load(name)
    exact_evpi = 390000.0  # attendu exact du contrat (verifie a la main dans la PR)
    assert out["engine"] == "pymc"
    assert out["action_no_info"] == "vendre"
    assert abs(out["eu_no_info"] - 200000.0) <= TOLERANCE["utility_abs"]
    assert abs(out["evpi"] - exact_evpi) <= TOLERANCE["utility_abs"]
    assert out["decision"] == expect_decision
    if name.startswith("forage-non-informatif"):
        assert abs(out["evsi_brute"]) <= TOLERANCE["utility_abs"]
    else:
        assert 0 < out["evsi_nette"] < out["evpi"]
    assert set(out["posteriors"]) == set(spec["signals"])
