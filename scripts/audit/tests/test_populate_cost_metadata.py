#!/usr/bin/env python3
"""Tests pour populate_cost_metadata.py — Issue #8056, profile quantbook."""

import json
import sys
from pathlib import Path

# Importer le module voisin (scripts/audit est sur sys.path via conftest ou ajout manuel).
HERE = Path(__file__).resolve().parent
AUDIT_DIR = HERE.parent
sys.path.insert(0, str(AUDIT_DIR))

import populate_cost_metadata as pcm  # noqa: E402


def _make_quantbook(n_code_cells: int = 10) -> dict:
    """Un notebook QuantBook minimal avec n cellules code."""
    nb = {
        "cells": [
            {"cell_type": "markdown", "metadata": {}, "source": ["# Demo\n"]},
            {"cell_type": "code", "execution_count": None, "metadata": {},
             "outputs": [], "source": ["qb = QuantBook()\n"]},
        ],
        "metadata": {"kernelspec": {"name": "python3"}},
        "nbformat": 4, "nbformat_minor": 5,
    }
    for _ in range(n_code_cells - 1):
        nb["cells"].append({"cell_type": "code", "execution_count": None,
                            "metadata": {}, "outputs": [], "source": ["x = 1\n"]})
    return nb


def _make_non_qc() -> dict:
    return {"cells": [{"cell_type": "code", "execution_count": None,
                       "metadata": {}, "outputs": [], "source": ["print('hi')\n"]}],
            "metadata": {}, "nbformat": 4, "nbformat_minor": 5}


# === Heuristic QCC ===

def test_qcc_heuristic_floor():
    """Peu de cellules → plancher 400 (cf #8056, cost-matrix.md)."""
    assert pcm.qcc_tokens_estimate(0) == 400
    assert pcm.qcc_tokens_estimate(1) == 400
    assert pcm.qcc_tokens_estimate(5) == 400  # 5×70=350 < 400


def test_qcc_heuristic_linear():
    """Au-delà du plancher, ~70 QCC/cellule."""
    assert pcm.qcc_tokens_estimate(10) == 700
    assert pcm.qcc_tokens_estimate(14) == 980   # acceptance #8056 : « 14 cellules ≈ 800-1200 »
    assert pcm.qcc_tokens_estimate(28) == 1960  # QC-Py-04 observé


# === Detection ===

def test_uses_quantbook_detect():
    assert pcm._uses_quantbook(_make_quantbook())
    assert not pcm._uses_quantbook(_make_non_qc())


def test_count_code_cells_ignores_empty():
    nb = _make_quantbook(3)
    nb["cells"].append({"cell_type": "code", "execution_count": None,
                        "metadata": {}, "outputs": [], "source": ["   \n"]})  # whitespace only
    assert pcm._count_code_cells(nb) == 3  # cellule vide non comptée


# === build_quantbook_cost : champs obligatoires + valeurs canoniques ===

def test_build_cost_has_all_mandatory_fields():
    cost = pcm.build_quantbook_cost(_make_quantbook(10), by="m:w", today="2026-07-26")
    mandatory = {"api_usd_est", "api_provider", "cpu_min", "gpu_required",
                 "network", "external_account", "reproducibility",
                 "metadata_written", "validator"}
    assert mandatory <= set(cost), f"champs obligatoires manquants: {mandatory - set(cost)}"


def test_build_cost_clears_litmus5_and_7():
    """validator=qc_cloud (Litmus 5) + qcc_tokens_est nonzero (Litmus 7)."""
    cost = pcm.build_quantbook_cost(_make_quantbook(10), by="m:w", today="2026-07-26")
    assert cost["validator"] == "qc_cloud"
    assert cost["qcc_tokens_est"] > 0


def test_build_cost_honest_nulls_for_notebook_specific():
    """reduced_pedagogical + free_alternative = null (jugement humain, jamais fabriqué)."""
    cost = pcm.build_quantbook_cost(_make_quantbook(10), by="m:w", today="2026-07-26")
    assert cost["reduced_pedagogical"] is None
    assert cost["free_alternative"] is None


def test_build_cost_matches_migrated_consensus():
    """Consensus des 13 quantbooks migrés (#8585) : api_provider=none, network=true,
    external_account=quantconnect-organization."""
    cost = pcm.build_quantbook_cost(_make_quantbook(10), by="m:w", today="2026-07-26")
    assert cost["api_provider"] == "none"
    assert cost["network"] is True
    assert cost["external_account"] == "quantconnect-organization"


# === Idempotence (HARD) ===

def test_populate_idempotent_never_overwrites(tmp_path):
    """Un notebook déjà peuplé est skippé — JAMAIS écraser un bloc existant."""
    nb = _make_quantbook(10)
    nb["metadata"]["cost"] = {"api_usd_est": 0.42, "validator": "manual"}  # bloc existant
    p = tmp_path / "nb.ipynb"
    p.write_text(json.dumps(nb, indent=1), encoding="utf-8")

    status = pcm.populate_notebook(p, profile="quantbook", by="m:w", today="2026-07-26", apply=True)
    assert status == "skipped-has-cost"
    # Le bloc existant est intact
    after = json.loads(p.read_text(encoding="utf-8"))
    assert after["metadata"]["cost"]["api_usd_est"] == 0.42
    assert after["metadata"]["cost"]["validator"] == "manual"


def test_populate_skips_non_qc(tmp_path):
    nb = _make_non_qc()
    p = tmp_path / "nb.ipynb"
    p.write_text(json.dumps(nb, indent=1), encoding="utf-8")
    assert pcm.populate_notebook(p, profile="quantbook", by="m:w", today="2026-07-26", apply=True) == "skipped-no-quantbook"


def test_populate_applies_and_writes(tmp_path):
    nb = _make_quantbook(10)
    p = tmp_path / "nb.ipynb"
    p.write_text(json.dumps(nb, indent=1), encoding="utf-8")
    status = pcm.populate_notebook(p, profile="quantbook", by="m:w", today="2026-07-26", apply=True)
    assert status == "populated"
    after = json.loads(p.read_text(encoding="utf-8"))
    assert after["metadata"]["cost"]["qcc_tokens_est"] == 700
    assert after["metadata"]["cost"]["validator"] == "qc_cloud"


def test_populate_dry_run_writes_nothing(tmp_path):
    nb = _make_quantbook(10)
    p = tmp_path / "nb.ipynb"
    original = json.dumps(nb, indent=1)
    p.write_text(original, encoding="utf-8")
    status = pcm.populate_notebook(p, profile="quantbook", by="m:w", today="2026-07-26", apply=False)
    assert status == "populated"  # rapporte qu'il peuplerait
    assert p.read_text(encoding="utf-8") == original  # mais n'écrit rien


def test_populate_preserves_notebook_structure(tmp_path):
    """La transformation ne touche QUE metadata.cost — cells/kernel/nbformat intacts."""
    nb = _make_quantbook(10)
    nb["metadata"]["kernelspec"] = {"name": "python3", "display_name": "Python 3"}
    nb["metadata"]["custom_field"] = "preserve-me"
    p = tmp_path / "nb.ipynb"
    p.write_text(json.dumps(nb, indent=1), encoding="utf-8")
    pcm.populate_notebook(p, profile="quantbook", by="m:w", today="2026-07-26", apply=True)
    after = json.loads(p.read_text(encoding="utf-8"))
    assert after["metadata"]["kernelspec"]["display_name"] == "Python 3"
    assert after["metadata"]["custom_field"] == "preserve-me"
    assert after["nbformat"] == 4
    assert len(after["cells"]) == len(nb["cells"])  # aucune cellule touchée


# =============================================================================
# Profile search-cpu (CPU-pur déterministe — Issue #8056, rollout Search tranche)
# =============================================================================

def _make_search_cpu(n_code: int = 10, nuget: bool = False) -> dict:
    """Un notebook CPU-pur minimal (algorithmes de recherche), n cellules code."""
    nb = {
        "cells": [
            {"cell_type": "markdown", "metadata": {}, "source": ["# Search demo\n"]},
        ],
        "metadata": {"kernelspec": {"name": "python3"}},
        "nbformat": 4, "nbformat_minor": 5,
    }
    first = '#r "nuget: QuikGraph, 1.0.0"\n' if nuget else "import heapq\n"
    nb["cells"].append({"cell_type": "code", "execution_count": 1, "metadata": {},
                        "outputs": [], "source": [first]})
    for _ in range(n_code - 1):
        nb["cells"].append({"cell_type": "code", "execution_count": 1, "metadata": {},
                            "outputs": [], "source": ["path = astar(graph, start, goal)\n"]})
    return nb


def _make_api_nb() -> dict:
    """Notebook qui appelle une API → NON éligible search-cpu."""
    return {"cells": [{"cell_type": "code", "execution_count": None, "metadata": {},
                       "outputs": [], "source": ["import openai\nclient = openai.ChatCompletion.create()\n"]}],
            "metadata": {}, "nbformat": 4, "nbformat_minor": 5}


def _make_gpu_nb() -> dict:
    """Notebook GPU → NON éligible search-cpu."""
    return {"cells": [{"cell_type": "code", "execution_count": None, "metadata": {},
                       "outputs": [], "source": ["x = torch.tensor([1.0]).cuda()\n"]}],
            "metadata": {}, "nbformat": 4, "nbformat_minor": 5}


# === Gate is_cpu_pure ===

def test_is_cpu_pure_true_for_stdlib():
    assert pcm.is_cpu_pure(_make_search_cpu(10))


def test_is_cpu_pure_false_for_quantbook():
    assert not pcm.is_cpu_pure(_make_quantbook(10))


def test_is_cpu_pure_false_for_api():
    assert not pcm.is_cpu_pure(_make_api_nb())


def test_is_cpu_pure_false_for_gpu():
    assert not pcm.is_cpu_pure(_make_gpu_nb())


def _nb_with(source: str) -> dict:
    """Notebook minimal à une cellule, source arbitraire (helper pour edge-cases)."""
    return {"cells": [{"cell_type": "code", "execution_count": None, "metadata": {},
                       "outputs": [], "source": [source]}],
            "metadata": {}, "nbformat": 4, "nbformat_minor": 5}


def test_is_cpu_pure_false_for_mistralai_sdk():
    """Le SDK officiel Mistral (`from mistralai import …`, sans `.` après mistral)
    doit être attrapé — concern #1 Hermes (po-2026) sur #8660."""
    assert not pcm.is_cpu_pure(_nb_with("from mistralai import Mistral\nclient = Mistral()\n"))


def test_is_cpu_pure_false_for_generic_http_libs():
    """requests/httpx/urllib = réseau → NON CPU-pur. Couvre l'import ET l'appel,
    et NE matche PAS le mot isolé « requests » en prose (concern #2 Hermes)."""
    # Imports + appels typiques → gate refuse.
    assert not pcm.is_cpu_pure(_nb_with("import requests\nr = requests.get('https://api.x')\n"))
    assert not pcm.is_cpu_pure(_nb_with("from httpx import Client\nhttpx.get('https://x')\n"))
    assert not pcm.is_cpu_pure(_nb_with("import urllib.request\nurllib.request.urlopen('https://x')\n"))
    # Le mot « requests » en prose NE doit PAS déclencher le gate (anti-FP G.1).
    assert pcm.is_cpu_pure(_nb_with("# On fait quelques requests vers le serveur local (prose).\nprint('ok')\n"))


# === build_search_cpu_cost ===

def test_search_cpu_cost_has_mandatory_fields():
    cost = pcm.build_search_cpu_cost(_make_search_cpu(10), by="m:w", today="2026-07-28")
    mandatory = {"api_usd_est", "api_provider", "cpu_min", "gpu_required",
                 "network", "external_account", "reproducibility",
                 "metadata_written", "validator"}
    assert mandatory <= set(cost)


def test_search_cpu_cost_canonical_values():
    cost = pcm.build_search_cpu_cost(_make_search_cpu(10), by="m:w", today="2026-07-28")
    assert cost["api_usd_est"] == 0.0
    assert cost["api_provider"] == "none"
    assert cost["qcc_tokens_est"] == 0
    assert cost["gpu_required"] is False
    assert cost["external_account"] == "none"
    assert cost["free_alternative"] == "self"  # sentinelle canonique
    assert cost["reduced_pedagogical"] is None  # honnête, pas fabriqué
    assert cost["reproducibility"] == "HIGH"  # déterministe
    assert cost["validator"] == "manual"  # inspection source, pas re-exec claimée


def test_search_cpu_network_false_without_nuget():
    cost = pcm.build_search_cpu_cost(_make_search_cpu(10, nuget=False), by="m:w", today="2026-07-28")
    assert cost["network"] is False


def test_search_cpu_network_true_with_nuget():
    """Restore NuGet au runtime = réseau requis."""
    cost = pcm.build_search_cpu_cost(_make_search_cpu(10, nuget=True), by="m:w", today="2026-07-28")
    assert cost["network"] is True


def test_search_cpu_cpu_min_heuristic():
    assert pcm.build_search_cpu_cost(_make_search_cpu(5), "", "")["cpu_min"] == 1    # ≤15
    assert pcm.build_search_cpu_cost(_make_search_cpu(20), "", "")["cpu_min"] == 2   # 16-25
    assert pcm.build_search_cpu_cost(_make_search_cpu(30), "", "")["cpu_min"] == 3   # >25


# === Dispatch populate_notebook profile=search-cpu ===

def test_search_cpu_populates_cpu_pure(tmp_path):
    nb = _make_search_cpu(10)
    p = tmp_path / "nb.ipynb"
    p.write_text(json.dumps(nb, indent=1), encoding="utf-8")
    status = pcm.populate_notebook(p, profile="search-cpu", by="m:w",
                                   today="2026-07-28", apply=True)
    assert status == "populated"
    after = json.loads(p.read_text(encoding="utf-8"))
    assert after["metadata"]["cost"]["validator"] == "manual"
    assert after["metadata"]["cost"]["api_provider"] == "none"


def test_search_cpu_skips_api_notebook(tmp_path):
    """Un notebook API n'est PAS éligible search-cpu → skip (ne pas fabriquer)."""
    nb = _make_api_nb()
    p = tmp_path / "nb.ipynb"
    p.write_text(json.dumps(nb, indent=1), encoding="utf-8")
    status = pcm.populate_notebook(p, profile="search-cpu", by="m:w",
                                   today="2026-07-28", apply=True)
    assert status == "skipped-not-cpu-pure"
    after = json.loads(p.read_text(encoding="utf-8"))
    assert "cost" not in after["metadata"]  # rien écrit


def test_search_cpu_idempotent(tmp_path):
    nb = _make_search_cpu(10)
    nb["metadata"]["cost"] = {"api_usd_est": 0.42}  # déjà peuplé
    p = tmp_path / "nb.ipynb"
    p.write_text(json.dumps(nb, indent=1), encoding="utf-8")
    status = pcm.populate_notebook(p, profile="search-cpu", by="m:w",
                                   today="2026-07-28", apply=True)
    assert status == "skipped-has-cost"
    after = json.loads(p.read_text(encoding="utf-8"))
    assert after["metadata"]["cost"]["api_usd_est"] == 0.42  # intact


def test_search_cpu_preserves_trailing_newline(tmp_path):
    """Byte-surgical : un notebook SANS trailing newline le reste (C913-L)."""
    nb = _make_search_cpu(10)
    p = tmp_path / "nb.ipynb"
    p.write_text(json.dumps(nb, indent=1), encoding="utf-8")  # pas de \n final
    pcm.populate_notebook(p, profile="search-cpu", by="m:w", today="2026-07-28", apply=True)
    assert not p.read_text(encoding="utf-8").endswith("\n")  # trailing-nl préservé (absent)


def test_search_cpu_preserves_cells(tmp_path):
    """Ne touche QUE metadata.cost — cells/kernel/nbformat intacts."""
    nb = _make_search_cpu(10)
    nb["metadata"]["custom_field"] = "keep"
    p = tmp_path / "nb.ipynb"
    p.write_text(json.dumps(nb, indent=1), encoding="utf-8")
    pcm.populate_notebook(p, profile="search-cpu", by="m:w", today="2026-07-28", apply=True)
    after = json.loads(p.read_text(encoding="utf-8"))
    assert after["metadata"]["custom_field"] == "keep"
    assert len(after["cells"]) == len(nb["cells"])


# =============================================================================
# Profile rl-cpu (RL CPU-pur — Issue #8056, rollout RL family)
# =============================================================================

def _make_rl_cpu(n_code: int = 10, gpu: bool = False) -> dict:
    """Un notebook RL CPU-pur minimal (gymnasium/stable-baselines3), n cellules code.
    Si `gpu=True`, ajoute un VRAI signal GPU (transfert explicite .cuda()) pour tester le skip.
    (Uniquement `torch.cuda.is_available()` ne compte PAS — c'est une sonde bénigne,
    cf test_is_rl_cpu_pure_true_for_cuda_availability_probe.)"""
    nb = {
        "cells": [
            {"cell_type": "markdown", "metadata": {},
             "source": ["# RL demo (cf gym.openai.com/envs/#classic_control)\n"]},
        ],
        "metadata": {"kernelspec": {"name": "python3"}},
        "nbformat": 4, "nbformat_minor": 5,
    }
    first = ("import torch\n"
             "model = Policy().cuda()  # real GPU transfer\n") if gpu else "import gymnasium as gym\n"
    nb["cells"].append({"cell_type": "code", "execution_count": 1, "metadata": {},
                        "outputs": [], "source": [first]})
    for _ in range(n_code - 1):
        nb["cells"].append({"cell_type": "code", "execution_count": 1, "metadata": {},
                            "outputs": [],
                            "source": ["obs, info = env.reset(seed=0)\naction = policy(obs)\n"]})
    return nb


# === Gate is_rl_cpu_pure ===

def test_is_rl_cpu_pure_true_for_local_rl():
    """gymnasium/stable-baselines3 local = CPU-pur RL → éligible."""
    assert pcm.is_rl_cpu_pure(_make_rl_cpu(10))


def test_is_rl_cpu_pure_ignores_openai_prose_fp():
    """FP prose critique (C920-L) : « gym.openai.com », « jeux d'OpenAI » ne sont PAS
    des appels API cloud (gymnasium/SB3 = libs locales). Le gate précis ne doit PAS
    skipper ces notebooks — sinon rl_1 (intro CartPole), rl_6c (PPO), rl_6d (SAC)
    resteraient non couverts."""
    assert pcm.is_rl_cpu_pure(_nb_with("env = gymnasium.make('CartPole-v1')  # voir gym.openai.com\n"))
    assert pcm.is_rl_cpu_pure(_nb_with("# Inspiré de spinningup.openai.com — algorithme PPO from scratch.\n"))
    assert pcm.is_rl_cpu_pure(_nb_with("PPO et SAC sont des algorithmes popularisés par OpenAI (Spinning Up).\n"))


def test_is_rl_cpu_pure_false_for_quantbook():
    assert not pcm.is_rl_cpu_pure(_make_quantbook(10))


def test_is_rl_cpu_pure_false_for_real_gpu():
    """Vrai signal GPU (transfert explicite `.cuda()`, `torch.cuda.synchronize`) → skippé.
    Le gate reste conservateur sur l'usage GPU réel : un notebook qui déplace tenseurs/modèles
    vers le GPU n'est PAS CPU-pur."""
    assert not pcm.is_rl_cpu_pure(_make_rl_cpu(10, gpu=True))
    assert not pcm.is_rl_cpu_pure(_nb_with("device = torch.device('cuda')\nx = x.cuda()\n"))
    assert not pcm.is_rl_cpu_pure(_nb_with("torch.cuda.synchronize()\n"))


def test_is_rl_cpu_pure_true_for_cuda_availability_probe():
    """Sonde CUDA ≠ exigence CUDA : un notebook qui affiche `torch.cuda.is_available()`
    pour info puis tourne en CPU (`device="cpu"`) reste rl-cpu-pur. Couvre rl_6e (GRPO
    from-scratch, CPU pédagogique — output committé « PyTorch 2.11.0+cpu, CUDA=False »,
    entraînement multi-seed [0,7,42] complet sur CPU). La sonde seule ne doit PAS
    skipper — c'était le faux-négatif qui laissait rl_6e sans cost metadata."""
    src_probe = ("import torch\n"
                 "print(f'CUDA={torch.cuda.is_available()}')\n"
                 "def rollout(env, policy, device='cpu'):\n"
                 "    return torch.FloatTensor(s).to(device)\n")
    assert pcm.is_rl_cpu_pure(_nb_with(src_probe))


def test_is_rl_cpu_pure_false_for_real_api_call():
    """Un VRAI appel API cloud (import/instance OpenAI/anthropic/replicate) → skippé.
    Le gate précis distingue l'appel réel de la prose (cf test ci-dessus)."""
    assert not pcm.is_rl_cpu_pure(_nb_with("from openai import OpenAI\nclient = OpenAI()\n"))
    assert not pcm.is_rl_cpu_pure(_nb_with("import openai\nr = openai.ChatCompletion.create()\n"))
    assert not pcm.is_rl_cpu_pure(_nb_with("from anthropic import Anthropic\nclient = Anthropic()\n"))


# === build_rl_cpu_cost ===

def test_rl_cpu_cost_has_mandatory_fields():
    cost = pcm.build_rl_cpu_cost(_make_rl_cpu(10), by="m:w", today="2026-07-28")
    mandatory = {"api_usd_est", "api_provider", "cpu_min", "gpu_required",
                 "network", "external_account", "reproducibility",
                 "metadata_written", "validator"}
    assert mandatory <= set(cost)


def test_rl_cpu_cost_canonical_values():
    """RL CPU-pur : gratuit, CPU, network False (pip local). Diffère de search-cpu :
    reproducibility MED (stochastique, seeds) vs HIGH (déterministe)."""
    cost = pcm.build_rl_cpu_cost(_make_rl_cpu(10), by="m:w", today="2026-07-28")
    assert cost["api_usd_est"] == 0.0
    assert cost["api_provider"] == "none"
    assert cost["qcc_tokens_est"] == 0
    assert cost["gpu_required"] is False
    assert cost["network"] is False  # pip install local, pas d'appel runtime
    assert cost["external_account"] == "none"
    assert cost["free_alternative"] == "self"  # sentinelle canonique
    assert cost["reduced_pedagogical"] is None  # honnête, pas fabriqué
    assert cost["reproducibility"] == "MED"  # stochastique (seeds), pas déterministe
    assert cost["validator"] == "manual"


def test_rl_cpu_cpu_min_heuristic():
    """cpu_min RL plus élevé que search-cpu (boucles d'entraînement vs algo single-pass)."""
    assert pcm.build_rl_cpu_cost(_make_rl_cpu(5), "", "")["cpu_min"] == 2    # ≤12
    assert pcm.build_rl_cpu_cost(_make_rl_cpu(15), "", "")["cpu_min"] == 3   # 13-18
    assert pcm.build_rl_cpu_cost(_make_rl_cpu(25), "", "")["cpu_min"] == 4   # >18


# === Dispatch populate_notebook profile=rl-cpu ===

def test_rl_cpu_populates_local_rl(tmp_path):
    nb = _make_rl_cpu(10)
    p = tmp_path / "nb.ipynb"
    p.write_text(json.dumps(nb, indent=1), encoding="utf-8")
    status = pcm.populate_notebook(p, profile="rl-cpu", by="m:w",
                                   today="2026-07-28", apply=True)
    assert status == "populated"
    after = json.loads(p.read_text(encoding="utf-8"))
    assert "cost" in after["metadata"]
    assert after["metadata"]["cost"]["reproducibility"] == "MED"


def test_rl_cpu_skips_gpu_notebook(tmp_path):
    """rl_6e-style (CUDA-hard) → skippé avec la raison rl-cpu."""
    nb = _make_rl_cpu(10, gpu=True)
    p = tmp_path / "nb.ipynb"
    p.write_text(json.dumps(nb, indent=1), encoding="utf-8")
    status = pcm.populate_notebook(p, profile="rl-cpu", by="m:w",
                                   today="2026-07-28", apply=True)
    assert status == "skipped-not-rl-cpu-pure"


def test_rl_cpu_idempotent(tmp_path):
    nb = _make_rl_cpu(10)
    nb["metadata"]["cost"] = {"existing": True}
    p = tmp_path / "nb.ipynb"
    p.write_text(json.dumps(nb, indent=1), encoding="utf-8")
    status = pcm.populate_notebook(p, profile="rl-cpu", by="m:w",
                                   today="2026-07-28", apply=True)
    assert status == "skipped-has-cost"
