"""Tests du garde de parametres GenAI (#20682).

Aucun reseau : la matrice est une fixture inline. Un test distinct verifie
que la matrice livree (param_matrix.json) est coherente avec les verdicts
que la garde sait traiter.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

ENV_DIR = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ENV_DIR))

import param_guard  # noqa: E402

MATRIX = {
    "gpt-5-mini": {
        "parametres": {
            "temperature": {"verdict": "REFUSE", "date": "2026-10-26", "source": "api.openai.com"},
            "top_p": {"verdict": "ACCEPTE", "date": "2026-10-26", "source": "api.openai.com"},
        }
    },
    "openai/gpt-5-mini": {
        "parametres": {
            "temperature": {"verdict": "REFUSE", "date": "2026-10-26", "source": "openrouter.ai"},
        }
    },
    "gpt-image-1": {
        "parametres": {
            "style": {"verdict": "IGNORE", "date": "2026-10-26", "source": "api.openai.com"},
        }
    },
    "gpt-5*": {
        "parametres": {
            "temperature": {"verdict": "REFUSE", "date": "2026-10-26", "source": "famille gpt-5, mesure sur gpt-5-mini"},
        }
    },
}


def test_param_refuse_est_signale_et_retire(capsys):
    params = param_guard.guard_call("gpt-5-mini", {"temperature": 0.0, "top_p": 0.9}, matrix=MATRIX)
    # Le parametre refuse ne part pas dans l'appel : plus de 400 silencieux.
    assert params == {"top_p": 0.9}
    out = capsys.readouterr().out
    assert "[param_guard]" in out
    assert "temperature" in out
    assert "2026-10-26" in out


def test_slug_openrouter_resout_vers_le_modele():
    warnings = param_guard.check_params(
        "openai/gpt-5-mini", {"temperature": 0.0}, matrix=MATRIX, echo=False
    )
    assert len(warnings) == 1
    assert "openrouter.ai" in warnings[0]


def test_modele_de_famille_herite_de_lentree_familiale():
    warnings = param_guard.check_params("gpt-5-nano", {"temperature": 0.3}, matrix=MATRIX, echo=False)
    assert len(warnings) == 1
    assert "famille" in warnings[0]


def test_parametre_ignore_est_garde_mais_signale(capsys):
    params = param_guard.guard_call("gpt-image-1", {"style": "vivid"}, matrix=MATRIX)
    # IGNORE : l'appel reussit, on garde le parametre (inoffensif) mais on le dit.
    assert params == {"style": "vivid"}
    out = capsys.readouterr().out
    assert "aucun effet" in out


def test_modele_inconnu_garde_silence():
    params = {"temperature": 0.5}
    assert param_guard.guard_call("modele-jamais-mesure", params, matrix=MATRIX) == params
    assert param_guard.check_params("modele-jamais-mesure", params, matrix=MATRIX, echo=False) == []


def test_parametre_accepte_passe_sans_bruit(capsys):
    params = param_guard.guard_call("gpt-5-mini", {"top_p": 0.9}, matrix=MATRIX)
    assert params == {"top_p": 0.9}
    assert capsys.readouterr().out == ""


def test_matrice_livree_est_coherente():
    shipped = param_guard.load_matrix()
    assert shipped, "param_matrix.json doit etre livre avec la garde"
    for key, entry in shipped.items():
        assert "parametres" in entry, f"{key} sans section parametres"
        for param, info in entry["parametres"].items():
            assert info.get("verdict") in param_guard.VERDICTS, f"{key}.{param} verdict inconnu"
            assert "date" in info and "source" in info, f"{key}.{param} sans date ou source"
