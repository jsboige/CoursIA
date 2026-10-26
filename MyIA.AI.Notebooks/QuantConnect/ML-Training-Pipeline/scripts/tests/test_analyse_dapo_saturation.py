# Tests de l'organe de saturation du budget de completion (DAPO/GRPO, #15293).
#
# L'organe doit distinguer trois etats, jamais deux :
#   SIGNAL_UTILE   -- le budget n'est pas la contrainte dominante ;
#   SIGNAL_PARTIEL -- le signal existe mais porte sur moins de la moitie des
#                     steps (c'est le cas mesure du bras 8B) ;
#   SIGNAL_NUL     -- toutes les steps saturees : le bras n'a rien appris,
#                     meme si `rc=0` et si le log est plein de metriques.
#
# Un detecteur se valide par ses faux negatifs : le cas 4 verifie que le
# verdict de saturation ne se laisse pas influencer par un gradient non nul
# (un run peut avoir un gradient et ne rien apprendre).
#
# Le regroupement par BRAS (`model_key`) est teste a part : un fichier qui
# n'est pas une graine (resume, baseline) ne doit pas pouvoir contaminer le
# verdict d'un bras.

from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

SCRIPTS = Path(__file__).resolve().parents[1]
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

import analyse_dapo_saturation as organ  # noqa: E402


def _artefact(
    n_steps: int = 10,
    budget: int = 384,
    longueur: float = 100.0,
    clipped: float = 0.0,
    grad: float = 1.0,
    zero_std: float = 0.0,
    reward: float = 0.5,
    seed: int = 0,
    model_key: str = "qwen3_8b",
) -> dict:
    log_history = []
    for step in range(n_steps):
        log_history.append(
            {
                "step": step,
                "completions/clipped_ratio": clipped,
                "completions/mean_length": longueur,
                "grad_norm": grad,
                "loss": 0.5,
                "frac_reward_zero_std": zero_std,
                "reward": reward,
            }
        )
    return {
        "model": "test/model",
        "model_key": model_key,
        "seed": seed,
        "max_completion_length": budget,
        "wallclock_s": 123.4,
        "log_history": log_history,
    }


def _ecrire(tmp_path: Path, nom: str, artefact: dict) -> Path:
    chemin = tmp_path / nom
    chemin.write_text(json.dumps(artefact), encoding="utf-8")
    return chemin


# --- les trois etats -------------------------------------------------------


def test_budget_large_sur_toutes_les_steps_donne_un_signal_utile():
    rapport = organ.mesurer(_artefact(longueur=100.0, clipped=0.1, grad=1.0))
    assert rapport["verdict"] == "SIGNAL_UTILE"
    assert rapport["frac_steps_satures"] == 0.0
    assert rapport["steps"] == 10


def test_budget_sature_a_cousir_donne_un_signal_nul():
    rapport = organ.mesurer(_artefact(longueur=384.0, clipped=1.0, grad=0.0))
    assert rapport["verdict"] == "SIGNAL_NUL"
    assert rapport["frac_steps_satures"] == 1.0
    assert rapport["frac_steps_tronquees"] == 1.0


def test_budget_sature_a_moitie_donne_un_signal_partiel():
    # 6 steps sur 10 au plafond, et un gradient present sur les 4 autres
    log_history = []
    for step in range(10):
        sature = step < 6
        log_history.append(
            {
                "step": step,
                "completions/clipped_ratio": 1.0 if sature else 0.2,
                "completions/mean_length": 384.0 if sature else 120.0,
                "grad_norm": 0.0 if sature else 0.8,
                "loss": 0.0 if sature else 0.4,
                "frac_reward_zero_std": 1.0 if sature else 0.1,
                "reward": 0.0 if sature else 0.5,
            }
        )
    artefact = _artefact()
    artefact["log_history"] = log_history
    rapport = organ.mesurer(artefact)
    assert rapport["verdict"] == "SIGNAL_PARTIEL"
    assert rapport["frac_steps_satures"] == 0.6
    assert rapport["frac_steps_sans_gradient"] == 0.6


# --- le faux negatif du detecteur ------------------------------------------


def test_un_gradient_present_ne_sauve_pas_un_bras_sature():
    # Un run peut avoir grad != 0 et ne rien apprendre : le verdict de
    # saturation doit dependre du budget, pas du gradient.
    rapport = organ.mesurer(_artefact(longueur=384.0, clipped=1.0, grad=0.9))
    assert rapport["verdict"] == "SIGNAL_NUL"
    assert rapport["frac_steps_sans_gradient"] == 0.0


def test_la_longueur_saturee_sans_clipped_ratio_a_1_compte_comme_saturee():
    # Le harness peut rapporter clipped_ratio < 1 alors que la longueur est au
    # plafond : c'est la longueur qui fait foi pour le budget.
    rapport = organ.mesurer(_artefact(longueur=384.0, clipped=0.9, grad=1.0))
    assert rapport["frac_steps_satures"] == 1.0
    assert rapport["verdict"] == "SIGNAL_NUL"


def test_un_ecart_type_nul_signale_une_termination_rompue():
    # Toutes les generations finissent exactement au plafond : le modele ne
    # termine jamais (contrat EOS rompu), ce qui n'est pas la meme chose que
    # "le modele veut ecrire plus long que le budget".
    rapport = organ.mesurer(_artefact(longueur=384.0, clipped=1.0, grad=0.0))
    assert rapport["mean_length_ecart_type"] == 0.0


def test_un_ecart_type_large_signale_une_pression_de_budget_reelle():
    artefact = _artefact()
    for i, entree in enumerate(artefact["log_history"]):
        entree["completions/mean_length"] = 384.0 if i % 2 == 0 else 240.0
    rapport = organ.mesurer(artefact)
    assert rapport["mean_length_ecart_type"] > 1.0


# --- robustesse ------------------------------------------------------------


def test_artefact_sans_log_history_est_illisible():
    rapport = organ.mesurer({"seed": 1, "max_completion_length": 384})
    assert rapport["verdict"] == "ILLISIBLE"


def test_artefact_sans_budget_est_illisible():
    artefact = _artefact()
    artefact.pop("max_completion_length")
    rapport = organ.mesurer(artefact)
    assert rapport["verdict"] == "ILLISIBLE"


def test_cle_absente_ne_casse_pas_la_mesure():
    artefact = _artefact()
    for entree in artefact["log_history"]:
        entree.pop("grad_norm", None)
    rapport = organ.mesurer(artefact)
    assert rapport["steps"] == 10
    assert rapport["frac_steps_sans_gradient"] is None


# --- le gain d'evaluation rapporte au nombre de steps vivantes --------------


def test_le_gain_est_divise_par_les_steps_qui_ont_porte_un_gradient():
    # 10 steps, 6 sans gradient -> 4 steps vivantes ; gain 0.20 -> 0.05/step.
    artefact = _artefact(longueur=384.0, clipped=1.0, grad=0.0)
    for i, entree in enumerate(artefact["log_history"]):
        entree["grad_norm"] = 0.0 if i < 6 else 1.0
    artefact["pre_eval"] = {"reward_mean": 0.10}
    artefact["post_eval"] = {"reward_mean": 0.30}
    rapport = organ.mesurer(artefact)
    assert rapport["steps_avec_gradient"] == 4
    assert rapport["gain_eval_recompense"] == 0.2
    assert rapport["gain_eval_par_step_avec_gradient"] == 0.05


def test_un_artefact_sans_eval_ne_rend_pas_de_gain():
    rapport = organ.mesurer(_artefact())
    assert rapport["gain_eval_recompense"] is None
    assert rapport["gain_eval_par_step_avec_gradient"] is None


def test_un_bras_sans_aucune_step_vivante_ne_divise_pas_par_zero():
    artefact = _artefact(longueur=384.0, clipped=1.0, grad=0.0)
    artefact["pre_eval"] = {"reward_mean": 0.10}
    artefact["post_eval"] = {"reward_mean": 0.30}
    rapport = organ.mesurer(artefact)
    assert rapport["steps_avec_gradient"] == 0
    assert rapport["gain_eval_par_step_avec_gradient"] is None


def test_fichier_illisible_est_signale_sans_raising(tmp_path: Path):
    rapport = organ.mesurer_fichiers([tmp_path / "absent.json"])
    assert rapport["hors_bras"][0]["fichier"] == "absent.json"


# --- le regroupement par bras ----------------------------------------------


def test_les_graines_sont_regroupees_par_model_key(tmp_path: Path):
    a = _ecrire(tmp_path, "a.json", _artefact(model_key="qwen3_8b", seed=0))
    b = _ecrire(tmp_path, "b.json", _artefact(model_key="minicpm5", seed=0))
    rapport = organ.mesurer_fichiers([a, b])
    assert set(rapport["bras"]) == {"qwen3_8b", "minicpm5"}


def test_un_fichier_hors_bras_ne_contamine_pas_le_verdict(tmp_path: Path):
    # Un `summary.json` (resume, sans log_history) ne doit pas faire passer un
    # bras sature en "illisible" -- c'est le faux negatif du regroupement.
    graine = _ecrire(tmp_path, "seed0.json", _artefact(longueur=384.0, clipped=1.0, grad=0.0))
    resume = tmp_path / "summary.json"
    resume.write_text(json.dumps({"module": "x"}), encoding="utf-8")
    rapport = organ.mesurer_fichiers([graine, resume])
    assert rapport["bras"]["qwen3_8b"]["verdict"] == "SIGNAL_NUL"
    assert [h["fichier"] for h in rapport["hors_bras"]] == ["summary.json"]
    assert rapport["verdict_global"] == "SIGNAL_NUL"


def test_le_verdict_du_bras_suit_la_graine_mediane(tmp_path: Path):
    # une graine nulle + une graine utile -> le bras n'est pas SIGNAL_NUL
    nulle = _ecrire(tmp_path, "seed0.json", _artefact(longueur=384.0, clipped=1.0, grad=0.0, seed=0))
    utile = _ecrire(tmp_path, "seed1.json", _artefact(longueur=100.0, clipped=0.1, grad=1.0, seed=1))
    rapport = organ.mesurer_fichiers([nulle, utile])
    assert rapport["bras"]["qwen3_8b"]["verdict"] != "SIGNAL_NUL"
    assert rapport["verdict_global"] != "SIGNAL_NUL"


def test_un_bras_sature_ne_tire_pas_le_verdict_global_si_un_autre_tient(tmp_path: Path):
    nul = _ecrire(tmp_path, "n.json", _artefact(longueur=384.0, clipped=1.0, grad=0.0,
                                                seed=0, model_key="qwen35"))
    partiel = _ecrire(tmp_path, "p.json", _artefact(longueur=300.0, clipped=0.5, grad=0.2,
                                                     seed=0, model_key="qwen3_8b"))
    rapport = organ.mesurer_fichiers([nul, partiel])
    assert rapport["bras"]["qwen35"]["verdict"] == "SIGNAL_NUL"
    assert rapport["verdict_global"] != "SIGNAL_NUL"


def test_le_code_de_sortie_vaut_1_si_tous_les_bras_sont_nuls(tmp_path: Path):
    a = _ecrire(tmp_path, "seed0.json", _artefact(longueur=384.0, clipped=1.0, grad=0.0, seed=0))
    b = _ecrire(tmp_path, "seed1.json", _artefact(longueur=384.0, clipped=1.0, grad=0.0, seed=1))
    assert organ.main([str(a), str(b)]) == 1
    c = _ecrire(tmp_path, "seed2.json", _artefact(longueur=100.0, clipped=0.1, grad=1.0, seed=2))
    assert organ.main([str(a), str(c)]) == 0


if __name__ == "__main__":
    raise SystemExit(pytest.main([__file__, "-q"]))
