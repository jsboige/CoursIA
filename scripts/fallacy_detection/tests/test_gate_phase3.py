#!/usr/bin/env python3
"""Tests du verdict du gate de Phase 3 (gate_phase3, #20233).

Les verdicts de comparaison (BEATS / BEATS_MAJORITY_ONLY / NO_BEATS) sont
epingles avec leurs marges -- points ET ecarts-types de la reference lexicale :
un BEATS a +0.05 sigma et un BEATS a +3 sigma ne disent pas la meme chose, et
le verdict doit les distinguer sans juger a leur place.

Les refus sont le coeur du gate : chaque non-comparabilite (niveau, corpus,
plis, mesure absente) doit rendre un motif QUI NOMME la valeur fautive, jamais
un chiffre qui aurait l'air d'un resultat.

Enfin, la reference REELLE du depot est chargee : le controle positif passe la
baseline lexicale elle-meme comme candidat (elle egale sa propre reference,
donc ne la bat pas : BEATS_MAJORITY_ONLY), et les trois valeurs de reference
(0.0034 / 0.2198 / sigma 0.042) sont epinglees -- une regeneration silencieuse
de baselines_branch.json fait tomber ces tests, pas seulement changer un
chiffre dans un rapport.

stdlib + pytest. Aucun acces reseau, aucun corpus requis : la reference reelle
est le seul fichier du depot lu.
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import gate_phase3 as gp  # noqa: E402

REPO_REFERENCE = (Path(__file__).resolve().parents[3]
                  / "MyIA.AI.Notebooks/GenAI/FallacyDetection/data/teacher"
                  / "baselines_branch.json")


def synthetic_reference(**overrides) -> dict:
    """Reference au contrat minimal du gate, valeurs proches des vraies."""
    base = {
        "corpus": {"path": "data/teacher/val_fr.jsonl",
                   "sha256": "a" * 64},
        "level": "branch",
        "seed": 42,
        "folds": 5,
        "node_level": {"measurable": False, "labels": 280, "support_max": 1},
        "baselines": {
            "majority_grouped": {"macro_f1_mean": 0.0034, "macro_f1_std": 0.0028},
            "lexical_centroid_grouped": {"macro_f1_mean": 0.2198,
                                         "macro_f1_std": 0.042},
        },
    }
    base.update(overrides)
    return base


def candidate_report(macro: float | None = 0.30, key: str = "ft", **overrides) -> dict:
    """Rapport candidat au contrat des organes existants (ft_floor/zeroshot_floor)."""
    base = {
        "corpus": {"path": "data/teacher/val_fr.jsonl", "sha256": "a" * 64,
                   "rows": 280},
        "model": "Qwen/Qwen3-0.6B",
        "model_revision": "c1899de2",
        "level": "branch",
        "seed": 42,
        "folds": 5,
        key: {"folds": [{"fold": 0, "macro_f1": macro}],
              "labels_total": 14,
              "macro_f1_mean": macro,
              "macro_f1_std": 0.05},
    }
    base.update(overrides)
    return base


def test_beats_franc_porte_ses_marges():
    verdict = gp.gate(synthetic_reference(), candidate_report(0.30))
    assert verdict["verdict"] == "BEATS"
    margins = verdict["margins"]
    assert margins["vs_lexical_points"] == pytest.approx(0.0802, abs=1e-6)
    assert margins["vs_majority_points"] == pytest.approx(0.2966, abs=1e-6)
    # (0.30 - 0.2198) / 0.042 = 1.91 sigma : la marge est publiee en ecarts-types
    assert margins["margin_vs_lexical_sigma"] == pytest.approx(1.91, abs=0.01)


def test_beats_fragile_est_encore_beats_mais_le_dit():
    verdict = gp.gate(synthetic_reference(), candidate_report(0.221))
    assert verdict["verdict"] == "BEATS"
    assert verdict["margins"]["margin_vs_lexical_sigma"] < 0.05


def test_egalite_stricte_avec_la_lexicale_nest_pas_un_beats():
    verdict = gp.gate(synthetic_reference(), candidate_report(0.2198))
    assert verdict["verdict"] == "BEATS_MAJORITY_ONLY"


def test_sous_la_lexicale_au_dessus_du_majoritaire():
    verdict = gp.gate(synthetic_reference(), candidate_report(0.10))
    assert verdict["verdict"] == "BEATS_MAJORITY_ONLY"


def test_sous_le_majoritaire():
    verdict = gp.gate(synthetic_reference(), candidate_report(0.001))
    assert verdict["verdict"] == "NO_BEATS"
    assert verdict["margins"]["vs_majority_points"] < 0


def test_ft_est_lu_avant_zero_shot():
    report = candidate_report(0.30, key="ft")
    report["zero_shot"] = {"macro_f1_mean": 0.01, "macro_f1_std": 0.0,
                           "folds": [], "labels_total": 14}
    assert gp.gate(synthetic_reference(), report)["candidate"]["source"] == "ft"


def test_zero_shot_seul_est_lu():
    # Cas reel de la brique 2 : 0.0145 est au-dessus du plancher majoritaire
    # (0.0034) mais sous la lexicale (0.2198) -- le verdict honnete est
    # BEATS_MAJORITY_ONLY, pas NO_BEATS.
    verdict = gp.gate(synthetic_reference(),
                      candidate_report(0.0145, key="zero_shot"))
    assert verdict["candidate"]["source"] == "zero_shot"
    assert verdict["verdict"] == "BEATS_MAJORITY_ONLY"
    assert verdict["margins"]["vs_lexical_points"] < 0


# --- Refus : chaque motif nomme la valeur fautive, jamais un chiffre avenant ---

def test_refus_niveau_node_nomme_le_niveau():
    verdict = gp.gate(synthetic_reference(),
                      candidate_report(0.40, level="node"))
    assert verdict["verdict"] == "REFUSED_LEVEL"
    assert "'node'" in verdict["refusal_reason"]
    assert verdict["margins"] is None


def test_refus_corpus_nomme_les_empreintes():
    report = candidate_report(0.40)
    report["corpus"] = {"path": "autre.jsonl", "sha256": "b" * 64, "rows": 14000}
    verdict = gp.gate(synthetic_reference(), report)
    assert verdict["verdict"] == "REFUSED_CORPUS"
    assert "bbbbbbbbbbbb" in verdict["refusal_reason"]
    assert "aaaaaaaaaaaa" in verdict["refusal_reason"]


def test_refus_graine_diffrente_nomme_les_plis():
    verdict = gp.gate(synthetic_reference(), candidate_report(0.40, seed=7))
    assert verdict["verdict"] == "REFUSED_FOLDS"
    assert "graine protocolaire" in verdict["refusal_reason"]


def test_refus_nombre_de_plis_diffrent():
    verdict = gp.gate(synthetic_reference(), candidate_report(0.40, folds=10))
    assert verdict["verdict"] == "REFUSED_FOLDS"
    assert "plis" in verdict["refusal_reason"]


def test_refus_rapport_sans_mesure():
    report = {"level": "branch", "corpus": {"sha256": "a" * 64},
              "seed": 42, "folds": 5, "model": "x"}
    verdict = gp.gate(synthetic_reference(), report)
    assert verdict["verdict"] == "REFUSED_NO_MEASURE"
    assert "ft" in verdict["refusal_reason"]


def test_refus_mesure_none():
    verdict = gp.gate(synthetic_reference(), candidate_report(None))
    assert verdict["verdict"] == "REFUSED_NO_MEASURE"
    assert "aucun pli" in verdict["refusal_reason"]


# --- Controle positif sur la reference reelle du depot ---

def test_reference_reelle_lexicale_comme_candidat():
    """La lexicale egale sa propre reference : elle ne la bat pas (stricte)."""
    reference = gp.load_reference(REPO_REFERENCE)
    report = candidate_report(
        reference["baselines"]["lexical_centroid_grouped"]["macro_f1_mean"])
    report["corpus"]["sha256"] = reference["corpus"]["sha256"]
    verdict = gp.gate(reference, report)
    assert verdict["verdict"] == "BEATS_MAJORITY_ONLY"
    assert verdict["margins"]["vs_lexical_points"] == pytest.approx(0.0, abs=1e-9)


def test_reference_reelle_valeurs_epinglees():
    """Une regeneration silencieuse de la reference fait tomber ce test."""
    reference = gp.load_reference(REPO_REFERENCE)
    assert reference["baselines"]["majority_grouped"]["macro_f1_mean"] == 0.0034
    assert reference["baselines"]["lexical_centroid_grouped"]["macro_f1_mean"] == 0.2198
    assert reference["baselines"]["lexical_centroid_grouped"]["macro_f1_std"] == 0.042
    assert reference["node_level"]["measurable"] is False


def test_reference_reelle_niveau_node_refuse():
    reference = gp.load_reference(REPO_REFERENCE)
    report = candidate_report(0.40, level="node")
    report["corpus"]["sha256"] = reference["corpus"]["sha256"]
    verdict = gp.gate(reference, report)
    assert verdict["verdict"] == "REFUSED_LEVEL"


def test_reference_incomplete_leve_gateinputerror(tmp_path):
    path = tmp_path / "ref.json"
    path.write_text(json.dumps({"level": "branch"}), encoding="utf-8")
    with pytest.raises(gp.GateInputError, match="champs absents"):
        gp.load_reference(path)


def test_reference_vierge_lexicale_nulle_est_rejetee(tmp_path):
    reference = synthetic_reference()
    reference["baselines"]["lexical_centroid_grouped"]["macro_f1_std"] = 0
    path = tmp_path / "ref.json"
    path.write_text(json.dumps(reference), encoding="utf-8")
    with pytest.raises(gp.GateInputError, match="ecart-type lexical nul"):
        gp.load_reference(path)


def test_main_rend_rc0_et_le_verdict_en_json(tmp_path, capsys):
    report_path = tmp_path / "ft_report.json"
    report_path.write_text(json.dumps(candidate_report(0.30)), encoding="utf-8")
    ref_path = tmp_path / "ref.json"
    ref_path.write_text(json.dumps(synthetic_reference()), encoding="utf-8")
    rc = gp.main(["--report", str(report_path), "--reference", str(ref_path),
                  "--json"])
    assert rc == 0
    out = capsys.readouterr().out
    # --json rend le verdict en JSON (objet complet en tete), puis la ligne en clair
    assert out.startswith("{")
    assert '"verdict": "BEATS"' in out
    assert "BEATS :" in out


def test_main_rapport_absent_rc2(tmp_path, capsys):
    ref_path = tmp_path / "ref.json"
    ref_path.write_text(json.dumps(synthetic_reference()), encoding="utf-8")
    rc = gp.main(["--report", str(tmp_path / "absent.json"),
                  "--reference", str(ref_path)])
    assert rc == 2
    assert "rapport illisible" in capsys.readouterr().err
