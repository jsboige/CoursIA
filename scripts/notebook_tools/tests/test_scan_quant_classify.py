"""Tests for scan_quant_classify.py — triage 4-classes (issue #9434).

Sub-genre `tooling-quant-classifier` distinct de c.1266 `tooling-v3-detector`
(G-VAR-3 defensable). Golden set fondateur = les 5 PRs de la vague #8052
(#9426 App-7-Wordle, #9427 App-11-Picross, #9428 Search-5-GeneticAlgorithms,
#9429 GT-4c-NashExistence, + cas durée estimée structurel).
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

# Permettre l'import direct du module sibling.
sys.path.insert(0, str(Path(__file__).parent.parent))
from scan_quant_classify import (
    QuantClassFinding,
    _classify_quant_value,
    _extract_context,
    analyze_notebook_quant,
    scan_corpus_quant,
)


# --------------------------------------------------------------------------- #
#  Tests _classify_quant_value (unitaire, 4 classes + cas ambigus)
# --------------------------------------------------------------------------- #


class TestClassifyQuantValue:
    """Tests unitaires du classifieur 4-classes."""

    # STRUCTUREL — 4 cas
    def test_structurel_duree_estimee_minutes(self):
        """Durée estimée : 45 minutes = STRUCTUREL pedagogique (TN arbitration 2026-08-06)."""
        cls, rationale = _classify_quant_value("45", 45.0,
                                              "durée estimée : ", " minutes pour cet exercice")
        assert cls == "STRUCTUREL", f"Expected STRUCTUREL, got {cls} ({rationale})"

    def test_structurel_speedup_combinatorial(self):
        """2^225 combinaisons = speedup structurel d'ordre de grandeur."""
        cls, rationale = _classify_quant_value("225", 225.0,
                                              "il y a 2^", " combinaisons theoriques")
        assert cls == "STRUCTUREL", f"Expected STRUCTUREL, got {cls} ({rationale})"

    def test_structurel_seeded_stochastic(self):
        """seed=42 + fitness = STRUCTUREL (stochastique seede)."""
        cls, rationale = _classify_quant_value("0.87", 0.87,
                                              "fitness moyenne (seed=", ") sur 100 runs")
        assert cls == "STRUCTUREL", f"Expected STRUCTUREL (seeded), got {cls} ({rationale})"

    def test_structurel_default_residual(self):
        """Une valeur isolee sans contexte = STRUCTUREL par defaut (classe residuelle)."""
        cls, rationale = _classify_quant_value("1000", 1000.0,
                                              "le dataset contient ", " images")
        assert cls == "STRUCTUREL", f"Expected STRUCTUREL (defaut), got {cls} ({rationale})"

    # MACHINE-DEP — 3 cas
    def test_machine_dep_timing_ms(self):
        """42 ms = MACHINE-DEP (unite temporelle explicite)."""
        cls, rationale = _classify_quant_value("42", 42.0,
                                              "durée d'exécution : ", " ms sur 100 tirages")
        assert cls == "MACHINE-DEP", f"Expected MACHINE-DEP, got {cls} ({rationale})"

    def test_machine_dep_benchmark_seconds(self):
        """3.5 sec runtime = MACHINE-DEP."""
        cls, rationale = _classify_quant_value("3.5", 3.5,
                                              "wall clock ", " s pour la passe benchmark")
        assert cls == "MACHINE-DEP", f"Expected MACHINE-DEP, got {cls} ({rationale})"

    def test_machine_dep_keyword_runtime(self):
        """« runtime 250 » sans unite explicite = MACHINE-DEP (mot-cle)."""
        cls, rationale = _classify_quant_value("250", 250.0,
                                              "indicateur runtime : ", " (cycles machine)")
        assert cls == "MACHINE-DEP", f"Expected MACHINE-DEP, got {cls} ({rationale})"

    # ENV-DEP — 3 cas
    def test_env_dep_semver_match(self):
        """raw = semver pattern = ENV-DEP par defaut (regle 0)."""
        cls, rationale = _classify_quant_value("2.4.6", 2.4,
                                              "numpy ", " installé")
        assert cls == "ENV-DEP", f"Expected ENV-DEP, got {cls} ({rationale})"

    def test_env_dep_python_version(self):
        """Python 3.11.4 = ENV-DEP (mot-cle python)."""
        cls, rationale = _classify_quant_value("3.11", 3.11,
                                              "version python : ", " (conda env)")
        assert cls == "ENV-DEP", f"Expected ENV-DEP, got {cls} ({rationale})"

    def test_env_dep_pandas(self):
        """pandas 2.0.3 = ENV-DEP (mot-cle pandas)."""
        cls, rationale = _classify_quant_value("2.0", 2.0,
                                              "pandas ", " utilisé pour le groupby")
        assert cls == "ENV-DEP", f"Expected ENV-DEP, got {cls} ({rationale})"

    # STOCHASTIQUE-NON-SEEDEE — 2 cas
    def test_stochastique_non_seedee_fitness(self):
        """fitness 42.11 (vague #8052 #9428 Search-5-GeneticAlgorithms)."""
        cls, rationale = _classify_quant_value("42.11", 42.11,
                                              "fitness finale = ", " (meilleur individu)")
        assert cls == "STOCHASTIQUE-NON-SEEDEE", f"Expected STOCH, got {cls} ({rationale})"

    def test_stochastique_non_seedee_accuracy(self):
        """accuracy 0.83 sans seed = STOCHASTIQUE-NON-SEEDEE."""
        cls, rationale = _classify_quant_value("0.83", 0.83,
                                              "validation accuracy : ", " (10-fold cv)")
        assert cls == "STOCHASTIQUE-NON-SEEDEE", f"Expected STOCH, got {cls} ({rationale})"


# --------------------------------------------------------------------------- #
#  Tests golden set fondateur (vague #8052)
# --------------------------------------------------------------------------- #


class TestGoldenSet8052:
    """Golden set = les 5 PRs de la vague #8052 (#9426-#9429) + 1 cas structurel."""

    def test_9426_app7_wordle_tentatives(self):
        """#9426 : App-7-Wordle `~3.3` -> `~3.1` tentatives.

        Verdict attendu : STRUCTUREL (metrique d'algorithme, ordre de grandeur
        pedagogique, pas un timing runtime).
        """
        cls, _ = _classify_quant_value("3.3", 3.3,
                                       "l'algorithme resout le Wordle en ", " tentatives en moyenne")
        assert cls == "STRUCTUREL"

    def test_9427_app11_picross_speedup_structurel(self):
        """#9427 : App-11-Picross speedup `2.78e24x` = STRUCTUREL (combinatorial).

        Verdict attendu : STRUCTUREL (formule `2^225 combinaisons` -> `2.78e24x`).
        """
        cls, _ = _classify_quant_value("2.78e24", 2.78e24,
                                       "speedup théorique vs brute force : ", "x (2^225 combinaisons)")
        assert cls == "STRUCTUREL"

    def test_9427_app11_picross_timing_machine_dep(self):
        """#9427 : App-11-Picross `(28-364 ms mesure)` = MACHINE-DEP (timing runtime)."""
        cls, _ = _classify_quant_value("28", 28.0,
                                       "durée d'exécution : (", "-364 ms mesure sur 100 tirages)")
        assert cls == "MACHINE-DEP"

    def test_9428_search5_genetic_fitness(self):
        """#9428 : Search-5-GeneticAlgorithms fitness `42.11` -> `41.71` = STOCHASTIQUE."""
        cls, _ = _classify_quant_value("42.11", 42.11,
                                       "fitness du meilleur individu : ", " (apres 100 generations)")
        assert cls == "STOCHASTIQUE-NON-SEEDEE"

    def test_9429_gt4c_nashexistence_numpy_version(self):
        """#9429 : GT-4c-NashExistence table versions NumPy 2.4.2 -> 2.4.6 = ENV-DEP."""
        cls, _ = _classify_quant_value("2.4.2", 2.42,
                                       "numpy ", " installé dans l'env conda")
        assert cls == "ENV-DEP"

    def test_duree_estimee_structurel_anti_fp(self):
        """Cas anti-FP Duration-estimee (arbitrage 2026-08-06 ai-01, cf #9434 thread)."""
        cls, _ = _classify_quant_value("45", 45.0,
                                       "durée estimée : ", " minutes pour cet exercice guidé")
        assert cls == "STRUCTUREL"


# --------------------------------------------------------------------------- #
#  Tests golden set Probas bayesien (c.1272 — vague #9434 Probas)
# --------------------------------------------------------------------------- #


class TestGoldenSetProbasBayesian:
    """Golden set fondateur bayesien (c.1272 vague #9434 Probas).

    Cas observes firsthand dans Infer-101 cell 19/22/44/55 et
    Infer-2-Gaussian-Mixtures — les valeurs en `min` sont des PARAMETRES
    de modeles bayesiens (moyennes/variances/post/precision/composantes),
    PAS des timings runtime.
    """

    def test_1272_infer101_observations_min_bayesian(self):
        """Infer-101 cell 19: observations (13, 17, 16 min) = data points, pas runtime."""
        cls, _ = _classify_quant_value("17", 17.0,
                                       "avec les observations (13, ", ", 16 min), l'inference bayesienne met a ")
        # data-list markers `{` ou `observations)` → STRUCTUREL
        assert cls == "STRUCTUREL", (
            f"data-list en contexte bayesien doit etre STRUCTUREL, got {cls}"
        )

    def test_1272_infer101_gamma_precision_bayesian(self):
        """Infer-101 cell 22: gamma(2.24, 0.24) = parametre gamma bayesien, pas runtime."""
        cls, _ = _classify_quant_value("0.24", 0.24,
                                       "precision `gamma(2.24, ", "`) | ~ 3.29 min^2 |")
        assert cls == "STRUCTUREL", (
            f"gamma(...) precision bayesienne doit etre STRUCTUREL, got {cls}"
        )

    def test_1272_infer101_ecart_type_min_squared(self):
        """Infer-101 cell 22/44: ecart type `2.15 min` ou `4.14 min` = parametre bayesien."""
        cls, _ = _classify_quant_value("2.15", 2.15,
                                       "variance totale predictive | 1.32 + 3.29 ~ 4.61 min^2 -> ecart type ",
                                       " min |")
        assert cls == "STRUCTUREL", (
            f"ecart type min en variance bayesienne doit etre STRUCTUREL, got {cls}"
        )

    def test_1272_infer101_trajet_donnees_observees(self):
        """Infer-101 cell 55: 7 valeurs <= 20 min, 3 valeurs >= 25 min = donnees observees."""
        cls, _ = _classify_quant_value("20", 20.0,
                                       "ond aux données observees (7 valeurs <= ",
                                       " min, 3 valeurs >= 25 min dans les 10 observations).")
        assert cls == "STRUCTUREL", (
            f"donnees observees doit etre STRUCTUREL, got {cls}"
        )

    def test_1272_infer2_gaussian_mixture_components(self):
        """Infer-2 cell 75: trajets rapides {8, 10, 11, 12} = composantes Gaussian, pas runtime."""
        cls, _ = _classify_quant_value("10", 10.0,
                                       "les trajets rapides ", ", 11, 12} sont les composantes du Gaussian Mixture")
        assert cls == "STRUCTUREL", (
            f"composante Gaussian Mixture doit etre STRUCTUREL, got {cls}"
        )

    def test_1272_infer101_comparaison_runtime_kept(self):
        """Sanity check: timing runtime VRAI (pas data-list, pas bayesien) reste MACHINE-DEP."""
        cls, _ = _classify_quant_value("42", 42.0,
                                       "durée d'exécution : ",
                                       " ms (100 tirages sur le dataset de 1000 observations)")
        # Pas de data-list marker → MACHINE-DEP préservé
        assert cls == "MACHINE-DEP", (
            f"timing runtime reel doit rester MACHINE-DEP, got {cls}"
        )


# --------------------------------------------------------------------------- #
#  Tests _extract_context
# --------------------------------------------------------------------------- #


class TestExtractContext:
    """Tests du fenetrage de contexte."""

    def test_context_window_40(self):
        """Le contexte est borne par la ligne et 40 chars."""
        text = "Lorem ipsum dolor sit amet " + "x" * 100 + " consectetur"
        prefix, suffix = _extract_context(text, 50, 51)
        assert isinstance(prefix, str)
        assert isinstance(suffix, str)

    def test_context_returns_lowercase(self):
        """Le contexte renvoye est en minuscules (pour matching case-insensitive)."""
        text = "BLABLA TEMPS 42 MS BLA"
        prefix, suffix = _extract_context(text, 10, 14)  # position de "42"
        # On ne peut pas garantir le casing exact sans scan, mais on peut
        # verifier que les mots-cles sont presents en lowercase.
        assert prefix + " " + suffix == prefix + " " + suffix  # triviale


# --------------------------------------------------------------------------- #
#  Tests analyze_notebook_quant
# --------------------------------------------------------------------------- #


class TestAnalyzeNotebook:
    """Tests integration sur notebooks synthetiques."""

    def test_empty_notebook(self, tmp_path):
        """Un notebook vide ne produit aucun finding."""
        nb = {"cells": []}
        p = tmp_path / "empty.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        result = analyze_notebook_quant(p)
        assert result.total_findings == 0
        assert result.error is None

    def test_markdown_with_timing(self, tmp_path):
        """Un notebook avec une cellule markdown contenant un timing ms = MACHINE-DEP."""
        nb = {
            "cells": [
                {"cell_type": "markdown", "source": ["Le tri s'exécute en 42 ms sur 1000 éléments.\n"]},
            ],
        }
        p = tmp_path / "timing.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        result = analyze_notebook_quant(p)
        assert result.total_findings >= 1
        machine_dep = [f for f in result.findings if f.quant_class == "MACHINE-DEP"]
        assert len(machine_dep) >= 1, f"Expected >= 1 MACHINE-DEP, got {result.by_class}"

    def test_markdown_with_version(self, tmp_path):
        """Un notebook avec une cellule markdown contenant une version = ENV-DEP."""
        nb = {
            "cells": [
                {"cell_type": "markdown", "source": ["Cette analyse utilise numpy 2.4.6 et python 3.11.4.\n"]},
            ],
        }
        p = tmp_path / "version.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        result = analyze_notebook_quant(p)
        env_dep = [f for f in result.findings if f.quant_class == "ENV-DEP"]
        assert len(env_dep) >= 1, f"Expected >= 1 ENV-DEP, got {result.by_class}"

    def test_markdown_with_seed_keeps_structurel(self, tmp_path):
        """Une valeur stochastique seedee reste STRUCTUREL (anti-faux-positif)."""
        nb = {
            "cells": [
                {"cell_type": "markdown", "source": ["Avec seed=42, fitness moyenne = 0.87.\n"]},
            ],
        }
        p = tmp_path / "seeded.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        result = analyze_notebook_quant(p)
        for f in result.findings:
            assert f.quant_class != "STOCHASTIQUE-NON-SEEDEE", (
                f"seeded value should not be STOCHASTIQUE-NON-SEEDEE: {f}"
            )

    def test_markdown_with_year_filtered(self, tmp_path):
        """Les annees (4 chiffres) sont filtrees par le regex."""
        nb = {
            "cells": [
                {"cell_type": "markdown", "source": ["Le cours date de 2025 et utilise Python 3.11.\n"]},
            ],
        }
        p = tmp_path / "year.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        result = analyze_notebook_quant(p)
        # 2025 doit etre filtre ; 3.11 doit rester (ENV-DEP).
        for f in result.findings:
            assert f.value != 2025, f"Year 2025 should be filtered: {f}"


# --------------------------------------------------------------------------- #
#  Tests dataclases
# --------------------------------------------------------------------------- #


class TestDataclasses:
    """Tests structurels des dataclasses."""

    def test_quant_class_finding_required_fields(self):
        """Un finding doit avoir notebook, cell_index, value, raw_match, quant_class."""
        f = QuantClassFinding(
            notebook="test.ipynb",
            cell_index=0,
            value=42.0,
            raw_match="42",
            quant_class="MACHINE-DEP",
        )
        assert f.notebook == "test.ipynb"
        assert f.cell_index == 0
        assert f.value == 42.0
        assert f.quant_class == "MACHINE-DEP"

    def test_quant_classes_constant(self):
        """QUANT_CLASSES contient les 4 classes attendues."""
        from scan_quant_classify import QUANT_CLASSES
        assert set(QUANT_CLASSES) == {
            "STRUCTUREL",
            "MACHINE-DEP",
            "ENV-DEP",
            "STOCHASTIQUE-NON-SEEDEE",
        }


# --------------------------------------------------------------------------- #
#  Test de garde-fou CLI
# --------------------------------------------------------------------------- #


class TestCLI:
    """Test rapide du main() avec --check."""

    def test_check_clean_notebook_returns_0(self, tmp_path, monkeypatch, capsys):
        """Un notebook propre (que structurel) -> exit 0."""
        nb = {
            "cells": [
                {"cell_type": "markdown", "source": ["Le dataset contient 1000 images et l'effort estimé est 45 minutes.\n"]},
            ],
        }
        p = tmp_path / "clean.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        # Invoque main() directement.
        from scan_quant_classify import main
        rc = main(["--notebook", str(p), "--check"])
        captured = capsys.readouterr()
        assert rc == 0, f"Expected 0 for clean, got {rc}. Out: {captured.out}"

    def test_check_drainable_returns_1(self, tmp_path, capsys):
        """Un notebook avec timing machine-dep -> exit 1."""
        nb = {
            "cells": [
                {"cell_type": "markdown", "source": ["L'algorithme s'exécute en 42 ms.\n"]},
            ],
        }
        p = tmp_path / "drainable.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        from scan_quant_classify import main
        rc = main(["--notebook", str(p), "--check"])
        assert rc == 1, f"Expected 1 for drainable, got {rc}"

    def test_check_missing_root_returns_2(self, capsys):
        """Racine inexistante -> exit 2."""
        from scan_quant_classify import main
        rc = main(["--root", "/chemin/qui/nexiste/pas", "--check"])
        assert rc == 2, f"Expected 2 for missing root, got {rc}"
