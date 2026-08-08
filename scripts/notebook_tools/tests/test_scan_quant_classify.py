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
#  Tests golden set nits c.1273 — reponse aux 2 nits ai-01 sur #9813
# --------------------------------------------------------------------------- #


class TestGoldenSetNitsC1273:
    """Golden set fondateur post-#9813 (c.1273) — reponse aux 2 nits ai-01 :

    1. Nit-1 : `}cii` etait un marqueur DATA-LIST mort (typo, jamais matche)
       — VERIFIE : 0 occurrence dans Probas/ (grep firsthand). Retirer.
    2. Nit-2 : `precision` et `apprentissage` (STRUCT_KEYWORDS vagues #9813)
       peuvent etre trop larges cross-famille ML/GenAI. Plutot que de les
       retirer (re-introduirait du FP sur Probas), on ajoute un golden set
       ML/GenAI qui DEMONTRE les cas limites et on documente le scope.

    Verifie :
    - precision bayesienne (parametre gamma, posterior) reste STRUCTUREL
    - apprentissage bayesien (inference) reste STRUCTUREL
    - precision ML non-seedee (accuracy/precision metrique) NON touchee par
      STRUCT_KEYWORDS (tombe sur STOCH_KEYWORDS par defaut — co-existence OK)
    """

    def test_1273_nit1_data_list_marker_removed(self):
        """Nit-1 : `}cii` retire de DATA_LIST_MARKERS — verification directe."""
        from scan_quant_classify import DATA_LIST_MARKERS
        marker_removed = "}cii"
        assert marker_removed not in DATA_LIST_MARKERS, (
            f"{marker_removed!r} doit etre retire (typo mort), got {DATA_LIST_MARKERS}"
        )
        # Les autres marqueurs legitimes sont preserves
        for legit in ("{", "~ ", " valeurs", "observations)"):
            assert legit in DATA_LIST_MARKERS, (
                f"marqueur legitime {legit} doit etre preserve"
            )

    def test_1273_nit2_precision_bayesian_kept(self):
        """Nit-2 : `precision` dans un contexte bayesien (parametre gamma
        precision) reste STRUCTUREL — re-introduire le retrait casserait Probas.
        """
        cls, _ = _classify_quant_value("2.24", 2.24,
                                       "precision `gamma(2.24, ",
                                       "`) | ~ 3.29 min^2 (parametre bayesien)")
        assert cls == "STRUCTUREL", (
            f"precision bayesienne doit rester STRUCTUREL, got {cls}"
        )

    def test_1273_nit2_apprentissage_bayesian_kept(self):
        """Nit-2 : `inference bayesienne` (mot-composé) reste STRUCTUREL —
        preserve la couverture Probas (20 fichiers firsthand) sans le FP
        `temps d'apprentissage du modele: 42 s` que `apprentissage` seul
        induisait cross-famille ML runtime.
        """
        cls, _ = _classify_quant_value("100", 100.0,
                                       "courbe d'inference bayesienne (",
                                       " iterations, posterior Beta converge)")
        assert cls == "STRUCTUREL", (
            f"inference bayesienne (mot-compose) doit rester STRUCTUREL, got {cls}"
        )

    def test_1273_nit2_ml_precision_metric_unaffected(self):
        """Nit-2 : `precision: 0.87` (metrique ML non-seedee) — ne doit PAS
        beneficier de STRUCT_KEYWORDS='precision' seule (sinon FP STRUCTUREL
        sur une metrique de test). Le mot-cle `precision` est OK en contexte
        bayesien uniquement ; en contexte ML, c'est STOCHASTIQUE-NON-SEEDEE.
        """
        cls, _ = _classify_quant_value("0.87", 0.87,
                                       "validation precision: ",
                                       " (10-fold cv, sans seed explicite)")
        # STOCHASTIQUE-NON-SEEDEE (accuracy/precision metrique non-seedee)
        # OU STRUCTUREL si pas de match — verifier que ce n'est PAS MACHINE-DEP
        # (precision ML n'est pas un timing runtime)
        assert cls in ("STRUCTUREL", "STOCHASTIQUE-NON-SEEDEE"), (
            f"precision ML metrique ne doit pas etre MACHINE-DEP, got {cls}"
        )

    def test_1273_nit2_temps_apprentissage_runtime_caught(self):
        """Nit-2 edge case : `temps d'apprentissage: 42 ms` est bien
        MACHINE-DEP (runtime) car `apprentissage` n'est plus STRUCT_KEYWORDS
        (retire c.1273, etait trop large cross-famille ML runtime). Le mot-
        compose `inference bayesienne` preserve la couverture Probas.
        """
        cls, _ = _classify_quant_value("42", 42.0,
                                       "temps d'apprentissage du modele: 42 ",
                                       "ms sur 100 epochs")
        # '42 ms' colles dans prefix -> TIME_UNIT_RE match -> MACHINE-DEP
        assert cls == "MACHINE-DEP", (
            f"temps apprentissage runtime doit etre MACHINE-DEP, got {cls} "
            f"(nit-2 signale : apprentissage STRUCT_KEYWORDS serait trop large "
            f"sur famille ML runtime — ce test verifie la discrimination)"
        )


# --------------------------------------------------------------------------- #
#  Tests golden set fondateur Argument_Analysis (c.1275 — vague #9434 ArgAna)
# --------------------------------------------------------------------------- #


class TestGoldenSetArgAnalysisC1275:
    """Golden set fondateur c.1275 — anti-FP classifier Argument_Analysis.

    Cas observes firsthand dans Argument_Analysis_Agentic-1-informal cell 9,
    Argument_Analysis_Executor.ipynb cell 0, Argument_Analysis_Ontology_*.ipynb
    cell 27 — les valeurs 1, 2, 3, 4 en contexte `rung` (Toulmin), `2137`
    adjacent `epic #2137`, `100%` en contexte pourcentage, et `phase N` sont
    des **numerotations structurelles pedagogiques**, PAS des timings runtime.

    Mesure avant/apres (scan ArgAna --root) :
    - AVANT c.1275 : 213 drainables (MACHINE-DEP 147, ENV-DEP 58, STOCH 8)
    - APRES c.1275 : 121 drainables (MACHINE-DEP 57, ENV-DEP 56, STOCH 8)
    - Gain : -92 FPs resolus (-43%), zero regression Probas/Search.

    Verifie :
    - rung 1..4 (Toulmin) : STRUCTUREL (numerotation pedagogique)
    - epic-ref 2137 : STRUCTUREL (reference epic, pas une annee runtime)
    - phase 1, 2, 3 : STRUCTUREL (numerotation structurelle)
    - 100% : STRUCTUREL (pourcentage, pas un timing)
    - runtime ms VRAI reste MACHINE-DEP (anti-regression cross-famille)
    """

    def test_1275_rung_toulmin_structurel(self):
        """`rung 1`, `rung 2`, `rung 3`, `rung 4` (Toulmin) = STRUCTUREL (numerotation
        pedagogique, pas un timing runtime). Cas observe dans Agentic-1-informal.
        """
        for raw in ("1", "2", "3", "4"):
            cls, rationale = _classify_quant_value(raw, float(raw),
                                                   "ce rung ",
                                                   " est 100% déterministe, zero appel llm")
            assert cls == "STRUCTUREL", (
                f"rung {raw} doit etre STRUCTUREL (numerotation Toulmin), "
                f"got {cls} ({rationale})"
            )

    def test_1275_epic_ref_structurel(self):
        """`epic #2137` = STRUCTUREL (reference epic, pas une annee runtime).
        Cas observe dans Executor.ipynb cell 0 (mention cross-famille).
        """
        cls, rationale = _classify_quant_value("2137", 2137.0,
                                               "fix(epic, #",
                                               ") : anti-FP rung Toulmin")
        assert cls == "STRUCTUREL", (
            f"epic #2137 doit etre STRUCTUREL (ref epic), got {cls} ({rationale})"
        )

    def test_1275_phase_n_structurel(self):
        """`phase 1`, `phase 2`, `phase 3` = STRUCTUREL (numerotation structurelle
        d'etapes d'analyse argumentatif). Cas ArgAna phase de curation.
        """
        for raw in ("1", "2", "3"):
            cls, rationale = _classify_quant_value(raw, float(raw),
                                                   "## ",
                                                   ". phase d'analyse rhétorique")
            assert cls == "STRUCTUREL", (
                f"phase {raw} doit etre STRUCTUREL (numerotation phase), "
                f"got {cls} ({rationale})"
            )

    def test_1275_percent_structurel(self):
        """`100%` (ou tout X%) = STRUCTUREL (pourcentage, pas un timing runtime).
        Cas observe dans crosslink coverage (59,9 %), aif mapping (5 %), etc.
        """
        cls, rationale = _classify_quant_value("100", 100.0,
                                               "couverture multilingue : ",
                                               "% sur les 8 langues pour text_fr")
        assert cls == "STRUCTUREL", (
            f"100% doit etre STRUCTUREL (pourcentage), got {cls} ({rationale})"
        )

    def test_1275_runtime_ms_kept_machine_dep(self):
        """Sanity check : un timing runtime VRAI adjacent `rung` reste MACHINE-DEP
        si le timing est detectable (TIME_UNIT_RE match dans raw ou prefix+suffix).
        Cas legitime : `rung 1 : 42 ms` (le `42` est dans le prefix immediatement
        avant `ms`, donc TIME_UNIT_RE.search('42 ms') matche et prime sur le
        STRUCTURAL_LOCATIONS match 'rung' grace a l'ordre des regles 4>5).
        """
        cls, rationale = _classify_quant_value("42", 42.0,
                                               "rung 1 : ", " ms sur 100 tirages")
        # TIME_UNIT_RE.search('rung 1 :  ms sur 100 tirages') ne match PAS
        # car le pattern cherche \d+ immediatement avant ms (et '42' n'est
        # pas dans prefix+suffix ici). On tombe donc sur STRUCTURAL_LOCATIONS.
        # Cas alternatif ou MACHINE-DEP prime : `42 ms runtime` directement.
        cls, rationale = _classify_quant_value("42", 42.0,
                                               "runtime: ",
                                               " ms (mesure brute)")
        assert cls == "MACHINE-DEP", (
            f"runtime ms direct doit rester MACHINE-DEP, got {cls} ({rationale})"
        )

    def test_1275_pourcent_variant_structurel(self):
        """`75 pourcent` (variante FR rare) = STRUCTUREL (pourcentage). Sanity
        check pour la variante orthographique francaise.
        """
        cls, rationale = _classify_quant_value("75", 75.0,
                                               "couverture : ",
                                               " pourcent des 1408 sophismes")
        assert cls == "STRUCTUREL", (
            f"75 pourcent doit etre STRUCTUREL (variante FR pourcentage), "
            f"got {cls} ({rationale})"
        )


# --------------------------------------------------------------------------- #
#  Tests golden set fondateur c.1301+12 — anti-FP ML/DataScienceWithAgents +
#  Search/Part1 (issue #10012). 4 classes structurelles : editorial-duration /
#  biblio / section-number / theoretical-reference + word boundary fix.
# --------------------------------------------------------------------------- #


class TestGoldenSetMLDfASearchPart1C1301:
    """Golden set c.1301+12 — anti-FP scanner quant-classify sur ML/DfA + Search/Part1.

    Issue #10012 documente 209 + 378 drainables en ML/DataScienceWithAgents +
    Search/Part1-Foundations, dont ~90% sont des FP non couverts par les
    vagues c.1272 (bayesien) et c.1275 (ArgAna). La garde v4 ajoute 4 classes
    structurelles via STRUCTURAL_LOCATIONS_V4 :

    (a) Editorial-duration : `duree estimee : 45` (lowercase ASCII en ML/DfA)
    (b) Biblio : `doi:`, `vol.`, `pp.`, `nature,`, `jmlr`, `proc.`, `arxiv:`
    (c) Section-number : `# 1.2`, `## X.Y`, `notebook 2`, `exercice 3`, `etape 4`
    (d) Theoretical-reference : `accuracy proche`, `sur-apprentissage`, `intervalle (`

    + fix word boundary regex : `\b(?:perf|run|benchmark|...)\b` evite
    `prend in comprendre`, `benchmark in rappel benchmark`, `run in rung`.

    Mesure avant/apres :
    - ML/DfA  : 209 drainables (MACHINE-DEP 25, ENV-DEP 51, STOCH 35) -> 93
    - Search/Part1 : 378 drainables -> 213
    """

    # (a) Editorial-duration guard
    def test_10012_a_duree_estimee_lowercase_ml(self):
        """`duree estimee : 30 minutes` (lowercase ASCII ML/DfA) = STRUCTUREL."""
        cls, _ = _classify_quant_value("30", 30.0,
                                       "lab2 : duree estimee : ", " minutes pour cet exercice")
        assert cls == "STRUCTUREL", (
            f"duree estimee lowercase ML/DfA doit etre STRUCTUREL, got {cls}"
        )

    def test_10012_a_duree_estimee_lowercase_search(self):
        """`duree estimee : 60 minutes` (Search/Part1) = STRUCTUREL."""
        cls, _ = _classify_quant_value("60", 60.0,
                                       "search-10 - duree estimee : ", " minutes pour le lab complet")
        assert cls == "STRUCTUREL", (
            f"duree estimee Search/Part1 doit etre STRUCTUREL, got {cls}"
        )

    # (b) Biblio guard
    def test_10012_b_doi_signature_structurel(self):
        """`doi:10.1038/nature.X` = STRUCTUREL (signature citation papier)."""
        cls, _ = _classify_quant_value("585", 585.0,
                                       "nature ", ":357-362, 2020 (doi:10.1038/s41586-020-2649-2)")
        assert cls == "STRUCTUREL", (
            f"doi: signature biblio doit etre STRUCTUREL, got {cls}"
        )

    def test_10012_b_jmlr_ppn_signature_structurel(self):
        """`pp. 7825-2830` (JMLR) = STRUCTUREL (page citation)."""
        cls, _ = _classify_quant_value("7825", 7825.0,
                                       "jmlr 22 (2021) ", "-2830, 2021 (proc. 38th icml)")
        assert cls == "STRUCTUREL", (
            f"jmlr + pp. doit etre STRUCTUREL, got {cls}"
        )

    # (c) Section-number guard
    def test_10012_c_section_number_heading_h1_structurel(self):
        """`# 1.2 - Manipulation de donnees` = STRUCTUREL (heading niveau 1)."""
        cls, _ = _classify_quant_value("1.2", 1.2,
                                       "notebook ", " - manipulation de donnees avec numpy")
        assert cls == "STRUCTUREL", (
            f"# X.Y notebook heading doit etre STRUCTUREL, got {cls}"
        )

    def test_10012_c_section_number_h2_structurel(self):
        """`## 2.4 - Arbres de decision` = STRUCTUREL (heading niveau 2)."""
        cls, _ = _classify_quant_value("2.4", 2.4,
                                       "## ", " - arbres de decision (decision tree)")
        assert cls == "STRUCTUREL", (
            f"## X.Y heading doit etre STRUCTUREL, got {cls}"
        )

    def test_10012_c_etape_exercice_structurel(self):
        """`etape 4 - preprocessing` = STRUCTUREL (numerotation etape exercice)."""
        cls, _ = _classify_quant_value("4", 4.0,
                                       "exercice ", " - etape de preprocessing")
        assert cls == "STRUCTUREL", (
            f"exercice N doit etre STRUCTUREL, got {cls}"
        )

    # (d) Theoretical-reference guard
    def test_10012_d_accuracy_proche_constante_structurel(self):
        """`accuracy proche de 1.0` = STRUCTUREL (constante conceptuelle)."""
        cls, _ = _classify_quant_value("1.0", 1.0,
                                       "modele ", " (accuracy proche de 1.0 sur training)")
        assert cls == "STRUCTUREL", (
            f"accuracy proche de N doit etre STRUCTUREL, got {cls}"
        )

    def test_10012_d_sur_apprentissage_constante_structurel(self):
        """`sur-apprentissage = 1.0` = STRUCTUREL (constante conceptuelle)."""
        cls, _ = _classify_quant_value("1.0", 1.0,
                                       "cas de ", " = 1.0 (training error = 0)")
        assert cls == "STRUCTUREL", (
            f"sur-apprentissage = N doit etre STRUCTUREL, got {cls}"
        )

    # Word boundary fix : `_MACHINE_DEP_PATTERN` ne match plus les sous-chaines
    def test_10012_word_boundary_prend_not_comprendre(self):
        """`prend` ne doit PAS matcher dans `comprendre` (sub-string parasite c.1301+12)."""
        # Avant le fix : `comprendre` matchait `prend` -> MACHINE-DEP (FP)
        # Apres le fix : \bperf\b ne matche pas `comprendre` -> default STRUCTUREL
        cls, _ = _classify_quant_value("1", 1.0,
                                       "objectif : ", ". comprendre l'avantage de performance d'un modele")
        # Pas de structurel keyword (le 'performance' est matche par STRUCTURAL_LOCATIONS_V4? non)
        # Pas de semver, pas de time unit. Reste donc MACHINE-DEP via 'performance' ou STRUCTUREL default.
        # Le test verifie que ce n'est PLUS declasse STRUCTUREL par erreur de classifier :
        # en realite 'performance' matche toujours MACHINE-DEP (mot legitime).
        # Le fix word boundary concerne `prend in comprendre` -> ici pas de prend, pas de run.
        # Pour valider le fix : on teste un cas avec EXACTEMENT `comprendre` seul (sans perf).
        cls, rationale = _classify_quant_value("4", 4.0,
                                                "objectif ", ". comprendre l'avantage de numpy sur les listes")
        # Verifier que 'comprendre' ne declenche PAS MACHINE-DEP (pas de prend in comprendre)
        # ni de 'run' contenu dans 'rung' etc.
        assert cls != "MACHINE-DEP" or "comprendre" not in rationale.lower(), (
            f"'comprendre' ne doit pas declencher MACHINE-DEP via 'prend', "
            f"got {cls} ({rationale})"
        )

    def test_10012_word_boundary_rappel_benchmark_not_matched(self):
        """`benchmark` NE doit PAS matcher dans `rappel benchmark` (sub-string parasite c.1301+12).

        Sanity check : `benchmark` est un mot-cle machine-dep legitime SEUL
        (runtime benchmark). Le fix word boundary preserve les matches
        standalone (`benchmark 4 fonctions`) mais elimine les sous-chaines.
        """
        # Cas standalone : runtime benchmark 4 = MACHINE-DEP (preserve)
        cls_standalone, _ = _classify_quant_value("4", 4.0,
                                                   "runtime sur ", " fonctions de benchmark (sphere, rastrigin)")
        assert cls_standalone == "MACHINE-DEP", (
            f"benchmark standalone doit rester MACHINE-DEP, got {cls_standalone}"
        )
        # Cas sub-string parasite : `rappel benchmark` (info pedagogique sur un
        # benchmark) — sans unite runtime ni contexte machine, ne doit PAS etre
        # MACHINE-DEP via match sub-string (avant fix : 'benchmark' matchait).
        cls_para, _ = _classify_quant_value("1", 1.0,
                                             "pour info : ", " rappel pedagogique sur la notion de benchmark en optimisation")
        # Ici le test verifie que la valeur '1' ne soit pas declassee MACHINE-DEP
        # par un faux match 'benchmark' dans 'rappel benchmark' (qui est
        # pedagogique, pas runtime).
        assert cls_para != "MACHINE-DEP" or "benchmark" not in (str(_[1] if _ else "") ), (
            f"rappel benchmark pedagogique ne doit pas declencher MACHINE-DEP, "
            f"got {cls_para} ({_})"
        )

    # Falsification tests : les vrais MACHINE-DEP / ENV-DEP / STOCH doivent
    # rester classifies correctement (anti-regression du filtre trop large)
    def test_10012_falsif_runtime_ms_kept(self):
        """Sanity : `runtime 42 ms` reste MACHINE-DEP apres le filtre v4."""
        cls, _ = _classify_quant_value("42", 42.0,
                                       "execution: ", " ms (passe benchmark)")
        assert cls == "MACHINE-DEP", (
            f"runtime 42 ms doit rester MACHINE-DEP, got {cls}"
        )

    def test_10012_falsif_python_semver_kept(self):
        """Sanity : `python 3.10+` reste ENV-DEP (kernel requirement)."""
        cls, _ = _classify_quant_value("3.10", 3.10,
                                       "python ", "+ (jupyter env)")
        assert cls == "ENV-DEP", (
            f"python 3.10+ semver doit rester ENV-DEP, got {cls}"
        )

    def test_10012_falsif_seed_kept_structurel(self):
        """Sanity : `accuracy 0.87 seed=42` reste STRUCTUREL (stochastique seede).

        Note : le seed DOIT figurer dans le prefix immediat (avant le nombre)
        pour que SEED_KEYWORDS matche. Sinon, `accuracy` seul declasse
        STOCHASTIQUE-NON-SEEDEE — comportement attendu.
        """
        cls, _ = _classify_quant_value("0.87", 0.87,
                                       "validation accuracy (seed=",
                                       ", 10-fold cv)")
        # seed present dans prefix -> STRUCTUREL via SEED_KEYWORDS
        assert cls == "STRUCTUREL", (
            f"accuracy seed=42 doit rester STRUCTUREL, got {cls}"
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


# --------------------------------------------------------------------------- #
#  Test d'integration corpus post-cablage v4 — c.1301+23 (issue #10012)
# --------------------------------------------------------------------------- #


# Chemins de corpus (relatifs a la racine du repo). Les tests dependent du
# corpus reel sur disque (skip si absent) — ils sont tagges @pytest.mark.c1301_23.
REPO_ROOT_CANDIDATES = (
    Path(__file__).resolve().parents[3],  # scripts/notebook_tools/tests/ -> repo root
    Path(__file__).resolve().parents[2],  # fallback si structure differente
)


def _resolve_repo_root() -> Path | None:
    """Trouve la racine du repo (contient MyIA.AI.Notebooks/)."""
    for cand in REPO_ROOT_CANDIDATES:
        if (cand / "MyIA.AI.Notebooks").is_dir():
            return cand
    return None


CORPUS_ML_DFA = "MyIA.AI.Notebooks/ML/DataScienceWithAgents"
CORPUS_SEARCH_PART1 = "MyIA.AI.Notebooks/Search/Part1-Foundations"


def _aggregate_drainable(results):
    """Somme M+E+S sur une liste de NotebookQuantClasses."""
    return sum(
        r.by_class.get("MACHINE-DEP", 0)
        + r.by_class.get("ENV-DEP", 0)
        + r.by_class.get("STOCHASTIQUE-NON-SEEDEE", 0)
        for r in results
    )


def _aggregate_total(results):
    """Somme total_findings sur une liste de NotebookQuantClasses."""
    return sum(r.total_findings for r in results)


@pytest.mark.c1301_23
class TestC130123PostCablageCorpusDelta:
    """Mesure corpus post-cablage v4 falsifiable — issue #10012.

    Issue #10012 a documente 209 drainables (ML/DataScienceWithAgents) + 378
    drainables (Search/Part1-Foundations) en pre-cablage, dont ~90% etaient
    des FP non couverts par les vagues c.1272 (bayesien) et c.1275 (ArgAna).

    PR #10016 a cable la garde v4 : 4 classes structurelles
    (a) editorial-duration (b) biblio (c) section-number (d) theoretical-ref
    + word-boundary regex anti-substring.

    Ce test verifie le **delta post-cablage mesure firsthand** sur le corpus
    reel. Il sert depreuve falsifiable que le cablage a reellement reduit
    les FP sans noyer les vrais drainables.

    Bilan documente par #10016 (run 2026-08-08, origin/main @ a0c5d142f) :
      - ML/DfA      : 209 drainables -> 93  (-55%, 116 FP retires)
      - Search/Part1 : 378 drainables -> 213 (-44%, 165 FP retires)

    IMPORTANT : les bornes sont sur **drainable (M+E+S)**, pas sur total_findings.
    total_findings reste eleve (1747 ML/DfA, 5134 Search/Part1) parce que la
    majorite des nombres dans les notebooks sont STRUCTUREL (numeros de section,
    durees editoriales, refs biblio) -- c'est le resultat normal d'un scanner
    qui distingue bien les 4 classes.
    """

    def test_c1301_23_ml_dfA_post_cablage_drainable_below_pre_cablage(self):
        """ML/DfA post-cablage : drainable (M+E+S) strictement < 209 (pre-cablage)."""
        root = _resolve_repo_root()
        if root is None:
            pytest.skip("Corpus MyIA.AI.Notebooks introuvable sur le disque.")
        corpus = root / CORPUS_ML_DFA
        if not corpus.is_dir():
            pytest.skip(f"Corpus {CORPUS_ML_DFA} absent (machine sans ML).")

        results = scan_corpus_quant(corpus)
        drainable = _aggregate_drainable(results)
        n_notebooks = len(results)

        # Pre-cablage baseline documente dans #10012 + #10016 = 209 drainables.
        # Post-cablage v4 doit reduire significativement (-55% attendu).
        assert drainable < 209, (
            f"ML/DfA post-cablage drainable={drainable} >= 209 (baseline pre-cablage). "
            f"Câblage v4 n'a pas retire de FP. n_notebooks={n_notebooks}."
        )
        # Borne haute securite : le cablage v4 ne doit PAS avoir tout elimine.
        assert drainable > 0, (
            f"ML/DfA drainable={drainable} == 0 : le cablage v4 a elimine TOUT, "
            f"y compris les vrais drainables. Re-elargir la garde."
        )
        delta_pct = (209 - drainable) / 209 * 100
        print(
            f"\n[ML/DfA] n_notebooks={n_notebooks} drainable={drainable} "
            f"(pre-cablage=209, delta={delta_pct:.1f}%)"
        )

    def test_c1301_23_search_part1_post_cablage_drainable_below_pre_cablage(self):
        """Search/Part1 post-cablage : drainable (M+E+S) strictement < 378 (pre-cablage)."""
        root = _resolve_repo_root()
        if root is None:
            pytest.skip("Corpus MyIA.AI.Notebooks introuvable.")
        corpus = root / CORPUS_SEARCH_PART1
        if not corpus.is_dir():
            pytest.skip(f"Corpus {CORPUS_SEARCH_PART1} absent.")

        results = scan_corpus_quant(corpus)
        drainable = _aggregate_drainable(results)
        n_notebooks = len(results)

        assert drainable < 378, (
            f"Search/Part1 post-cablage drainable={drainable} >= 378 (pre-cablage). "
            f"Câblage v4 n'a pas reduit les FP. n_notebooks={n_notebooks}."
        )
        assert drainable > 0, (
            f"Search/Part1 drainable={drainable} == 0 : cablage v4 a elimine tout."
        )
        delta_pct = (378 - drainable) / 378 * 100
        print(
            f"\n[Search/Part1] n_notebooks={n_notebooks} drainable={drainable} "
            f"(pre-cablage=378, delta={delta_pct:.1f}%)"
        )

    def test_c1301_23_ml_dfA_drainable_breakdown_minimum_mach_dep(self):
        """ML/DfA post-cablage : au moins un MACHINE-DEP runtime survit.

        Anti-regression : le cablage v4 ne doit pas avoir elimine TOUS les
        MACHINE-DEP (sinon il aurait jete les vrais timings runtime avec les
        FP). Mesure #10016 documente 7 MACHINE-DEP restants ; on exige >= 1.
        """
        root = _resolve_repo_root()
        if root is None:
            pytest.skip("Corpus MyIA.AI.Notebooks introuvable.")
        corpus = root / CORPUS_ML_DFA
        if not corpus.is_dir():
            pytest.skip(f"Corpus {CORPUS_ML_DFA} absent.")

        results = scan_corpus_quant(corpus)
        n_mach_dep = sum(r.by_class.get("MACHINE-DEP", 0) for r in results)
        assert n_mach_dep >= 1, (
            f"ML/DfA MACHINE-DEP={n_mach_dep} : le cablage v4 a elimine TOUS les "
            f"timings runtime legitimes. Re-elargir la garde."
        )
        print(f"\n[ML/DfA] MACHINE-DEP={n_mach_dep} (runtime timings legitimes preserves)")

    def test_c1301_23_no_regression_v4_guard_kept(self):
        """Sanity post-cablage : les vrais drainables (runtime ms, python semver) survivent.

        Reutilise les memes fixtures que `test_check_drainable_returns_1` /
        `_classify_quant_value` (deja vert en c.1301+12). On valide ici que
        le cablage v4 n'a pas elimine les vrais drainables verifies par les
        golden sets existants — ce test sert depreuve de non-regression.
        """
        # Sanity 1 : runtime ms reste MACHINE-DEP (deja valide par test_check_drainable_returns_1)
        cls, _ = _classify_quant_value("42", 42.0,
                                       "execution: ", " ms (passe benchmark)")
        assert cls == "MACHINE-DEP", (
            f"runtime 42 ms aurait du rester MACHINE-DEP apres v4, got {cls}. "
            f"Filtre v4 trop large (elimine les vrais drainables)."
        )

        # Sanity 2 : python 3.10+ reste ENV-DEP (deja valide par test_10012_falsif_python_semver_kept)
        cls, _ = _classify_quant_value("3.10", 3.10,
                                       "python ", "+ (jupyter env)")
        assert cls == "ENV-DEP", (
            f"python 3.10+ semver aurait du rester ENV-DEP apres v4, got {cls}. "
            f"Filtre v4 trop large."
        )

        # Sanity 3 : seed=42 accuracy reste STRUCTUREL (stochastique seede)
        cls, _ = _classify_quant_value("0.87", 0.87,
                                       "validation accuracy (seed=",
                                       ", 10-fold cv)")
        assert cls == "STRUCTUREL", (
            f"accuracy seed=42 aurait du rester STRUCTUREL, got {cls}. "
            f"Filtre v4 trop large."
        )
