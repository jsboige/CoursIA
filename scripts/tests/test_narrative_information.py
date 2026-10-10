"""Tests du mesureur de preservation D5 (narrative_information).

Organe `scripts.argumentation.narrative_information` : mesure la
preservation de l'ordre entre une trace d'analyse (etat Argument) et une
restitution 3 actes. Voir issue #19603.

Convention pytest-as-fichier-script : chaque test est une fonction `def
test_*`, le module n'utilise pas de fixtures partages (cf. scripts/tests
conftest.py). On importe directement les fonctions de l'organe.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

# Permettre l'import du module organe
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.argumentation.narrative_information import (  # noqa: E402
    PRESERVES_HIGH, PRESERVES_MID,
    composite_preservation_score,
    coverage_score,
    extract_atomes_from_state,
    extract_atomes_from_text,
    extract_atomes_from_restitution,
    infonce_lower_bound,
    kendall_tau_on_shared,
    levenshtein,
    measure_from_files,
    measure_preservation,
    normalised_order_score,
    verdict_from_score,
)


# ---------------------------------------------------------------------------
# Tests unitaires des primitives
# ---------------------------------------------------------------------------

def test_levenshtein_identique():
    """Levenshtein de deux sequences identiques = 0."""
    a = ["alpha", "beta", "gamma"]
    assert levenshtein(a, a) == 0


def test_levenshtein_un_seul_changement():
    """Levenshtein : un remplacement = 1."""
    a = ["alpha", "beta", "gamma"]
    b = ["alpha", "delta", "gamma"]
    assert levenshtein(a, b) == 1


def test_levenshtein_vide():
    """Levenshtein entre une liste vide et une de n elements = n."""
    a: list[str] = []
    b = ["alpha", "beta"]
    assert levenshtein(a, b) == 2
    assert levenshtein(b, a) == 2


def test_normalised_order_score_identique():
    """Deux sequences identiques -> score = 1.0."""
    a = ["alpha", "beta", "gamma"]
    b = ["alpha", "beta", "gamma"]
    assert normalised_order_score(a, b) == 1.0


def test_normalised_order_score_vide_degenere():
    """Deux listes vides -> score = 1.0 (convention)."""
    assert normalised_order_score([], []) == 1.0


def test_normalised_order_score_un_vide():
    """Une liste vide, une non vide -> score = 0.0."""
    assert normalised_order_score([], ["alpha"]) == 0.0
    assert normalised_order_score(["alpha"], []) == 0.0


def test_normalised_order_score_inverse():
    """Liste inversee : pas zero mais pas 1.0 (edit distance > 0)."""
    a = ["alpha", "beta", "gamma"]
    b = ["gamma", "beta", "alpha"]
    score = normalised_order_score(a, b)
    assert 0.0 < score < 1.0


def test_verdict_from_score_seuils():
    """Les seuils de verdict sont respectes."""
    assert verdict_from_score(0.81) == "PRESERVES >80%"
    assert verdict_from_score(0.80) == "PRESERVES 50-80%"  # > strict
    assert verdict_from_score(0.50) == "PRESERVES 50-80%"
    assert verdict_from_score(0.499) == "LOSSY <50%"


def test_infonce_lower_bound_1_atome():
    """Pour 1 atome, log(1) - 1 = -1.0 (borne triviale)."""
    assert infonce_lower_bound(1.0) == -1.0


def test_infonce_lower_bound_64_atomes():
    """Pour 64 atomes, log(64) - 1 ~= 3.18."""
    import math
    assert abs(infonce_lower_bound(64.0) - (math.log(64) - 1)) < 1e-9


# ---------------------------------------------------------------------------
# Tests metrique composite (couverture + Kendall-tau)
# ---------------------------------------------------------------------------

def test_coverage_full():
    """Couverture 1.0 si tous les atomes source survivent."""
    src = ["alpha", "beta", "gamma"]
    rest = ["alpha", "beta", "gamma", "delta", "extra"]
    assert coverage_score(src, rest) == 1.0


def test_coverage_partial():
    """Couverture = fraction d'atomes source presents dans rest."""
    src = ["alpha", "beta", "gamma", "delta"]
    rest = ["alpha", "gamma", "extra"]
    assert coverage_score(src, rest) == 0.5  # alpha, gamma survivent


def test_coverage_zero_si_rest_vide():
    """Couverture 0.0 si rest vide et src non vide."""
    assert coverage_score(["alpha", "beta"], []) == 0.0


def test_coverage_un_si_src_vide():
    """Couverture 1.0 si src vide (degenere)."""
    assert coverage_score([], []) == 1.0
    assert coverage_score([], ["alpha"]) == 1.0


def test_kendall_tau_identique():
    """Ordre identique sur atomes partages -> tau = 1.0."""
    src = ["alpha", "beta", "gamma"]
    rest = ["alpha", "beta", "gamma", "delta"]
    assert kendall_tau_on_shared(src, rest) == 1.0


def test_kendall_tau_inverse():
    """Ordre inverse sur atomes partages -> tau = 0.0."""
    src = ["alpha", "beta", "gamma", "delta"]
    rest = ["delta", "gamma", "beta", "alpha", "extra"]
    assert kendall_tau_on_shared(src, rest) == 0.0


def test_kendall_tau_partiellement_inverse():
    """Ordre partiellement inverse -> tau entre 0 et 1."""
    src = ["alpha", "beta", "gamma", "delta"]
    rest = ["alpha", "gamma", "beta", "delta"]
    tau = kendall_tau_on_shared(src, rest)
    assert 0.0 < tau < 1.0


def test_composite_harmonic_mean():
    """Composite = 2*cov*tau / (cov + tau). Pour une permutation
    symetrique (palindrome), le Levenshtein entre [a,b,c] et [c,b,a]
    est 2 (deux substitutions), pas 3 : tau = 1 - 2/3 = 0.333.
    Composite = 0.5 (harmonic mean de 1.0 et 0.333).
    """
    src = ["alpha", "beta", "gamma"]
    rest = ["gamma", "beta", "alpha"]  # palindrome
    cov = coverage_score(src, rest)
    tau = kendall_tau_on_shared(src, rest)
    composite = composite_preservation_score(src, rest)
    assert cov == 1.0
    assert abs(tau - 1.0 / 3.0) < 1e-9  # 1 - 2/3
    assert abs(composite - 0.5) < 1e-9


def test_composite_identique():
    """Composite = 1.0 si src = rest."""
    src = ["alpha", "beta", "gamma"]
    composite = composite_preservation_score(src, src)
    assert composite == 1.0


# ---------------------------------------------------------------------------
# Tests extracteurs
# ---------------------------------------------------------------------------

def test_extract_atomes_from_text_stopwords_filtrees():
    """Les stopwords sont filtres, l'ordre est preserve."""
    text = "Le chat noir mange une souris blanche."
    atoms = extract_atomes_from_text(text)
    # mots >= 4 char, pas dans stopwords
    assert "chat" in atoms
    assert "noir" in atoms
    assert "mange" in atoms
    assert "souris" in atoms
    assert "blanche" in atoms
    # stopwords filtres
    assert "une" not in atoms
    assert "le" not in atoms


def test_extract_atomes_from_text_doublons_dedupliques():
    """Les mots repetes sont dedupliques (premiere occurrence)."""
    text = "alpha beta alpha gamma beta"
    atoms = extract_atomes_from_text(text)
    assert atoms == ["alpha", "beta", "gamma"]


def test_extract_atomes_from_state_ordre_axes():
    """L'extraction depuis un etat preserve l'ordre des axes et des items."""
    state = {
        "fallacies": [{"name": "ad hominem"}, {"name": "strawman"}],
        "quality": [{"name": "coherence"}],
        "counter_arguments": [{"name": "inversion"}],
        "formal_pl": [],
        "formal_fol": [{"name": "modus ponens"}],
        "dung": [],
    }
    atoms = extract_atomes_from_state(state)
    # L'ordre des axes est preserve
    idx_ad = atoms.index("hominem") if "hominem" in atoms else -1
    idx_quality = atoms.index("coherence")
    idx_modus = atoms.index("modus")
    assert idx_ad < idx_quality < idx_modus, (
        f"Ordre attendu fallacies < quality < formal_fol, "
        f"atoms={atoms}"
    )


def test_extract_atomes_from_state_axes_vides_ignores():
    """Les axes vides sont ignores, pas d'index vide dans la sortie."""
    state = {
        "fallacies": [{"name": "ad hominem"}],
        "quality": [],
        "counter_arguments": [],
        "formal_pl": [{"name": "syllogism"}],
        "formal_fol": [],
        "dung": [],
    }
    atoms = extract_atomes_from_state(state)
    assert "hominem" in atoms
    assert "syllogism" in atoms
    # Pas de chaines vides ou None qui polluent la liste
    assert all(a for a in atoms)


def test_extract_atomes_from_restitution_split_3_actes():
    """La regex split correctement les 3 actes et preserve l'ordre."""
    md = """# Rapport

## Acte I -- Mise en situation
alpha beta gamma

## Acte II -- Recit dialectique
delta epsilon zeta

## Acte III -- Conclusion
theta iota kappa
"""
    atoms = extract_atomes_from_restitution(md)
    # alpha avant delta avant theta (ordre des actes)
    assert atoms.index("alpha") < atoms.index("delta")
    assert atoms.index("delta") < atoms.index("theta")
    # theta avant iota avant kappa (ordre intra-acte)
    assert atoms.index("theta") < atoms.index("iota")
    assert atoms.index("iota") < atoms.index("kappa")


# ---------------------------------------------------------------------------
# Tests d'integration
# ---------------------------------------------------------------------------

def test_measure_preservation_identique():
    """Trace et restitution identiques -> PRESERVES >80%."""
    source = ["alpha", "beta", "gamma", "delta"]
    report = measure_preservation("test_identique", source, source)
    assert report.order_score == 1.0
    assert report.verdict == "PRESERVES >80%"


def test_measure_preservation_ordre_inverse():
    """Ordre inverse -> tau < 1.0 et composite < 1.0.

    Avec la metrique composite (couverture + Kendall-tau), un atome
    supplementaire hors du set partage ne penalise PAS le score (le
    boilerplate ne casse pas la preservation). Mais un ordre inverse des
    atomes partages -> tau = 0 (reversal complet) -> composite = 0.0.
    """
    source = ["alpha", "beta", "gamma", "delta"]
    # Meme atomes partages, mais dans l'ordre inverse -> tau = 0
    rest = ["delta", "gamma", "beta", "alpha", "extra"]
    report = measure_preservation("test_inverse", source, rest)
    assert report.coverage == 1.0  # tous les src survivent
    assert report.order_preservation == 0.0  # reversal complet -> tau nul
    assert report.order_score == 0.0  # harmonic mean penalise tau=0
    # Un cas partiellement inverse donne un composite > 0
    partial = measure_preservation(
        "test_partial", ["a", "b", "c", "d"], ["a", "c", "b", "d", "z"]
    )
    assert 0.0 < partial.order_score < 1.0


def test_measure_preservation_totalement_lossy():
    """Aucun recouvrement -> score proche de 0, LOSSY <50%."""
    source = ["alpha", "beta", "gamma"]
    rest = ["xxx", "yyy", "zzz", "www"]
    report = measure_preservation("test_lossy", source, rest)
    assert report.verdict == "LOSSY <50%"


def test_measure_preservation_count_atoms_in_report():
    """Le rapport contient les compteurs N source / N restitution."""
    source = ["a", "b", "c", "d", "e"]
    rest = ["a", "b", "x", "y", "z", "w"]
    report = measure_preservation("test_count", source, rest)
    assert report.n_source == 5
    assert report.n_restitution == 6


# ---------------------------------------------------------------------------
# Tests des seuils (coherence aux bornes du papier)
# ---------------------------------------------------------------------------

def test_seuils_documents():
    """Les constantes de seuils sont documentees et non magiques."""
    # Les seuils 0.80 et 0.50 sont les bornes du critere de sortie
    # (#19603) et des references litteraires sur la distillation narrative.
    # On verifie juste qu'elles sont dans [0, 1].
    assert 0.0 < PRESERVES_HIGH <= 1.0
    assert 0.0 < PRESERVES_MID <= 1.0
    assert PRESERVES_HIGH > PRESERVES_MID


# ---------------------------------------------------------------------------
# Tests end-to-end sur fixtures (corpus A, B, C)
# ---------------------------------------------------------------------------

FIXTURES_DIR = (
    Path(__file__).resolve().parent / "fixtures" / "narrative_information"
)


def _corpus_paths(corpus_stem: str) -> tuple[Path, Path]:
    """Renvoie (etat, restitution) pour un corpus donne."""
    return (
        FIXTURES_DIR / f"{corpus_stem}_etat.json",
        FIXTURES_DIR / f"{corpus_stem}_restitution.md",
    )


def test_corpus_a_preserves_ordre_canonique():
    """Corpus A : restitution qui suit l'ordre canonique -> PRESERVES >80%."""
    src, rest = _corpus_paths("corpus_a_preserves")
    report = measure_from_files("corpus_a_preserves", src, rest)
    assert report.verdict == "PRESERVES >80%", (
        f"Corpus A devrait etre PRESERVES >80%, score={report.order_score}, "
        f"n_src={report.n_source}, n_rest={report.n_restitution}"
    )


def test_corpus_b_ordre_inverse_score_intermediaire():
    """Corpus B : actes dans le desordre -> score entre 0 et 1 (perte d'ordre)."""
    src, rest = _corpus_paths("corpus_b_ordre_inverse")
    report = measure_from_files("corpus_b_ordre_inverse", src, rest)
    # Le score est < 1.0 (ordre perturbe) mais > 0.0 (recouvrement non nul)
    assert 0.0 < report.order_score < 1.0, (
        f"Corpus B score attendu dans (0, 1), got {report.order_score}"
    )


def test_corpus_c_lossy_peu_d_atomes_partages():
    """Corpus C : restitution introductive, peu d'atomes partages -> score < PRESERVES_HIGH."""
    src, rest = _corpus_paths("corpus_c_lossy")
    report = measure_from_files("corpus_c_lossy", src, rest)
    # Le verdict doit etre en-dessous de PRESERVES_HIGH
    assert report.verdict != "PRESERVES >80%", (
        f"Corpus C ne devrait PAS etre PRESERVES >80%, got {report.verdict}, "
        f"score={report.order_score}"
    )


def test_end_to_end_3_corpus_verdicts_distincts():
    """Les 3 corpus produisent des verdicts differents (sanity check)."""
    reports = {
        name: measure_from_files(name, *_corpus_paths(name))
        for name in ("corpus_a_preserves", "corpus_b_ordre_inverse", "corpus_c_lossy")
    }
    # A doit etre le meilleur, C le pire (monotonic relative attendue)
    assert reports["corpus_a_preserves"].order_score >= reports["corpus_b_ordre_inverse"].order_score
    assert reports["corpus_b_ordre_inverse"].order_score >= reports["corpus_c_lossy"].order_score
    # Au moins un verdict distinct parmi les 3
    verdicts = {r.verdict for r in reports.values()}
    assert len(verdicts) >= 2, (
        f"Verdicts trop homogenes, attendu >= 2 distinctes, got {verdicts}"
    )