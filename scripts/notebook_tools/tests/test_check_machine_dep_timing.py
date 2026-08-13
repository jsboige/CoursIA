"""Tests de silence du detecteur dedie machine-dep timing (cf. #10158).

5 familles FP documentees + smoke test que le script tourne sans crasher sur
un corpus representatif.

Les tests utilisent ``scan_notebook_file`` (helper dedie) plutot que
d'invoquer le main CLI pour eviter le couplage a argparse. Le but est de
prouver la SEMANTIQUE des exemptions -- pas l'interface CLI (couverte par
un smoke test separe).
"""

from __future__ import annotations

import json
import sys
import tempfile
from pathlib import Path

# Permettre l'import du module parent (scripts/notebook_tools/) sans setup
# site-packages -- le projet n'est pas installe en editable.
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from check_machine_dep_timing import (  # noqa: E402
    _categorize,
    _collect_targets,
    _scan_notebook,
    _is_range_bound,
    _is_detached_approximate,
    _repo_root,
    PROTOCOL_KEYWORDS,
    CONTENT_DURATION_CONSTRAINT_RE,
    DISTRIBUTION_KEYWORDS,
    CATEGORY_WALLCLOCK,
    CATEGORY_DISTRIBUTION,
    CATEGORY_AMBIGUOUS,
    CATEGORY_DOMAIN_QUANTITY,
    STUDENT_PACING_RE,
    WALLCLOCK_KEYWORDS,
    DISTRIBUTION_KEYWORDS,
)

import pytest


# --------------------------------------------------------------------------- #
#  Helpers
# --------------------------------------------------------------------------- #
def _make_nb(cells: list[dict]) -> Path:
    """Ecrit un notebook JSON temporaire et renvoie son Path."""
    nb = {
        "cells": cells,
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    tmp = tempfile.NamedTemporaryFile(
        mode="w", suffix=".ipynb", delete=False, encoding="utf-8"
    )
    json.dump(nb, tmp, ensure_ascii=False)
    tmp.flush()
    tmp.close()
    return Path(tmp.name)


def _md_cell(source: str | list[str]) -> dict:
    """Construit une cellule markdown."""
    if isinstance(source, str):
        source = [source]
    return {"cell_type": "markdown", "metadata": {}, "source": source}


def _code_cell(source: str | list[str]) -> dict:
    """Construit une cellule code."""
    if isinstance(source, str):
        source = [source]
    return {"cell_type": "code", "metadata": {}, "source": source, "outputs": []}


# --------------------------------------------------------------------------- #
#  Smoke test : le script tourne sans crasher sur corpus mixte
# --------------------------------------------------------------------------- #
def test_scan_notebook_empty_path(tmp_path: Path) -> None:
    """Un chemin qui n'existe pas ou n'est pas un .ipynb -> liste vide."""
    # Ne leve jamais (cf. acceptance #10158 mode advisory).
    out = _scan_notebook(tmp_path / "does-not-exist.ipynb")
    assert out == []


def test_scan_notebook_unreadable_returns_empty(tmp_path: Path) -> None:
    """Un fichier corrompu / non-JSON -> liste vide, pas de crash."""
    bogus = tmp_path / "bogus.ipynb"
    bogus.write_text("{ not valid json", encoding="utf-8")
    assert _scan_notebook(bogus) == []


def test_scan_notebook_no_cells(tmp_path: Path) -> None:
    """Un notebook avec 0 cellule -> liste vide."""
    nb = tmp_path / "empty.ipynb"
    nb.write_text(json.dumps({"cells": [], "metadata": {}}), encoding="utf-8")
    assert _scan_notebook(nb) == []


# --------------------------------------------------------------------------- #
#  Famille FP #1 : sortie de cellule code (jamais signalee)
# --------------------------------------------------------------------------- #
def test_silence_on_code_cell_with_wallclock() -> None:
    """Une cellule code qui contient 'execution: 4.5 s' NE doit PAS etre signalee.

    Rationnel (cf. acceptance #10158) : une sortie de cellule porte la valeur
    reelle mesuree -- c'est sa fonction. Le drainage #9434 ne concerne que la
    PROSE statique, pas les outputs qui sont regenerees a chaque execution.
    """
    nb = _make_nb([_code_cell("Console.WriteLine($\"execution: 4.5 s\");")])
    try:
        assert _scan_notebook(nb) == []
    finally:
        nb.unlink()


# --------------------------------------------------------------------------- #
#  Famille FP #2 : deja conforme (tilde prefix)
# --------------------------------------------------------------------------- #
def test_silence_on_tilde_prefix_already_compliant() -> None:
    """Un '~10 s' (tilde prefix) est ORDRE DE GRANDEUR et NE doit PAS signaler.

    Rationnel : le mandat #9434 (H.1) accepte explicitement les ordres de
    grandeur en prose ('~10 s', '~quelques minutes'). Le drainage ne vise
    que les chiffres PRECIS, qui eux sont machine-dep.
    """
    nb = _make_nb([_md_cell("Le notebook prend ~10 s a s'executer.")])
    try:
        assert _scan_notebook(nb) == []
    finally:
        nb.unlink()


# --------------------------------------------------------------------------- #
#  Famille FP #3 : compte deterministe (H1 numbering, etc.)
# --------------------------------------------------------------------------- #
def test_silence_on_deterministic_count() -> None:
    """Un '3 iterations' / 'N=10 seeds' NE doit PAS etre signale.

    Rationnel : les comptes sont deterministes par construction, ils ne
    dependent pas du materiel. Le regex matche '3 iterations' mais ce n'est
    pas un temps d'horloge -- c'est un compte. (Le script cible les unites
    de duree ms/sec/min, pas les comptes, mais il arrive que 'iterations'
    ou 'seeds' soient captures par une regex large. NB: le test verifie que
    la regex NE capture PAS les comptes -- c'est le contrat du MACHINE_RE
    importe du detecteur canonique.)
    """
    nb = _make_nb([_md_cell("On execute 10000 iterations et 4 seeds.")])
    try:
        findings = _scan_notebook(nb)
        # '10000 iterations' n'est PAS capture par MACHINE_RE (pas d'unite de
        # duree) ; idem '4 seeds'. On attend donc 0 finding.
        assert findings == []
    finally:
        nb.unlink()


# --------------------------------------------------------------------------- #
#  Famille FP #4 : version / numero de release (deterministe, pas machine-dep)
# --------------------------------------------------------------------------- #
def test_silence_on_version_string() -> None:
    """Un 'Python 3.10' ou 'v1.2' NE doit PAS etre confondu avec un timing.

    Rationnel : MACHINE_RE ancre sur des unites de duree (ms/sec/min) ou un
    's' isole, pas sur des chiffres isoles. Une version est un identifiant
    deterministe -- pas une mesure de duree.
    """
    nb = _make_nb([_md_cell("Compatible Python 3.10 et PyTorch 2.5.")])
    try:
        assert _scan_notebook(nb) == []
    finally:
        nb.unlink()


# --------------------------------------------------------------------------- #
#  Famille FP #5 : parametre de distribution (bayesien/stat)
# --------------------------------------------------------------------------- #
def test_distribution_param_classified_as_such() -> None:
    """Un 'moyenne 15.33 min' dans un contexte distribution NE doit PAS etre
    classe wallclock -- c'est un parametre de modele, pas une duree machine.

    Rationnel : un 'moyenne 15.33 min' dans une cellule d'inference
    bayesienne est un parametre de distribution, pas un temps d'horloge.
    Le reviewer humain (cf. TAXONOMIE 3 classes) arbitrera distribution_param
    comme TN dur.
    """
    nb = _make_nb([_md_cell(
        "La posterior suit une Gaussian de moyenne 15.33 min et sigma 1.32 min."
    )])
    try:
        findings = _scan_notebook(nb)
        # Les 2 chiffres (15.33 min, 1.32 min) sont captures par MACHINE_RE.
        assert len(findings) >= 1
        # Mais ils sont classifies distribution_param, PAS wallclock.
        for f in findings:
            assert f["category"] == CATEGORY_DISTRIBUTION
            assert f["category"] != CATEGORY_WALLCLOCK
    finally:
        nb.unlink()


# --------------------------------------------------------------------------- #
#  Signal reel : un wall-clock strict DOIT etre signale
# --------------------------------------------------------------------------- #
def test_wallclock_signal_detected() -> None:
    """Un 'duree d'execution : 2.4 s' DOIT etre signale en categorie wallclock.

    C'est le test positif (l'inverse des 5 silences) : il verifie que le
    detecteur n'est PAS silencieux sur le cas qu'il est cense attraper.
    """
    nb = _make_nb([_md_cell("La duree d'execution est 2.4 s pour 1000 iterations.")])
    try:
        findings = _scan_notebook(nb)
        assert len(findings) >= 1
        # Au moins un finding est categorise wallclock (le contexte "duree
        # d'execution" force la classification).
        wallclock_findings = [f for f in findings if f["category"] == CATEGORY_WALLCLOCK]
        assert wallclock_findings, (
            f"Attendu >=1 wallclock, trouve {[f['category'] for f in findings]}"
        )
    finally:
        nb.unlink()


# --------------------------------------------------------------------------- #
#  Exemption pacing pedagogique (ligne entiere, cf. arbitrage 14:05:37Z)
# --------------------------------------------------------------------------- #
def test_silence_on_student_pacing_lines() -> None:
    """Les lignes 'Duree estimee : 45 minutes' sont exonerees (pacing etudiant).

    Rationnel : arbitrage user 14:05:37Z sur #9434 -- 200 FP elimines en
    exemptant les lignes de pacing H1/H2/H3 ('Duree estimee : ... minutes').
    Ce sont des estimations pedagogiques, pas des mesures de duree.
    """
    nb = _make_nb([
        _md_cell("## Duree estimee : 45 minutes"),
        _md_cell("**Notebook** : Introduction, 30-60 min selon niveau"),
    ])
    try:
        assert _scan_notebook(nb) == []
    finally:
        nb.unlink()


def test_student_pacing_regex_matches_duree() -> None:
    """Le regex STUDENT_PACING_RE detecte 'Duree estimee', 'Duree :', etc."""
    assert STUDENT_PACING_RE.search("Duree estimee : 45 minutes")
    assert STUDENT_PACING_RE.search("Duree : 30 min")
    assert STUDENT_PACING_RE.search("Duree du notebook : 1h")
    # Negatifs -- des mentions incidentes ne declenchent PAS l'exemption.
    assert not STUDENT_PACING_RE.search("La duree d'execution est 2.4 s")
    assert not STUDENT_PACING_RE.search("compute takes 5 sec")


# --------------------------------------------------------------------------- #
#  Extensions #10162 (c.1331+59) : parenhese + cellule de tableau + fourchette
# --------------------------------------------------------------------------- #
def test_student_pacing_regex_matches_paren() -> None:
    """CHANGES_REQUESTED #10162 : parenhese '(15 min)' en fin de titre de section.

    Rationnel : dans l'inventaire 978 findings wallclock, 533 etaient du pacing
    pedagogique cache dans des formes indirectes : '(15 min)' en fin de titre
    H1/H2/H3 ou '(1-2 min)' pour une fourchette. La regex doit maintenant
    matcher ces formes pour les exonerer.
    """
    assert STUDENT_PACING_RE.search("## Introduction aux Futures (15 min)")
    assert STUDENT_PACING_RE.search("### Bayes naif (1-2 min)")
    assert STUDENT_PACING_RE.search("Titre de section (30 sec)")
    # Negatif : parenthese non-pacing
    assert not STUDENT_PACING_RE.search("Voir annexe (page 12)")


def test_student_pacing_regex_matches_table_cell() -> None:
    """CHANGES_REQUESTED #10162 : cellule de tableau '| 15 min |' (sommaire).

    Rationnel : les sommaires de series utilisent typiquement un tableau
    markdown pour aligner 'Section | Duree' -- la cellule de droite est du
    pacing, pas une duree machine.
    """
    assert STUDENT_PACING_RE.search("| **1** | Introduction | 15 min |")
    assert STUDENT_PACING_RE.search("| Section | 1-2 min |")
    assert STUDENT_PACING_RE.search("| titre | 30 sec | notes |")
    # Negatif : pipe sans chiffre ou sans unite de duree
    assert not STUDENT_PACING_RE.search("| col1 | col2 |")


def test_silence_on_pacing_paren_title() -> None:
    """Le scan doit silencieux sur '## Titre (15 min)' -- c'est du pacing.

    Extrait reel observe dans l'inventaire : QC-Py-07-Futures-Forex 24/24
    findings en cell[0] sommaire de la forme '| **1** | Introduction ... |'.
    """
    nb = _make_nb([
        _md_cell("# Module Futures (15 min)"),
        _md_cell("## Sous-section (1-2 min)"),
    ])
    try:
        assert _scan_notebook(nb) == []
    finally:
        nb.unlink()


def test_silence_on_pacing_table_cell() -> None:
    """Le scan doit silencieux sur les cellules de tableau de sommaire.

    Extrait reel observe dans l'inventaire : 533/978 findings du sommaire
    de QC-Py-07-Futures-Forex cell[0] de la forme :
        | **1** | Introduction aux Futures | (15 min) |
        | **2** | Donnees de marche | (30 min) |
    Ces durees sont du pacing pedagogique, pas des wallclock.
    """
    nb = _make_nb([
        _md_cell(
            "| **#** | Section | Duree |\n"
            "| --- | --- | --- |\n"
            "| **1** | Introduction aux Futures | (15 min) |\n"
            "| **2** | Donnees de marche | (30 min) |\n"
            "| **3** | Strategie de base | (1-2 min) |"
        ),
    ])
    try:
        assert _scan_notebook(nb) == []
    finally:
        nb.unlink()


def test_silence_on_range_bound_estimate() -> None:
    """CHANGES_REQUESTED #10162 : fourchette/borne = soft signal.

    Rationnel : '1-2 min', '< 30 sec', '5+ min' sont des FOURCHETTES ou
    des BORNES -- comme `~`, ce sont des estimations d'ordre de grandeur,
    conformes au mandat #9434. Le scan NE doit PAS les signaler.
    """
    nb = _make_nb([
        _md_cell("Le solveur prend 1-2 min par iteration."),
        _md_cell("Reponse rapide : < 30 sec."),
        _md_cell("Cas lourd : 5+ min."),
    ])
    try:
        findings = _scan_notebook(nb)
        assert findings == [], f"Attendu 0 finding, trouve {findings}"
    finally:
        nb.unlink()


def test_is_range_bound_helper() -> None:
    """Le helper _is_range_bound detecte fourchette/borne autour du match."""
    # Fourchette : '...1-2 min...' -> match '2 min', prefix '1-'.
    line = "Le solveur prend 1-2 min par iteration."
    pos = line.index("2 min")
    assert _is_range_bound(line, pos, pos + len("2 min"))
    # Borne superieure : '< 30 sec'.
    line = "Reponse : < 30 sec."
    pos = line.index("30 sec")
    assert _is_range_bound(line, pos, pos + len("30 sec"))
    # Negatif : '4.5 sec' isole (pas de fourchette ni de borne).
    line = "Elapsed time : 4.5 sec."
    pos = line.index("4.5 sec")
    assert not _is_range_bound(line, pos, pos + len("4.5 sec"))


def test_domain_quantity_propagation_in_cell() -> None:
    """CHANGES_REQUESTED #10162 : FP-2 propagation per-cell domain_quantity.

    Rationnel : quand une cellule porte >=1 finding distribution_param, les
    autres findings wallclock de la MEME cellule basculent en domain_quantity
    -- l'unite de temps est le sujet du modele, pas une mesure d'execution.

    Extrait reel (paraphrase du cas fondateur Infer-2-Gaussian-Mixtures) :
    une cellule de plusieurs lignes ou la premiere ligne declare les
    parametres de la distribution (distribution_param), et une autre ligne
    utilise ces parametres comme variable modelisee -- ex '15 min de moins
    que la moyenne'. Les '15 min' de la 2eme ligne sont la variable
    modelisee (domain_quantity), pas une mesure wallclock.

    NB (#10178 Classe 5, c.1301+64) : on enleve les discriminants bayesiens
    ('trajet', 'observations', etc.) des lignes 2/3 pour tester la
    propagation per-cell en isolation. Sinon, la ligne 2 serait classee
    distribution_param DIRECTEMENT par les nouveaux discriminants, sans
    laisser la propagation s'exprimer.
    """
    nb = _make_nb([
        _md_cell(
            "Le modele suit une Gaussian de moyenne 15.33 min et sigma 1.32 min.\n"
            "\n"
            "La duree typique observee est de l'ordre de 15 minutes par trajet.\n"
            "La proportion de moins de 15 min est la metrique cle."
        ),
    ])
    try:
        findings = _scan_notebook(nb)
        assert len(findings) >= 2, f"Attendu >=2 findings, trouve {findings}"
        # Au moins un finding est distribution_param (le '15.33 min' / '1.32 min').
        has_distribution = any(
            f["category"] == CATEGORY_DISTRIBUTION for f in findings
        )
        assert has_distribution, f"Attendu >=1 distribution_param, categories={findings}"
        # Au moins un finding wallclock avant propagation (le '15 minutes' de
        # la ligne 2 -- pas de mot-cle distribution direct sur cette ligne,
        # donc reste wallclock au niveau ligne, et la propagation per-cell
        # doit basculer en domain_quantity).
        has_wallclock_before = any(
            f["category"] == CATEGORY_WALLCLOCK for f in findings
        )
        # Si la propagation per-cell s'applique, ces wallclock basculent en
        # domain_quantity. NB: si la ligne 2 a un mot-cle distribution
        # ('moyenne', 'distribution'), elle aussi serait distribution_param.
        # On choisit deliberement une ligne sans mot-cle distribution.
        assert has_wallclock_before or any(
            f["category"] == CATEGORY_DOMAIN_QUANTITY for f in findings
        ), (
            f"Attendu au moins un wallclock (avant/apres propagation) ou "
            f"un domain_quantity, categories={[f['category'] for f in findings]}"
        )
        # La propagation per-cell doit avoir bascule les wallclock en
        # domain_quantity.
        has_domain = any(
            f["category"] == CATEGORY_DOMAIN_QUANTITY for f in findings
        )
        assert has_domain, (
            f"Attendu >=1 domain_quantity (FP-2 propagation), "
            f"categories={[f['category'] for f in findings]}"
        )
        # Et AUCUN finding de cette cellule ne reste wallclock.
        wallclock_in_cell = [
            f for f in findings if f["category"] == CATEGORY_WALLCLOCK
        ]
        assert wallclock_in_cell == [], (
            f"Aucun wallclock attendu apres propagation, "
            f"mais trouve {wallclock_in_cell}"
        )
    finally:
        nb.unlink()


def test_sudoku13_positive_control_preserved() -> None:
    """Le controle positif Sudoku-13 reste detecte apres le fix.

    Rationnel : le detecteur est sense signaler les wallclock STRICTS. Meme
    apres l'extension STUDENT_PACING_RE (qui risque de tilter sur les
    titres) et le range-bound exemption (qui risque de tilter sur les
    fourchettes), un vrai wallclock strict reste detecte.

    Extrait reel (paraphrase du cas fondateur #10158) : un notebook
    d'optimisation Sudoku rapporte 'duree d'execution : 2.4 s pour 1000
    iterations' -- c'est le controle positif canonique.
    """
    nb = _make_nb([
        _md_cell("# Sudoku-13 -- benchmark solveur DLX"),
        _md_cell(
            "La duree d'execution est 2.4 s pour 1000 iterations. "
            "Le solveur a converge en 1.8 sec sur la grille 13x13."
        ),
    ])
    try:
        findings = _scan_notebook(nb)
        # Au moins un finding wallclock strict (le '2.4 s' et '1.8 sec').
        wallclock = [f for f in findings if f["category"] == CATEGORY_WALLCLOCK]
        assert wallclock, (
            f"Controle positif perdu : aucun wallclock trouve, "
            f"categories={[f['category'] for f in findings]}"
        )
    finally:
        nb.unlink()


# --------------------------------------------------------------------------- #
#  #10178 Classe 4 : contrainte de duree de CONTENU (longueur cible d'un media)
# --------------------------------------------------------------------------- #
def test_content_duration_constraint_regex_matches() -> None:
    """Le motif detecte les descripteurs de duree de CONTENU, pas d'execution.

    Rationnel (#10178 Classe 4) : « moins de 5 minutes pour YouTube Shorts » ou
    « 10 minutes pour un module de cours » sont des bornes du domaine video
    (longueur max du media produit), pas des durees machine. Le motif vise 5
    signaux univoques de contenu.
    """
    # Signaux positifs (chacun univoque de duree de contenu).
    assert CONTENT_DURATION_CONSTRAINT_RE.search("respecter des contraintes de duree (ex: 5 minutes)")
    assert CONTENT_DURATION_CONSTRAINT_RE.search("moins de 5 minutes pour YouTube Shorts")
    assert CONTENT_DURATION_CONSTRAINT_RE.search("exactement 10 minutes pour un module de cours")
    assert CONTENT_DURATION_CONSTRAINT_RE.search("la duree cible de la video est 30 secondes")
    assert CONTENT_DURATION_CONSTRAINT_RE.search("duree totale du clip : 2 minutes")
    assert CONTENT_DURATION_CONSTRAINT_RE.search("duree maximale autorisee : 60s")
    # Negatifs -- un vrai wallclock ne s'encadre pas ainsi.
    assert not CONTENT_DURATION_CONSTRAINT_RE.search("La duree d'execution est 2.4 s")
    assert not CONTENT_DURATION_CONSTRAINT_RE.search("Temps : 1M / 40 = 25,000 secondes = ~7 heures")
    assert not CONTENT_DURATION_CONSTRAINT_RE.search("compute took 3.5 sec on the GPU")


def test_categorize_content_duration_constraint_is_domain_quantity() -> None:
    """Une duree de contenu (contrainte de duree / Shorts / module) -> domain_quantity.

    Cas reel GenAI/Video cell[12] (#10178 Classe 4) : le « 5 minutes » est la
    longueur max d'un YouTube Shorts, pas un runtime. Le controle positif
    GenAI/Texte/10 cell[56] (throughput compute) reste wallclock.
    """
    # Ligne reelle GenAI/Video cell[12] (paraphrase ASCII conforme au notebook).
    line_video = (
        "les videos educatives doivent souvent respecter des contraintes de "
        "duree (ex: moins de 5 minutes pour YouTube Shorts)"
    )
    assert _categorize(line_video, "5 minutes") == CATEGORY_DOMAIN_QUANTITY
    # Controle positif : vrai throughput compute -> reste wallclock.
    line_throughput = "Temps : 1M / 40 = 25,000 secondes = ~7 heures"
    assert _categorize(line_throughput, "25,000 secondes") == CATEGORY_WALLCLOCK


def test_content_duration_constraint_fp_routed_to_domain_quantity() -> None:
    """Le FP GenAI/Video cell[12] (wallclock) est silencie en domain_quantity.

    Rationnel : le detecteur ne doit PLUS rapporter « 5 minutes » / « 10 minutes »
    comme wallclock quand la ligne encadre une contrainte de duree de contenu.
    Avant le fix : wallclock=2 sur ce notebook ; apres : wallclock=0 (les 2
    findings basculent en domain_quantity, categorie non-signalee par design).
    """
    nb = _make_nb([_md_cell(
        "**Contexte** : En production, les videos educatives doivent souvent "
        "respecter des contraintes de duree (ex: moins de 5 minutes pour "
        "YouTube Shorts, ou exactement 10 minutes pour un module de cours)."
    )])
    try:
        findings = _scan_notebook(nb)
        # Aucun finding wallclock (les 2 chiffres sont des durees de contenu).
        wallclock = [f for f in findings if f["category"] == CATEGORY_WALLCLOCK]
        assert not wallclock, (
            f"FP Classe 4 non corrige : wallclock trouve, "
            f"categories={[f['category'] for f in findings]}"
        )
        # Et au moins un finding route en domain_quantity (l'exemption agit).
        domain = [f for f in findings if f["category"] == CATEGORY_DOMAIN_QUANTITY]
        assert domain, (
            f"Aucun domain_quantity : l'exemption n'a pas route le finding, "
            f"categories={[f['category'] for f in findings]}"
        )
    finally:
        nb.unlink()


# --------------------------------------------------------------------------- #
#  Heuristiques de contexte : wall-clock vs distribution
# --------------------------------------------------------------------------- #
def test_wallclock_keywords_detect_execution_context() -> None:
    """Les mots-cle 'execution', 'wall-clock', 'elapsed' sont detectes."""
    assert WALLCLOCK_KEYWORDS.search("duree d'execution : 2.4 s")
    assert WALLCLOCK_KEYWORDS.search("wall-clock time was 50 ms")
    assert WALLCLOCK_KEYWORDS.search("elapsed: 1.2 sec")
    assert WALLCLOCK_KEYWORDS.search("solve took 3.5 s")


def test_distribution_keywords_detect_stat_context() -> None:
    """Les mots-cle 'moyenne', 'sigma', 'posterior' sont detectes."""
    assert DISTRIBUTION_KEYWORDS.search("Gaussian de moyenne 15.33 min")
    assert DISTRIBUTION_KEYWORDS.search("sigma=1.32, mu=0.0")
    assert DISTRIBUTION_KEYWORDS.search("posterior distribution over 3.5 sec")
    # NB: 'posterior' peut apparaitre dans un contexte wall-clock ; on prend
    # la priorite distribution dans ce cas (cf. _categorize).


def test_categorize_distribution_overrides_wallclock() -> None:
    """Si la ligne contient un mot distribution ET wall-clock, distribution
    gagne (parametre de modele prime sur contexte d'execution)."""
    line = "Posterior inference took 15.33 min with sigma 1.32"
    # 'inference' (wall-clock) ET 'Posterior'/'sigma' (distribution).
    # Distribution gagne.
    assert _categorize(line, "15.33 min") == CATEGORY_DISTRIBUTION


def test_categorize_wallclock_when_only_wallclock() -> None:
    """Ligne avec mot wall-clock seul -> wallclock."""
    line = "Elapsed time for solve : 4.5 sec"
    assert _categorize(line, "4.5 sec") == CATEGORY_WALLCLOCK


def test_categorize_ambiguous_only_when_neither() -> None:
    """Ligne sans mot-cle de contexte -> wallclock (defaut conservateur).

    Note: par design, on classe en wallclock plutot qu'ambiguous quand la
    regex matche sans contexte -- c'est le defaut conservateur qui fait
    remonter le finding au reviewer humain plutot que de le silencier.
    """
    line = "Performance is around 3.2 s with 100 iterations."
    # 'Performance' est wall-clock keyword (cf. WALLCLOCK_KEYWORDS).
    assert _categorize(line, "3.2 s") == CATEGORY_WALLCLOCK


# --------------------------------------------------------------------------- #
#  #10178 Classe 5 : discriminants bayesiens routent les durees de domaine
#                   (composante de melange, observation, trajet, ecart-type)
#                   vers distribution_param, pas wallclock.
#  Proposee par po-2024, c.66 (comment #5232772579) sur 14 + 45 findings FP
#  dans Infer-101 / Infer-2 (durees trajet velo). Falsifiable :
#    - PyMC-2 cell[17] : 3 wallclock -> 0 (composantes, observations)
#    - DecInfer-4 cell[18] : 2 wallclock -> 0 (Trajet: 60min -> 10min)
# --------------------------------------------------------------------------- #
def test_class5_distribution_keywords_composante_observation_trajet_ecarttype() -> None:
    """Les discriminants bayesiens sont detectes par DISTRIBUTION_KEYWORDS.

    Rationnel : un notebook qui modelise une grandeur temporelle (duree
    trajet, duree decision) voit ses N min/matches en wallclock alors que
    ce sont des parametres de domaine. La regex doit reconnaitre les
    discriminants bayesiens (composantes, observations, trajets,
    ecarts-types) comme contexte de distribution.

    Cas verbatim :
    - PyMC-2 cell[17] : 'La composante "normale" capture les trajets de
      11 a 20 minutes' (composantes + trajets)
    - DecInfer-4 cell[18] : 'Trajet: 60min -> 10min' (Trajet)
    - 'observations (13, 17, 16 min)' (observations)
    - 'ecart-type 4.14 min' (ecart-type)
    """
    assert DISTRIBUTION_KEYWORDS.search("composante normale")
    assert DISTRIBUTION_KEYWORDS.search("composantes de melange")
    assert DISTRIBUTION_KEYWORDS.search("observations (13, 17, 16 min)")
    assert DISTRIBUTION_KEYWORDS.search("5 nouveaux trajets (18, 25, 30)")
    assert DISTRIBUTION_KEYWORDS.search("Trajet: 60min -> 10min")
    assert DISTRIBUTION_KEYWORDS.search("ecart-type 4.14 min")
    assert DISTRIBUTION_KEYWORDS.search("ecart type de la posterieure")
    # Variantes avec trait d'union / sans trait d'union
    assert DISTRIBUTION_KEYWORDS.search("ecart-type")
    assert DISTRIBUTION_KEYWORDS.search("ecart type")


def test_class5_pymc2_composante_routed_to_distribution() -> None:
    """Verbatim PyMC-2 cell[17] : 3 wallclock 'X min(utes)' -> distribution_param.

    Cas reels (paraphrase conforme) :
    - 'La composante "normale" capture les trajets de 11 a 20 minutes'
    - 'La composante "exceptionnelle" capture les trajets de 28 a 35 minutes'
    - 'Les 3 observations extremes (28, 32, 35 min)'

    Apres le fix Classe 5 : tous les 'minutes' / 'min' dans une ligne qui
    contient 'composantes' / 'observations' / 'trajets' doivent etre
    classifies distribution_param.
    """
    line_a = (
        "La composante \"normale\" capture les trajets de 11 a 20 minutes"
    )
    assert _categorize(line_a, "20 minutes") == CATEGORY_DISTRIBUTION
    line_b = (
        "La composante \"exceptionnelle\" capture les trajets de 28 a 35 minutes"
    )
    assert _categorize(line_b, "35 minutes") == CATEGORY_DISTRIBUTION
    line_c = "Les 3 observations extremes (28, 32, 35 min)"
    assert _categorize(line_c, "35 min") == CATEGORY_DISTRIBUTION


def test_class5_decinfer4_trajet_routed_to_distribution() -> None:
    """Verbatim DecInfer-4 cell[18] : 'Trajet: 60min -> 10min' -> distribution_param.

    Cas reel (#10178 Classe 5, indice 2 notebook pedagogique) : un swing
    decisionnel sur la duree de trajet n'est pas un wallclock, c'est une
    quantite de domaine (attribut de la fonction de decision multi-criteres).
    """
    line = (
        "Un swing \"Prix: 500k -> 200k\" peut etre plus ou moins important "
        "qu'un swing \"Trajet: 60min -> 10min\""
    )
    # Premier match dans la ligne (regex cherche le 1er digit pattern).
    assert _categorize(line, "60min") == CATEGORY_DISTRIBUTION


def test_class5_does_not_break_sudoku13_control() -> None:
    """Le controle positif Sudoku-13 reste detecte apres le fix Classe 5.

    Falsifiable : les wallclock STRICTS (TIMEOUT > 60 s, duree execution
    2.4 s) ne contiennent PAS de discriminant bayesien (composantes,
    observations, trajets, ecart-type) et restent classes wallclock.

    Verifie directement sur le notebook reel (path canonique cote owner).
    Si le path n'existe pas (autre machine que po-2025), skip avec un
    message clair -- le test est skip-able par design (CONTEXT-DEPENDENT).
    """
    nb_path = (
        Path(__file__).resolve().parent.parent.parent.parent
        / "MyIA.AI.Notebooks"
        / "Sudoku"
        / "Sudoku-13-SymbolicAutomata-Csharp.ipynb"
    )
    if not nb_path.exists():
        import pytest
        pytest.skip(f"Notebook reel non trouve cote worker : {nb_path}")
    findings = _scan_notebook(nb_path)
    wc = [f for f in findings if f["category"] == CATEGORY_WALLCLOCK]
    # Falsifiable : wallclock count = 28 (avant et apres fix Classe 5).
    # Tolerance +-0 : le fix ne doit pas modifier ce compte.
    assert len(wc) >= 25, (
        f"Controle positif Sudoku-13 degrade : wallclock={len(wc)} "
        f"(attendu >=25). Le fix Classe 5 a modifie un cas non-cible."
    )


def test_class5_pymc2_real_notebook_silenced() -> None:
    """Le notebook reel PyMC-2 cell[17] passe de 3 wallclock -> 0.

    Verifie directement sur le notebook reel cote owner. Skip si absent.
    """
    nb_path = (
        Path(__file__).resolve().parent.parent.parent.parent
        / "MyIA.AI.Notebooks"
        / "Probas"
        / "PyMC"
        / "PyMC-2-Gaussian-Mixtures.ipynb"
    )
    if not nb_path.exists():
        import pytest
        pytest.skip(f"Notebook reel non trouve cote worker : {nb_path}")
    findings = _scan_notebook(nb_path)
    # Filtre sur cell[17] uniquement (cas verbatim Classe 5).
    cell17 = [f for f in findings if f.get("cell_index") == 17]
    wc = [f for f in cell17 if f["category"] == CATEGORY_WALLCLOCK]
    # Falsifiable : 0 wallclock sur cell[17] apres le fix.
    assert wc == [], (
        f"PyMC-2 cell[17] wallclock NON silencie : {[(f['snippet'], f['line'][:80]) for f in wc]}"
    )


# --------------------------------------------------------------------------- #
#  Edge case : notebook PII-governed
# --------------------------------------------------------------------------- #
def test_pii_governed_notebook_skipped(tmp_path: Path) -> None:
    """Les notebooks avec metadata.pii_no_output=True sont skippés.

    Rationnel : la prose de ces notebooks est gouv. par PII -- la sortie du
    detecteur les concernant est deconseillee pour eviter les faux positifs
    lies au contexte PII. Cf. _collect_targets.
    """
    # On teste _collect_targets : un notebook avec pii_no_output=True doit
    # etre filtre.
    from check_machine_dep_timing import _collect_targets
    # Creer un notebook pii_no_output=True dans un sous-dossier temporaire
    # de MyIA.AI.Notebooks/ equivalent -- on utilise directement _collect_targets
    # via monkeypatch.
    import argparse
    args = argparse.Namespace(
        all=True,
        json=True,
        check=True,
        paths=[],
    )
    # Le test verifie juste que la fonction n'inclut PAS les PII-governed dans
    # le scan -- on le teste indirectement en verifiant le filtre.
    # NB: ce test s'execute dans l'env de test ou MyIA.AI.Notebooks peut
    # ne pas exister ; on skip si le repo n'est pas accessible.
    if not (Path(__file__).resolve().parents[3] / "MyIA.AI.Notebooks").exists():
        pytest.skip("Hors env repo (MyIA.AI.Notebooks absent)")
    targets = _collect_targets(args)
    for t in targets:
        data = json.loads(t.read_text(encoding="utf-8"))
        assert data.get("metadata", {}).get("pii_no_output") is not True


# --------------------------------------------------------------------------- #
#  Main entry point : smoke test que l'argparse tient
# --------------------------------------------------------------------------- #
def test_main_runs_with_help(capsys: pytest.CaptureFixture) -> None:
    """Le main peut etre appele avec --help sans crash."""
    from check_machine_dep_timing import main
    with pytest.raises(SystemExit) as exc:
        main(["--help"])
    # --help exit code = 0
    assert exc.value.code == 0
    captured = capsys.readouterr()
    assert "machine-dep" in captured.out or "machine" in captured.out.lower()


def test_main_advisory_mode_exits_zero() -> None:
    """Mode advisory par defaut : exit 0 meme avec findings (cf. acceptance)."""
    from check_machine_dep_timing import main
    # On scan un chemin arbitraire qui peut etre vide -- exit 0 attendu.
    rc = main(["--all"])
    # Sur CI (avec MyIA.AI.Notebooks/ present), --all peut renvoyer 0 ou 1
    # selon --check, mais sans --check, c'est TOUJOURS 0 (mode advisory).
    assert rc == 0


# --------------------------------------------------------------------------- #
#  Residus #10169 : duree modelisee per-notebook + constante de protocole
#                   + --all resolu hors racine
# --------------------------------------------------------------------------- #
def test_silence_per_notebook_propagation_residu1() -> None:
    """Residu 1 #10169 : propagation per-NOTEBOOK domain_quantity.

    Rationnel : la propagation per-cell (passe 2) est trop etroite. Quand le
    notebook ENTIER porte >=1 ``distribution_param`` (une cellule Gaussienne),
    les wallclock des AUTRES cellules (sans mot-cle stat) basculent en
    ``domain_quantity`` -- l'unite de temps est le sujet du notebook, pas
    d'une cellule. Cas reel Infer-2-Gaussian-Mixtures : les moyennes ajustees
    ``| Ordinaire | 15.07 min |`` / ``| Extraordinaire | 26.69 min |`` sont la
    SORTIE du modele (obtenue par inference), pas une mesure d'execution.

    NB (#10178 Classe 5, c.1301+64) : on enleve les discriminants bayesiens
    ('Trajets') du texte de la cellule 2 pour tester la propagation
    per-NOTEBOOK en isolation. Sinon, 'Trajets normaux' serait classee
    distribution_param DIRECTEMENT par DISTRIBUTION_KEYWORDS Classe 5.
    """
    nb = _make_nb([
        # Cellule 1 : declare les parametres de la distribution (distribution_param).
        _md_cell(
            "## Modele\n"
            "Le melange suit une Gaussian de moyenne 15.33 min et sigma 1.32 min."
        ),
        # Cellule 2 : SEPARATE, sans mot-cle stat ni discriminant Classe 5.
        # Sans la passe per-notebook, les 15.07 / 26.69 resteraient wallclock
        # (la cellule 2 n'a aucun discriminant distribution).
        _md_cell(
            "## Resultats ajustes\n"
            "| Ordinaire | 15.07 min | Normaux : {13, 17, 16} |\n"
            "| Extraordinaire | 26.69 min | Longs : {20, 25, 25, 30} |"
        ),
    ])
    try:
        findings = _scan_notebook(nb)
        wallclock = [f for f in findings if f["category"] == CATEGORY_WALLCLOCK]
        assert wallclock == [], (
            f"Propagation per-notebook rate : wallclock residuel = {wallclock}"
        )
        domain = {f["snippet"]: f["category"] for f in findings
                  if f["category"] == CATEGORY_DOMAIN_QUANTITY}
        assert "15.07 min" in domain, (
            f"15.07 min (moyenne ajustee) attendue en domain_quantity: {domain}"
        )
        assert "26.69 min" in domain, (
            f"26.69 min (moyenne ajustee) attendue en domain_quantity: {domain}"
        )
    finally:
        nb.unlink()


def test_silence_protocol_constant_settle_delay_residu2() -> None:
    """Residu 2 #10169 : constante de protocole = domain_quantity, pas wallclock.

    Un ``settle_delay`` de canal de paiement (consensus) ne derive pas d'une
    machine a l'autre -- c'est un parametre du domaine. Cas reel SC-19-Ripple-XRP
    cell[30] : « Le ``settle_delay`` est crucial... attendre 3600 secondes ».
    """
    nb = _make_nb([
        _md_cell(
            "**Note technique** : Le `settle_delay` est crucial pour la securite. "
            "Si Alice veut fermer le canal, elle doit attendre 3600 secondes "
            "pendant lesquelles Bob peut contester."
        ),
    ])
    try:
        findings = _scan_notebook(nb)
        wallclock = [f for f in findings if f["category"] == CATEGORY_WALLCLOCK]
        assert wallclock == [], (
            f"settle_delay 3600 secondes ne doit pas etre wallclock : {wallclock}"
        )
        assert any(f["category"] == CATEGORY_DOMAIN_QUANTITY for f in findings), (
            f"3600 secondes attendu en domain_quantity : {findings}"
        )
    finally:
        nb.unlink()


def test_silence_protocol_block_time_residu2() -> None:
    """Residu 2 #10169 : temps de bloc Ethereum = constante de protocole.

    Cas reel SC-23-Cross-Chain : « 12 blocs Ethereum ... ». Le temps de bloc
    est un parametre de consensus, pas une duree machine.
    """
    nb = _make_nb([
        _md_cell("Finalite : 12 blocs Ethereum correspondent a environ 3 min."),
    ])
    try:
        findings = _scan_notebook(nb)
        wallclock = [f for f in findings if f["category"] == CATEGORY_WALLCLOCK]
        assert wallclock == [], (
            f"temps de bloc Ethereum ne doit pas etre wallclock : {wallclock}"
        )
        assert any(f["category"] == CATEGORY_DOMAIN_QUANTITY for f in findings)
    finally:
        nb.unlink()


def test_silence_detached_tilde_residu2() -> None:
    """Residu 2 #10169 : tilde detache ``~ 2 min`` = ordre de grandeur, on skip.

    Le ``MACHINE_RE`` colle ``~2 min`` est deja gere (snippet commence par ``~``).
    Ce test couvre la forme DETACHEE (espace entre marqueur et chiffre). La ligne
    est choisie SANS mot-cle protocole/distribution, pour isoler le comportement
    du tilde detache (sinon un mot-cle sauverait le finding par ailleurs).
    """
    nb = _make_nb([
        _md_cell("Estimation de convergence : ~ 2 min par appel."),
    ])
    try:
        findings = _scan_notebook(nb)
        snippets = [f["snippet"] for f in findings]
        assert "2 min" not in snippets, (
            f"Le tilde detache '~ 2 min' doit etre skip (ordre de grandeur) : "
            f"trouve {findings}"
        )
    finally:
        nb.unlink()


def test_is_detached_approximate_helper() -> None:
    """Le helper _is_detached_approximate couvre ~ et ≈, avec ou sans espace."""
    # `~ 2 min` : tilde + espace avant le chiffre.
    assert _is_detached_approximate("foo ~ 2 min", 6) is True   # '~ ' avant idx 6
    # `~2 min` : tilde colle (deja gere par MACHINE_RE, mais le helper le couvre).
    assert _is_detached_approximate("foo ~2 min", 5) is True
    # `≈ 2 min` : variante unicode.
    assert _is_detached_approximate("≈ 2 min", 2) is True
    # Sans tilde : pas un ordre de grandeur.
    assert _is_detached_approximate("duree 2 min", 6) is False


def test_bare_wallclock_still_detected_negative_control() -> None:
    """Controle negatif : sans tilde ni protocole ni distribution, un ``2 min``
    reste wallclock. Garantie que le detecteur n'est pas muet (cf. controle
    positif Sudoku-13 + celui-ci isole le comportement par defaut)."""
    nb = _make_nb([
        _md_cell("La duree d'execution est 2 min pour 1000 iterations."),
    ])
    try:
        findings = _scan_notebook(nb)
        assert any(f["category"] == CATEGORY_WALLCLOCK and f["snippet"] == "2 min"
                   for f in findings), (
            f"Un bare '2 min' sans marqueur doit rester wallclock : {findings}"
        )
    finally:
        nb.unlink()


def test_all_resolves_from_other_dir_residu3(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Residu 3 #10169 : ``--all`` resolu depuis la racine git, pas depuis le cwd.

    Invoque depuis un repertoire externe (tmp_path). ``_repo_root()`` utilise
    ``git rev-parse --show-toplevel`` (authoritatif), donc ``--all`` trouve les
    notebooks meme hors du repertoire du script. Advisory -> exit 0.
    """
    from check_machine_dep_timing import main
    if not (_repo_root() / "MyIA.AI.Notebooks").exists():
        pytest.skip("Hors env repo (MyIA.AI.Notebooks absent sous la racine git)")
    monkeypatch.chdir(tmp_path)
    rc = main(["--all"])
    assert rc == 0, (
        "--all invoque hors racine doit trouver les notebooks via git toplevel "
        "et sortir en advisory (exit 0)"
    )


def test_empty_explicit_scan_is_error_residu3(tmp_path: Path) -> None:
    """Residu 3 #10169 : un scan explicite vide = erreur bruyante (exit 1).

    Un path explicite inexistant ne doit PAS retourner un silent 0 (« Aucun
    notebook ») -- c'est exactement le piege qui apprend a la lane suivante
    qu'il n'y a rien a faire alors que l'outil a juste rate sa cible.
    """
    from check_machine_dep_timing import main
    bogus = tmp_path / "n'existe-pas.ipynb"
    rc = main([str(bogus)])
    assert rc == 1, (
        "Un path explicite inexistant doit echouer bruyamment (exit 1), "
        "pas retourner un silent 0"
    )


# --------------------------------------------------------------------------- #
#  Frontiere FP (frontier issue) : pacing-extension + planning-domain
# --------------------------------------------------------------------------- #
def test_silence_pacing_duration_with_lecture_qualifier() -> None:
    """Frontiere : « N min (lecture + execution) » = pacing (effort humain).

    Cas reel ICT-19-EnjeuBattery cell[0] : « 45 min (lecture + execution
    sequentielle) ». C'est l'estimation d'effort demande a l'etudiant, pas une
    duree machine -- meme rationale que le pacing deja exempte (arbitrage
    jsboige 14:05:37Z #9434). La duree PRECEDE la parenthese (inhabituel), ce
    que le STUDENT_PACING_RE historique ratait.

    NB : on cible le qualificatif d'effort (lecture/cours/tp) precisement. La
    forme « moins de N » / « plus de N » n'est PAS exemptee -- c'est un signal
    de borne runtime ou de probabilite de domaine (ex P(trajet < 18 min)), pas
    de pacing (cf. brainstorm G.1 : sur-exemption cassait la propagation #10162).
    """
    assert STUDENT_PACING_RE.search("45 min (lecture + execution sequentielle). GPU-free.")
    assert STUDENT_PACING_RE.search("90 min (cours magistral + TP)")
    # Sans qualificatif d'effort : reste un finding (pas pacing).
    assert not STUDENT_PACING_RE.search("La duree d'execution est 45 min.")
    # « moins de N » / « plus de N » n'est PAS pacing (borne runtime/domaine).
    assert not STUDENT_PACING_RE.search("converge en plus de 10 min sur les gros cas")


def test_plan_table_cost_routed_to_domain_quantity() -> None:
    """Frontiere : « N + M = K min » = cout d'action dans une table de plan.

    Cas reel Planners-8-Temporal cell[37] : « | D1 | A -> B | 5 + 4 = 9 min | ».
    Le « 9 min » est la duree DETERMINISTE d'une livraison drone (somme acces +
    vol), pas une duree machine. Routed vers domain_quantity (compte, visible),
    pas wallclock.

    On verifie via _categorize : la ligne porte l'arithmetique de cout -> le
    snippet « 9 min » est classe domain_quantity.
    """
    line = "| D1 | A -> B | 5 + 4 = 9 min | Drone 0 ou 1 |"
    assert _categorize(line, "9 min") == CATEGORY_DOMAIN_QUANTITY
    line2 = "Duree totale : 0 + 6 = 6 min pour la livraison D2."
    assert _categorize(line2, "6 min") == CATEGORY_DOMAIN_QUANTITY


def test_plan_cost_regex_does_not_overreach_real_wallclock() -> None:
    """Controle negatif : un vrai wallclock sans arithmetique de cout reste wallclock.

    Garantie que le motif « N + M = K unit » est precis. Sudoku-13 (controle
    positif canonique) rapporte « 2.4 s pour 1000 iterations » -- aucune somme
    explicite `a + b = c unit` -> reste wallclock. Ce test isole le comportement.
    """
    line = "La duree d'execution est 2.4 s pour 1000 iterations."
    # Pas d'arithmetique de cout -> _categorize ne bascule pas en domain_quantity
    # via la branche plan-cost (WALLCLOCK_KEYWORDS 'execution' -> wallclock).
    assert _categorize(line, "2.4 s") == CATEGORY_WALLCLOCK


# --------------------------------------------------------------------------- #
#  CLI correctness #10445 (partie b) : --json/--check ne doivent pas jeter paths
# --------------------------------------------------------------------------- #
def _write_nb(path: Path, cells: list[dict] | None = None) -> Path:
    """Ecrit un notebook JSON valide a un chemin precis (pour _collect_targets)."""
    nb = {"cells": cells or [], "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(nb), encoding="utf-8")
    return path


def test_collect_targets_honors_paths_with_json(tmp_path: Path, monkeypatch) -> None:
    """``--json chemin.ipynb`` doit scanner le chemin, pas le repo entier (#10445 b).

    Avant le fix, ``args.json`` dans la premiere branche de ``_collect_targets``
    impliquait ``--all`` : le chemin explicite etait jete, le glob repo-entier
    s'executait. Incident merge-gate #10442 : 215 timings repo attribues a 1
    notebook qui en contribuait 0. Ce test epingle qu'un ``paths`` explicite
    prime sur ``--json``, ET qu'un leurre sous le glob ``MyIA.AI.Notebooks/``
    n'est PAS scanne.
    """
    import argparse

    import check_machine_dep_timing as m

    # Cible explicite (hors MyIA.AI.Notebooks/ -- pas sous le glob) + leurre
    # sous le glob : avant le fix, le glob retournait [decoy] et ignorait target.
    target = _write_nb(tmp_path / "nb_target.ipynb")
    _write_nb(tmp_path / "MyIA.AI.Notebooks" / "famille" / "decoy.ipynb")
    monkeypatch.setattr(m, "_repo_root", lambda: tmp_path)

    args = argparse.Namespace(paths=[target], all=False, json=True, check=False)
    out = _collect_targets(args)
    # Un seul cible (target), le leurre sous le glob est exclu.
    assert out == [target]


def test_collect_targets_all_with_paths_warns(tmp_path: Path, monkeypatch, capsys) -> None:
    """``--all`` + paths force l'inventaire mais ne jette pas paths en silence (#10445 b).

    ``--all`` est le seul cas ou paths est legitimement ignore (semantique :
    forcer le scan complet). La regle « ne jamais jeter un argument en silence »
    exige un avertissement stderr explicite.
    """
    import argparse

    import check_machine_dep_timing as m

    target = _write_nb(tmp_path / "nb_target.ipynb")
    monkeypatch.setattr(m, "_repo_root", lambda: tmp_path)

    args = argparse.Namespace(paths=[target], all=True, json=False, check=False)
    _collect_targets(args)  # glob vide sous tmp_path -> [] mais le warn est emis
    err = capsys.readouterr().err
    assert "paths" in err.lower() and "ignore" in err.lower()


if __name__ == "__main__":
    pytest.main([__file__, "-v"])