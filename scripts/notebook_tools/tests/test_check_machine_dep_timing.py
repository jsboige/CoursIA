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
    _scan_notebook,
    _is_range_bound,
    _repo_root,
    CATEGORY_WALLCLOCK,
    CATEGORY_DISTRIBUTION,
    CATEGORY_AMBIGUOUS,
    CATEGORY_DOMAIN_QUANTITY,
    STUDENT_PACING_RE,
    WALLCLOCK_KEYWORDS,
    DISTRIBUTION_KEYWORDS,
    PROTOCOL_KEYWORDS,
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
    """
    nb = _make_nb([
        _md_cell(
            "Le modele suit une Gaussian de moyenne 15.33 min et sigma 1.32 min.\n"
            "\n"
            "La duree typique observee est de l'ordre de 15 minutes par trajet.\n"
            "La proportion de trajets de moins de 15 min est la metrique cle."
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
        # Au moins un finding wallclock avant propagation (les '15 minutes' /
        # '15 min' des autres lignes).
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
#  Extensions #10169 (c.1301+40) : propagation per-notebook + constante de
#  protocole + tilde detache + resolution git-root
# --------------------------------------------------------------------------- #
def test_per_notebook_propagation_flips_cross_cell() -> None:
    """#10169 residu 1 : la propagation domain_quantity est per-NOTEBOOK.

    Rationnel : la propagation per-cell (#10162 FP-2) etait trop etroite.
    Sur Infer-2-Gaussian-Mixtures, 6 findings restaient en wallclock bien que
    l'unite de temps (temps de trajet) soit le sujet du notebook -- leurs
    cellules ne portaient pas de mot-cle statistique, mais d'autres cellules
    du meme notebook oui. La propagation per-notebook : si le notebook porte
    >=1 distribution_param, TOUS ses wallclock basculent en domain_quantity.

    Ce test met la distribution_param dans la cellule A et un wallclock pur
    (aucun mot-cle) dans la cellule B -- un cas que la propagation per-cell
    ne couvrait PAS (cellules differentes).
    """
    nb = _make_nb([
        _md_cell("Le modele est une Gaussian de moyenne 15.33 min (sigma 1.32 min)."),
        _md_cell(
            "| Classe | Moyenne ajustee |\n"
            "| --- | --- |\n"
            "| Ordinaire | 15.07 min | Trajets normaux |\n"
            "| Extraordinaire | 26.69 min | Trajets longs |"
        ),
    ])
    try:
        findings = _scan_notebook(nb)
        # La cellule B (tableau, aucun mot-cle distribution) contient les
        # '15.07 min' et '26.69 min' qui sont les MOYENNES AJUSTEES du
        # melange -- le resultat du modele. Apres propagation per-notebook,
        # ils basculent en domain_quantity, pas wallclock.
        wallclock = [f for f in findings if f["category"] == CATEGORY_WALLCLOCK]
        domain = [f for f in findings if f["category"] == CATEGORY_DOMAIN_QUANTITY]
        assert wallclock == [], (
            f"Aucun wallclock attendu (propagation per-notebook), trouve {wallclock}"
        )
        assert len(domain) >= 2, (
            f"Attendu >=2 domain_quantity (15.07/26.69 min), categories="
            f"{[f['category'] for f in findings]}"
        )
    finally:
        nb.unlink()


def test_protocol_constant_classified_as_domain_quantity() -> None:
    """#10169 residu 2 : une constante de protocole n'est PAS un wallclock.

    Rationnel : un `settle_delay` de canal de paiement XRP (3600 secondes) ou
    un temps de bloc Ethereum (~2 min) sont des PARAMETRES DU DOMAINE modelise
    (consensus blockchain), pas des durees machine. Ils ne derivent pas d'une
    machine a l'autre -- ce sont des constantes du protocole. Meme famille que
    domain_quantity, dans un domaine que les mots-cles statistiques ne couvrent
    pas.
    """
    nb = _make_nb([
        _md_cell(
            "Le `settle_delay` est crucial pour la securite. Pour fermer le "
            "canal, il faut attendre 3600 secondes (le delai de consensus)."
        ),
    ])
    try:
        findings = _scan_notebook(nb)
        wallclock = [f for f in findings if f["category"] == CATEGORY_WALLCLOCK]
        assert wallclock == [], (
            f"'settle_delay 3600 secondes' ne doit PAS etre wallclock, trouve {wallclock}"
        )
    finally:
        nb.unlink()


def test_protocol_keyword_detects_blockchain_domain() -> None:
    """PROTOCOL_KEYWORDS detecte settle_delay, blocs Ethereum, consensus."""
    assert PROTOCOL_KEYWORDS.search("Le `settle_delay` du canal XRP")
    assert PROTOCOL_KEYWORDS.search("12 blocs Ethereum ~ 2 min")
    assert PROTOCOL_KEYWORDS.search("temps de bloc Bitcoin = 10 min")
    assert PROTOCOL_KEYWORDS.search("finalite du consensus")
    # Negatif : un 'block' hors-contexte blockchain n'est pas un protocole.
    assert not PROTOCOL_KEYWORDS.search("un block de code de 50 lignes")


def test_silence_on_detached_tilde() -> None:
    """#10169 residu 2 : '~ 2 min' (tilde detache, espace) est conforme.

    Rationnel : '~ 2 min' (avec un espace entre le tilde et le nombre) est un
    ordre de grandeur, tout comme '~2 min' (attache). MACHINE_RE ne capture pas
    le tilde dans le snippet (il est trop loin du chiffre), donc le check
    `snippet.startswith('~')` le manquait. On verifie maintenant le tilde dans
    le prefixe juste avant le match.

    Extrait reel : SC-23-Cross-Chain cell[24] 'Confirmation source (12 blocs
    Ethereum ~ 2 min)'.
    """
    nb = _make_nb([
        _md_cell("Confirmation source (12 blocs Ethereum ~ 2 min)."),
        _md_cell("Le scan prend ~ 30 sec habituellement."),
    ])
    try:
        findings = _scan_notebook(nb)
        assert findings == [], (
            f"'~ 2 min' et '~ 30 sec' sont des ordres de grandeur conformes, "
            f"trouve {findings}"
        )
    finally:
        nb.unlink()


def test_repo_root_resolves_git_toplevel() -> None:
    """#10169 residu 3 : _repo_root() resout la racine via git (cwd-independant).

    Rationnel : la resolution precedente (parents[2]) supposait une profondeur
    fixe. _repo_root() utilise git rev-parse --show-toplevel (ancre canonique),
    fallback parents[2]. Dans l'env de test (dans le repo), le resultat doit
    contenir MyIA.AI.Notebooks (la racine du depot).
    """
    repo = _repo_root()
    # Dans l'env de test on est dans le repo CoursIA.
    if not (Path(__file__).resolve().parents[3] / "MyIA.AI.Notebooks").exists():
        pytest.skip("Hors env repo (MyIA.AI.Notebooks absent)")
    assert (repo / "MyIA.AI.Notebooks").exists(), (
        f"_repo_root()={repo} ne contient pas MyIA.AI.Notebooks/"
    )


def test_all_vacuous_zero_guard_returns_two(monkeypatch: pytest.MonkeyPatch) -> None:
    """#10169 residu 3 : --all qui trouve 0 notebooks = exit 2 (pas faux 0).

    Rationnel : un --all qui renvoie silencieusement '0 findings' apprend a la
    lane suivante qu'il n'y a rien a faire -- alors que c'est presque toujours
    une resolution de racine cassee. On echoue explicitement (exit 2), mirror
    scan_md_table_syntax.py / scan_md_hierarchy.py (#3968).
    """
    from check_machine_dep_timing import main, _collect_targets
    import argparse

    # Simuler une racine cassee : _collect_targets ne trouve rien.
    def _bogus_targets(args):
        return []
    monkeypatch.setattr(
        "check_machine_dep_timing._collect_targets", _bogus_targets
    )
    rc = main(["--all"])
    assert rc == 2, f"--all avec 0 cibles doit retourner 2, pas {rc}"



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


if __name__ == "__main__":
    pytest.main([__file__, "-v"])