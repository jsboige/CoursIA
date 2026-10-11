#!/usr/bin/env python3
"""Epinglage du payload SEMANTIQUE de la table d'alignement academique.

Complement de ``test_align_academic_to_argumentum.py`` : ce dernier teste la
MACHINERIE sur une mini-taxonomie synthetique et reste hermetique ; celui-ci
teste le CONTENU produit sur la taxonomie Argumentum reelle du depot, et
confronte les artefacts commis a une execution fraiche de l'organe.

Raison d'etre (revue NanoClaw 5469985194, reserve 1) : « un revert silencieux de
``causalite douteuse`` repasserait Logic-13 a 80 % sans faire bouger un check ».
Les deux tests de derive ci-dessous rendent ce revert impossible en silence :

- ``test_les_4_termes_ajoutes_sont_epingles`` : les 4 termes de la tranche C sont
  nommes, sur leur entree exacte ;
- ``test_les_4_termes_sont_porteurs`` : controle NEGATIF -- retirer un terme fait
  tomber son etiquette en NOT_FOUND. C'est ce qui distingue un mot-cle utile d'un
  mot-cle decoratif, et c'est le test qui rougit si l'un des 4 est reverte ;
- ``test_table_commise_egale_execution_fraiche`` : la table commise est rejouee ;
- ``test_rapport_commis_egale_execution_fraiche`` : les compteurs de couverture
  (12/3/0 et 17/4/2) sont epingles, pas seulement affiches.

stdlib only, aucun acces reseau. La taxonomie cible est celle du depot.
"""

import ast
import csv
import hashlib
import json
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
SCRIPTS_DIR = HERE.parent.parent  # scripts/
sys.path.insert(0, str(SCRIPTS_DIR))

from fallacy_detection.align_academic_to_argumentum import (  # noqa: E402
    LOGIC_LABELS,
    LOGIC_SOURCE,
    MAFALDA_L2,
    MAFALDA_SOURCE,
    _DEFAULT_TAXO,
    _REPO_ROOT,
    align_label,
    build,
    load_argumentum,
)

ACADEMIC_DIR = (
    _REPO_ROOT / "MyIA.AI.Notebooks/GenAI/FallacyDetection/data/academic"
)
COMMITTED_CSV = ACADEMIC_DIR / "logic_mafalda_to_argumentum.csv"
COMMITTED_JSON = ACADEMIC_DIR / "alignment_report.json"

# Couverture attendue, par source. Ces valeurs sont la raison d'etre de la
# tranche C : elles sont epinglees ici pour qu'un revert lexical les fasse
# rougir au lieu de les faire baisser en silence.
EXPECTED_COVERAGE = {
    LOGIC_SOURCE: {"total": 15, "DIRECT": 12, "PARTIAL": 3, "NOT_FOUND": 0},
    MAFALDA_SOURCE: {"total": 23, "DIRECT": 17, "PARTIAL": 4, "NOT_FOUND": 2},
}

# Les 4 quasi-manques lexicaux fermes par la tranche C (jugement d'alignement
# c.6074873532) et le 5e pris pour symetrie. Chaque entree porte la cible et le
# verdict SANS le terme -- deux formes mesurees le 2026-10-09, et la distinction
# est le sujet du test :
#   - les 4 quasi-manques de la tranche C CREENT l'alignement (NOT_FOUND -> DIRECT) ;
#   - le 5e (MAFALDA False cause, symetrie) PROMOUVOIT un PARTIAL en DIRECT, la
#     seule feuille 697 que les deux taxonomies doivent viser.
TRANCHE_C_TERMS = [
    (LOGIC_SOURCE, "Bandwagon", "appel à la bande", "1395", "NOT_FOUND"),
    (MAFALDA_SOURCE, "Appeal to popularity", "appel à la bande", "1395", "NOT_FOUND"),
    (LOGIC_SOURCE, "Sunk cost fallacy", "coûts irrécupérables", "440", "NOT_FOUND"),
    (LOGIC_SOURCE, "False cause", "causalité douteuse", "697", "NOT_FOUND"),
    (MAFALDA_SOURCE, "False cause", "causalité douteuse", "697", "PARTIAL"),
]


@pytest.fixture(scope="module")
def argum():
    return load_argumentum(_DEFAULT_TAXO)


def _keywords(source: str, label: str) -> list[str]:
    """Liste de mots-cles encodee pour (source, label). Casse si absentee."""
    if source == LOGIC_SOURCE:
        hits = [kw for lbl, kw in LOGIC_LABELS if lbl == label]
    elif source == MAFALDA_SOURCE:
        hits = [kw for lbl, kw, _l1 in MAFALDA_L2 if lbl == label]
    else:  # pragma: no cover - garde-fou
        raise AssertionError(f"source inconnue : {source}")
    assert hits, f"etiquette absente de l'inventaire {source} : {label}"
    return hits[0]


# ---------------------------------------------------------------------------
# 1. Les 4 (+1) termes sont nommes, sur leur entree exacte.
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("source,label,term,_pk,sans_attendu", TRANCHE_C_TERMS)
def test_les_termes_de_la_tranche_c_sont_epingles(source, label, term, _pk, sans_attendu):
    assert term in _keywords(source, label), (
        f"{source}/{label} a perdu le mot-cle {term!r} : couverture en baisse, "
        f"la tranche C est revertee"
    )


# ---------------------------------------------------------------------------
# 2. Controle NEGATIF : chaque terme est porteur (le retirer degrade l'alignement).
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("source,label,term,_pk,sans_attendu", TRANCHE_C_TERMS)
def test_les_termes_sont_porteurs(source, label, term, _pk, sans_attendu, argum):
    """Sans le terme, l'etiquette n'atteint PLUS la feuille : le terme est porteur.

    L'assertion exacte (et non « pas DIRECT ») est ce qui rend le test falsifiable
    dans les deux sens : elle rougit si le terme est retire de l'inventaire (la
    liste devient identique, donc le verdict reste DIRECT), et elle rougit aussi
    si l'alignement se degrade pour une autre raison.
    """
    kws = _keywords(source, label)
    avec = align_label(label, source, kws, argum)
    assert avec.verdict == "DIRECT", (
        f"{source}/{label} devrait s'aligner en DIRECT avec {term!r}, "
        f"obtenu {avec.verdict}"
    )
    sans = align_label(label, source, [k for k in kws if k != term], argum)
    assert sans.verdict == sans_attendu, (
        f"{source}/{label} : attendu {sans_attendu} sans {term!r}, obtenu "
        f"{sans.verdict} -- si c'est DIRECT, le terme a disparu de l'inventaire"
    )


def test_les_termes_atteignent_leur_cible():
    """Les 5 termes visent la feuille annoncee dans le body de la PR."""
    argum = load_argumentum(_DEFAULT_TAXO)
    for src, label, _term, pk, _sans in TRANCHE_C_TERMS:
        a = align_label(label, src, _keywords(src, label), argum)
        assert a.best_pk == pk, (
            f"{src}/{label} atteint pk={a.best_pk}, attendu {pk}"
        )


# ---------------------------------------------------------------------------
# 3. La symetrie False cause : les deux taxonomies convergent sur la meme feuille.
# ---------------------------------------------------------------------------

def test_false_cause_converge_entre_les_deux_taxonomies(argum):
    """MAFALDA-L2 et LOGIC portent le meme label : ils doivent viser la meme feuille.

    L'asymetrie d'origine (extension portee sur la seule entree LOGIC) etait un
    artefact du perimetre du jugement cede, pas un choix semantique -- mesure du
    2026-10-09 : la feuille 697 est la cible correcte des deux cotes.
    """
    logic = align_label("False cause", LOGIC_SOURCE, _keywords(LOGIC_SOURCE, "False cause"), argum)
    mafalda = align_label("False cause", MAFALDA_SOURCE, _keywords(MAFALDA_SOURCE, "False cause"), argum)
    assert logic.best_pk == mafalda.best_pk == "697"
    assert logic.verdict == mafalda.verdict == "DIRECT"


# ---------------------------------------------------------------------------
# 4. Les artefacts commis egale une execution fraiche de l'organe.
# ---------------------------------------------------------------------------

def _fresh_build():
    alignments, report = build(_DEFAULT_TAXO)
    return alignments, report


def test_table_commise_egale_execution_fraiche():
    """La table commise est rejouee : aucune edition manuelle, aucun revert muet."""
    assert COMMITTED_CSV.exists(), f"table absente : {COMMITTED_CSV}"
    alignments, _ = _fresh_build()
    fresh = [a.to_row() for a in alignments]

    committed = list(csv.DictReader(COMMITTED_CSV.read_text(encoding="utf-8").splitlines()))
    assert len(committed) == len(fresh), (
        f"la table commise porte {len(committed)} lignes, une execution fraiche "
        f"en produit {len(fresh)} : regenerer par l'organe (NOTICE)"
    )

    for i, (c_row, f_row) in enumerate(zip(committed, fresh), start=1):
        for key, f_val in f_row.items():
            expected = "" if f_val is None else str(f_val)
            assert c_row[key] == expected, (
                f"ligne {i}, colonne {key!r} : table commise {c_row[key]!r} != "
                f"execution fraiche {expected!r}"
            )


def test_rapport_commis_egale_execution_fraiche():
    """Les compteurs de couverture sont epingles, pas seulement affiches."""
    assert COMMITTED_JSON.exists(), f"rapport absent : {COMMITTED_JSON}"
    _, report = _fresh_build()
    committed = json.loads(COMMITTED_JSON.read_text(encoding="utf-8"))
    assert committed == report, (
        "le rapport commis diverge d'une execution fraiche : regenerer par "
        "l'organe (commande de la NOTICE), jamais a la main"
    )


def test_couverture_par_source_epinglee():
    _, report = _fresh_build()
    for source, expected in EXPECTED_COVERAGE.items():
        stats = report["by_source"][source]
        for key, value in expected.items():
            assert stats[key] == value, (
                f"{source}.{key} = {stats[key]}, attendu {value} "
                f"(couverture en baisse : un mot-cle a ete retire ?)"
            )


def test_labels_not_found_documentes():
    """Les 2 NOT_FOUND restants sont ceux documentes comme attendus."""
    _, report = _fresh_build()
    assert sorted(report["by_source"][MAFALDA_SOURCE]["labels_not_found"]) == [
        "Appeal to values",
        "Fallacy of logic",
    ]
    assert report["by_source"][LOGIC_SOURCE]["labels_not_found"] == []
    assert report["argumentum_families_never_hit"] == []


# ---------------------------------------------------------------------------
# 5. L'ancre de reproductibilite ne porte aucun chemin machine.
# ---------------------------------------------------------------------------

def test_ancre_de_reproductibilite_est_un_chemin_relatif():
    _, report = _fresh_build()
    anchor = report["argumentum_csv"]
    assert "\\" not in anchor, f"chemin Windows dans l'artefact : {anchor!r}"
    assert ":" not in anchor, f"chemin absolu (lecteur) dans l'artefact : {anchor!r}"
    assert not anchor.startswith("/"), f"chemin absolu dans l'artefact : {anchor!r}"
    assert anchor == (
        "MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/data/"
        "argumentum_fallacies_taxonomy.csv"
    )


def test_ancre_de_reproductibilite_porte_l_empreinte_du_csv():
    """L'empreinte rend l'ancre verifiable meme si le chemin devient illisible."""
    _, report = _fresh_build()
    attendu = hashlib.sha256(_DEFAULT_TAXO.read_bytes()).hexdigest()
    assert report["argumentum_csv_sha256"] == attendu
    assert len(report["argumentum_csv_sha256"]) == 64


# ---------------------------------------------------------------------------
# 6. Le nom porte la provenance, pas un cardinal (reserve 2 de NanoClaw).
# ---------------------------------------------------------------------------

def test_le_nom_de_source_ne_porte_aucun_cardinal():
    """« Logic-13 » annoncait 13 pour 15 entrees : le nom ne compte plus rien."""
    assert LOGIC_SOURCE == "LOGIC"
    assert not any(ch.isdigit() for ch in LOGIC_SOURCE), (
        "le libelle de source ne doit pas porter de cardinal -- le compte fait "
        "foi dans le champ `total` du rapport et dans EXPECTED_COVERAGE"
    )


def test_le_cardinal_reel_est_celui_du_test_pas_du_nom():
    """Le chiffre qui fait foi : 15 entrees encodees, 23 pour MAFALDA-L2."""
    assert len(LOGIC_LABELS) == EXPECTED_COVERAGE[LOGIC_SOURCE]["total"] == 15
    assert len(MAFALDA_L2) == EXPECTED_COVERAGE[MAFALDA_SOURCE]["total"] == 23


def test_les_mots_cles_commis_sont_relisibles():
    """Garde-fou de forme : la colonne keywords du CSV est une liste litterale."""
    committed = list(csv.DictReader(COMMITTED_CSV.read_text(encoding="utf-8").splitlines()))
    for row in committed:
        parsed = ast.literal_eval(row["keywords"])
        assert isinstance(parsed, list) and parsed
        assert all(isinstance(k, str) and k for k in parsed)
