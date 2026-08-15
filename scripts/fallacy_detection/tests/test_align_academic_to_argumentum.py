#!/usr/bin/env python3
"""Tests pour ``scripts/fallacy_detection/align_academic_to_argumentum.py``.

Phase 2 / sous-grain CPU de l'EPIC #10355. Hermetique : stdlib only. Synthetise
une mini-taxonomie Argumentum (3 feuilles) puis verifie l'alignement des
etiquettes academiques (Logic-13, MAFALDA-L2) -- noms EN directs, cognates FR,
chevauchement lexical, verdicts DIRECT/PARTIAL/NOT_FOUND, et le rapport de
couverture par famille.
"""

import csv
import io
import sys
import zipfile
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
SCRIPTS_DIR = HERE.parent.parent  # scripts/
sys.path.insert(0, str(SCRIPTS_DIR))

from fallacy_detection.align_academic_to_argumentum import (  # noqa: E402
    ARGUMENTUM_FAMILIES,
    Alignment,
    ArgumentumEntry,
    LOGIC_13,
    MAFALDA_L2,
    _jaccard,
    _norm,
    _tokens,
    align_label,
    build,
    coverage_report,
    load_argumentum,
    main,
)


# ---------------------------------------------------------------------------
# Helpers : mini-taxonomie Argumentum synthetique.
# ---------------------------------------------------------------------------

TAXO_HEADER = (
    "PK,Famille,Sous-Famille,nom_vulgarisé,text_fr,desc_fr,"
    "Simple_name_en,text_en,desc_en"
)


def _write_taxo(path: Path, rows: list[list[str]]) -> Path:
    """Ecrit une mini-taxonomie Argumentum CSV (UTF-8 no-BOM)."""
    out = io.StringIO()
    w = csv.writer(out, lineterminator="\n")
    w.writerow(TAXO_HEADER.split(","))
    for r in rows:
        w.writerow(r)
    path.write_text(out.getvalue(), encoding="utf-8")
    return path


SAMPLE_ROWS = [
    # racine (doit etre ignoree)
    ["0", "Argument fallacieux", "", "", "Argument fallacieux", "", "", "", ""],
    # ad hominem -> Influence
    ["101", "Influence", "Attaque",
     "Attaque personnelle", "Attaque personnelle",
     "Vous disqualifiez la personne plutot que son argument.",
     "Ad hominem", "Ad hominem", "Attacking the person rather than the argument."],
    # generalisation hative -> Insuffisance
    ["207", "Insuffisance", "Argument bâclé",
     "Généralisation hâtive", "Généralisation hâtive",
     "Vous generalisez a partir d'anecdotes sans preuve solide.",
     "Hasty generalization", "Hasty generalization",
     "Basing an argument on impressions or anecdotes."],
    # pomme de terre (irrelevant, pour tester le NON match)
    ["999", "Tricherie", "Divers", "Faux pretexte", "Faux pretexte",
     "Un argument sans rapport reel avec le sujet.", "", "", "Unrelated claim."],
]


@pytest.fixture
def taxo_path(tmp_path: Path) -> Path:
    return _write_taxo(tmp_path / "taxo.csv", SAMPLE_ROWS)


@pytest.fixture
def argum(taxo_path: Path) -> list[ArgumentumEntry]:
    return load_argumentum(taxo_path)


# ---------------------------------------------------------------------------
# Tokenisation / heuristiques.
# ---------------------------------------------------------------------------

def test_tokens_filters_stopwords_and_short():
    t = _tokens("The Ad Hominem is a fallacy of reasoning")
    assert "the" not in t  # stopword
    assert "is" not in t
    assert "ad" not in t  # < 3 chars
    assert "hominem" in t
    assert "fallacy" not in t  # stopword (metier)
    assert "reasoning" not in t  # stopword


def test_jaccard_basic():
    assert _jaccard({"a", "b"}, {"b", "c"}) == pytest.approx(1 / 3)
    assert _jaccard(set(), {"a"}) == 0.0
    assert _jaccard({"a"}, {"a"}) == 1.0


def test_norm_strips_accents():
    assert _norm("Généralisation") == "generalisation"
    assert _norm("Ad hominem") == "ad hominem"
    assert _norm("Pétition-de-principe") == "petition de principe"


# ---------------------------------------------------------------------------
# load_argumentum : saute la racine, garde les feuilles.
# ---------------------------------------------------------------------------

def test_load_argumentum_skips_root(argum: list[ArgumentumEntry]):
    # Racine "Argument fallacieux" exclue -> 3 feuilles sur 4 lignes.
    assert len(argum) == 3
    assert all(e.famille != "Argument fallacieux" for e in argum)


def test_load_argumentum_bom_tolerant(tmp_path: Path):
    # UTF-8 BOM au debut : decode utf-8-sig doit le retirer, pas casser le header.
    bom = b"\xef\xbb\xbf"
    body = ",".join(TAXO_HEADER.split(",")) + "\n"
    p = tmp_path / "bom.csv"
    p.write_bytes(bom + body.encode("utf-8"))
    rows = load_argumentum(p)
    assert len(rows) == 0  # header seul, aucune feuille


# ---------------------------------------------------------------------------
# align_label : verdicts DIRECT / PARTIAL / NOT_FOUND.
# ---------------------------------------------------------------------------

def test_align_direct_en_name_match(argum: list[ArgumentumEntry]):
    # "Ad hominem" correspond exact au Simple_name_en d'entry 101.
    a = align_label("Ad hominem", "TEST", ["ad hominem", "attaque personnelle"], argum)
    assert a.verdict == "DIRECT"
    assert a.best_pk == "101"
    assert a.best_famille == "Influence"
    assert a.score >= 0.8


def test_align_direct_cognate_fr(argum: list[ArgumentumEntry]):
    # "Hasty generalization" via Simple_name_en, mais aussi cognate FR presente.
    a = align_label("Hasty generalization", "TEST",
                    ["hasty generalization", "généralisation hâtive"], argum)
    assert a.verdict == "DIRECT"
    assert a.best_pk == "207"
    assert a.best_famille == "Insuffisance"


def test_align_not_found_when_no_overlap(argum: list[ArgumentumEntry]):
    # Etiquette sans aucun rapport avec les 3 entries -> NOT_FOUND.
    a = align_label("Quantum entanglement fallacy", "TEST",
                    ["quantum", "intrication"], argum)
    assert a.verdict == "NOT_FOUND"
    assert a.best_pk is None


# ---------------------------------------------------------------------------
# build : pipeline complet sur la mini-taxonomie.
# ---------------------------------------------------------------------------

def test_build_returns_alignments_and_report(taxo_path: Path):
    alignments, report = build(taxo_path)
    # Logic-13 (15 entrees encodees) + MAFALDA-L2 (23) = 38 alignements.
    assert len(alignments) == len(LOGIC_13) + len(MAFALDA_L2)
    assert "Logic13" in report["by_source"]
    assert "MAFALDA-L2" in report["by_source"]
    assert report["argumentum_total_leaves"] == 3


def test_coverage_report_structure(taxo_path: Path):
    _, report = build(taxo_path)
    # Toutes les 7 familles Argumentum sont cles du dict.
    assert set(report["argumentum_families_hit"].keys()) == set(ARGUMENTUM_FAMILIES)
    # Sur la mini-taxo, seules Influence + Insuffisance sont touchees.
    hit = [f for f, n in report["argumentum_families_hit"].items() if n > 0]
    assert "Influence" in hit
    assert "Insuffisance" in hit
    # Les 5 autres familles (Tricherie sauf entry 999 non matchee, etc.) ne le
    # sont pas sur cette mini-taxo.
    assert report["argumentum_families_never_hit"]


# ---------------------------------------------------------------------------
# main : exit codes + fichiers de sortie.
# ---------------------------------------------------------------------------

def test_main_missing_taxonomy_returns_2(tmp_path: Path):
    rc = main(["--taxonomy", str(tmp_path / "absent.csv"), "--report"])
    assert rc == 2


def test_main_writes_outputs(tmp_path: Path, taxo_path: Path):
    out_csv = tmp_path / "mapping.csv"
    out_json = tmp_path / "report.json"
    rc = main([
        "--taxonomy", str(taxo_path),
        "--out-csv", str(out_csv),
        "--out-json", str(out_json),
    ])
    assert rc == 0
    assert out_csv.exists()
    assert out_json.exists()
    # Le CSV a un header + au moins 38 lignes de donnees.
    text = out_csv.read_text(encoding="utf-8")
    assert "academic_label" in text.splitlines()[0]
    assert len(text.splitlines()) >= 1 + len(LOGIC_13) + len(MAFALDA_L2)


def test_main_report_to_stdout(taxo_path: Path, capsys):
    rc = main(["--taxonomy", str(taxo_path), "--report"])
    assert rc == 0
    captured = capsys.readouterr()
    assert "Couverture academique" in captured.out
    assert "Logic13" in captured.out
    assert "MAFALDA-L2" in captured.out
    assert "Familles Argumentum touchees" in captured.out


# ---------------------------------------------------------------------------
# Sanity : les listes academiques encodees sont conformes aux papiers.
# ---------------------------------------------------------------------------

def test_logic_13_has_core_types():
    labels = {l for l, _ in LOGIC_13}
    # Les types les plus cites du papier Jin 2021 doivent etre presents.
    for core in ["Ad hominem", "Straw man", "Slippery slope", "Red herring"]:
        assert core in labels, f"Logic-13 missing core type: {core}"


def test_mafalda_l2_has_23_distinct_and_l1_categories():
    labels = [l for l, _, _ in MAFALDA_L2]
    l1_cats = {c for _, _, c in MAFALDA_L2}
    # 3 categories L1 (Pathos / Logos / Ethos) documentees par Helwe 2023.
    assert l1_cats == {"Pathos", "Logos", "Ethos"}
    # ~23 classes (on accepte 21..25 vu les chevauchements Pathos/Logos encodes).
    assert 21 <= len(labels) <= 25
