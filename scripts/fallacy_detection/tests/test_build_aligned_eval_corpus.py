"""Tests du builder de corpus aligne pour le test externe humain (#20222).

Chaque propriete promise par le docstring du builder est mesuree ici :
join exact insensible a la casse, pont declare avec justification, exclusions
motivees, lignes NOT_FOUND sans paire, familles a zero mesurees, et
compatibilite du JSONL produit avec l'echantillonneur (load_corpus).
"""

from __future__ import annotations

import csv
import importlib.util
import json
import sys
from pathlib import Path

import pytest

_HERE = Path(__file__).resolve().parent
_SCRIPTS = _HERE.parent
# Le builder vit dans scripts/fallacy_detection/, les tests dans .../tests/.
_spec = importlib.util.spec_from_file_location(
    "build_aligned_eval_corpus", _SCRIPTS / "build_aligned_eval_corpus.py"
)
builder = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(builder)

_spec2 = importlib.util.spec_from_file_location(
    "sample_external_eval", _SCRIPTS / "sample_external_eval.py"
)
sampler = importlib.util.module_from_spec(_spec2)
_spec2.loader.exec_module(sampler)

TABLE_FIELDS = ["academic_label", "academic_source", "keywords", "best_pk", "best_famille",
                "best_name", "score", "verdict", "candidates (pk,famille,score)"]


def _write_table(path: Path, rows: list[dict]) -> None:
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=TABLE_FIELDS)
        writer.writeheader()
        for row in rows:
            full = {f: "" for f in TABLE_FIELDS}
            full.update(row)
            full["academic_source"] = "MAFALDA-L2"
            writer.writerow(full)


def _write_gold(path: Path, records: list[dict]) -> None:
    with path.open("w", encoding="utf-8") as handle:
        for record in records:
            handle.write(json.dumps(record, ensure_ascii=False) + "\n")


def _gold_with(text: str, label: str) -> dict:
    """Record gold minimal : un span [0, len) portant label."""
    return {"text": text, "labels": [[0, len(text), label]]}


BASE_ROWS = [
    {"academic_label": "Slippery slope", "best_famille": "Erreur mathematique",
     "best_name": "Pente glissante", "verdict": "DIRECT"},
    {"academic_label": "Appeal to popularity", "best_famille": "Obstruction",
     "best_name": "Appel a la bande", "verdict": "DIRECT"},
    {"academic_label": "Ad hominem", "best_famille": "Obstruction",
     "best_name": "Ad hominem", "verdict": "DIRECT"},
    {"academic_label": "Appeal to values", "best_famille": "Erreur mathematique",
     "best_name": "Appel a la probabilite", "verdict": "NOT_FOUND"},
    {"academic_label": "Fallacy of proportion", "best_famille": "Tricherie",
     "best_name": "Biais de proportionnalite", "verdict": "DIRECT"},
]


def _run(tmp_path: Path, records: list[dict], rows: list[dict] | None = None) -> tuple[Path, dict]:
    gold = tmp_path / "gold.jsonl"
    table = tmp_path / "table.csv"
    out = tmp_path / "out"
    _write_gold(gold, records)
    _write_table(table, rows if rows is not None else BASE_ROWS)
    rc = builder.main(["--gold", str(gold), "--table", str(table), "--out-dir", str(out)])
    assert rc == 0
    report = json.loads((out / "join_report.json").read_text(encoding="utf-8"))
    return out / "aligned_corpus.jsonl", report


def test_exact_join_case_insensitive(tmp_path):
    corpus_path, report = _run(tmp_path, [_gold_with("Si on ecoute les joueurs, bientot plus personne ne jouera.", "slippery slope")])
    pairs = [json.loads(l) for l in corpus_path.read_text(encoding="utf-8").splitlines()]
    assert len(pairs) == 1
    assert pairs[0]["node"] == "Erreur mathematique/Pente glissante"
    assert pairs[0]["match"] == "exact"
    assert report["joined_exact"] == 1 and report["joined_bridge"] == 0


def test_declared_bridge_with_rationale(tmp_path):
    corpus_path, report = _run(tmp_path, [_gold_with("Tout le monde le fait donc c'est vrai.", "ad populum")])
    pairs = [json.loads(l) for l in corpus_path.read_text(encoding="utf-8").splitlines()]
    assert len(pairs) == 1
    assert pairs[0]["node"] == "Obstruction/Appel a la bande"
    assert pairs[0]["match"] == "bridge:Appeal to popularity"
    stats = report["label_stats"]["ad populum"]
    assert stats["joined_bridge"] == 1
    assert stats["bridge"]["to"] == "Appeal to popularity"
    assert stats["bridge"]["rationale"]  # le pont porte toujours sa justification


def test_exclusions_motivated(tmp_path):
    _, report = _run(tmp_path, [
        _gold_with("Texte neutre.", "nothing"),
        _gold_with("Soit tu es avec nous soit contre nous.", "false dilemma"),
    ])
    assert report["pairs_total"] == 0
    assert report["excluded_by_label"] == {"false dilemma": 1, "nothing": 1}
    assert "marqueur d'absence" in report["label_stats"]["nothing"]["reason"]
    assert report["label_stats"]["false dilemma"]["reason"]


def test_notfound_table_row_never_pairs(tmp_path):
    _, report = _run(tmp_path, [_gold_with("Nos valeurs le prouvent.", "Appeal to values")])
    assert report["pairs_total"] == 0
    assert "NOT_FOUND" in report["label_stats"]["Appeal to values"]["reason"]


def test_zero_family_measured_not_omitted(tmp_path):
    _, report = _run(tmp_path, [_gold_with("Pente.", "slippery slope")])
    # Tricherie n'est touchee par aucun span du gold de test : mesuree a 0.
    assert report["family_counts"]["Tricherie"] == 0
    assert report["family_counts"]["Erreur mathematique"] == 1


def test_duplicate_labels_same_node_merged_once(tmp_path):
    """Regressrun1 (c.6373865101) : deux libelles d'un meme span roulant vers le
    meme noeud ('ad hominem' exact + 'guilt by association' pont) ne produisent
    qu'UNE paire -- la campagne run1 livree portait 2 item_id en double (le
    contenu adresse l'id) et etait refusee par le render comme par le mesureur."""
    record = {
        "text": "Delores defends equal pay, coming from someone disagreeable.",
        "labels": [
            [0, 60, "ad hominem"],
            [0, 60, "guilt by association"],
        ],
    }
    corpus_path, report = _run(tmp_path, [record])
    pairs = [json.loads(l) for l in corpus_path.read_text(encoding="utf-8").splitlines()]
    assert len(pairs) == 1
    assert pairs[0]["node"] == "Obstruction/Ad hominem"
    assert pairs[0]["source_labels"] == ["ad hominem", "guilt by association"]
    assert report["pairs_total"] == 1
    assert report["merged_duplicate_pairs"] == 1
    # Les stats par label restent au niveau du span : chaque libelle a joine.
    assert report["label_stats"]["ad hominem"]["joined_exact"] == 1
    assert report["label_stats"]["guilt by association"]["joined_bridge"] == 1


def test_distinct_pairs_never_touched_by_merge(tmp_path):
    """Deux libelles differents vers deux noeuds differents : aucune fusion."""
    corpus_path, report = _run(tmp_path, [
        _gold_with("Cas A pente glissante.", "slippery slope"),
        _gold_with("Cas B appel a la bande.", "ad populum"),
    ])
    pairs = [json.loads(l) for l in corpus_path.read_text(encoding="utf-8").splitlines()]
    assert len(pairs) == 2
    assert report["merged_duplicate_pairs"] == 0
    assert all("source_labels" not in p for p in pairs)


def test_sampler_loads_corpus(tmp_path):
    corpus_path, _ = _run(tmp_path, [
        _gold_with("Cas A pente glissante.", "slippery slope"),
        _gold_with("Cas B appel a la bande.", "ad populum"),
        _gold_with("Cas C ad hominem.", "Ad hominem"),
    ])
    loaded = sampler.load_corpus(corpus_path, "/")
    assert {r["family"] for r in loaded} == {"Erreur mathematique", "Obstruction"}
    assert all("text" in r and "node" in r for r in loaded)


# ---------------------------------------------------------------------------
# Regle des PARTIAL (ecart mecanique n°3 de #10355 §4).
#
# Une ligne PARTIAL ne porte qu'un chevauchement lexical : elle ne prouve pas
# l'identite du noeud, et le score ne les separe pas (mesure du 2026-11-08 : un
# 0,08 CORRECT -- « Circular reasoning » -> « Argument circulaire » -- voisine
# un 0,09 FAUX -- « Appeal to authority » -> « Referencement plethorique »).
# Un plancher de score serait donc un remplacement a l'aveugle : l'identite
# s'adjuge par ecrit dans PARTIAL_ADJUDICATIONS, et l'adjudication se perime
# quand la table deplace le noeud.
# ---------------------------------------------------------------------------

PARTIAL_ADJUDGED = {
    "academic_label": "Appeal to fear", "best_famille": "Influence",
    "best_name": "Appel à la terreur", "score": "0.12", "verdict": "PARTIAL",
}
PARTIAL_UNADJUDGED = {
    "academic_label": "Appeal to tradition", "best_famille": "Tricherie",
    "best_name": "Tradition", "score": "0.09", "verdict": "PARTIAL",
}


def test_partial_adjugee_entre_dans_le_corpus(tmp_path):
    """Couple (label -> noeud) adjuge : la paire entre, avec le noeud adjuge."""
    corpus_path, report = _run(
        tmp_path,
        [_gold_with("Si tu sors, il t'arrivera malheur.", "appeal to fear")],
        rows=[PARTIAL_ADJUDGED],
    )
    pairs = [json.loads(l) for l in corpus_path.read_text(encoding="utf-8").splitlines()]
    assert len(pairs) == 1
    assert pairs[0]["node"] == "Influence/Appel à la terreur"
    assert report["pairs_total"] == 1
    assert report["label_stats"]["appeal to fear"]["joined_exact"] == 1


def test_partial_non_adjugee_est_exclue_avec_motif(tmp_path):
    """Aucune adjudication : la ligne est exclue, son motif nomme le candidat."""
    corpus_path, report = _run(
        tmp_path,
        [_gold_with("On a toujours fait ainsi.", "appeal to tradition")],
        rows=[PARTIAL_UNADJUDGED],
    )
    assert corpus_path.read_text(encoding="utf-8") == ""
    assert report["pairs_total"] == 0
    assert report["excluded_by_label"] == {"appeal to tradition": 1}
    stats = report["label_stats"]["appeal to tradition"]
    assert stats["excluded"] == 1
    assert "PARTIAL non adjugee" in stats["reason"]
    assert "0.09" in stats["reason"]
    assert "Tricherie/Tradition" in stats["reason"]


def test_adjudication_perimee_est_exclue(tmp_path):
    """Une adjudication dont le noeud a bouge est perimee, pas valide."""
    stale = dict(PARTIAL_ADJUDGED, best_name="Référencement pléthorique")
    corpus_path, report = _run(
        tmp_path,
        [_gold_with("Si tu sors, il t'arrivera malheur.", "appeal to fear")],
        rows=[stale],
    )
    assert corpus_path.read_text(encoding="utf-8") == ""
    assert report["pairs_total"] == 0
    reason = report["label_stats"]["appeal to fear"]["reason"]
    assert "adjudication perimee" in reason
    assert "Appel à la terreur" in reason
    assert "Référencement pléthorique" in reason


def test_adjudication_perimee_par_changement_de_famille(tmp_path):
    """Temoin de changement de famille : le nom reste, la famille bouge.

    La ligne reelle « Appeal to fear » porte un candidat d'une autre famille
    dans sa colonne candidates (50, Insuffisance, 0.08) : un recalibrage de
    l'aligneur peut faire changer la meilleure famille sans toucher au nom.
    Si l'adjudication ne comparait que le nom, la paire entrerait sous un
    noeud « Insuffisance/Appel a la terreur » qui n'existe pas dans
    Argumentum. Les deux etats temoignent : A (famille adjugee) la paire
    entre ; B (seule la famille change) l'adjudication est perimee et le
    motif nomme les DEUX couples famille/noeud.
    """
    records = [_gold_with("Si tu sors, il t'arrivera malheur.", "appeal to fear")]
    # Etat A : la table telle qu'adjugee -- la paire entre.
    corpus_a, report_a = _run(tmp_path, records, rows=[PARTIAL_ADJUDGED])
    pairs_a = [json.loads(l) for l in corpus_a.read_text(encoding="utf-8").splitlines()]
    assert len(pairs_a) == 1
    assert pairs_a[0]["node"] == "Influence/Appel à la terreur"
    assert report_a["pairs_total"] == 1
    # Etat B : seul best_famille change (le candidat 50 passe en tete).
    state_b = tmp_path / "etat_b"
    state_b.mkdir()
    moved = dict(PARTIAL_ADJUDGED, best_famille="Insuffisance")
    corpus_b, report_b = _run(state_b, records, rows=[moved])
    assert corpus_b.read_text(encoding="utf-8") == ""
    assert report_b["pairs_total"] == 0
    reason = report_b["label_stats"]["appeal to fear"]["reason"]
    assert "adjudication perimee" in reason
    assert "Influence/Appel à la terreur" in reason
    assert "Insuffisance/Appel à la terreur" in reason

