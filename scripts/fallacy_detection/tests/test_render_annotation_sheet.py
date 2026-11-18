#!/usr/bin/env python3
"""Tests du rendu de la feuille d'annotation (#20222, grain 3).

Deux choses sont verifiees ici, et pas seulement « le script tourne » :

1. **L'aveuglement survit au rendu.** Le document remis a l'evaluateur porte
   l'espace de reponse entier (c'est sa consigne) mais **jamais** l'etiquette
   d'un item dans le bloc de cet item : le test detient la cle et la cherche
   dans chaque bloc.
2. **La chaine se referme.** Une feuille convertie est acceptee par le mesureur
   reel (``score_external_eval.load_key``/``load_raters``) : le contrat entre les
   deux organes est teste, pas suppose.

Fixtures synthetiques uniquement : aucun verbatim du corpus reel.
"""

from __future__ import annotations

import csv
import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import render_annotation_sheet as renderer
import score_external_eval as scorer

VOCAB_NODES = [
    "Appeal/Authority",
    "Appeal/Emotion",
    "Causal/Oversimplified",
    "Causal/Post_Hoc",
    "Relevance/Red_Herring",
]


def write_jsonl(path: Path, records: list[dict]) -> Path:
    path.write_text(
        "".join(json.dumps(record, ensure_ascii=False) + "\n" for record in records),
        encoding="utf-8",
    )
    return path


def make_vocab(tmp_path: Path) -> Path:
    """Vocabulaire synthetique : cinq noeuds, trois familles de premier niveau."""
    return write_jsonl(
        tmp_path / "aligned.jsonl",
        [{"text": f"exemple {index}", "node": node} for index, node in enumerate(VOCAB_NODES)],
    )


def make_sheet(tmp_path: Path, count: int = 3) -> Path:
    """Feuille aveugle synthetique, dans l'ordre du tirage."""
    return write_jsonl(
        tmp_path / "sheet.jsonl",
        [{"item_id": f"eval-{index:04d}", "text": f"Enonce numero {index}."} for index in range(count)],
    )


def run_render(tmp_path: Path, sheet: Path, vocab: Path, label: str = "reviewer-1") -> Path:
    out_dir = tmp_path / "pass1" / label
    code = renderer.main(
        [
            "render",
            "--sheet",
            str(sheet),
            "--vocab",
            str(vocab),
            "--out-dir",
            str(out_dir),
            "--label",
            label,
        ]
    )
    assert code == 0
    return out_dir


def test_render_emits_document_template_and_manifest(tmp_path: Path) -> None:
    out_dir = run_render(tmp_path, make_sheet(tmp_path), make_vocab(tmp_path))

    document = (out_dir / "annotation_reviewer-1.md").read_text(encoding="utf-8")
    answers = (out_dir / "answers_reviewer-1.csv").read_text(encoding="utf-8")
    manifest = json.loads((out_dir / "render_manifest_reviewer-1.json").read_text(encoding="utf-8"))

    assert manifest["items"] == 3
    assert manifest["families"] == 3
    assert manifest["vocabulary_nodes"] == 5
    assert manifest["issue"] == 20222
    # Le document porte les enonces ; le gabarit porte une ligne par enonce.
    assert "Enonce numero 2." in document
    rows = list(csv.DictReader(answers.splitlines()))
    assert [row["item_id"] for row in rows] == ["eval-0000", "eval-0001", "eval-0002"]
    assert all(row["node"] == "" for row in rows)


def test_manifest_is_label_named_and_refuses_overwrite(tmp_path: Path) -> None:
    """Deux evaluateurs dans le meme dossier ne s'ecrasent pas ; le meme label refuse (review #22233)."""
    sheet, vocab = make_sheet(tmp_path), make_vocab(tmp_path)
    shared = tmp_path / "pass1"

    for label in ("reviewer-1", "reviewer-2"):
        code = renderer.main(
            ["render", "--sheet", str(sheet), "--vocab", str(vocab), "--out-dir", str(shared), "--label", label]
        )
        assert code == 0
    manifests = sorted(p.name for p in shared.glob("render_manifest_*.json"))
    assert manifests == ["render_manifest_reviewer-1.json", "render_manifest_reviewer-2.json"]

    # Un second rendu du meme label ne peut pas ecraser silencieusement le manifeste pinne.
    with pytest.raises(SystemExit, match="existe deja"):
        renderer.main(
            ["render", "--sheet", str(sheet), "--vocab", str(vocab), "--out-dir", str(shared), "--label", "reviewer-1"]
        )


def test_answer_space_is_closed_and_complete(tmp_path: Path) -> None:
    out_dir = run_render(tmp_path, make_sheet(tmp_path), make_vocab(tmp_path))
    document = (out_dir / "annotation_reviewer-1.md").read_text(encoding="utf-8")
    for node in VOCAB_NODES:
        assert f"- `{node}`" in document
    for family in sorted({node.split("/")[0] for node in VOCAB_NODES}):
        assert f"### {family}" in document


def test_each_item_block_carries_no_label(tmp_path: Path) -> None:
    """L'aveuglement tient au niveau du bloc : la cle ne fuit pas dans l'item.

    Le test detient l'etiquette de chaque item et la cherche dans son propre
    bloc. L'espace de reponse, lui, la contient par construction -- c'est la
    consigne -- donc la recherche est bornee au bloc.
    """
    truth = {
        "eval-0000": "Causal/Post_Hoc",
        "eval-0001": "Appeal/Emotion",
        "eval-0002": "Relevance/Red_Herring",
    }
    sheet = write_jsonl(
        tmp_path / "sheet.jsonl",
        [{"item_id": item_id, "text": f"Enonce de {item_id}."} for item_id in truth],
    )
    out_dir = run_render(tmp_path, sheet, make_vocab(tmp_path))
    document = (out_dir / "annotation_reviewer-1.md").read_text(encoding="utf-8")

    blocks = document.split("### Enonce ")
    assert len(blocks) == len(truth) + 1
    for block in blocks[1:]:
        item_id = block.split("`")[1]
        assert item_id in truth
        assert truth[item_id] not in block, f"l'etiquette de {item_id} figure dans son bloc"


def test_render_refuses_a_leaky_sheet(tmp_path: Path) -> None:
    """Une cle de correction passee par erreur est refusee, pas rendue."""
    leaky = write_jsonl(
        tmp_path / "key.jsonl",
        [{"item_id": "eval-0000", "text": "Enonce.", "node": "Appeal/Authority"}],
    )
    with pytest.raises(SystemExit) as excinfo:
        renderer.main(
            [
                "render",
                "--sheet",
                str(leaky),
                "--vocab",
                str(make_vocab(tmp_path)),
                "--out-dir",
                str(tmp_path / "out"),
                "--label",
                "reviewer-1",
            ]
        )
    assert "node" in str(excinfo.value)


def test_render_refuses_duplicate_item_ids(tmp_path: Path) -> None:
    sheet = write_jsonl(
        tmp_path / "sheet.jsonl",
        [{"item_id": "eval-0000", "text": "a"}, {"item_id": "eval-0000", "text": "b"}],
    )
    with pytest.raises(SystemExit) as excinfo:
        renderer.main(
            [
                "render",
                "--sheet",
                str(sheet),
                "--vocab",
                str(make_vocab(tmp_path)),
                "--out-dir",
                str(tmp_path / "out"),
                "--label",
                "reviewer-1",
            ]
        )
    assert "deux fois" in str(excinfo.value)


def test_render_refuses_an_unusable_label(tmp_path: Path) -> None:
    with pytest.raises(SystemExit):
        renderer.main(
            [
                "render",
                "--sheet",
                str(make_sheet(tmp_path)),
                "--vocab",
                str(make_vocab(tmp_path)),
                "--out-dir",
                str(tmp_path / "out"),
                "--label",
                "../escape",
            ]
        )


def test_fence_adapts_to_backticks_in_text(tmp_path: Path) -> None:
    """Un texte portant un bloc de code ne doit pas fermer son propre bloc."""
    sheet = write_jsonl(
        tmp_path / "sheet.jsonl",
        [{"item_id": "eval-0000", "text": "Soit ```x``` un litteral."}],
    )
    out_dir = run_render(tmp_path, sheet, make_vocab(tmp_path))
    document = (out_dir / "annotation_reviewer-1.md").read_text(encoding="utf-8")
    assert "````" in document
    assert "Soit ```x``` un litteral." in document


def write_answers(path: Path, rows: list[tuple[str, str]]) -> Path:
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.writer(handle)
        writer.writerow(["item_id", "node"])
        writer.writerows(rows)
    return path


def run_convert(tmp_path: Path, answers: Path, vocab: Path, *extra: str) -> Path:
    out = tmp_path / "reviewer-1.jsonl"
    code = renderer.main(
        ["convert", "--answers", str(answers), "--vocab", str(vocab), "--out", str(out), *extra]
    )
    assert code == 0
    return out


def test_convert_emits_the_scorer_shape(tmp_path: Path) -> None:
    answers = write_answers(
        tmp_path / "answers.csv",
        [("eval-0000", "Causal/Post_Hoc"), ("eval-0001", "Appeal/Emotion")],
    )
    out = run_convert(tmp_path, answers, make_vocab(tmp_path))
    records = [json.loads(line) for line in out.read_text(encoding="utf-8").splitlines()]
    assert records == [
        {"item_id": "eval-0000", "node": "Causal/Post_Hoc", "family": "Causal"},
        {"item_id": "eval-0001", "node": "Appeal/Emotion", "family": "Appeal"},
    ]


def test_convert_output_is_accepted_by_the_real_scorer(tmp_path: Path) -> None:
    """Le contrat entre les deux organes : feuille convertie -> mesureur reel."""
    answers = write_answers(
        tmp_path / "answers.csv",
        [("eval-0000", "Causal/Post_Hoc"), ("eval-0001", "Appeal/Emotion")],
    )
    out = run_convert(tmp_path, answers, make_vocab(tmp_path))

    key = write_jsonl(
        tmp_path / "key.jsonl",
        [
            {"item_id": "eval-0001", "family": "Appeal", "node": "Appeal/Emotion"},
            {"item_id": "eval-0000", "family": "Causal", "node": "Causal/Post_Hoc"},
        ],
    )
    key_map = scorer.load_key(key, "/")
    annotations = tmp_path / "pass1"
    annotations.mkdir()
    (annotations / "reviewer-1.jsonl").write_text(out.read_text(encoding="utf-8"), encoding="utf-8")
    raters = scorer.load_raters(annotations, key_map, "/")
    assert raters["reviewer-1"]["eval-0000"] == {"node": "Causal/Post_Hoc", "branch": "Causal"}


def test_convert_refuses_an_unknown_node(tmp_path: Path) -> None:
    answers = write_answers(tmp_path / "answers.csv", [("eval-0000", "Causal/Posthoc")])
    with pytest.raises(SystemExit) as excinfo:
        renderer.main(
            [
                "convert",
                "--answers",
                str(answers),
                "--vocab",
                str(make_vocab(tmp_path)),
                "--out",
                str(tmp_path / "out.jsonl"),
            ]
        )
    assert "absent du vocabulaire" in str(excinfo.value)


def test_convert_refuses_duplicate_ratings(tmp_path: Path) -> None:
    answers = write_answers(
        tmp_path / "answers.csv",
        [("eval-0000", "Causal/Post_Hoc"), ("eval-0000", "Appeal/Emotion")],
    )
    with pytest.raises(SystemExit) as excinfo:
        renderer.main(
            [
                "convert",
                "--answers",
                str(answers),
                "--vocab",
                str(make_vocab(tmp_path)),
                "--out",
                str(tmp_path / "out.jsonl"),
            ]
        )
    assert "deux fois" in str(excinfo.value)


def test_convert_refuses_partial_by_default(tmp_path: Path) -> None:
    answers = write_answers(
        tmp_path / "answers.csv",
        [("eval-0000", "Causal/Post_Hoc"), ("eval-0001", ""), ("eval-0002", "")],
    )
    with pytest.raises(SystemExit) as excinfo:
        renderer.main(
            [
                "convert",
                "--answers",
                str(answers),
                "--vocab",
                str(make_vocab(tmp_path)),
                "--out",
                str(tmp_path / "out.jsonl"),
            ]
        )
    assert "2 enonce(s) non rempli(s)" in str(excinfo.value)


def test_convert_accepts_partial_only_on_request_and_reports_the_drop(tmp_path: Path) -> None:
    answers = write_answers(
        tmp_path / "answers.csv",
        [("eval-0000", "Causal/Post_Hoc"), ("eval-0001", ""), ("eval-0002", "")],
    )
    out = run_convert(tmp_path, answers, make_vocab(tmp_path), "--allow-partial")
    records = [json.loads(line) for line in out.read_text(encoding="utf-8").splitlines()]
    assert len(records) == 1
    assert records[0]["item_id"] == "eval-0000"


def test_convert_refuses_an_empty_template(tmp_path: Path) -> None:
    answers = write_answers(tmp_path / "answers.csv", [("eval-0000", ""), ("eval-0001", "")])
    with pytest.raises(SystemExit):
        renderer.main(
            [
                "convert",
                "--answers",
                str(answers),
                "--vocab",
                str(make_vocab(tmp_path)),
                "--out",
                str(tmp_path / "out.jsonl"),
                "--allow-partial",
            ]
        )


def test_end_to_end_render_then_convert_a_full_pass(tmp_path: Path) -> None:
    """Parcours complet : feuille -> document + gabarit -> feuille mesurable."""
    sheet = make_sheet(tmp_path, count=3)
    vocab = make_vocab(tmp_path)
    out_dir = run_render(tmp_path, sheet, vocab)

    answers_path = out_dir / "answers_reviewer-1.csv"
    rows = list(csv.reader(answers_path.read_text(encoding="utf-8").splitlines()))
    assert rows[0] == ["item_id", "node"]
    filled = [(rows[index][0], VOCAB_NODES[index - 1]) for index in range(1, len(rows))]
    write_answers(answers_path, filled)

    out = run_convert(tmp_path, answers_path, vocab)
    records = [json.loads(line) for line in out.read_text(encoding="utf-8").splitlines()]
    assert [record["item_id"] for record in records] == ["eval-0000", "eval-0001", "eval-0002"]
    assert all(record["node"] in VOCAB_NODES for record in records)
