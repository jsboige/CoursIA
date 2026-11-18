"""Tests hermetiques du lot apparie (#10355, section 2b).

Le maitre est injecte : aucune completion reseau. Les controles reconnaissent
les titres dans les questions lettrees, ce qui verifie le vote et non une lettre
fixe soumise a la loterie du melange.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

_SCRIPTS = Path(__file__).resolve().parents[2]
if str(_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(_SCRIPTS))

from fallacy_detection import cartesian_dataset_builder as B  # noqa: E402
from fallacy_detection import generate_teacher_corpus as G  # noqa: E402
from fallacy_detection import paired_scenario_corpus as P  # noqa: E402


def _texts() -> dict:
    nodes = {
        f"F{i}": {"fr": (f"Sophisme {i}", f"Definition du sophisme {i}.", []),
                  "en": (f"Fallacy {i}", f"Definition of fallacy {i}.", [])}
        for i in range(1, 9)
    }
    nodes.update({
        f"V{i}": {"fr": (f"Vertu {i}", f"Definition de la vertu {i}.", []),
                  "en": (f"Virtue {i}", f"Definition of virtue {i}.", [])}
        for i in range(1, 9)
    })
    scenario = {
        "path": "s/1", "title": "Scenario EN", "smoothTalker": "Locuteur EN",
        "drawer": "Auditeur EN", "context": "Contexte EN", "issue": "Position EN",
        "titre": "Scenario FR", "baratineur": "Meme locuteur",
        "piocheur": "Meme auditeur", "contexte": "Contexte FR", "enjeu": "Meme position",
    }
    return {"nodes": nodes, "scenarios": {"s/1": scenario}}


def _record(pk: int = 1, pair_id: str = "val-F1-s/1") -> dict:
    return {
        "pair_id": pair_id, "split": "val", "polarity": "fallacy", "node_pk": pk,
        "node_key": f"F{pk}", "family": "Famille", "depth": 2, "is_leaf": True,
        "scenario_path": "s/1", "text": "Texte positif valide par le corpus.",
        "completion_tokens": 50, "finish_reason": "stop", "roundtrip": True,
    }


def _reply(text: str, tokens: int = 60) -> G.Reply:
    return G.Reply(text=text, completion_tokens=tokens, finish_reason="stop")


def _choose(title: str):
    def answer(prompt: str) -> G.Reply:
        for line in prompt.splitlines():
            if len(line) > 3 and line[1] == "." and line[3:].startswith(title + " :"):
                return _reply(line[0], 3)
        raise AssertionError(f"candidat {title!r} absent du vote")
    return answer


class ScriptedTeacher:
    def __init__(self, script):
        self.script = list(script)
        self.calls: list[str] = []

    def complete(self, prompt: str, *, max_tokens: int, temperature: float) -> G.Reply:
        self.calls.append(prompt)
        if not self.script:
            raise AssertionError("maitre scripte a court de reponses")
        item = self.script.pop(0)
        return item(prompt) if callable(item) else item


def test_positive_prompt_reused_and_loyal_prompt_keeps_roles():
    texts = _texts()
    pair = P.pair_from_record(_record())
    positive = B.render_prompt(pair, texts, "fr")
    negative = P.render_loyal_prompt(pair, texts, "fr")
    assert "commits the fallacy" in positive
    assert "defending the speaker's position loyally" in negative
    for field in ("Scenario FR", "Contexte FR", "Meme position", "Meme locuteur", "Meme auditeur"):
        assert field in positive and field in negative
    assert "Sophisme 1" not in negative
    assert "Do not name it" not in negative


def test_only_explicitly_validated_fallacies_are_selected():
    eligible = [_record(pk=1, pair_id="val-F1-a"), _record(pk=2, pair_id="val-F2-b")]
    rejected = _record(pk=3, pair_id="val-F3-c")
    rejected["roundtrip"] = False
    virtue = _record(pk=4, pair_id="val-V4-d")
    virtue["polarity"] = "virtue"
    selected = P.select_positive_pairs([rejected, virtue, *eligible], 2, 42)
    assert [row["pair_id"] for row in selected] == ["val-F1-a", "val-F2-b"]
    with pytest.raises(ValueError):
        P.select_positive_pairs(eligible, 0, 42)


def test_oppositions_resolve_pk_targets_without_approximate_titles(tmp_path):
    path = tmp_path / "virtues.csv"
    path.write_text(
        "pk,path,family_fr,crossLink_Opposes\n"
        "10,1,Famille,1;3;bad\n11,2,Famille,3\n12,3,Famille,\n",
        encoding="utf-8")
    assert P.load_virtue_oppositions(path) == {"F1": ("V10",), "F3": ("V10", "V11")}
    assert P.counterpart_virtues("F2", P.load_virtue_oppositions(path)) == ()


def test_make_vote_is_deterministic_and_same_polarity():
    texts = _texts()
    first = P.make_vote("texte", "F1", texts, seed=42, distractors=5)
    second = P.make_vote("texte", "F1", texts, seed=42, distractors=5)
    assert first == second
    assert len(first["candidates"]) == 6
    assert all(key.startswith("F") for key in first["candidates"])
    assert G.parse_choice(_choose("Sophisme 1")(first["question"]).text,
                          first["candidates"]) == "F1"


@pytest.mark.parametrize("picks,target,expected", [
    (["F2"], "F1", "accepted"),
    (["F1"], "F1", "target_reclassified"),
    ([None], "F1", "vote_unparsed"),
    ([], "F1", "vote_missing"),
])
def test_classify_attempt_is_fail_closed(picks, target, expected):
    assert P.classify_attempt(picks, target) == expected


def test_negative_control_rejects_target_and_accepts_linked_virtue():
    teacher = ScriptedTeacher([_choose("Sophisme 2"), _choose("Vertu 7"), _choose("Vertu 7")])
    control, reasons = P.evaluate_negative(
        "Defense loyale", "F1", ("V7", "V8"), _texts(), teacher,
        seed=42, distractors=5)
    assert reasons == []
    assert control["fallacy_rejected"] is True
    assert control["virtue_reclassified"] is True


def test_negative_control_missing_vote_is_not_absence_proof():
    teacher = ScriptedTeacher([_reply("aucune idee", 3)])
    control, reasons = P.evaluate_negative(
        "Defense douteuse", "F1", (), _texts(), teacher, seed=42, distractors=5)
    assert reasons == ["negative_vote_unparsed"]
    assert control["fallacy_rejected"] is False


def test_negative_control_requires_virtue_when_taxonomy_provides_one():
    teacher = ScriptedTeacher([_choose("Sophisme 2"), _choose("Vertu 2")])
    _control, reasons = P.evaluate_negative(
        "Defense loyale", "F1", ("V7",), _texts(), teacher, seed=42, distractors=5)
    assert reasons == ["virtue_not_reclassified"]


def test_generate_pair_accepts_and_pairs_same_speaker():
    teacher = ScriptedTeacher([
        _reply("Une defense loyale de la meme position, avec une raison verifiable."),
        _choose("Sophisme 2"), _choose("Vertu 7"),
    ])
    result = P.generate_pair(
        _record(), _texts(), teacher, oppositions={"F1": ("V7",)}, seed=42)
    assert result["status"] == "accepted"
    positive, negative = result["arms"]
    P.validate_pair(result["arms"])
    assert positive.text == "Texte positif valide par le corpus."
    assert positive.speaker == negative.speaker == "Meme locuteur"
    assert positive.speaker_role == negative.speaker_role == "smoothTalker"
    assert positive.control["source_prompt"] == B.render_prompt(
        P.pair_from_record(_record()), _texts(), "fr")
    assert len(teacher.calls) == 3


def test_generate_pair_retries_then_rejects_with_named_reason():
    teacher = ScriptedTeacher([
        _reply("Court", 3),
        _reply("Une defense qui reproduit exactement le sophisme cible.", 50),
        _choose("Sophisme 1"),
    ])
    result = P.generate_pair(
        _record(), _texts(), teacher, oppositions={}, seed=42, max_attempts=2)
    assert result["status"] == "rejected"
    assert result["arms"] == []
    assert result["attempts"][0]["rejection_reasons"] == ["negative_below_token_floor"]
    assert result["attempts"][1]["rejection_reasons"] == ["negative_target_reclassified"]


def test_validate_pair_refuses_unchecked_negative():
    result = P.generate_pair(
        _record(), _texts(), ScriptedTeacher([
            _reply("Une defense loyale de la meme position, avec une raison verifiable."),
            _choose("Sophisme 2")]), oppositions={}, seed=42)
    positive, negative = result["arms"]
    negative.control["fallacy_rejected"] = False
    with pytest.raises(ValueError, match="non controle"):
        P.validate_pair([positive, negative])


def test_role_shortcut_is_chance_on_balanced_pairs():
    result = P.generate_pair(
        _record(), _texts(), ScriptedTeacher([
            _reply("Une defense loyale de la meme position, avec une raison verifiable."),
            _choose("Sophisme 2")]), oppositions={}, seed=42)
    metric = P.role_shortcut(result["arms"])
    assert metric["best_role_only_accuracy"] == 0.5
    assert metric["by_role"]["smoothTalker"] == {
        "n": 2, "with_fallacy": 1, "without_fallacy": 1, "fallacy_rate": 0.5}


def test_checkpoint_resume_does_not_call_completed_pair(tmp_path):
    existing = {"pair_id": "val-F1-s/1", "status": "rejected", "arms": [], "attempts": []}
    (tmp_path / P.CHECKPOINT_NAME).write_text(json.dumps(existing) + "\n", encoding="utf-8")
    second = _record(pk=2, pair_id="val-F2-s/1")
    teacher = ScriptedTeacher([
        _reply("Une defense loyale de la meme position, avec une raison verifiable."),
        _choose("Sophisme 3"),
    ])
    P.run_generation([_record(), second], _texts(), teacher, out_dir=tmp_path,
                     oppositions={}, seed=42, lang="fr", distractors=5,
                     max_attempts=2, max_tokens=300)
    assert len(teacher.calls) == 2
    assert [row["pair_id"] for row in P.load_checkpoint(tmp_path / P.CHECKPOINT_NAME)] == [
        "val-F1-s/1", "val-F2-s/1"]


def test_write_and_replay_report_without_checkpoint(tmp_path):
    texts = _texts()
    result = P.generate_pair(
        _record(), texts, ScriptedTeacher([
            _reply("Une defense loyale de la meme position, avec une raison verifiable."),
            _choose("Sophisme 2")]), oppositions={}, seed=42)
    source = tmp_path / "source.jsonl"
    source.write_text(json.dumps(_record()) + "\n", encoding="utf-8")
    report_path, _ = P.write_report(
        tmp_path, [result], corpus_path=tmp_path / P.CORPUS_NAME,
        source_corpus=source, params={"seed": 42}, provenance="checkpoint_local")
    (tmp_path / P.CHECKPOINT_NAME).write_text("", encoding="utf-8")
    (tmp_path / P.CHECKPOINT_NAME).unlink()
    results, provenance = P.load_results_for_report(tmp_path)
    assert provenance == "rapport_publie"
    assert [row["pair_id"] for row in results] == [result["pair_id"]]
    assert [row["status"] for row in results] == ["accepted"]
    assert results[0]["attempts"] == result["attempts"]
    report = json.loads(report_path.read_text(encoding="utf-8"))
    assert report["n_accepted_pairs"] == 1
    assert report["n_rows"] == 2
    assert report["role_shortcut"]["best_role_only_accuracy"] == 0.5
    assert len(report["corpus"]["sha256"]) == 64


def test_write_report_preserves_rejection_reasons(tmp_path):
    result = P.generate_pair(
        _record(), _texts(), ScriptedTeacher([
            _reply("Une defense qui reproduit exactement le sophisme cible."),
            _choose("Sophisme 1")]), oppositions={}, seed=42, max_attempts=1)
    source = tmp_path / "source.jsonl"
    source.write_text(json.dumps(_record()) + "\n", encoding="utf-8")
    report_path, _ = P.write_report(
        tmp_path, [result], corpus_path=tmp_path / P.CORPUS_NAME,
        source_corpus=source, params={}, provenance="checkpoint_local")
    report = json.loads(report_path.read_text(encoding="utf-8"))
    assert (tmp_path / P.CORPUS_NAME).read_text(encoding="utf-8") == ""
    assert report["rejection_reasons_final_attempt"] == {"negative_target_reclassified": 1}


def test_real_taxonomy_has_counterparts_but_not_for_every_fallacy():
    oppositions = P.load_virtue_oppositions()
    assert oppositions
    assert all(key.startswith("F") for key in oppositions)
    assert all(virtue.startswith("V") for values in oppositions.values() for virtue in values)


def test_published_artifacts_are_lf_and_fingerprint_matches_blob(tmp_path):
    """Les empreintes citees doivent etre reproductibles sur le blob committe.

    Sur Windows, write_text sans newline traduit en CRLF ; git normalise alors
    CRLF -> LF au commit et l'empreinte du worktree ne correspond plus au blob.
    Les artefacts publies s'ecrivent donc en LF : disque == blob committé.
    """
    texts = _texts()
    result = P.generate_pair(
        _record(), texts, ScriptedTeacher([
            _reply("Une defense loyale de la meme position, avec une raison verifiable."),
            _choose("Sophisme 2")]), oppositions={}, seed=42)
    source = tmp_path / "source.jsonl"
    source.write_text(json.dumps(_record()) + "\n", encoding="utf-8")
    corpus_path = tmp_path / P.CORPUS_NAME
    _report_path, _md_path = P.write_report(
        tmp_path, [result], corpus_path=corpus_path,
        source_corpus=source, params={}, provenance="checkpoint_local")
    for path in (corpus_path, tmp_path / P.REPORT_NAME, tmp_path / P.REPORT_MD_NAME):
        data = path.read_bytes()
        assert b"\r" not in data, f"{path.name} doit etre ecrit en LF"
    report = json.loads((tmp_path / P.REPORT_NAME).read_text(encoding="utf-8"))
    assert report["corpus"]["sha256"] == P.sha256_file(corpus_path)


def test_report_only_does_not_construct_teacher(monkeypatch, tmp_path):
    monkeypatch.setattr(P.G, "HubTeacher", lambda **_kwargs: (_ for _ in ()).throw(
        AssertionError("--report-only ne doit pas construire de maitre")))
    result = {"pair_id": "val-F1-s/1", "status": "rejected", "arms": [], "attempts": []}
    (tmp_path / P.CHECKPOINT_NAME).write_text(json.dumps(result) + "\n", encoding="utf-8")
    source = tmp_path / "source.jsonl"
    source.write_text(json.dumps(_record()) + "\n", encoding="utf-8")
    rc = P.main(["--report-only", "--corpus", str(source), "--out-dir", str(tmp_path),
                 "--limit", "1"])
    assert rc == 0
    assert (tmp_path / P.REPORT_NAME).exists()
