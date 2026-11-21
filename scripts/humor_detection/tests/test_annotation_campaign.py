"""Tests hors reseau de la campagne ColBERT et de ses reprises (#20301)."""
from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from fallacy_detection.generate_teacher_corpus import Reply  # noqa: E402
from humor_detection import annotation_campaign as C  # noqa: E402


class ScriptedTeacher:
    def __init__(self, answers: list[str], prompt_tokens: int = 11):
        self.answers = list(answers)
        self.prompt_tokens = prompt_tokens
        self.prompts: list[str] = []

    def complete(self, prompt: str, *, max_tokens: int, temperature: float) -> Reply:
        self.prompts.append(prompt)
        answer = self.answers.pop(0) if self.answers else "Z"
        return Reply(answer, 5, "stop", self.prompt_tokens)


class MuteTeacher:
    def complete(self, prompt: str, *, max_tokens: int, temperature: float) -> Reply:
        raise AssertionError("un vote couvert par le checkpoint ne doit pas etre rejoue")


def _csv(path: Path, body: str) -> Path:
    path.write_text("text,humor\n" + body, encoding="utf-8", newline="\n")
    return path


def test_load_corpus_preserves_controls_and_multiline_csv(tmp_path):
    path = _csv(tmp_path / "corpus.csv",
                '"A headline, not a joke",False\n"Line one\nLine two",True\n')
    items = C.load_corpus(path)
    assert [(item.text, item.humor) for item in items] == [
        ("A headline, not a joke", False), ("Line one\nLine two", True)]
    assert [item.item_id for item in items] == ["colbert-000000", "colbert-000001"]


def test_load_corpus_rejects_bad_label_or_text(tmp_path):
    with pytest.raises(ValueError, match="etiquette"):
        C.load_corpus(_csv(tmp_path / "bad.csv", "texte,inconnu\n"))
    with pytest.raises(ValueError, match="texte vide"):
        C.load_corpus(_csv(tmp_path / "empty.csv", " ,True\n"))


def test_stratified_draw_balances_and_is_independent_of_order():
    items = [C.CorpusItem(f"i-{index}", str(index), index < 3) for index in range(6)]
    first = C.stratified_draw(items, 4, seed=7)
    second = C.stratified_draw(list(reversed(items)), 4, seed=7)
    assert first == second
    assert sum(item.humor for item in first) == 2
    assert [item.item_id for item in first] == sorted(item.item_id for item in first)


def test_annotate_uses_actual_usage_and_records_unparsed_roundtrip():
    item = C.CorpusItem("i1", "texte", True)
    rows = C.annotate_item(item, "a", "famille", "m", ScriptedTeacher(["A", "B", "Z"]))
    assert [row["task"] for row in rows] == ["forme", "intensite", "roundtrip"]
    assert rows[0]["label"] == "pun" and rows[1]["label"] == "1"
    assert rows[2]["label"] is None and rows[2]["parse_failed"]
    assert all(row["prompt_tokens"] == 11 for row in rows)
    assert all(row["prompt_tokens_source"] == "api" for row in rows)
    assert sum(row["completion_tokens"] for row in rows) == 15


def test_resume_after_forme_parse_failure_never_duplicates_votes(tmp_path):
    item = C.CorpusItem("i1", "texte", True)
    first = ScriptedTeacher(["Z", "A"])
    produced = C.annotate_item(item, "a", "f", "m", first)
    C._append_jsonl(tmp_path / "annotations.jsonl", produced)
    resumed = C.annotate_item(item, "a", "f", "m", MuteTeacher(), existing=produced)
    assert resumed == []


def test_run_campaign_resumes_complete_and_refuses_duplicates(tmp_path):
    items = [C.CorpusItem("i1", "texte", True)]
    clients = {
        "a": ("F1", "m1", ScriptedTeacher(["A", "A", "A"])),
        "b": ("F2", "m2", ScriptedTeacher(["A", "B", "A"])),
    }
    report = C.run_campaign(items, clients, tmp_path, chance_draws=20)
    assert report["n_annotations"] == 6
    assert report["roundtrip_agreement"]["pairwise"]["a vs b"]["n"] == 1
    corpus = _csv(tmp_path / "corpus.csv", "texte,True\n")
    manifest = C.run_campaign(items, {"a": ("F1", "m1", MuteTeacher()),
                                      "b": ("F2", "m2", MuteTeacher())}, tmp_path,
                              corpus_path=corpus)
    import hashlib
    assert manifest["corpus_sha256"] == hashlib.sha256(corpus.read_bytes()).hexdigest()
    assert manifest["sample_item_ids"] == ["i1"]
    assert "texte" not in json.dumps(manifest)
    before = (tmp_path / "annotations.jsonl").read_bytes()
    C.run_campaign(items, {"a": ("F1", "m1", MuteTeacher()),
                           "b": ("F2", "m2", MuteTeacher())}, tmp_path)
    assert (tmp_path / "annotations.jsonl").read_bytes() == before
    C._append_jsonl(tmp_path / "annotations.jsonl", [json.loads(before.splitlines()[0])])
    with pytest.raises(ValueError, match="checkpoint duplique"):
        C.run_campaign(items, clients, tmp_path)


def test_unparsed_roundtrip_is_counted_not_sent_to_kappa(tmp_path):
    item = C.CorpusItem("i1", "texte", True)
    clients = {
        "a": ("F1", "m1", ScriptedTeacher(["A", "A", "Z"])),
        "b": ("F2", "m2", ScriptedTeacher(["A", "B", "A"])),
    }
    report = C.run_campaign([item], clients, tmp_path, chance_draws=20)
    assert report["parse_failures"] == {"roundtrip": 1}
    assert report["roundtrip_agreement"]["pairwise"] == {}
    assert report["roundtrip"]["a"] == {
        "measured": 0, "unparsed": 1, "same_label": 0, "rate": None,
    }
    assert report["roundtrip"]["b"]["measured"] == 1


def test_disagreement_adds_justified_vote_and_full_cost(tmp_path):
    items = [C.CorpusItem("i1", "texte", True), C.CorpusItem("i2", "autre", False)]
    clients = {
        "a": ("F1", "m1", ScriptedTeacher(["A", "A", "B", "A", "B", "B"])),
        "b": ("F2", "m2", ScriptedTeacher(["A", "B", "A", "B", "A", "B",
                                           "Justification. reponse : B"])),
    }
    report = C.run_campaign(items, clients, tmp_path, chance_draws=20)
    assert report["n_disambiguation"] == 1
    assert report["token_cost"]["total_tokens"] == 13 * 16
    assert "Justifie d'abord" in clients["b"][2].prompts[-1]
    before = (tmp_path / "annotations.jsonl").read_bytes()
    C.run_campaign(items, {"a": ("F1", "m1", MuteTeacher()),
                           "b": ("F2", "m2", MuteTeacher())}, tmp_path)
    assert (tmp_path / "annotations.jsonl").read_bytes() == before


def test_par_forme_is_anchor_conditioned_not_human_ground_truth():
    records = []
    for item in ("i1", "i2", "i3"):
        for annotator, initial, final in (("a", "pun", "sociale"),
                                          ("b", "pun", "pun")):
            for task, label in (("forme", initial), ("intensite", "1"),
                                ("roundtrip", final)):
                records.append({"id": item, "annotator": annotator, "task": task,
                                "label": label, "parse_failed": False,
                                "prompt_tokens": 2, "completion_tokens": 3})
    report = C.campaign_report(records, [C.CorpusItem("i1", "x", True)], chance_draws=20)
    assert report["roundtrip_agreement"]["pairwise"]["a vs b"]["n"] == 3
    for task in ("forme", "roundtrip"):
        assert set(report["par_forme"][task]) == {"a", "b"}
        assert report["par_forme"][task]["a"]["pun"]["pairwise"]["a vs b"]["n"] == 3
    assert "pas verite humaine" in report["par_forme_note"]
    assert report["token_cost"]["total_tokens"] == 18 * 5
    assert report["chance"]["n_draws"] == 20


def test_env_path_is_explicit_and_values_stay_out_of_report(tmp_path):
    env = _csv(tmp_path / "not-used.csv", "x,False\n")
    secret_path = tmp_path / ".env"
    secret_path.write_text("# comment\nVLLM_API_KEY=secret-de-test\n", encoding="utf-8")
    assert C.load_shared_env(secret_path)["VLLM_API_KEY"] == "secret-de-test"
    report = C.campaign_report([], [C.CorpusItem("i", "x", True)])
    assert "secret-de-test" not in json.dumps(report)
    assert env.exists()


def test_build_clients_passes_file_credentials_without_network(monkeypatch):
    captured = {}

    class Client:
        def __init__(self, *args, **kwargs):
            captured["args"] = args
            captured["kwargs"] = kwargs
            captured["secret"] = kwargs.get("api_key")

        def complete(self, prompt, **kwargs):
            raise AssertionError("la construction des clients ne fait aucun appel")

    monkeypatch.setattr(C, "OpenAIJudge", Client)
    monkeypatch.setattr(C.G, "HubTeacher", Client)
    monkeypatch.delenv("CLAUDISH_PROXY_KEY", raising=False)
    clients = C.build_clients({"CLAUDISH_PROXY_KEY": "credential-only-in-test",
                               "VLLM_API_KEY": "hub-credential-only-in-test"})
    assert clients["claudish"][0] == "GLM (claudish)"
    assert clients["claudish"][1] == "glm-5.2"
    assert captured["secret"] == "credential-only-in-test"
    assert captured["args"][1] == "https://models.myia.io/v1/chat/completions"
    assert clients["qwen"][0] == "Qwen"


def test_main_dry_run_never_builds_a_network_client(tmp_path, monkeypatch):
    path = _csv(tmp_path / "corpus.csv", "controle,False\nblague,True\n")

    def fail_if_called(*args, **kwargs):
        raise AssertionError("le dry-run ne doit pas construire de client reseau")

    monkeypatch.setattr(C, "build_clients", fail_if_called)
    assert C.main(["--corpus", str(path), "--out", str(tmp_path / "out"),
                   "--limit", "2", "--dry-run"]) == 0
