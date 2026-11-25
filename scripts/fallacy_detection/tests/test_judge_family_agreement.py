#!/usr/bin/env python3
"""Tests de l'organe d'accord inter-familles (EPIC #10355, section 2a).

Tout tourne **sans reseau** : les juges sont injectes (scripted, puis muets)
et la capture du corps HTTP passe par un ``urlopen`` remplace. Le dernier bloc
relit le vrai split val committé et rejoue tirage + questionnaire — aucune
completion n'est demandee, il reste executable en CI.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

_SCRIPTS = Path(__file__).resolve().parents[2]
if str(_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(_SCRIPTS))

from fallacy_detection import generate_teacher_corpus as G  # noqa: E402
from fallacy_detection import judge_family_agreement as J  # noqa: E402

REPO = Path(__file__).resolve().parents[3]
CORPUS = REPO / "MyIA.AI.Notebooks/GenAI/FallacyDetection/data/teacher/val_fr.jsonl"


# --------------------------------------------------------------------------
# Donnees synthetiques
# --------------------------------------------------------------------------

def _texts() -> dict:
    """Mini-index de textes : 3 sophismes, 2 vertus, tous distincts de titre."""
    return {"nodes": {
        "F1": {"fr": ("Sophisme A", "Definition du sophisme A.", []),
               "en": ("Fallacy A", "Definition of fallacy A.", [])},
        "F2": {"fr": ("Sophisme B", "Definition du sophisme B.", []),
               "en": ("Fallacy B", "Definition of fallacy B.", [])},
        "F3": {"fr": ("Sophisme C", "Definition du sophisme C.", []),
               "en": ("Fallacy C", "Definition of fallacy C.", [])},
        "V1": {"fr": ("Vertu X", "Definition de la vertu X.", []),
               "en": ("Virtue X", "Definition of virtue X.", [])},
        "V2": {"fr": ("Vertu Y", "Definition de la vertu Y.", []),
               "en": ("Virtue Y", "Definition of virtue Y.", [])},
    }, "scenarios": {}}


def _records(n_per_family: int = 4) -> list[dict]:
    """Paires synthetiques : 3 familles de 4, roundtrip alterne."""
    records = []
    families = ("ad_hominem", "appeal", "equivocation")
    for family in families:
        for i in range(n_per_family):
            records.append({
                "pair_id": f"val-F{i + 1}-{family[:3]}-{i}",
                "node_key": "F1" if i % 2 == 0 else "F2",
                "polarity": "fallacy", "family": family,
                "text": f"Texte de la paire {family}-{i}.",
                "roundtrip": (i % 3 != 0),  # faux chaque 3e : 2/3 mesurables vrais
            })
    return records


class ScriptedJudge:
    """Juge injecte : rend les reponses preparees, dans l'ordre des appels."""

    def __init__(self, answers: list[str]):
        self.answers = list(answers)
        self.calls = 0

    def complete(self, prompt: str, *, max_tokens: int, temperature: float) -> G.Reply:
        answer = self.answers[min(self.calls, len(self.answers) - 1)]
        self.calls += 1
        return G.Reply(text=answer, completion_tokens=1, finish_reason="stop")


class MuteJudge:
    """Juge qui echoue au premier appel : tout appel est un defaut de test."""

    def complete(self, prompt: str, *, max_tokens: int, temperature: float) -> G.Reply:
        raise AssertionError("appel rejoue alors que le checkpoint le couvre")


# --------------------------------------------------------------------------
# Intervalle de confiance Wilson
# --------------------------------------------------------------------------

def test_wilson_ci_reference():
    # 243/280 (l'auto-accord committé) : bornes de reference calculees separement.
    lo, hi = J.wilson_ci(243, 280)
    assert abs(lo - 0.8232) < 1e-3
    assert abs(hi - 0.9026) < 1e-3


def test_wilson_ci_contains_point_estimate_and_shrinks():
    small = J.wilson_ci(8, 10)
    big = J.wilson_ci(800, 1000)
    p = 0.8
    assert small[0] < p < small[1]
    assert big[0] < p < big[1]
    assert (big[1] - big[0]) < (small[1] - small[0])


def test_wilson_ci_zero_measured_is_not_a_rate():
    assert J.wilson_ci(0, 0) is None


def test_wilson_ci_degenerate_all_hits():
    lo, hi = J.wilson_ci(10, 10)
    assert lo < 1.0
    assert hi == pytest.approx(1.0)


# --------------------------------------------------------------------------
# Tirage apparie
# --------------------------------------------------------------------------

def test_draw_pairs_proportional_and_deterministic():
    records = _records()
    drawn_a = J.draw_pairs(records, 9, seed=42)
    drawn_b = J.draw_pairs(records, 9, seed=42)
    assert [r["pair_id"] for r in drawn_a] == [r["pair_id"] for r in drawn_b]
    # 3 familles de meme taille, n divisible : quota exact de 3 chacune.
    counts = {f: sum(1 for r in drawn_a if r["family"] == f)
              for f in ("ad_hominem", "appeal", "equivocation")}
    assert counts == {"ad_hominem": 3, "appeal": 3, "equivocation": 3}
    # Ordre final trie : le tirage ne depend pas de l'ordre des lignes.
    ids = [r["pair_id"] for r in drawn_a]
    assert ids == sorted(ids)


def test_draw_pairs_largest_remainder():
    # 2 familles (3 et 1 elements), n=2 : quotas exacts 1,5/0,5 -> 2/0 ou 1/1
    # selon les restes ; dans les deux cas la somme fait n et aucune famille
    # ne depasse son effectif.
    records = [{"pair_id": f"a{i}", "family": "A", "node_key": "F1",
                "polarity": "fallacy", "text": "t", "roundtrip": True} for i in range(3)]
    records += [{"pair_id": "b0", "family": "B", "node_key": "F1",
                 "polarity": "fallacy", "text": "t", "roundtrip": False}]
    drawn = J.draw_pairs(records, 2, seed=7)
    assert len(drawn) == 2
    counts = {"A": 0, "B": 0}
    for r in drawn:
        counts[r["family"]] += 1
    assert counts["A"] <= 3 and counts["B"] <= 1


# --------------------------------------------------------------------------
# Questionnaire
# --------------------------------------------------------------------------

def test_build_questions_reuses_roundtrip_frame():
    records = _records(2)
    questions = J.build_questions(records[:2], _texts(), seed=1, distractors=1)
    assert len(questions) == 2
    question = questions[0]
    # Cadre FR octet pour octet celui du controle aller-retour.
    assert "Voici un texte :" in question.question
    assert "Reponds uniquement par la lettre." in question.question
    assert records[0]["text"] in question.question
    # Candidats = cible + 1 distracteur de meme polarite, en ordre melange.
    assert len(question.candidates) == 2
    assert question.target in question.candidates
    assert all(c[0] == question.target[0] for c in question.candidates)
    # Le titre de la cible apparait bien parmi les candidats affiches.
    titles = [line[3:].split(" : ")[0] for line in question.question.splitlines()
              if line[:2] in ("A.", "B.")]
    assert _texts()["nodes"][question.target]["fr"][0] in titles


def test_build_questions_deterministic_same_seed():
    records = _records(2)
    a = J.build_questions(records[:2], _texts(), seed=9, distractors=1)
    b = J.build_questions(records[:2], _texts(), seed=9, distractors=1)
    assert a == b


# --------------------------------------------------------------------------
# Agregation
# --------------------------------------------------------------------------

def test_summarise_unparsed_is_not_a_vote():
    summary = J.summarise_picks(
        picks=["F1", "F2", None, None], targets=["F1", "F1", "F1", "F1"],
        families=["A", "A", "A", "A"])
    assert summary["n_pairs"] == 4
    assert summary["n_measured"] == 2
    assert summary["n_unparsed"] == 2
    assert summary["hits"] == 1
    assert summary["rate"] == 0.5
    assert summary["ci95_wilson"][0] <= 0.5 <= summary["ci95_wilson"][1]


def test_summarise_by_family_buckets():
    summary = J.summarise_picks(
        picks=["F1", "F2", "F1"], targets=["F1", "F1", "F1"],
        families=["ad_hominem", "ad_hominem", "appeal"])
    assert summary["by_family"]["ad_hominem"] == {
        "n": 2, "measured": 2, "hits": 1, "rate": 0.5,
        "ci95": pytest.approx([0.0945, 0.9055], abs=1e-3)}
    assert summary["by_family"]["appeal"]["hits"] == 1


def test_auto_accord_subset_reads_roundtrip_field():
    drawn = _records()[:6]
    subset = J.auto_accord_subset(drawn)
    # [:6] = ad_hominem i0..3 (F,T,T,F) + appeal i0..1 (F,T) -> 3 vrais sur 6.
    assert subset["n_pairs"] == 6
    assert subset["n_measured"] == 6
    assert subset["hits"] == 3
    assert subset["rate"] == pytest.approx(3 / 6)


# --------------------------------------------------------------------------
# Client : hygiene de secrets et de dialecte
# --------------------------------------------------------------------------

def test_openai_judge_requires_key(monkeypatch):
    monkeypatch.delenv("OPENAI_API_KEY", raising=False)
    with pytest.raises(ValueError, match="OPENAI_API_KEY absente"):
        J.OpenAIJudge(name="openai", url="https://example.invalid/v1/chat/completions",
                      model="x", api_key_env="OPENAI_API_KEY")


def test_openai_judge_body_has_no_vllm_dialect(monkeypatch):
    captured = {}

    class _Resp:
        def read(self):
            return json.dumps({"choices": [{"message": {"content": "B"},
                                            "finish_reason": "stop"}],
                               "usage": {"completion_tokens": 1, "prompt_tokens": 9}}).encode()

        def __enter__(self):
            return self

        def __exit__(self, *args):
            return False

    def _fake_urlopen(req, timeout=None):
        captured["body"] = json.loads(req.data.decode("utf-8"))
        captured["headers"] = req.headers
        return _Resp()

    monkeypatch.setattr(J.urllib.request, "urlopen", _fake_urlopen)
    judge = J.OpenAIJudge(name="openai", url="https://example.invalid/v1/chat/completions",
                          model="gpt-test", api_key_env="OPENAI_API_KEY", api_key="k-test")
    reply = judge.complete("question", max_tokens=400, temperature=0.0)
    assert reply.text == "B"
    assert reply.prompt_tokens == 9
    body = captured["body"]
    assert body["model"] == "gpt-test"
    assert body["temperature"] == 0.0
    # Le dialecte thinking est vLLM maison : les API publiques le rejettent.
    assert "chat_template_kwargs" not in body
    assert captured["headers"]["Authorization"] == "Bearer k-test"


# --------------------------------------------------------------------------
# Mesure : checkpoint et reprise
# --------------------------------------------------------------------------

def test_run_measurement_checkpoint_and_resume(tmp_path):
    records = _records(2)[:3]
    texts = _texts()
    questions = J.build_questions(records, texts, seed=3, distractors=1)
    targets = [q.candidates.index(q.target) for q in questions]
    letters = ["ABCDEFGH"[i] for i in targets]
    first = ScriptedJudge(letters)
    picks = J.run_measurement({"j1": first}, questions, tmp_path, sleep=lambda _: None)
    assert first.calls == 3
    assert picks["j1"] == {q.pair_id: q.target for q in questions}
    checkpoint = tmp_path / "judge_family_agreement.checkpoint.jsonl"
    rows = [json.loads(line) for line in checkpoint.read_text(encoding="utf-8").splitlines()]
    assert len(rows) == 3
    assert all(row["pick"] == row["target"] for row in rows)

    # Reprise : un juge muet ne doit jamais etre appele, tout est servi du
    # checkpoint — c'est la propriete qui rend un run interrompu rejouable.
    resumed = J.run_measurement({"j1": MuteJudge()}, questions, tmp_path,
                                 sleep=lambda _: None)
    assert resumed["j1"] == picks["j1"]


def test_run_measurement_unparsed_pick_is_none(tmp_path):
    records = _records(2)[:2]
    questions = J.build_questions(records, _texts(), seed=5, distractors=1)
    judge = ScriptedJudge(["aucune idee", "peut-etre C ou D"])
    picks = J.run_measurement({"j1": judge}, questions, tmp_path, sleep=lambda _: None)
    assert all(pick is None for pick in picks["j1"].values())


def test_load_picks_report_falls_back_to_committed_report(tmp_path):
    # Sans checkpoint (clone frais), les picks viennent du rapport committé.
    report = {"per_pair": [
        {"pair_id": "p1", "picks": {"j1": "F1", "j2": None}},
        {"pair_id": "p2", "picks": {"j1": "F2", "j2": "F1"}},
    ]}
    (tmp_path / "judge_family_agreement.json").write_text(
        json.dumps(report), encoding="utf-8")
    picks = J.load_picks_for_report(tmp_path, ["j1", "j2"])
    assert picks["j1"] == {"p1": "F1", "p2": "F2"}
    assert picks["j2"] == {"p1": None, "p2": "F1"}


def test_load_picks_report_prefers_local_checkpoint(tmp_path):
    # Un run partiel local ne s'efface jamais derriere un rapport publie.
    (tmp_path / "judge_family_agreement.json").write_text(
        json.dumps({"per_pair": [{"pair_id": "p1", "picks": {"j1": "F2"}}]}),
        encoding="utf-8")
    (tmp_path / "judge_family_agreement.checkpoint.jsonl").write_text(
        json.dumps({"judge": "j1", "pair_id": "p1", "pick": "F1",
                    "target": "F1"}) + "\n", encoding="utf-8")
    picks = J.load_picks_for_report(tmp_path, ["j1"])
    assert picks["j1"] == {"p1": "F1"}


def test_load_picks_report_nothing_to_replay(tmp_path):
    with pytest.raises(FileNotFoundError):
        J.load_picks_for_report(tmp_path, ["j1"])


def test_report_written_with_sha256(tmp_path):
    records = _records(2)[:4]
    texts = _texts()
    questions = J.build_questions(records, texts, seed=11, distractors=1)
    letters = ["ABCDEFGH"[q.candidates.index(q.target)] for q in questions]
    picks = J.run_measurement({"j1": ScriptedJudge(letters)}, questions, tmp_path,
                               sleep=lambda _: None)
    picks_by_judge = {"j1": picks["j1"]}
    meta = [{"name": "j1", "family": "Test", "model": "fake-1",
             "url": "https://example.invalid"}]
    json_path, md_path = J.write_report(
        tmp_path, meta, picks_by_judge, questions, records,
        corpus_path=CORPUS,
        params={"seed": 11, "n_pairs": len(records), "distractors": 1,
                "temperature": 0.0, "max_tokens": 400, "lang": "fr"})
    report = json.loads(json_path.read_text(encoding="utf-8"))
    assert report["schema"] == 1
    assert report["corpus"]["n_total"] == 280
    assert len(report["corpus"]["sha256"]) == 64
    assert report["judges"][0]["hits"] == report["judges"][0]["n_measured"]
    md = md_path.read_text(encoding="utf-8")
    # Le SHA-256 du rapport JSON ne peut pas vivre dans le JSON : il est pose
    # dans le rendu markdown.
    assert J.sha256_file(json_path) in md
    assert "generateur (auto-accord, sous-ensemble)" in md


# --------------------------------------------------------------------------
# Corpus reel : tirage rejouable, aucune completion demandee
# --------------------------------------------------------------------------

def test_real_corpus_draw_and_questions():
    records = J.load_corpus(CORPUS)
    assert len(records) == 280
    drawn = J.draw_pairs(records, 200, seed=42)
    assert len(drawn) == 200
    corpus_ids = {r["pair_id"] for r in records}
    assert all(r["pair_id"] in corpus_ids for r in drawn)
    # Stratification proportionnelle : chaque famille garde son poids (+/- 1).
    total_by_family = {}
    for r in records:
        total_by_family[r["family"]] = total_by_family.get(r["family"], 0) + 1
    for family, total in total_by_family.items():
        drawn_n = sum(1 for r in drawn if r["family"] == family)
        assert abs(drawn_n - 200 * total / 280) <= 1
    # Le questionnaire se construit sur la vraie taxonomie (5 distracteurs de
    # meme polarite), sans aucun appel reseau.
    texts = G.B.load_texts()
    questions = J.build_questions(drawn, texts, seed=42)
    assert len(questions) == 200
    assert all(len(q.candidates) == 6 for q in questions)
    assert all(q.target in q.candidates for q in questions)
    # Determinisme : meme graine, meme questionnaire.
    again = J.build_questions(J.draw_pairs(records, 200, seed=42), texts, seed=42)
    assert again == questions
    # L'auto-accord du sous-ensemble se calcule sans appel.
    subset = J.auto_accord_subset(drawn)
    assert subset["n_measured"] == 200
    assert 0.75 <= subset["rate"] <= 0.95  # 0,8679 global attendu
