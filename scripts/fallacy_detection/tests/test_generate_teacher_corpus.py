#!/usr/bin/env python3
"""Tests de l'organe de generation enseignant (tranche B, EPIC #10355, #17578).

Tout tourne **sans reseau** : le maitre est injecte (``FakeTeacher``) et rend les
reponses preparees par le test. Le dernier bloc relit les vraies paires du depot
et confronte leur compte au manifeste de la tranche A — il ne rend aucune
generation, donc il reste executable en CI.
"""
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

_SCRIPTS = Path(__file__).resolve().parents[2]
if str(_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(_SCRIPTS))

from fallacy_detection import cartesian_dataset_builder as B  # noqa: E402
from fallacy_detection import generate_teacher_corpus as G  # noqa: E402

REPO = Path(__file__).resolve().parents[3]
PHASE2 = REPO / "MyIA.AI.Notebooks/GenAI/FallacyDetection/data/phase2"
MANIFEST = PHASE2 / "manifest.json"


# --------------------------------------------------------------------------
# Donnees synthetiques
# --------------------------------------------------------------------------

def _texts() -> dict:
    """Mini-index de textes : 4 noeuds (2 sophismes, 2 vertus) et 1 scenario."""
    nodes = {
        "F1": {"fr": ("Sophisme A", "Definition du sophisme A.", ["un exemple assez long pour compter"]),
               "en": ("Fallacy A", "Definition of fallacy A.", ["an example long enough to count here"])},
        "F2": {"fr": ("Sophisme B", "Definition du sophisme B.", []),
               "en": ("Fallacy B", "Definition of fallacy B.", [])},
        "F3": {"fr": ("Sophisme C", "Definition du sophisme C.", []),
               "en": ("Fallacy C", "Definition of fallacy C.", [])},
        "V1": {"fr": ("Vertu A", "Definition de la vertu A.", ["un exemple de vertu assez long"]),
               "en": ("Virtue A", "Definition of virtue A.", ["an example of virtue long enough"])},
        "V2": {"fr": ("Vertu B", "Definition de la vertu B.", []),
               "en": ("Virtue B", "Definition of virtue B.", [])},
    }
    scenario = {
        "path": "scen/001.csv",
        "title": "Titre EN", "smoothTalker": "Le baratineur EN", "drawer": "Le piocheur EN",
        "context": "Contexte EN", "issue": "Enjeu EN",
        "titre": "Titre FR", "baratineur": "Le baratineur", "piocheur": "Le piocheur",
        "contexte": "Contexte FR", "enjeu": "Enjeu FR",
    }
    return {"nodes": nodes, "scenarios": {scenario["path"]: scenario}}


def _pair(polarity: str = "fallacy", node_pk: int = 1) -> B.Pair:
    return B.Pair(pair_id="val-F1-1", split="val", polarity=polarity, node_pk=node_pk,
                  family="Fam", depth=2, is_leaf=True, scenario_path="scen/001.csv")


class FakeTeacher:
    """Maitre scriptable : rend les reponses preparees, dans l'ordre, et les trace."""

    def __init__(self, script):
        self.script = list(script)
        self.calls: list[tuple[str, float]] = []

    def complete(self, prompt: str, *, max_tokens: int = 0, temperature: float = 0.0) -> G.Reply:
        self.calls.append((prompt, temperature))
        if not self.script:
            raise AssertionError("FakeTeacher a court de reponses preparees")
        item = self.script.pop(0)
        return item(prompt) if callable(item) else item


def _reply(text: str, tokens: int = 60) -> G.Reply:
    return G.Reply(text=text, completion_tokens=tokens, finish_reason="stop")


def _oracle(title: str):
    """Vote la lettre du candidat portant ``title``, quel que soit le melange.

    Les candidats sont melanges par ``rng`` a chaque tour : la lettre d'un noeud
    change d'un tour a l'autre. Un test qui rendrait une lettre fixe mesurerait
    la loterie du melange, pas le vote.
    """
    def answer(prompt: str) -> G.Reply:
        for line in prompt.splitlines():
            if len(line) > 3 and line[1] == "." and line[3:].startswith(title + " :"):
                return _reply(line[0], tokens=3)
        raise AssertionError(f"candidat {title!r} absent de la question de vote")
    return answer


# --------------------------------------------------------------------------
# Mecanique du controle
# --------------------------------------------------------------------------

def test_parse_choice_resolves_letter_and_ignores_noise():
    candidates = ["F7", "F9", "F3"]
    assert G.parse_choice("B", candidates) == "F9"
    assert G.parse_choice("b.", candidates) == "F9"
    assert G.parse_choice("Je choisis la reponse C", candidates) == "F3"
    assert G.parse_choice("La reponse est A", candidates) == "F7"


def test_parse_choice_rend_none_sans_lettre_exploitable():
    assert G.parse_choice("aucune idee", ["F1", "F2"]) is None
    assert G.parse_choice("Je ne sais pas", ["F1", "F2"]) is None
    assert G.parse_choice("", ["F1", "F2"]) is None
    # « F » est une lettre, mais aucun 6e candidat n'existe : rien a resoudre.
    assert G.parse_choice("F", ["F1", "F2"]) is None


def test_parse_choice_ne_lit_pas_un_mot_courant_comme_un_vote():
    """Defaut mesure a l'ecriture du module : le balayage caractere par caractere
    lisait l'article « La » et le mot « a » comme un vote pour le candidat A."""
    assert G.parse_choice("La description ne correspond a aucune option",
                          ["F1", "F2"]) is None
    assert G.parse_choice("a", ["F1", "F2"]) is None
    # ...mais la lettre majuscule isolee, elle, est bien un vote.
    assert G.parse_choice("A", ["F1", "F2"]) == "F1"


def test_parse_choice_suit_un_marqueur_explicite():
    assert G.parse_choice("reponse : B", ["F7", "F9", "F3"]) == "F9"
    assert G.parse_choice("Option C", ["F7", "F9", "F3"]) == "F3"
    assert G.parse_choice("Reponse: C.", ["F7", "F9", "F3"]) == "F3"


def test_parse_choice_ignore_une_lettre_hors_candidats():
    # 'D' existe dans l'alphabet mais il n'y a que 3 candidats : on ne doit pas
    # retomber sur un index inexistant.
    assert G.parse_choice("D", ["F1", "F2", "F3"]) is None
    assert G.parse_choice("reponse : D", ["F1", "F2", "F3"]) is None


def test_majority_tranche_et_distingue_non_mesure():
    target = "F1"
    assert G.majority(["F1", "F1", "F2"], target) is True
    assert G.majority(["F2", "F2", "F1"], target) is False
    # Egalite parfaite entre la cible et un autre noeud : aucun gagnant unique,
    # donc pas de majorite pour la cible (compte comme rate, jamais comme succes).
    assert G.majority(["F1", "F2"], target) is False
    # Aucun tour exploitable : NON MESURE, pas « rate ».
    assert G.majority([None, None], target) is None
    # Un seul tour exploitable fait foi (les None ne votent pas).
    assert G.majority([None, "F1"], target) is True


def test_pick_distractors_respecte_la_polarite_et_exclut_la_cible():
    import random
    keys = ["F1", "F2", "F3", "F4", "V1", "V2"]
    picked = G.pick_distractors("F1", keys, 2, random.Random(0))
    assert len(picked) == 2
    assert all(k.startswith("F") for k in picked), picked
    assert "F1" not in picked


def test_pick_distractors_refuse_quand_la_polarite_est_trop_pauvre():
    import random
    with pytest.raises(ValueError):
        G.pick_distractors("F1", ["F1", "F2", "V1"], 3, random.Random(0))


def test_build_choice_question_porte_le_texte_les_candidats_et_la_consigne():
    texts = _texts()
    question = G.build_choice_question("Le texte genere.", ["F1", "F2"], texts, "fr")
    assert "Le texte genere." in question
    assert "Sophisme A" in question and "Sophisme B" in question
    assert "A. " in question and "B. " in question
    assert "uniquement par la lettre" in question
    # La definition du noeud est transmise (le controle doit discriminer sur elle).
    assert "Definition du sophisme A." in question


# --------------------------------------------------------------------------
# Mesure anti-circularite (sur la SORTIE)
# --------------------------------------------------------------------------

def test_example_overlap_est_mesure_sur_la_sortie():
    record = G.Record(
        pair_id="p", split="val", polarity="fallacy", node_pk=1, family="Fam", depth=1,
        is_leaf=True, scenario_path="s", lang="fr", node_key="F1",
        text="Un texte qui reprend un exemple assez long pour compter, mot pour mot.",
        completion_tokens=40, finish_reason="stop", attempts=1,
        examples=["un exemple assez long pour compter"])
    assert record.example_overlap() is True


def test_example_overlap_ignore_les_exemples_courts():
    """Un exemple sous ``EXAMPLE_MIN_LEN`` est trop court pour etre une recopie."""
    record = G.Record(
        pair_id="p", split="val", polarity="fallacy", node_pk=1, family="Fam", depth=1,
        is_leaf=True, scenario_path="s", lang="fr", node_key="F1",
        text="Un texte quelconque.", completion_tokens=40, finish_reason="stop",
        attempts=1, examples=["court"])
    assert len("court") < B.EXAMPLE_MIN_LEN
    assert record.example_overlap() is False


# --------------------------------------------------------------------------
# Generation d'une paire
# --------------------------------------------------------------------------

def test_generate_one_regenere_une_sortie_sous_le_plancher():
    """14 tokens ne portent pas les 2-4 phrases demandees : on regenere, on ne jette pas."""
    texts = _texts()
    teacher = FakeTeacher([
        _reply("Trop court.", tokens=14),
        _reply("Un texte complet, en deux ou trois phrases, qui porte le sophisme.", tokens=70),
        _oracle("Sophisme A"),
    ])
    record, verdict, picks = G.generate_one(
        _pair(), texts, teacher, lang="fr", rng=__import__("random").Random(0),
        votes=1, distractors=1, min_tokens=25)
    assert record.attempts == 2
    assert record.completion_tokens == 70
    assert verdict is True
    assert len(picks) == 1


def test_generate_one_ne_regenere_pas_une_sortie_conforme():
    texts = _texts()
    teacher = FakeTeacher([
        _reply("Un texte conforme, assez long pour porter les phrases demandees.", tokens=63),
        _oracle("Sophisme A"),
    ])
    record, verdict, _picks = G.generate_one(
        _pair(), texts, teacher, lang="fr", rng=__import__("random").Random(0),
        votes=1, distractors=1)
    assert record.attempts == 1
    assert verdict is True


def test_generate_one_accepte_un_texte_sous_le_plancher_quand_les_retries_sont_epuises():
    """Le plancher est un declencheur de regeneration, pas une garantie (R1, #17578).

    Deux tirages courts et les retries epuises : le texte court **entre** dans le
    corpus, et ``attempts`` montre que la regeneration a bien ete tentee. C'est ce
    cas que ``n_below_floor`` doit rendre visible -- ``n_empty`` ne le voit pas.
    """
    import random
    texts = _texts()
    teacher = FakeTeacher([
        _reply("Court.", tokens=4), _reply("Court.", tokens=4),
        _oracle("Sophisme A"),
    ])
    record, verdict, _picks = G.generate_one(
        _pair(), texts, teacher, lang="fr", rng=random.Random(0),
        votes=1, distractors=1, min_tokens=25, retries=1)
    assert record.text == "Court."
    assert record.completion_tokens == 4
    assert record.attempts == 2        # la regeneration a bien eu lieu
    assert verdict is True             # le texte court est tout de meme vote


def test_generate_one_rend_non_mesure_si_la_generation_est_vide():
    texts = _texts()
    teacher = FakeTeacher([_reply("", tokens=0)] * 3)
    record, verdict, picks = G.generate_one(
        _pair(), texts, teacher, lang="fr", rng=__import__("random").Random(0),
        votes=2, distractors=1, retries=2)
    assert record.text == ""
    assert verdict is None
    assert picks == []
    # Les tours de vote ne sont pas consommes quand il n'y a rien a voter.
    assert len(teacher.script) == 0


def test_generate_one_vote_majoritaire_sur_plusieurs_tours():
    """Le verdict est la majorite : 2 tours sur 3 reviennent a la cible."""
    import random
    texts = _texts()
    teacher = FakeTeacher([
        _reply("Le sophisme A, en deux phrases.", tokens=60),
        _oracle("Sophisme A"), _oracle("Sophisme A"), _oracle("Sophisme B"),
    ])
    record, verdict, picks = G.generate_one(
        _pair("fallacy", 1), texts, teacher, lang="fr", rng=random.Random(0),
        votes=3, distractors=2)
    assert verdict is True
    assert picks.count("F1") == 2
    assert record.node_key == "F1"


def test_generate_one_perd_le_vote_si_la_majorite_va_ailleurs():
    """Deux tours sur trois vers un voisin : la cible n'est pas majoritaire."""
    import random
    texts = _texts()
    teacher = FakeTeacher([
        _reply("Un texte qui ressemble au voisin, en deux phrases.", tokens=60),
        _oracle("Sophisme B"), _oracle("Sophisme B"), _oracle("Sophisme A"),
    ])
    _record, verdict, picks = G.generate_one(
        _pair("fallacy", 1), texts, teacher, lang="fr", rng=random.Random(0),
        votes=3, distractors=2)
    assert verdict is False
    assert picks.count("F1") == 1


def test_generate_one_suit_la_polarite_de_la_vertu():
    """Une vertu se reclasser parmi des vertus, jamais parmi des sophismes."""
    import random
    texts = _texts()
    teacher = FakeTeacher([
        _reply("Une vertu en deux phrases, portee par le piocheur.", 60),
        _oracle("Vertu A"), _oracle("Vertu A"),
    ])
    record, verdict, _picks = G.generate_one(
        _pair("virtue", 1), texts, teacher, lang="fr", rng=random.Random(1),
        votes=2, distractors=1)
    assert record.node_key == "V1"
    assert verdict is True
    # Les questions de vote ne doivent proposer que des vertus.
    question = teacher.calls[1][0]
    assert "Vertu A" in question and "Vertu B" in question
    assert "Sophisme A" not in question


# --------------------------------------------------------------------------
# Echantillonnage, resume, reprise
# --------------------------------------------------------------------------

def test_stratified_sample_couvre_les_familles_avant_de_doubler():
    """Le round-robin touche chaque famille avant d'en reprendre une deuxieme fois."""
    import random
    pairs = [B.Pair(f"p{i}", "val", "fallacy", i, fam, 1, True, "s")
             for i, fam in enumerate(["A", "A", "A", "B", "B", "C"], start=1)]
    sample = G.stratified_sample(pairs, 3, random.Random(0))
    assert sorted(p.family for p in sample) == ["A", "B", "C"]


def test_stratified_sample_rend_tout_si_la_limite_depasse():
    import random
    pairs = [B.Pair(f"p{i}", "val", "fallacy", i, "A", 1, True, "s") for i in range(3)]
    assert len(G.stratified_sample(pairs, 10, random.Random(0))) == 3


def _records_and_verdicts():
    texts = _texts()
    def make(pair_id, family, text, examples):
        return G.Record(pair_id=pair_id, split="val", polarity="fallacy", node_pk=1,
                        family=family, depth=1, is_leaf=True, scenario_path="s",
                        lang="fr", node_key="F1", text=text, completion_tokens=50,
                        finish_reason="stop", attempts=1, examples=examples)
    records = [
        make("p1", "A", "Un texte propre.", []),
        make("p2", "A", "Un texte qui recopie un exemple assez long pour compter ici.",
             ["un exemple assez long pour compter"]),
        make("p3", "B", "", []),
    ]
    return texts, records


def test_summarise_compte_les_vides_le_recouvrement_et_le_non_mesure():
    _texts, records = _records_and_verdicts()
    summary = G.summarise(records, [True, False, None])
    assert summary["n_pairs"] == 3
    assert summary["n_empty"] == 1
    assert summary["example_overlap"] == 1
    assert summary["roundtrip_measured"] == 2      # le verdict None ne vote pas
    assert summary["roundtrip_hits"] == 1
    assert summary["roundtrip_rate"] == 0.5
    assert summary["by_family"]["A"] == {"n": 2, "hit": 1, "measured": 2}
    assert summary["by_family"]["B"]["measured"] == 0


def test_summarise_nomme_les_denominateurs_et_publie_le_plancher():
    """R1/R4 (#17578) : le plancher se publie, les moyennes nomment leur population.

    ``n_pairs`` et ``by_family`` comptent les 3 paires ; ``mean_completion_tokens``
    et ``example_overlap`` ne portent que sur les 2 **generees** -- un texte vide
    n'a ni longueur ni recouvrement a moyenner.
    """
    _texts, records = _records_and_verdicts()
    records[1].completion_tokens = 8          # genere, mais sous le plancher
    summary = G.summarise(records, [True, False, None], min_tokens=25)
    assert summary["n_pairs"] == 3
    assert summary["n_generated"] == 2
    assert summary["n_below_floor"] == 1
    assert summary["below_floor_pairs"] == ["p2"]
    # La moyenne porte sur les 2 generees (50 et 8), pas sur les 3 paires.
    assert summary["mean_completion_tokens"] == 29.0
    assert summary["example_overlap"] == 1
    # Le plancher par defaut est celui du module : 8 < 25 y est compte aussi.
    assert G.summarise(records, [True, False, None])["n_below_floor"] == 1


def test_run_ecrit_un_checkpoint_et_reprend_sans_refaire(tmp_path):
    import random
    texts = _texts()
    pairs = [_pair("fallacy", 1)]
    checkpoint = tmp_path / "val_fr.jsonl"

    first = FakeTeacher([_reply("Un texte en deux phrases.", 60), _oracle("Sophisme A")])
    records, verdicts = G.run(pairs, texts, first, lang="fr", seed=0, votes=1,
                              distractors=1, checkpoint=checkpoint)
    assert len(records) == 1 and verdicts == [True]
    assert checkpoint.exists()
    lines = checkpoint.read_text(encoding="utf-8").strip().splitlines()
    assert len(lines) == 1
    assert json.loads(lines[0])["pair_id"] == "val-F1-1"

    # Reprise : la paire deja faite ne rappelle pas le maitre.
    second = FakeTeacher([])
    records2, verdicts2 = G.run(pairs, texts, second, lang="fr", seed=0, votes=1,
                                distractors=1, checkpoint=checkpoint)
    assert len(records2) == 1 and verdicts2 == [True]
    assert second.calls == []
    assert len(checkpoint.read_text(encoding="utf-8").strip().splitlines()) == 1


def test_run_publie_la_reprise_et_le_nombre_de_paires_rejouees(tmp_path):
    """R3 (#17578) : une reprise n'est pas un run neuf.

    Le tirage des distracteurs consomme ``rng`` dans l'ordre des paires traitees ;
    une reprise repart d'un ``Random(seed)`` neuf et ne rejoue que les manquantes,
    donc les distracteurs different d'un run ininterrompu a ``seed`` egal. Le
    rapport doit le dire plutot que de laisser croire a un tirage unique.
    """
    texts = _texts()
    pairs = [_pair("fallacy", 1)]
    checkpoint = tmp_path / "val_fr.jsonl"

    fresh: dict = {}
    first = FakeTeacher([_reply("Un texte en deux phrases.", 60), _oracle("Sophisme A")])
    G.run(pairs, texts, first, lang="fr", seed=0, votes=1, distractors=1,
          checkpoint=checkpoint, stats=fresh)
    assert fresh == {"resumed": False, "n_resumed": 0, "n_todo": 1}

    resumed: dict = {}
    second = FakeTeacher([])
    G.run(pairs, texts, second, lang="fr", seed=0, votes=1, distractors=1,
          checkpoint=checkpoint, stats=resumed)
    assert resumed == {"resumed": True, "n_resumed": 1, "n_todo": 0}


# --------------------------------------------------------------------------
# Client HTTP : le dialecte thinking et l'hygiene des secrets
# --------------------------------------------------------------------------

def test_hub_teacher_refuse_un_repli_litteral_sans_cle(monkeypatch):
    monkeypatch.delenv(G.DEFAULT_API_KEY_ENV, raising=False)
    with pytest.raises(ValueError):
        G.HubTeacher()


def test_hub_teacher_porte_le_dialecte_vllm_et_le_retire_du_niveau_racine(monkeypatch):
    """Le piege mesure le 2026-10-09 : le thinking se coupe dans ``chat_template_kwargs``.

    Un ``enable_thinking`` au niveau racine est ignore par vLLM : le budget part
    en ``reasoning_tokens`` et le contenu revient vide a ``finish_reason: length``.
    """
    captured: dict = {}

    class FakeResponse:
        def __enter__(self):
            return self

        def __exit__(self, *exc):
            return False

        def read(self):
            return json.dumps({
                "choices": [{"message": {"content": "ok"}, "finish_reason": "stop"}],
                "usage": {"completion_tokens": 3},
            }).encode()

    def fake_urlopen(request, timeout=None):
        captured["body"] = json.loads(request.data.decode("utf-8"))
        return FakeResponse()

    monkeypatch.setattr(G.urllib.request, "urlopen", fake_urlopen)
    teacher = G.HubTeacher(api_key="cle-de-test")
    reply = teacher.complete("prompt")

    assert captured["body"]["chat_template_kwargs"] == {"enable_thinking": False}
    assert "enable_thinking" not in captured["body"]
    assert reply.text == "ok" and reply.completion_tokens == 3
    assert reply.finish_reason == "stop"


# --------------------------------------------------------------------------
# Ancrage sur les vraies sources du depot
# --------------------------------------------------------------------------

def test_load_pairs_confronte_les_comptes_au_manifeste():
    """Les paires relues portent exactement les comptes declares par la tranche A."""
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    checked = 0
    for split in B.SPLITS:
        if not (PHASE2 / f"{split}.csv").exists():
            continue  # train.csv n'est pas suivi (volumineux)
        pairs = G.load_pairs(split)
        assert len(pairs) == manifest["counts"][split], split
        assert all(p.split == split for p in pairs)
        assert all(p.scenario_path and p.family for p in pairs)
        checked += 1
    assert checked >= 2, "aucun CSV de split relu : l'ancrage ne mesure rien"


def test_les_prompts_reels_ne_transmettent_aucun_exemple():
    """Anti-circularite cote PROMPT, mesuree sur les vraies donnees."""
    texts = B.load_texts()
    sample = G.stratified_sample(G.load_pairs("val"), 40, __import__("random").Random(0))
    for pair in sample:
        prompt = B.render_prompt(pair, texts, lang="fr")
        assert B.prompt_contains_example(pair, texts, "fr") is False
        key = G.node_key(pair)
        for example in texts["nodes"][key]["fr"][2]:
            if len(example) >= B.EXAMPLE_MIN_LEN:
                assert example not in prompt


def test_module_invocable_en_ligne_de_commande():
    """Le point d'entree CLI s'importe et repond : garde contre une erreur d'import."""
    result = subprocess.run(
        [sys.executable, "-m", "fallacy_detection.generate_teacher_corpus", "--help"],
        cwd=str(_SCRIPTS), capture_output=True, text=True,
        encoding="utf-8", errors="replace", timeout=120)
    assert result.returncode == 0, result.stderr
    assert "--distractors" in result.stdout
