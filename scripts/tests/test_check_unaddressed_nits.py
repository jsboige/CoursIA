"""Tests for scripts/check_unaddressed_nits.py (#11044, gate B.0).

L'organe encode une seule question : « cette remarque de review a-t-elle ete
LEVEE avant le merge ? ». Toute sa correction tient dans ce qui compte comme
levee — et c'est precisement la que les deux defauts trouves en review sont nes.
Les deux sont couverts ici :

  - **Le bruit ne leve pas** (defaut signale par Hermes sur #11045) : un
    commentaire de bot CI ou un tag de protocole nu, poste entre le nit et le
    merge, ne repond a rien. Sans ce filtre l'organe reproduisait exactement le
    defaut qu'il traque, et sur ce depot ou les bots commentent a chaque push le
    failure mode etait la regle, pas l'exception.
  - **Un commit ne leve pas** : un push muet est indiscernable d'un push qui
    repond. Sur l'incident fondateur #10761, le « traitement » etait un rebase
    qui n'adressait aucun des deux nits. Ce qui leve une remarque est une phrase,
    pas un SHA.

S'y ajoutent la borne anti-retroactivite (un commentaire poste APRES le merge
est une annonce de merge, pas une reponse) et la normalisation des accents (les
agents ecrivent « sont adresses », les marqueurs disent « sont adresses »).

Aucun appel reseau : `analyse()` est pur, on lui passe des payloads construits.
"""
import importlib.util
import sys
from datetime import datetime, timezone
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
CHECK_PATH = HERE.parent / "check_unaddressed_nits.py"

spec = importlib.util.spec_from_file_location("check_unaddressed_nits", CHECK_PATH)
mod = importlib.util.module_from_spec(spec)
sys.modules["check_unaddressed_nits"] = mod
spec.loader.exec_module(mod)


def at(hour: int) -> str:
    return f"2026-08-14T{hour:02d}:00:00Z"


MERGED = datetime(2026, 8, 14, 20, 0, tzinfo=timezone.utc)

# Un nit user : CRLF (redige dans l'UI web), poste 11 h avant le merge.
USER_NIT = {
    "author": {"login": "jsboige"},
    "createdAt": at(9),
    "body": "Attention 2 nits:\r\n- il va falloir splitter\r\n- l'attribution est fausse",
}


def run(comments, commits=None, threads=None):
    data = {
        "number": 0,
        "title": "t",
        "comments": comments,
        "reviews": [],
        "commits": commits if commits is not None else [{"committedDate": at(19)}],
    }
    return mod.analyse(data, threads or [], MERGED)


def test_nit_seul_bloque():
    assert run([USER_NIT])["blocked"] is True


def test_commit_posterieur_ne_leve_pas():
    """#10761 : le rebase de 19:41 n'adressait aucun des nits de 11:07."""
    res = run([USER_NIT], commits=[{"committedDate": at(19)}])
    assert res["blocked"] is True
    assert res["blocking"][0]["code_pushed_after"] is True  # rapporte, pas decisif


@pytest.mark.parametrize(
    "noise",
    [
        pytest.param({"author": {"login": "github-actions"}, "createdAt": at(12),
                      "body": "Golden set: 0 diff. Variation cap: OK."},
                     id="bot-ci"),
        pytest.param({"author": {"login": "codecov"}, "createdAt": at(12),
                      "body": "Coverage: 91.2% (+0.1%)"},
                     id="bot-codecov"),
        pytest.param({"author": {"login": "jsboige"}, "createdAt": at(12),
                      "body": "[CLAIMED] lane myia-po-2023:CoursIA -- paths: a/b"},
                     id="tag-protocole-nu"),
        pytest.param({"author": {"login": "jsboige"}, "createdAt": at(12),
                      "body": "[DISPATCH->inbox] grain suivant poste en DM"},
                     id="tag-dispatch"),
    ],
)
def test_le_bruit_ne_leve_pas_un_nit(noise):
    """Defaut Hermes sur #11045 : n'importe quel bruit eteignait le nit."""
    assert run([USER_NIT, noise])["blocked"] is True


def test_vraie_reponse_humaine_leve():
    reply = {"author": {"login": "jsboige"}, "createdAt": at(12),
             "body": "Bien vu, l'attribution est corrigee en cellule 0 et 2."}
    assert run([USER_NIT, reply])["blocked"] is False


def test_tag_de_protocole_portant_une_levee_leve():
    """Un tag n'est disqualifie que s'il est NU : `[DONE] ... sont adresses` repond."""
    done = {"author": {"login": "jsboige"}, "createdAt": at(12),
            "body": "[DONE] les 2 nits sont adresses, commit abc123."}
    assert run([USER_NIT, done])["blocked"] is False


def test_accents_absents_matchent_quand_meme():
    """Les agents ecrivent sans accents ; les marqueurs sont accentues."""
    assert mod.has_marker("les 2 points sont adresses", mod.LIFT_MARKERS)
    assert mod.has_marker("les 2 points sont adressés", mod.LIFT_MARKERS)
    assert not mod.has_marker("rien a voir", mod.LIFT_MARKERS)


def test_commentaire_post_merge_ne_leve_pas():
    """La borne anti-retroactivite : l'annonce de merge n'est pas une reponse.

    Sans elle, le gate ratait son propre incident fondateur — mon commentaire de
    merge « eteignait » un nit vieux de 17 h.
    """
    after = {"author": {"login": "jsboige"}, "createdAt": at(21),  # apres MERGED
             "body": "Merge apres verification des checks."}
    assert run([USER_NIT, after])["blocked"] is True


def test_thread_inline_non_resolu_bloque():
    thread = {"resolved": False, "outdated": False, "path": "a.py", "line": 12,
              "author": "jsboige", "body": "ce nom est trompeur", "createdAt": at(10)}
    res = run([], threads=[thread])
    assert res["blocked"] is True
    assert res["blocking"][0]["kind"] == "INLINE-UNRESOLVED"


def test_thread_inline_resolu_ne_bloque_pas():
    thread = {"resolved": True, "outdated": False, "path": "a.py", "line": 12,
              "author": "jsboige", "body": "ce nom est trompeur", "createdAt": at(10)}
    assert run([], threads=[thread])["blocked"] is False


def test_pr_propre_ne_bloque_pas():
    assert run([])["blocked"] is False


# --- Durcissements (triage 07-15..07-31, approuves par ai-01 le 2026-08-15) ---

def test_verdict_positif_en_queue_decharge():
    """Classe FP no 1 : titre CONCERNS, conclusion « ne bloque pas »."""
    bot = {"author": {"login": "hermes-bot"}, "createdAt": at(12),
           "body": "Review Hermes: COMMENT_WITH_CONCERNS. Le scope est large "
                   "et deux cellules manquent d'interp. Apres relecture du "
                   "diff et des outputs, verdict final: ne bloque pas."}
    assert run([bot])["blocked"] is False  # le bot concluant positivement n'est pas une reserve
    # et son verdict constitue une reponse qui leve le nit user :
    assert run([USER_NIT, bot])["blocked"] is False


def test_negation_hors_queue_ne_decharge_pas():
    """La negation ne compte que si elle est dans les 300 derniers chars."""
    filler = " ".join(["developpement"] * 80)
    bot = {"author": {"login": "hermes-bot"}, "createdAt": at(12),
           "body": "Verdict initial: ne bloque pas, mais " + filler +
                   " et au final il va falloir splitter avant merge."}
    assert run([bot])["blocked"] is True


def test_lift_capitalise_leve():
    """« Je lève ma CHANGES_REQUESTED » ne matchait pas les LIFT_MARKERS lowercase."""
    lift = {"author": {"login": "jsboige"}, "createdAt": at(12),
            "body": "Je leve ma CHANGES_REQUESTED apres le commit abc."}
    assert mod.has_marker(lift["body"], mod.LIFT_MARKERS)


def test_lift_capitalise_accents_leve():
    lift = {"author": {"login": "jsboige"}, "createdAt": at(12),
            "body": "Levée de ma réserve : les 2 nits sont traités."}
    assert mod.has_marker(lift["body"], mod.LIFT_MARKERS)


def test_excerpt_porte_la_queue():
    """Le verdict final doit rester visible dans l'excerpt des PRs longues."""
    filler = " ".join(["contexte"] * 60)
    body = "Review: " + filler + " verdict final: ne bloque pas."
    excerpt = mod._excerpt(body)
    assert "ne bloque pas" in excerpt
