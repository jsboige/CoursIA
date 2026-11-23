"""Tests pour le scope d'override applique a la NATURE de la reserve (#27873).

L'organe `check_unaddressed_nits.analyse` doit distinguer une reserve de
PERSONA (portee par le self-bot, marqueur persona dans le corps) d'une
reserve USER (voix nue du mainteneur) — meme lorsqu'elles sont toutes deux
posees sous le login de poussee partage `jsboige`.

Defaut fondateur : PR #27153. Le commentaire `[OVERRIDE] lane
myia-ai-01:CoursIA` du 2026-11-21T20:54:39Z ne leve que la reserve
`clusterManager-Myia` (review NanoClaw) et dit explicitement « Le Concern du
mainteneur du 17/11 sur la portee face au depot Stacks attend son arbitrage »
— l'organe rendait neanmoins `rc=0` : la reserve user du mainteneur
(`Concern:` du 2026-11-17T18:53:52Z) etait comptee comme levee, parce que la
forme « mention de persona » (`_override_scopes_reserve`, l. 5416) etait
acceptee des que l'AUTEUR de la reserve etait `jsboige`.

Acceptance :
  1. Un override qui ne nomme qu'une reserve de persona ne leve PAS une
     reserve USER portee par `jsboige` : la PR reste bloquee sur elle.
  2. La levee de la reserve de persona par le meme override reste acquise
     (le correctif ne durcit pas ce qui doit rester leve).
  3. La forme historique « Levee de la reserve Hermes » reste un scope
     pour une reserve de persona (`clusterManager-Myia`) ET pour une reserve
     `jsboige` dont le corps porte le marqueur de persona (self-bot).
  4. L'appel historique sans corps de reserve conserve son comportement
     (fail-open sur l'absence d'information).
"""
import importlib.util
import sys
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
CHECK_PATH = HERE.parent / "check_unaddressed_nits.py"

spec = importlib.util.spec_from_file_location("check_unaddressed_nits", CHECK_PATH)
mod = importlib.util.module_from_spec(spec)
sys.modules["check_unaddressed_nits"] = mod
spec.loader.exec_module(mod)


def at(day: str, hour: int, minute: int = 0) -> str:
    return f"2026-11-{day}T{hour:02d}:{minute:02d}:00Z"


MERGED = datetime(2026, 11, 22, 8, 0, tzinfo=timezone.utc)

# --- corps REELS de la PR #27153 (verbatim) -------------------------------
# Reserve USER du mainteneur : voix nue, marqueur « Concern: » en tete.
CONCERN_USER_27153 = (
    "Concern: Attention, je rappelle qu'on est passé par "
    "https://github.com/jsboige/CoursIA/issues/26786 donc il ne faudrait "
    "pas continuer à mouliner dans le vide alors que la portée de notre "
    "travail reste très superficielle par rapport au travail titanesque "
    "qui a été effectué sur le dépôt stacks.\n"
    "Si on veut continuer l'issue groth, alors elle doit largement "
    "s'appuyer sur le travail déjà accompli par d'autres et le présenter."
)

# Override du coordinateur : ne leve QUE la reserve clusterManager-Myia et
# dit explicitement que le Concern du mainteneur attend son arbitrage.
OVERRIDE_27153 = (
    "[OVERRIDE] lane myia-ai-01:CoursIA\n"
    "\n"
    "Je lève la réserve de clusterManager-Myia (review NanoClaw du "
    "17/11, point B.2 lake build) : `lean-matrix / Lean CI "
    "(grothendieck_lean)` est en succès à la tête e1479d594a.\n"
    "\n"
    "Le Concern du mainteneur du 17/11 sur la portée face au dépôt Stacks "
    "attend son arbitrage : cette tranche livre l'engagement 1 (section "
    "« État de l'art » dans les deux README) et la suite de P99 reste "
    "gelée."
)

# Reserve de PERSONA : auteur clusterManager-Myia, corps marque.
RESERVE_PERSONA_27153 = {
    "author": {"login": "clusterManager-Myia"},
    "createdAt": at("17", 19, 5),
    "body": "**[NanoClaw]** structural review — slot 1 récence\n"
            "Défaut constaté : le job `lean-matrix` n'a pas de statut "
            "d'attestation dans le body de la PR.",
}


def run(comments, reviews=None, pr_author="jsboige", merged=MERGED, **extra):
    data = {
        "number": 27153,
        "title": "Feat(groth,#2159): P99 tranche 1 SES C0 categorique",
        "author": {"login": pr_author},
        "comments": comments,
        "reviews": reviews if reviews is not None else [],
        "commits": [{"committedDate": at("21", 20, 0)}],
    }
    data.update(extra)
    return mod.analyse(data, [], merged)


def comments_27153():
    return [
        {
            "author": {"login": "jsboige"},
            "createdAt": at("17", 18, 53),
            "body": CONCERN_USER_27153,
        },
        RESERVE_PERSONA_27153,
        {
            "author": {"login": "myia-ai-01"},
            "createdAt": at("21", 20, 54),
            "body": OVERRIDE_27153,
        },
    ]


def scope(lift_body, nit_author, nit_body=None):
    """Appel du scope d'override, tolérant à la signature historique (2
    arguments) : sur l'organe d'avant le correctif, l'absence du corps de
    la réserve est une absence d'information (fail-open conserve), pas une
    erreur de signature — le test doit alors echouer SUR LE FOND, pas sur
    un TypeError."""
    try:
        return mod._override_scopes_reserve(lift_body, nit_author, nit_body)
    except TypeError:
        return mod._override_scopes_reserve(lift_body, nit_author)


# ---------------------------------------------------------------------------
# Acceptance 1 — le defaut : l'override qui ne nomme qu'une reserve de
# persona n'eteint PAS la reserve user du mainteneur.
# ---------------------------------------------------------------------------

def test_override_qui_nomme_une_persona_ne_leve_pas_reserve_user():
    """#27873 — le cas fondateur (#27153). L'override nomme
    `clusterManager-Myia` et dit que le Concern attend son arbitrage : la
    reserve USER du mainteneur doit SURVIVRE (PR bloquee)."""
    res = run(comments_27153())
    assert res["blocked"] is True, (
        "Un [OVERRIDE] qui ne nomme que la reserve de persona ne doit pas "
        "eteindre la reserve USER du mainteneur (#27873, PR #27153)."
    )
    auteurs = sorted({b.get("author") for b in res["blocking"]})
    assert "jsboige" in auteurs, (
        "La reserve user du mainteneur doit rester dans le blocking : "
        f"blocking = {res['blocking']}"
    )


def test_leve_de_la_reserve_persona_reste_acquise():
    """#27873 — le correctif ne doit pas durcir la levee LEGITIME : la
    reserve de persona nommee par l'override reste levee (absente du
    blocking)."""
    res = run(comments_27153())
    restants = {b.get("author") for b in res["blocking"]}
    assert "clusterManager-Myia" not in restants, (
        "La reserve de persona explicitement nommee par l'override doit "
        "rester levee : le correctif ne porte que sur la reserve user."
    )


def test_scope_unitaire_reserve_user_non_scopee_par_la_mention_persona():
    """#27873 — au niveau unitaire : la mention « Hermes/NanoClaw » ne scope
    plus une reserve `jsboige` dont le corps ne porte PAS le marqueur de
    persona (reserve user)."""
    assert not scope(
        OVERRIDE_27153, "jsboige", CONCERN_USER_27153)


def test_scope_unitaire_reserve_persona_marquee_reste_scopeee():
    """#27873 — non-regression : une reserve `jsboige` dont le corps porte le
    marqueur de persona (self-bot qui la porte) reste scopee par la mention
    de persona (forme canonique #11639)."""
    assert scope(
        "Levée de la réserve Hermes.", "jsboige",
        "**[NanoClaw]** structural review — la reserve de la persona.")


def test_scope_unitaire_persona_authentique_inchange():
    """#27873 — non-regression : une reserve de la persona
    `clusterManager-Myia` reste scopee par la mention de persona."""
    assert scope(
        "Levée de la réserve Hermes.", "clusterManager-Myia")


def test_scope_unitaire_appel_historique_sans_corps_preserve():
    """#27873 — non-regression : l'appel sans corps de reserve (signature
    historique) conserve le comportement d'avant (fail-open : un scope ne
    peut pas nommer ce qu'il n'a pas sous les yeux)."""
    assert scope("Levée de la réserve Hermes.", "jsboige")


def test_scope_unitaire_login_nomme_lève_la_reserve_user():
    """#27873 — non-regression : la forme « login nomme » reste un scope
    valide pour une reserve user : nommer le login dans une phrase de levee
    affirmative lève la reserve."""
    assert scope(
        "Je lève aussi la réserve de jsboige.", "jsboige", CONCERN_USER_27153)
