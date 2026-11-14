"""Tests Q185 -- la voix adjointe leve par phrase les reserves de bot.

Sign-off user du 2026-11-13 (registre Q185, « OK pour Q185 ») : l'adjoint
coordonnateur, lane ``myia-po-2025:CoursIA-2``, poste sous son identite
GitHub App propre ``coursia-lane-po-2025[bot]`` et peut lever par phrase
UNIQUEMENT les reserves emises par un bot -- persona Hermes (review
``[Hermes]`` du self-bot ``jsboige``, ou ``clusterManager-Myia``),
bots automatises (``BOT_LOGINS``). Hors perimetre, fail-closed : le
coordinateur ``myia-ai-01``, les nits user voix nue de ``jsboige``, toute
reserve d'une autre lane ou d'un humain, et la PR portee par l'App
elle-meme (trappe #13495). La grammaire est CELLE du coordinateur
(``[OVERRIDE] lane`` pose en tete #13030 + phrase de levee affirmative
nommant la reserve #14216) : jamais une grammaire plus lache.

Fixtures dans le style de ``test_check_unaddressed_nits_17437.py`` :
lignes d'auteur typees (``__typename`` Bot vs User), preuve d'identite
portee par la ligne, jamais par une sonde.
"""

import importlib.util
import sys
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
CHECK_PATH = HERE.parent / "check_unaddressed_nits.py"

spec = importlib.util.spec_from_file_location(
    "check_unaddressed_nits_q185", CHECK_PATH
)
mod = importlib.util.module_from_spec(spec)
sys.modules["check_unaddressed_nits_q185"] = mod
spec.loader.exec_module(mod)

ADJOINT_APP_BARE = "coursia-lane-po-2025"
ADJOINT_APP_REST = "coursia-lane-po-2025[bot]"


def at(hour: int) -> str:
    return f"2026-11-13T{hour:02d}:00:00Z"


MERGED = datetime(2026, 11, 13, 20, 0, tzinfo=timezone.utc)

# --- reserves --------------------------------------------------------------
#
# Hermes sous le self-bot jsboige : canal review de la persona (B.0 classe
# ces reviews par le marqueur pose, pas par le login partage).

HERMES_JSBOIGE_REVIEW = {
    "author": {"login": "jsboige"},
    "state": "COMMENTED", "submittedAt": at(10),
    "body": "[Hermes] COMMENT_WITH_CONCERNS — tests exécutés en local : 44/44 "
            "pass, mais 2 edge cases non couverts.",
}

# Hermes sous clusterManager-Myia (alias de persona, reviewer principal).

HERMES_CMM_REVIEW = {
    "author": {"login": "clusterManager-Myia"},
    "state": "COMMENTED", "submittedAt": at(10),
    "body": "[Hermes] COMMENT_WITH_CONCERNS — 2 edge cases non couverts.",
}

# Bot automatise : la reserve d'un BOT_LOGINS vit par l'etat natif
# CHANGES_REQUESTED (classify() rend None pour ces auteurs).

COPILOT_CR = {
    "author": {"login": "copilot-pull-request-reviewer", "__typename": "Bot"},
    "state": "CHANGES_REQUESTED", "submittedAt": at(10),
    "body": "CHANGES_REQUESTED: the multi-seed evidence is missing.",
}

# Reserve du coordinateur : hors perimetre adjoint, quelle que soit la
# qualite de la phrase de levee.

AI01_CR = {
    "author": {"login": "myia-ai-01"},
    "state": "CHANGES_REQUESTED", "submittedAt": at(10),
    "body": "CHANGES_REQUESTED: le multi-seed manque (4 seeds exigés).",
}

# Nit user voix nue (CRLF UI web) : le canal des nits du user.

USER_NIT = {
    "author": {"login": "jsboige"},
    "createdAt": at(9),
    "body": "Attention 2 nits:\r\n- il va falloir splitter\r\n"
            "- l'attribution est fausse",
}

# --- levees ----------------------------------------------------------------
#
# Grammaire Q185 : meme forme que le coordinateur, lane adjointe en tete.

ADJ_OVERRIDE_HERMES = (
    "[OVERRIDE] lane myia-po-2025:CoursIA-2 — réserve de Hermes levée : "
    "re-vérifiée en local, les 2 edge cases sont couverts."
)
ADJ_OVERRIDE_CMM = (
    "[OVERRIDE] lane myia-po-2025:CoursIA-2 — réserve de clusterManager-Myia "
    "levée : re-vérifiée en local, les 2 edge cases sont couverts."
)
ADJ_OVERRIDE_COPILOT = (
    "[OVERRIDE] lane myia-po-2025:CoursIA-2 — réserve de "
    "copilot-pull-request-reviewer[bot] levée : avis automatique, re-vu "
    "manuellement."
)
ADJ_OVERRIDE_AI01 = (
    "[OVERRIDE] lane myia-po-2025:CoursIA-2 — réserve de myia-ai-01 levée : "
    "le multi-seed est fourni."
)
ADJ_OVERRIDE_USER = (
    "[OVERRIDE] lane myia-po-2025:CoursIA-2 — réserve de jsboige levée : "
    "les 2 nits sont traités."
)

# Forme #14166 : le login du tiers nomme dans une phrase d'EXCLUSION --
# la nomination seule n'est pas un scope (#14216). La premiere phrase porte
# une levee VIVE pour que le commentaire entre dans explicit_lifts et que
# c'est bien la garde de negation qui refuse.

ADJ_OVERRIDE_EXCLUSION = (
    "[OVERRIDE] lane myia-po-2025:CoursIA-2 — Levée de ma révision "
    "adjointe : les vérifications sont refaites. La réserve de "
    "clusterManager-Myia n'est pas concernée par cette levée."
)


def adjoint_lift(body: str, hour: int = 12) -> dict:
    """Levee par l'App adjointe, preuve de type portee par la ligne
    (orthographe GraphQL nue + ``__typename: Bot`` -> REST suffixee)."""
    return {"author": {"login": ADJOINT_APP_BARE, "__typename": "Bot"},
            "createdAt": at(hour), "body": body}


def run(reserve: dict | None, lift: dict, pr_author: dict | None = None,
        extra_comments: tuple = ()):
    """PR d'un worker ; la reserve est un tiers, la trappe OVERRIDE le seul
    chemin de levee -- l'auteur de la levee est parametrable."""
    data = {
        "number": 0, "title": "t",
        "author": pr_author or {"login": "myia-po-2026"},
        "comments": [lift, *extra_comments],
        "reviews": [reserve] if reserve is not None else [],
        "commits": [{"committedDate": at(19)}],
    }
    return mod.analyse(data, [], MERGED)


# --- (a)/(b) : le perimetre accede -- reserves de bot ----------------------


def test_q185_adjoint_leve_hermes_sous_jsboige():
    """(a) La review Hermes du self-bot jsboige (marqueur pose) est une
    reserve de bot au sens Q185 : la voix adjointe la leve."""
    res = run(HERMES_JSBOIGE_REVIEW, adjoint_lift(ADJ_OVERRIDE_HERMES))
    assert res["blocked"] is False


def test_q185_adjoint_leve_hermes_cluster_manager():
    """(b) clusterManager-Myia (alias de persona, PERSONA_ALIAS_LOGINS) :
    reserve de bot, levee par la voix adjointe."""
    res = run(HERMES_CMM_REVIEW, adjoint_lift(ADJ_OVERRIDE_CMM))
    assert res["blocked"] is False


def test_q185_adjoint_leve_reserve_bot_logins():
    """(b) Un bot automatise de BOT_LOGINS (copilot, CHANGES_REQUESTED
    natif, login type Bot normalise REST) : levee par la voix adjointe."""
    res = run(COPILOT_CR, adjoint_lift(ADJ_OVERRIDE_COPILOT))
    assert res["blocked"] is False


# --- (c)/(d)/(e)/(f) : le perimetre refuse -- fail-closed ------------------


def test_q185_adjoint_ne_leve_pas_la_reserve_du_coordinateur():
    """(c) Une reserve CHANGES_REQUESTED du coordinateur myia-01 reste
    debout devant un override adjoint qui la nomme correctement : hors
    perimetre bot, et le rouge explique la cause (note Q185)."""
    res = run(AI01_CR, adjoint_lift(ADJ_OVERRIDE_AI01))
    assert res["blocked"] is True
    assert res["blocking"][0]["author"] == "myia-ai-01"
    assert any("Q185" in o["why"] for o in res.get("ignored_overrides", ()))


def test_q185_adjoint_ne_leve_pas_le_nit_user():
    """(d) Un nit user voix nue de jsboige (pas de marqueur persona) n'est
    pas une reserve de bot : l'override adjoint echoue, fail-closed."""
    res = run(None, adjoint_lift(ADJ_OVERRIDE_USER),
              extra_comments=(USER_NIT,))
    assert res["blocked"] is True
    assert res["blocking"][0]["author"] == "jsboige"
    assert any("Q185" in o["why"] for o in res.get("ignored_overrides", ()))


def test_q185_adjoint_ne_leve_pas_sur_sa_propre_pr():
    """(e) Trappe #13495 : la PR est portee par l'App adjointe elle-meme
    (auteur type Bot, lu par l'overlay) -- l'override de la meme App ne
    leve pas la reserve Hermes d'un tiers, la reserve etant par ailleurs
    dans le perimetre bot pour isoler LA barriere qui refuse."""
    res = run(HERMES_JSBOIGE_REVIEW, adjoint_lift(ADJ_OVERRIDE_HERMES),
              pr_author={"login": ADJOINT_APP_BARE, "__typename": "Bot"})
    assert res["blocked"] is True


def test_q185_adjoint_mention_exclusion_nest_pas_un_scope():
    """(f) Le corps fondateur #14166 transpose a l'adjoint : le login nomme
    dans une phrase d'EXCLUSION ne leve pas -- la garde de negation #14216
    s'applique a la voix adjointe comme a celle du coordinateur."""
    res = run(HERMES_CMM_REVIEW, adjoint_lift(ADJ_OVERRIDE_EXCLUSION))
    assert res["blocked"] is True
    assert res["blocking"][0]["author"] == "clusterManager-Myia"


# --- (g) : la preuve d'identite est le TYPE de la ligne --------------------


def test_q185_forme_nue_typee_user_n_est_pas_l_adjoint():
    """(g) L'homonyme UTILISATEUR du slug de l'App, type User par la ligne :
    pas la voix adjointe -- la borne suffixee echoue, comme pour #17437."""
    lift = {"author": {"login": ADJOINT_APP_BARE, "__typename": "User"},
            "createdAt": at(12), "body": ADJ_OVERRIDE_HERMES}
    res = run(HERMES_JSBOIGE_REVIEW, lift)
    assert res["blocked"] is True
    # ... et c'est la note #13316 genérique qui le nomme (pas une voix de
    # levee du tout), pas la note Q185 d'un adjoint reconnu mais refuse.
    assert any("n'est pas un compte de levée" in o["why"]
               for o in res.get("ignored_overrides", ()))


def test_q185_orthographe_rest_suffixee_directe():
    """L'orthographe REST suffixee (lecture CLI deja suffixee) est
    idempotente : la voix adjointe est reconnue dans les deux orthographes."""
    lift = {"author": {"login": ADJOINT_APP_REST},
            "createdAt": at(12), "body": ADJ_OVERRIDE_HERMES}
    res = run(HERMES_JSBOIGE_REVIEW, lift)
    assert res["blocked"] is False


# --- (h) : temoins -- le coordinateur et jsboige ne bougent pas ------------


def test_q185_controle_coordinateur_leve_toujours():
    """(h) Temoin : l'override du coordinateur myia-ai-01 leve la reserve
    Hermes -- pouvoirs inchanges par Q185."""
    lift = {"author": {"login": "myia-ai-01"}, "createdAt": at(12),
            "body": "[OVERRIDE] lane myia-ai-01:CoursIA — réserve de "
                    "Hermes levée : re-vérifiée en local."}
    res = run(HERMES_JSBOIGE_REVIEW, lift)
    assert res["blocked"] is False


def test_q185_controle_jsboige_refuse_toujours():
    """(h) Temoin #13316 : une phrase de levee signee jsboige reste refusee
    sur la reserve d'un TIERS (clusterManager-Myia) -- Q185 n'elargit rien
    pour le login partage. La reserve Hermes sous jsboige elle-meme releve
    de la voie self-lift preexistante, pas de la trappe arbitre."""
    lift = {"author": {"login": "jsboige"}, "createdAt": at(12),
            "body": ADJ_OVERRIDE_CMM}
    res = run(HERMES_CMM_REVIEW, lift)
    assert res["blocked"] is True
    assert any("n'est pas un compte de levée" in o["why"]
               for o in res.get("ignored_overrides", ()))


# --- parite des anti-patterns coordinateur sur la voix adjointe ------------


def test_q185_adjoint_override_nu_ne_leve_rien():
    """Un [OVERRIDE] adjoint sans phrase de levee ne leve rien -- can_lift
    l'ecarte comme tag de protocole nu (parite test_coord_override_nu)."""
    res = run(HERMES_JSBOIGE_REVIEW, adjoint_lift(
        "[OVERRIDE] lane myia-po-2025:CoursIA-2 — arbitrage : le point 3 "
        "est traité en argument, voir #11058."))
    assert res["blocked"] is True


def test_q185_adjoint_sans_override_ne_leve_pas():
    """Un tiers (l'adjoint compris) qui ecrit une phrase de levee SANS
    [OVERRIDE] ne leve pas la reserve d'autrui (#11145)."""
    res = run(HERMES_JSBOIGE_REVIEW, adjoint_lift(
        "Réserve de Hermes levée : re-vérifiée en local, tout est couvert."))
    assert res["blocked"] is True


def test_q185_adjoint_override_post_merge_ne_leve_pas():
    """La borne temporelle #10761 : un override adjoint POSTERIEUR au
    cutoff ne peut pas avoir eteint la reserve avant la decision."""
    res = run(HERMES_JSBOIGE_REVIEW, adjoint_lift(ADJ_OVERRIDE_HERMES,
                                                  hour=21))
    assert res["blocked"] is True


def test_q185_adjoint_emission_informelle_ni_ne_leve_ni_ne_bloque():
    """Parite #13598, cote LEVEE seulement : un commentaire adjoint sans
    [OVERRIDE] ni mot de levee ne leve rien (has_live_lift manque). Q185 ne
    grantit PAS le pouvoir de hold du coordinateur : ce commentaire ne
    devient pas non plus une reserve (l'adjoint n'est pas dans
    LIFT_OVERRIDE_LOGINS) -- il sort dans la queue non evaluee."""
    informal = adjoint_lift(
        "J'attends le run GPU avant de trancher sur cette PR.")
    res = run(HERMES_JSBOIGE_REVIEW, informal)
    assert res["blocked"] is True
    assert len(res["blocking"]) == 1  # seule la reserve Hermes bloque


# --- reporting : une levee adjointe reussie ne fabrique pas de note --------


def test_q185_levee_adjointe_reussie_sans_fausse_note():
    """Le contre-pied du report #13316 : une levee adjointe qui LEVE ne doit
    produire AUCUNE note « n'est pas un compte de levée » -- sinon chaque
    geste adjoint legitime s'afficherait comme un override ignore."""
    res = run(HERMES_JSBOIGE_REVIEW, adjoint_lift(ADJ_OVERRIDE_HERMES))
    assert res["blocked"] is False
    assert not any("n'est pas un compte de levée" in o["why"]
                   for o in res.get("ignored_overrides", ()))


# --- potence : le litteral est epingle --------------------------------------


def test_q185_constant_adjoint_epinglee():
    """La potence : la voix adjointe est l'App po-2025 en orthographe REST,
    et elle est DISJOINTE de la voix coordinateur (les pouvoirs ne se
    cumulent pas par une edition future silencieuse)."""
    assert mod.ADJOINT_LIFT_LOGINS == {ADJOINT_APP_REST}


def test_q185_levee_adjointe_disjointe_du_coordinateur():
    """L'adjoint n'entre pas dans LIFT_OVERRIDE_LOGINS : ses pouvoirs sont
    les siens (bot only), jamais ceux du coordinateur."""
    assert mod.LIFT_OVERRIDE_LOGINS == {"myia-ai-01"}
    assert not (mod.LIFT_OVERRIDE_LOGINS & mod.ADJOINT_LIFT_LOGINS)
