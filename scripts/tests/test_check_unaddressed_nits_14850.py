"""Tests pour la discrimination de voie par meme login (#14850).

L'organe `check_unaddressed_nits.analyse` doit distinguer les LEVEES
legitimes par un auteur de meme login (persona, lane tierce, override
coordinateur) d'une VOIE NUE ordinaire, qui equivaut a une auto-reponse
de l'auteur de la reserve. Sans discrimination, une review `LGTM` voix
nue de `jsboige` eteint la reserve user posee en voix nue par `jsboige`.

Incident fondateur : PR #14795. Le commentaire `[myia-po-2024:CoursIA-2]
Reponse a la reserve user du 2026-09-05T18:09:49Z` etait comptabilise
comme levee alors qu'il n'etait qu'une voie nue sous meme login prefixee
d'une lane tierce -- sans que la clause de discrimination ne soit posee.

Acceptance :
  1. Voie NUE par meme login (LGTM, Verdict: OK, RAS, sans prefixe de
     role) ne leve PAS une reserve user en voix nue sous meme login.
  2. Un prefixe de LANE TIERCE `[machine:workspace]` leve la reserve
     (voie distincte, pas par le login mais par la lane prefixee).
  3. Un prefixe PERSONA `[Hermes]` / `[NanoClaw]` leve la reserve UNIQUEMENT
     si le nit est aussi en persona (extension de #14947 -- persona leve
     SA voix, pas celle du user nu).
  4. Un OVERRIDE coordinateur `[OVERRIDE] lane <machine>` leve la reserve
     (arbitre tiers nomme).
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
    return f"2026-09-05T{hour:02d}:00:00Z"


MERGED = datetime(2026, 9, 6, 18, 0, tzinfo=timezone.utc)

# Reserve user voix nue, posee 18:09:49Z (issue #14850, PR #14795 head).
# Le marqueur CONCERN_LABEL « Concern: » est en debut de paragraphe, ce qui
# satisfait la regex `^[\s*_#>\-]*concerns?\s*\d*\s*:` (L2375).
USER_RESERVE_NUE = {
    "author": {"login": "jsboige"},
    "createdAt": "2026-09-05T18:09:49Z",
    "body": "Concern: le retrait du S8 doit etre rebase-propre avant merge.\n"
            "Le contenu du carnet derive et le merge de la tranche D2 ne le "
            "corrige pas. Il va falloir rebaser proprement avant de merger.",
}


def run(comments, commits=None, threads=None, reviews=None, pr_author="jsboige",
        **extra):
    data = {
        "number": 0,
        "title": "t",
        "author": {"login": pr_author},
        "comments": comments,
        "reviews": reviews if reviews is not None else [],
        "commits": commits if commits is not None else [{"committedDate": at(17)}],
    }
    data.update(extra)
    return mod.analyse(data, threads or [], MERGED)


# -----------------------------------------------------------------------------
# Acceptance 1 -- Lift avec prefixe de ROLE (`[ai-01]`, etc.) NE leve PAS la
# reserve user nue sous meme login partage. Discrimination par scope-emetteur :
# la voie nue par meme login reste preservee (#12319) ; un prefixe de ROLE
# distinct du user (coordinateur, lane, autre agent) cree un scope distinct
# qui n'a pas voix sur la reserve voie nue du user.
# -----------------------------------------------------------------------------

def test_role_prefix_meme_login_ne_leve_pas_reserve_user_nue():
    """#14850 cas fondateur (21:11:29Z PR #14795) -- un `[ai-01] Je leve ma
    propre reserve` par `jsboige` n'eteint PAS la reserve user voix nue
    posee par `jsboige`. Le prefixe `[ai-01]` identifie un EMETTEUR distinct
    du user -- c'est le coordinateur lane, pas la voix du user.

    Avant le fix : la voie nue par meme login etait consideree comme
    self-lift legitime (voie 3 de l'ancien code `return True`) ; le filet
    acceptait une levee `[ai-01]` par `jsboige` comme eteignant la reserve
    voix nue de `jsboige`. Apres le fix : tout prefixe de ROLE generique
    dans le lift exclut la voie nue (scope-emetteur)."""
    lift_ai01 = {
        "author": {"login": "jsboige"},
        "createdAt": "2026-09-06T21:11:29Z",
        "body": "[ai-01] Je leve ma propre reserve -- elle est perimee, et "
                "c'est ma mesure qui l'a posee.",
    }
    res = run([USER_RESERVE_NUE, lift_ai01])
    assert res["blocked"] is True, (
        "Un prefixe de ROLE `[ai-01]` (coordinateur lane) dans le lift, "
        "meme avec EXPLICIT_LIFT_MARKER, n'a pas voix sur la reserve user "
        "voix nue sous meme login partage. C'est exactement le scope-emetteur "
        "de l'acceptance 1 de #14850 (incidente fondateur : PR #14795 "
        "commentaire 21:11:29Z)."
    )


def test_hold_directive_role_prefix_ne_leve_pas_reserve_user_nue():
    """Extension : un `[ai-01] HOLD merge` (directive de blocage) ne leve
    pas non plus la reserve user. Le prefixe de ROLE reste hors scope de
    la voie nue."""
    lift_hold = {
        "author": {"login": "jsboige"},
        "createdAt": "2026-09-06T02:35:35Z",
        "body": "[ai-01] HOLD merge -- la reserve user du 18:09:49Z n'est "
                "pas levee. Verdict protocole.",
    }
    res = run([USER_RESERVE_NUE, lift_hold])
    assert res["blocked"] is True, (
        "Un `[ai-01] HOLD merge` est un signal de protocole (directive "
        "coordinateur), pas une levee. Il ne leve pas une reserve user "
        "voix nue. Cf #14850 acceptance 1."
    )


# -----------------------------------------------------------------------------
# Acceptance 2 -- Cross-lane `[machine:workspace]` est SCOPEE a sa lane.
# -----------------------------------------------------------------------------
# Acceptance 2 dit "scoper la levee a l'emetteur, pas a la PR" (#14850 body).
# Un prefixe de lane tierce `[machine:workspace]` identifie un EMETTEUR
# distinct du user, mais PAS l'emetteur de la reserve voix nue. La levee
# est scopee a la lane -- elle leve les reserves de CETTE lane, pas les
# reserves user voix nue. Avant le fix, ce commentaire etait comptabilise
# comme levee PR-wide ; apres le fix, il est SCOPE a la lane.
#
# Reproduit le commentaire reel de #14795 :
# `[myia-po-2024:CoursIA-2] Reponse a la reserve user du 18:09:49Z`
# -- qui ne leve PAS la reserve voix nue de l'utilisateur, mais leverait
# une reserve `[myia-po-2024:CoursIA-2]` sur la meme PR.

def test_cross_lane_meme_login_ne_leve_pas_reserve_user_nue():
    """#14850 acceptance 2 : une levee prefixee d'une lane tierce
    (`[myia-po-2024:CoursIA-2]`) est SCOPEE a cette lane -- elle ne leve
    PAS une reserve voix nue user posee sous le meme login partage.

    Reproduit le cas fondateur #14795 : le commentaire 18:28:07Z
    `[myia-po-2024:CoursIA-2] Reponse a la reserve user du 18:09:49Z`
    etait comptabilise comme levee avant le fix (le filet acceptait la
    voie nue sous meme login comme levee PR-wide). Apres le fix, le
    prefixe de lane SCOPE la levee : cette lane ne leve que SES reserves.
    """
    lift_cross_lane = {
        "author": {"login": "jsboige"},
        "createdAt": "2026-09-05T18:28:07Z",
        "body": "[myia-po-2024:CoursIA-2] Reponse a la reserve user du "
                "2026-09-05T18:09:49Z. La tranche D2 est livree par "
                "668df097a2, kernel gametheory-wsl installe, 14/14 "
                "cellules OK. La reserve est levee.",
    }
    res = run([USER_RESERVE_NUE, lift_cross_lane])
    assert res["blocked"] is True, (
        "Une levee prefixee `[machine:workspace]` est scopee a CETTE lane. "
        "Elle ne leve pas une reserve voix nue du user -- c'est exactement "
        "le scope-emetteur de la voie 2 du fix #14850. Le cas fondateur "
        "#14795 18:28:07Z doit rendre blocked=True."
    )


def test_cross_lane_meme_login_leve_reserve_de_la_lane():
    """#14850 acceptance 2 (jumeau) : la levee scopee par lane leve
    les reserves DE CETTE LANE. Une reserve posee par la meme lane
    (avec le meme prefixe `[machine:workspace]`) est levee par une
    levee de meme lane -- c'est la voie 2 du fix, dans son volet
    levant (non-bloquant).
    """
    reserve_de_la_lane = {
        "author": {"login": "jsboige"},
        "createdAt": "2026-09-05T18:09:49Z",
        "body": "[myia-po-2024:CoursIA-2] Concern: la tranche D2 du "
                "carnet n'est pas alignee avec le merge prevu.",
    }
    lift_de_la_lane = {
        "author": {"login": "jsboige"},
        "createdAt": "2026-09-05T18:28:07Z",
        "body": "[myia-po-2024:CoursIA-2] Tranche D2 livree par "
                "668df097a2, kernel gametheory-wsl installe, 14/14 "
                "cellules OK. La reserve est levee.",
    }
    res = run([reserve_de_la_lane, lift_de_la_lane])
    assert res["blocked"] is False, (
        "Une levee scopee `[machine:workspace]` leve les reserves "
        "DE CETTE lane. La voie 2 du fix #14850 a un volet levant "
        "(meme lane)."
    )


# -----------------------------------------------------------------------------
# Acceptance 3 -- Extension de la garde #14947 : PERSONA leve SA voix,
# pas la voie nue du user. Si la reserve est nue, la levee persona est
# BLOQUEE (cf Voie 1 du fix).
# -----------------------------------------------------------------------------

def test_persona_meme_login_reserve_nue_bloquee():
    """#14947 (etendu #14850) -- une levee `[Hermes]` ne peut pas
    eteindre une reserve voix nue du user sous meme login. La garde
    #14947 tient ; la voie nue n'etait qu'un cas particulier que
    #14850 nommait explicitement."""
    lift_persona = {
        "author": {"login": "jsboige"},
        "createdAt": "2026-09-06T15:56:45Z",
        "body": "[Hermes] RAS sur le merge de la tranche D2, OK pour moi.",
    }
    res = run([USER_RESERVE_NUE, lift_persona])
    assert res["blocked"] is True, (
        "La persona leve SA propre voix, pas la voie nue du user. La "
        "garde #14947 doit rester effective ici -- sinon on reintroduit "
        "le defaut fondateur de #14937."
    )


def test_persona_meme_login_reserve_persona_leve():
    """Cas ou la persona leve SA reserve posee en persona sous meme login :
    voie 1 du fix -- la garde de #14947 tient (persona leve personne)."""
    user_reserve_persona = {
        "author": {"login": "jsboige"},
        "createdAt": "2026-09-05T18:09:49Z",
        "body": "[Hermes] Concern: l'attribution est ambigue, il faudrait "
                "un lemma dedie.",
    }
    lift_persona_qui_leve = {
        "author": {"login": "jsboige"},
        "createdAt": "2026-09-05T19:26:40Z",
        "body": "[Hermes] Lemma dedie ajoute, attribution clarifiee.",
    }
    res = run([user_reserve_persona, lift_persona_qui_leve])
    assert res["blocked"] is False, (
        "La persona leve SA reserve posee en persona : voie 1 du fix, "
        "compatible avec la garde de #14947."
    )


# -----------------------------------------------------------------------------
# Acceptance 4 -- OVERRIDE coordinateur leve la reserve, meme login.
# -----------------------------------------------------------------------------

def test_override_coordinateur_leve_reserve_nue():
    """L'arbitre tiers nomme par `[OVERRIDE] lane <machine>` leve la
    reserve. Meme login ou pas, le discriminant OVERRIDE est le 3e voie
    du fix #14850. Tell c.11639."""
    lift_override = {
        "author": {"login": "jsboige"},
        "createdAt": "2026-09-06T15:56:45Z",
        "body": "[OVERRIDE] lane myia-ai-01 : la reserve est levee par "
                "autorite coordinateur.",
    }
    res = run([USER_RESERVE_NUE, lift_override])
    assert res["blocked"] is False, (
        "L'override coordinateur est le 3e voie du fix #14850 (Tell "
        "c.11639). La reserve est levee par autorite coordinateur, "
        "independamment du login."
    )


# -----------------------------------------------------------------------------
# Anti-regression -- la garde CROSS-LOGIN (#13609) tient toujours.
# -----------------------------------------------------------------------------
#
# Note d'implementation : `_lift_eligible` (L3555+) ne reconnait que trois
# categories de levee :
#   - meme login AVEC discriminant (persona, cross-lane prefixe, override
#     coordinateur) -- fix #14850
#   - jsboige leveant la reserve d'une PERSONA cross-login (#13609,
#     Hermes/NanoClaw poste sous clusterManager-Myia puis levee sous
#     jsboige)
#   - override coordinateur (myia-ai-01 + [OVERRIDE] lane <machine>)
#
# Le cas general "un tiers anonyme leve la reserve user" n'est PAS
# couvert : `_lift_eligible` retourne False des lors que `lift_author !=
# nit_author` et qu'aucun des discriminants ci-dessus n'est porte. Les
# tests suivants verifient donc que ce comportement historique tient
# apres le fix #14850 : aucun court-circuit ne doit s'ouvrir pour les
# tiers anonymes.

def test_cross_login_tiers_anonyme_ne_leve_pas():
    """Comportement historique : un commentaire par un tiers anonyme
    (login distinct, ni persona, ni override) NE leve PAS la reserve
    user sous ce depot. La porte est fermee par `_lift_eligible` meme
    apres le fix #14850 (la voie nue par meme login reste la cible du
    fix ; ici on est cross-login, et le filet est deja en place)."""
    user_reserve = {
        "author": {"login": "jsboige"},
        "createdAt": "2026-09-05T18:09:49Z",
        "body": "Concern: l'attribution est ambigue, il va falloir la corriger.",
    }
    lift_tiers = {
        "author": {"login": "another-contributor"},
        "createdAt": "2026-09-05T19:26:40Z",
        "body": "Verdict : LGTM, je laisse passer. Les nits sont adresses.",
    }
    res = run([user_reserve, lift_tiers])
    assert res["blocked"] is True, (
        "Le filet `_lift_eligible` reste ferme pour un tiers anonyme : "
        "le seul chemin de levee par un tiers non-coordinateur est la "
        "voie #13609 (persona Hermes/NanoClaw sous jsboige levant SA "
        "reserve posee sous clusterManager-Myia)."
    )


def test_cross_login_persona_ne_leve_pas_reserve_user():
    """Symetrique : la persona levee sous l'autre login ne leve PAS
    une reserve posee par l'utilisateur (jsboige). La garde #13609
    porte SPECIFIQUEMENT sur le sens `jsboige leve reserve persona`,
    pas l'inverse. Sans cette borne, la persona pourrait eteindre la
    voix du user sous pretexte d'alias de compte."""
    user_reserve = {
        "author": {"login": "jsboige"},
        "createdAt": "2026-09-05T18:09:49Z",
        "body": "Concern: l'attribution est ambigue, il va falloir la corriger.",
    }
    lift_persona_cross_login = {
        "author": {"login": "clusterManager-Myia"},
        "createdAt": "2026-09-05T19:26:40Z",
        "body": "[Hermes] RAS, attribution traitee dans le dernier commit. "
                "Les nits sont adresses.",
    }
    res = run([user_reserve, lift_persona_cross_login])
    assert res["blocked"] is True, (
        "La garde #13609 est ORIONTEE : jsboige leve la reserve d'une "
        "persona, pas l'inverse. Le commentaire [Hermes] par "
        "clusterManager-Myia ne leve donc pas une reserve posee par "
        "jsboige -- c'est exactement la protection de la voix user "
        "que la voie nue par meme login de #14850 renforce."
    )
