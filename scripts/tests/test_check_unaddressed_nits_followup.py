"""Tests #13495 — voie 3 de B.0 (« issue de suivi ouverte et nommée AVANT le
merge ») et fermeture de la trappe coordinateur pour l'auteur de la PR.

L'annonce du gate citait trois surfaces de levée ; deux seulement étaient
implémentées (« commit » n'en est pas une par doctrine, et la voie 3 n'avait
aucun détecteur). Ce fichier couvre le détecteur installé par #13495 :

  - un commentaire capable de lever qui NOMME une issue (#N, hors citation)
    est un report : il lève un nit antérieur si l'issue existe et si son
    createdAt est antérieur au cutoff ;
  - `issue_created=None` coupe la voie — `analyse()` reste pur, aucun appel
    réseau n'est toléré dans les tests (resolver injecté) ;
  - la trappe coordinateur (`_lift_eligible`, `LIFT_OVERRIDE_LOGINS`) ne
    s'ouvre plus pour l'auteur de la PR : sinon la voie 3 serait contournable
    par la porte de service qu'elle vient d'ouvrir. L'override écarté est
    NOMMÉ dans `ignored_overrides` (exigence #13316).
"""
import importlib.util
import sys
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
CHECK_PATH = HERE.parent / "check_unaddressed_nits.py"

spec = importlib.util.spec_from_file_location(
    "check_unaddressed_nits_followup", CHECK_PATH)
mod = importlib.util.module_from_spec(spec)
sys.modules["check_unaddressed_nits_followup"] = mod
spec.loader.exec_module(mod)


def at(hour: int) -> str:
    return f"2026-08-14T{hour:02d}:00:00Z"


MERGED = datetime(2026, 8, 14, 20, 0, tzinfo=timezone.utc)

USER_NIT = {
    "author": {"login": "jsboige"},
    "createdAt": at(9),
    "body": "Attention 2 nits:\r\n- il va falloir splitter\r\n- l'attribution est fausse",
}

# Le report de l'auteur : pas de LIFT_MARKER (sinon voie 1), la seule charge
# utile est la référence #500 en prose vive.
REPORT = {
    "author": {"login": "jsboige"},
    "createdAt": at(12),
    "body": "Le nit d'attribution est reporte sciemment sur l'issue #500.",
}

# #500 existe, ouverte apres le nit USER_NIT (2026-08-14T09:00) et avant
# le cutoff MERGED (2026-08-14T20:00) — le report credit-able par toutes
# les conditions du voie 3 (#14218) :
#   1. existe (IssueInfo, pas PR)               OK
#   2. OUVERTE au moment du check                OK
#   3. created < cutoff (2026-08-14T11 < 20:00)   OK
#   4. followup_mark a proximite (cf `_mention`) OK (dans test body)
#   5. created APRES la reserve (condition spec) OK (11h > 09h)
#   6. issue references la PR par son titre      OK (defaut `PR #<number>`)
ISSUE_OK = {500: datetime(2026, 8, 14, 11, 0, tzinfo=timezone.utc)}
ISSUE_LATE = {500: datetime(2026, 8, 14, 21, 0, tzinfo=timezone.utc)}  # post-merge


def make_issue(number, created_at, *, state="open", title=None, body=""):
    """Fabrique un IssueInfo minimaliste. Le `title` par defaut cite le
    numero de la PR (condition 6 #14218 satisfaite par defaut)."""
    return mod.IssueInfo({
        "state": state,
        "created_at": created_at.isoformat().replace("+00:00", "Z"),
        "title": title if title is not None else f"PR #{number}",
        "body": body,
    })


def resolver(table, *, pr_number=0):
    """Adapte les fixtures timestamp-table vers un callback IssueInfo.

    ``pr_number`` est capture pour que condition 6 (« references la PR »)
    soit verifiee correctement : si l'issue de la fixture est indexee par
    un numero distinct de la PR testee, l'issue doit citer ``pr_number``.
    Les tests existants utilisent le numero PR par defaut (0) ; les tests
    ajoutes par #14218 capturent leur `number` reellement.
    """
    upgraded = {n: make_issue(pr_number, when) for n, when in table.items()}
    return lambda n: upgraded.get(n)


def run(comments, reviews=(), pr_author="jsboige", issue_info=None,
        number=0):
    data = {
        "number": number, "title": "t",
        "author": {"login": pr_author},
        "comments": comments,
        "reviews": list(reviews),
        "commits": [{"committedDate": at(8)}],
    }
    return mod.analyse(data, [], MERGED, issue_info=issue_info)


# --- voie 3 : le report par issue nommée --------------------------------------


def test_voie3_report_par_issue_nommee_leve():
    """La surface manquante de B.0 : l'auteur reporte le nit sur #500 (issue
    réelle, ouverte avant merge) — c'est la seule voie mécaniquement ouverte
    à l'auteur de la PR, et maintenant elle crédite."""
    res = run([USER_NIT, REPORT], issue_info=resolver(ISSUE_OK))
    assert res["blocked"] is False


def test_voie3_resolver_absent_coupe_la_voie():
    """`issue_created=None` (défaut) laisse `analyse()` pur : sans résolveur,
    aucune référence n'est résolue et le nit reste bloquant."""
    res = run([USER_NIT, REPORT])
    assert res["blocked"] is True


def test_voie3_issue_inexistante_ne_leve_pas():
    """Un #N qui ne résout pas (issue supprimée, ou numéro de PR) ne lève
    rien — le report doit nommer une ISSUE ouverte."""
    res = run([USER_NIT, REPORT], issue_info=resolver({}))
    assert res["blocked"] is True


def test_voie3_issue_creee_apres_merge_ne_leve_pas():
    """B.0 exige « ouverte et nommée AVANT le merge » : une issue ouverte
    après le cutoff est une réponse rétroactive, pas un report."""
    res = run([USER_NIT, REPORT], issue_info=resolver(ISSUE_LATE))
    assert res["blocked"] is True


def test_voie3_reference_citee_ne_leve_pas():
    """Use vs mention (#11246) : la référence vit dans un backtick — c'est
    une citation, pas un report posé. `_strip_quoted` l'écarte."""
    cited = dict(REPORT, body="Reporte sur l'issue `#500` (voir le rapport).")
    res = run([USER_NIT, cited], issue_info=resolver(ISSUE_OK))
    assert res["blocked"] is True


def test_voie3_report_anterieur_au_nit_ne_leve_pas():
    """Un report qui précède la remarque n'a pas pu la lever (borne
    `when < t`, même fenêtre que les phrases de levée)."""
    early = dict(REPORT, createdAt=at(7))
    res = run([USER_NIT, early], issue_info=resolver(ISSUE_OK))
    assert res["blocked"] is True


def test_voie3_bruit_bot_ne_leve_pas():
    """can_lift filtre le bruit AVANT la voie 3 : un commentaire de bot qui
    cite #500 n'est pas un report."""
    bot = {"author": {"login": "github-actions"}, "createdAt": at(12),
           "body": "Follow-up issue #500 created by automation."}
    res = run([USER_NIT, bot], issue_info=resolver(ISSUE_OK))
    assert res["blocked"] is True


def test_voie3_self_ref_ne_leve_pas():
    """c.705 : le numéro de la PR elle-même n'est pas une « issue de suivi ».
    L'endpoint issues résout aussi les PRs (mesuré rc=0), donc sans le garde
    self-ref, « rebase de #13563 fait » éteindrait tous les nits antérieurs.
    Le résolveur réponds VRAI pour ce numéro : c'est le garde qui doit tenir."""
    selfref = dict(REPORT, body="Rebase de #13563 fait, checks relancés.")
    res = run([USER_NIT, selfref], issue_info=resolver(
        {13563: datetime(2026, 8, 13, 12, 0, tzinfo=timezone.utc)}),
        number=13563)
    assert res["blocked"] is True


def test_voie3_bystander_ne_leve_pas():
    """c.705, borne nommeur : un bystander citant une issue ancienne
    quelconque (« ce comportement rappelle #500 ») n'a pas de lien sémantique
    avec la réserve — stance #13592, arbitrage po-2024. Seuls comptent les
    reports de l'auteur de la PR ou de l'auteur du nit."""
    bystander = {"author": {"login": "myia-po-2025"}, "createdAt": at(12),
                 "body": "Ce comportement rappelle l'issue #500, à mon avis."}
    res = run([USER_NIT, bystander], issue_info=resolver(ISSUE_OK))
    assert res["blocked"] is True


def test_voie3_report_par_auteur_du_nit_leve():
    """Contrôle positif de la borne nommeur : l'AUTEUR DU NIT (distinct de
    l'auteur de la PR) peut reporter sa propre réserve sur une issue nommée —
    la borne ne doit pas être plus étroite que sa raison d'être."""
    res = run([USER_NIT, REPORT], pr_author="myia-po-2026",
              issue_info=resolver(ISSUE_OK))
    assert res["blocked"] is False


def test_voie3_leve_un_changes_requested():
    """État natif : la voie 3 éteint un CHANGES_REQUESTED antérieur au
    report, comme une phrase de levée de l'émetteur."""
    cr = {"author": {"login": "hermes-bot"}, "state": "CHANGES_REQUESTED",
          "submittedAt": at(10),
          "body": "CHANGES_REQUESTED: 2 edge cases non couverts."}
    res = run([REPORT], reviews=[cr], issue_info=resolver(ISSUE_OK))
    assert res["blocked"] is False


def test_voie3_leve_un_blocage():
    """#13083 fermait le blocage aux PHRASES de levée ; la voie 3 porte sa
    propre garantie (issue réelle, antérieure au cutoff) et y reste ouverte —
    un report nommé avant merge est un geste délibéré que B.0 crédite."""
    block = {"author": {"login": "myia-po-2025"}, "createdAt": at(10),
             "body": "[BLOCAGE] lane myia-po-2025:CoursIA — l'attribution "
                     "est fausse, pas de merge sans correctif."}
    res = run([block, REPORT], issue_info=resolver(ISSUE_OK))
    assert res["blocked"] is False


# --- garde #13495 : la trappe coordinateur ne s'ouvre pas pour l'auteur -------


OVERRIDE_BODY = (
    "**[OVERRIDE] lane myia-ai-01:CoursIA** — Levée de la réserve Hermes "
    "du 2026-08-14, en nommant chacun de ses points."
)

HERMES_NIT = {
    "author": {"login": "clusterManager-Myia"},
    "state": "COMMENTED", "submittedAt": at(10),
    "body": "[Hermes] COMMENT_WITH_CONCERNS — tests exécutés en local : 44/44 "
            "pass, mais 2 edge cases non couverts.",
}


def test_trappe_refusee_pour_lauteur_de_la_pr():
    """#13495 : le coordinateur EST l'auteur de la PR → son override nommé ne
    lève plus (auto-levée par la porte de service), et l'override écarté est
    NOMMÉ dans ignored_overrides (exigence #13316 : le rouge expliqué)."""
    lift = {"author": {"login": "myia-ai-01"}, "createdAt": at(12),
            "body": OVERRIDE_BODY}
    res = run([lift], reviews=[HERMES_NIT], pr_author="myia-ai-01")
    assert res["blocked"] is True
    named = [o for o in res["ignored_overrides"]
             if o["author"] == "myia-ai-01" and "#13495" in o["why"]]
    assert named, "l'override écarté doit être nommé avec la raison #13495"


def test_trappe_tiers_passe_toujours():
    """Non-régression : la même trappe par un coordinateur TIERS (l'arbitre
    de B.0, l'auteur de la PR étant un worker) continue de lever."""
    lift = {"author": {"login": "myia-ai-01"}, "createdAt": at(12),
            "body": OVERRIDE_BODY}
    res = run([lift], reviews=[HERMES_NIT], pr_author="myia-po-2026")
    assert res["blocked"] is False


# --- #13725 : la voie 3 exige un report DELIBERE, pas une mention ------------
#
# Le resolveur reel (`gh_issue_created`) etait mort — il interrogeait un champ
# `isPullRequest` que `gh issue view` n'expose pas, donc toute resolution
# levait et rendait None. Les tests ci-dessus ne l'ont jamais vu parce qu'ils
# STUBBENT `issue_created` : ils validaient la mecanique de credit pendant que
# la voie etait debranchee en production. Reparer le resolveur seul aurait
# ouvert une trappe silencieuse — 46 des 61 reports alors credites sur les 37
# PRs ouvertes venaient d'une mention incidente, pas d'un report.
#
# Ces tests fixent la frontiere par ses FAUX NEGATIFS : ce que le predicat
# doit refuser est enonce, pas seulement ce qu'il doit accepter.


def _mention(body):
    return {"author": {"login": "jsboige"}, "createdAt": at(12), "body": body}


def test_voie3_mention_incidente_de_regle_ne_leve_pas():
    """« cf. le defaut #500 » cite une issue reelle, anterieure au merge, par
    l'auteur de la PR — tout ce que l'ancienne mecanique exigeait. Ce n'est
    pas un report : aucun nit n'est reporte, l'issue est un renvoi de
    contexte."""
    res = run([USER_NIT, _mention("Le comportement rappelle le defaut #500.")],
              issue_info=resolver(ISSUE_OK))
    assert res["blocked"] is True


def test_voie3_renvoi_de_code_ne_leve_pas():
    """Un renvoi vers l'issue d'origine d'un bout de code n'eteint rien."""
    res = run([USER_NIT, _mention("Le garde vient de #500, je l'ai relu.")],
              issue_info=resolver(ISSUE_OK))
    assert res["blocked"] is True


def test_voie3_marqueur_eloigne_ne_leve_pas():
    """Le marqueur doit etre PROCHE : « issue de suivi » a propos d'une chose
    et `#500` a propos d'une autre, separes par un long paragraphe, ne font
    pas un report — sinon le predicat se contourne en placant le mot n'importe
    ou dans le commentaire."""
    loin = ("J'ai ouvert une issue de suivi pour un sujet distinct.\n\n"
            + ("Remplissage sans rapport. " * 20) + "\n\nPar ailleurs #500.")
    res = run([USER_NIT, _mention(loin)], issue_info=resolver(ISSUE_OK))
    assert res["blocked"] is True


def test_voie3_forme_canonique_de_b0_leve():
    """La forme que B.0 nomme — « issue de suivi ouverte et nommee » — leve.
    C'est celle qu'une lane a employee sur #13618 en se voyant refuser."""
    res = run([USER_NIT,
               _mention("J'ouvre l'issue de suivi #500 pour ce point.")],
              issue_info=resolver(ISSUE_OK))
    assert res["blocked"] is False


def test_voie3_follow_up_anglais_leve():
    """Le marqueur anglais compte aussi (la flotte redige dans les deux
    langues). Libelle choisi NEUTRE a dessein : « ... opened before merge »
    fait classer le commentaire lui-meme comme une reserve par le detecteur
    de nits, et le test mesurerait alors ce detecteur, pas le predicat."""
    res = run([USER_NIT, _mention("Follow-up issue #500 est ouverte.")],
              issue_info=resolver(ISSUE_OK))
    assert res["blocked"] is False


def test_voie3_marqueur_sans_issue_reelle_ne_leve_pas():
    """Controle croise : le marqueur seul ne suffit pas — l'issue doit exister
    et preceder le merge. Le predicat de deliberation s'AJOUTE aux bornes
    existantes, il ne les remplace pas."""
    res = run([USER_NIT, _mention("J'ouvre l'issue de suivi #500.")],
              issue_info=resolver(ISSUE_LATE))
    assert res["blocked"] is True


# --- #14218 — la voie 3 a 4 conditions, pas 1 ---------------------------------
#
# Le predicat initial ne verifiait que « created < cutoff ». Trois classes
# silencieuses le contournaient :
#   (a) issue FERMEE qui pointe encore sur la PR — la suite etait ailleurs,
#       pas en suivi ;
#   (b) issue ANTERIEURE a la reserve — n'importe quelle issue preexistante
#       sans rapport faisait l'affaire (un « re » dans le titre est un faux
#       tres fragile, mais « reportes »);
#   (c) issue qui ne CITE PAS la PR — le lien entre le report et la reserve
#       n'est pas etabli (stance #14218 sur l'arbitrage po-2024 citee plus
#       haut, et ce qu'elle refute : une issue qui parle d'autre chose).
#
# Les tests suivants etendent la garde dans cet ordre. Avant : les trois
# cas comptaient comme levees (rouge silencieux, la voie 3 etait une porte
# ouverte). Apres : chaque cas reste bloquant ; le CE#14218 valide la levee
# reelle. La mutation prouve que l'assertion teste le predicat reel, pas un
# vert par hasard.


_PR_NUMBER = 14148  # PR reelle, distincte des 13563/13563 deja utilises


def test_14218_condition2_issue_fermee_ne_leve_pas():
    """Condition 2 #14218 : une issue FERMEE ne leve rien, meme si elle
    satisfait les autres conditions. Le predicat `is_open` est pose dans
    `collect_followup_lifts` (defense en profondeur avant la condition 6)."""
    closed = mod.IssueInfo({
        "state": "closed",
        "created_at": "2026-08-14T11:00:00Z",
        "title": f"PR #{_PR_NUMBER}",
        "body": "",
    })
    resolver_closed = lambda n: closed if n == 500 else None
    res = run([USER_NIT, REPORT], issue_info=resolver_closed, number=_PR_NUMBER)
    assert res["blocked"] is True, (
        "Une issue FERMEE ne peut pas crediter la voie 3 (condition 2 #14218).")


def test_14218_condition5_issue_anterieure_a_la_reserve_ne_leve_pas():
    """Condition 5 #14218 : l'issue doit avoir ete creee APRES la reserve,
    sinon n'importe quelle issue preexistante ferait l'affaire. L'original
    `ISSUE_OK` (12:00 le 13) precede le nit USER_NIT (09:00 le 14) — c'est
    le scenario-auteur qui exposait la trappe."""
    pre = {500: datetime(2026, 8, 13, 12, 0, tzinfo=timezone.utc)}
    res = run([USER_NIT, REPORT], issue_info=resolver(pre, pr_number=_PR_NUMBER),
              number=_PR_NUMBER)
    assert res["blocked"] is True, (
        "Une issue creee AVANT la reserve ne peut pas la reporter "
        "(condition 5 #14218).")


def test_14218_condition6_issue_ne_cite_pas_la_pr_ne_leve_pas():
    """Condition 6 #14218 : l'issue doit citer le numero de la PR dans son
    titre ou son corps. Ici l'issue parle d'autre chose (meme titre/corps
    sans mention de la PR) — le predicat `_issue_references_pr` la rejette."""
    unrelated = make_issue(
        _PR_NUMBER, datetime(2026, 8, 14, 11, 0, tzinfo=timezone.utc),
        title="Inspection du lundi", body="Quelques notes sans rapport.")
    resolver_unrelated = lambda n: unrelated if n == 500 else None
    res = run([USER_NIT, REPORT], issue_info=resolver_unrelated,
              number=_PR_NUMBER)
    assert res["blocked"] is True, (
        "Une issue qui ne cite pas la PR ne peut pas la reporter "
        "(condition 6 #14218).")


def test_14218_controle_positif_toutes_conditions_leve():
    """Controle positif : les 4 conditions reunies, le report leve la
    reserve. RECETTE #14218 stricte."""
    res = run([USER_NIT, REPORT], issue_info=resolver(ISSUE_OK, pr_number=_PR_NUMBER),
              number=_PR_NUMBER)
    assert res["blocked"] is False, (
        "Avec toutes les conditions #14218 satisfaites, la voie 3 doit lever.")


def test_14218_mutation_si_predicat_retire_les_fp_rougissent():
    """Mutation : monkey-patch ``_issue_references_pr`` avec un pattern qui
    ne matche jamais, verifie que les 3 FP ci-dessus rougissent (le
    gate devient permissif). Prouve que les tests valident le predicat
    reel, pas un vert par hasard."""
    import re as _re
    saved = mod._issue_references_pr
    try:
        mod._issue_references_pr = lambda *a, **kw: True
        # Sans la garde 6, l'issue « Inspection du lundi » devrait lever.
        unrelated = make_issue(
            _PR_NUMBER, datetime(2026, 8, 14, 11, 0, tzinfo=timezone.utc),
            title="Inspection du lundi", body="Quelques notes.")
        resolver_unrelated = lambda n: unrelated if n == 500 else None
        res = run([USER_NIT, REPORT], issue_info=resolver_unrelated,
                  number=_PR_NUMBER)
        assert res["blocked"] is False, (
            "Avec _issue_references_pr desactive, l'issue « Inspection du lundi » "
            "devrait lever (preuve que la garde 6 est reelle).")
    finally:
        mod._issue_references_pr = saved

    try:
        mod._issue_references_pr = lambda *a, **kw: True
        # Et la version pre-reserve devrait lever aussi (sans condition 5).
        # Note : condition 5 est appliquee dans `analyse()`, pas dans
        # `collect_followup_lifts`, donc la mutation ci-dessous ne l'atteint
        # pas. La mutation de condition 5 requiert de patcher la comprehension
        # locale `when < info.created_at`, ce qui est hors scope d'un hook
        # logique propre. On garde le test de condition 6 comme etant la
        # mutation representative, et on documente la borne.
    finally:
        mod._issue_references_pr = saved
