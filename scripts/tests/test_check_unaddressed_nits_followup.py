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

# #500 existe, ouverte la veille du merge — le report créditable de B.0.
ISSUE_OK = {500: datetime(2026, 8, 13, 12, 0, tzinfo=timezone.utc)}
ISSUE_LATE = {500: datetime(2026, 8, 14, 21, 0, tzinfo=timezone.utc)}  # post-merge


def resolver(table):
    return lambda n: table.get(n)


def run(comments, reviews=(), pr_author="jsboige", issue_created=None):
    data = {
        "number": 0, "title": "t",
        "author": {"login": pr_author},
        "comments": comments,
        "reviews": list(reviews),
        "commits": [{"committedDate": at(8)}],
    }
    return mod.analyse(data, [], MERGED, issue_created=issue_created)


# --- voie 3 : le report par issue nommée --------------------------------------


def test_voie3_report_par_issue_nommee_leve():
    """La surface manquante de B.0 : l'auteur reporte le nit sur #500 (issue
    réelle, ouverte avant merge) — c'est la seule voie mécaniquement ouverte
    à l'auteur de la PR, et maintenant elle crédite."""
    res = run([USER_NIT, REPORT], issue_created=resolver(ISSUE_OK))
    assert res["blocked"] is False


def test_voie3_resolver_absent_coupe_la_voie():
    """`issue_created=None` (défaut) laisse `analyse()` pur : sans résolveur,
    aucune référence n'est résolue et le nit reste bloquant."""
    res = run([USER_NIT, REPORT])
    assert res["blocked"] is True


def test_voie3_issue_inexistante_ne_leve_pas():
    """Un #N qui ne résout pas (issue supprimée, ou numéro de PR) ne lève
    rien — le report doit nommer une ISSUE ouverte."""
    res = run([USER_NIT, REPORT], issue_created=resolver({}))
    assert res["blocked"] is True


def test_voie3_issue_creee_apres_merge_ne_leve_pas():
    """B.0 exige « ouverte et nommée AVANT le merge » : une issue ouverte
    après le cutoff est une réponse rétroactive, pas un report."""
    res = run([USER_NIT, REPORT], issue_created=resolver(ISSUE_LATE))
    assert res["blocked"] is True


def test_voie3_reference_citee_ne_leve_pas():
    """Use vs mention (#11246) : la référence vit dans un backtick — c'est
    une citation, pas un report posé. `_strip_quoted` l'écarte."""
    cited = dict(REPORT, body="Reporte sur l'issue `#500` (voir le rapport).")
    res = run([USER_NIT, cited], issue_created=resolver(ISSUE_OK))
    assert res["blocked"] is True


def test_voie3_report_anterieur_au_nit_ne_leve_pas():
    """Un report qui précède la remarque n'a pas pu la lever (borne
    `when < t`, même fenêtre que les phrases de levée)."""
    early = dict(REPORT, createdAt=at(7))
    res = run([USER_NIT, early], issue_created=resolver(ISSUE_OK))
    assert res["blocked"] is True


def test_voie3_bruit_bot_ne_leve_pas():
    """can_lift filtre le bruit AVANT la voie 3 : un commentaire de bot qui
    cite #500 n'est pas un report."""
    bot = {"author": {"login": "github-actions"}, "createdAt": at(12),
           "body": "Follow-up issue #500 created by automation."}
    res = run([USER_NIT, bot], issue_created=resolver(ISSUE_OK))
    assert res["blocked"] is True


def test_voie3_leve_un_changes_requested():
    """État natif : la voie 3 éteint un CHANGES_REQUESTED antérieur au
    report, comme une phrase de levée de l'émetteur."""
    cr = {"author": {"login": "hermes-bot"}, "state": "CHANGES_REQUESTED",
          "submittedAt": at(10),
          "body": "CHANGES_REQUESTED: 2 edge cases non couverts."}
    res = run([REPORT], reviews=[cr], issue_created=resolver(ISSUE_OK))
    assert res["blocked"] is False


def test_voie3_leve_un_blocage():
    """#13083 fermait le blocage aux PHRASES de levée ; la voie 3 porte sa
    propre garantie (issue réelle, antérieure au cutoff) et y reste ouverte —
    un report nommé avant merge est un geste délibéré que B.0 crédite."""
    block = {"author": {"login": "myia-po-2025"}, "createdAt": at(10),
             "body": "[BLOCAGE] lane myia-po-2025:CoursIA — l'attribution "
                     "est fausse, pas de merge sans correctif."}
    res = run([block, REPORT], issue_created=resolver(ISSUE_OK))
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
