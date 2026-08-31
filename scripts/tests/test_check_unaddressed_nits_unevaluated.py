"""Tests #13779 — l'echappatoire « A RELIRE » ne masque plus, et ne sous-declare plus.

`_print_unevaluated` existe pour que l'organe CESSE DE CERTIFIER SON SILENCE
(#13512) : ce qu'il n'a pas su classer, il l'imprime. Deux defauts vidaient la
promesse de sa substance, tous deux dans la selection `to_read` :

  - **repli EXCLUSIF** : `after_lc or unevaluated[-3:]` — des qu'UN commentaire
    suivait le dernier commit, toute la queue anterieure sortait de
    l'affichage. Le critere presuppose qu'un commit traite ce qui le precede,
    quand B.0 dit l'inverse en toutes lettres (« un commit pousse apres la
    remarque ne la leve PAS a lui seul »).
  - **compte du sous-ensemble presente comme total** : l'en-tete imprimait
    `len(rows)`, pas `unevaluated_total`.

Mesure fondatrice, PR #13712 (2026-08-30) : 5 non evalues, 3 affiches — et
parmi les 2 masques, le `[ADJOINT PREFLIGHT]` de 19:30:49Z dont le point non
traite motivait le HOLD du coordinateur sur cette PR meme. Sur la seule PR ou
l'echappatoire a servi, elle a cache le commentaire qui justifiait le blocage,
et l'a cache parce qu'un commit etait passe apres lui.

Les tests sont ecrits par leurs FAUX NEGATIFS : chacun echoue sur le code
d'avant. Aucun appel reseau — `analyse()` est pur.
"""
import contextlib
import importlib.util
import io
import sys
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
CHECK_PATH = HERE.parent / "check_unaddressed_nits.py"

spec = importlib.util.spec_from_file_location(
    "check_unaddressed_nits_unevaluated", CHECK_PATH)
mod = importlib.util.module_from_spec(spec)
sys.modules["check_unaddressed_nits_unevaluated"] = mod
spec.loader.exec_module(mod)

COMMIT_AT = "2026-08-30T10:00:00Z"
CUTOFF = datetime(2026, 8, 30, 13, 0, tzinfo=timezone.utc)

# Prose sans aucun CONCERN_MARKERS : l'organe ne la classe pas — c'est admis,
# et c'est exactement la population que « A RELIRE » existe pour rendre visible.
PREFLIGHT = ("[ADJOINT PREFLIGHT] Relecture complete : le point 3 sur la "
             "provenance reste ouvert, la cellule 12 ne porte pas la sortie "
             "qu'annonce la prose.")
LATER = "[REPONSE PREFLIGHT] Les points 1 et 2 sont traites au nouveau head."


def _c(at, body, login="jsboige"):
    return {"author": {"login": login}, "createdAt": at, "body": body}


def _pr(comments, commit_at=COMMIT_AT):
    return {"number": 13712, "title": "t", "author": {"login": "jsboige"},
            "commits": [{"committedDate": commit_at}],
            "reviews": [], "comments": comments}


def _run(comments):
    return mod.analyse(_pr(comments), [], CUTOFF)


def test_13779_precondition_bodies_are_genuinely_unclassified():
    """Sans ca les tests suivants passeraient pour la mauvaise raison."""
    assert mod.classify("jsboige", PREFLIGHT) is None
    assert mod.classify("jsboige", LATER) is None


def test_13779_pre_last_commit_comment_survives_a_later_one():
    """LE faux negatif fondateur : un commit posterieur ne doit rien masquer."""
    res = _run([_c("2026-08-30T09:30:00Z", PREFLIGHT),
                _c("2026-08-30T11:00:00Z", LATER)])
    bodies = [u["body"] for u in res["unevaluated"]]
    assert PREFLIGHT in bodies, (
        "le commentaire anterieur au dernier commit a ete masque par "
        "l'existence d'un commentaire posterieur — defaut #13779")
    assert LATER in bodies
    assert res["unevaluated_total"] == 2


def test_13779_displayed_count_matches_total_when_nothing_is_omitted():
    """Le cas de la mesure #13712 : 5 non evalues, 5 affiches."""
    res = _run([_c("2026-08-30T09:%02d:00Z" % m, PREFLIGHT + str(m))
                for m in (10, 30)]
               + [_c("2026-08-30T11:%02d:00Z" % m, LATER + str(m))
                  for m in (0, 30, 45)])
    assert res["unevaluated_total"] == 5
    assert len(res["unevaluated"]) == 5


def test_13779_header_prints_the_total_not_the_displayed_count():
    """L'en-tete sous-declarait ce que l'organe n'avait pas lu."""
    res = _run([_c("2026-08-30T09:%02d:00Z" % m, PREFLIGHT + str(m))
                for m in (10, 20, 30, 40, 50)]
               + [_c("2026-08-30T11:00:00Z", LATER)])
    assert res["unevaluated_total"] == 6
    assert len(res["unevaluated"]) == 4, "1 posterieur + queue de 3 anterieurs"
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        mod._print_unevaluated(res)
    head = buf.getvalue()
    assert "A RELIRE : 6 commentaire(s)" in head, (
        "le compte imprime doit etre le TOTAL non evalue, pas les lignes "
        "affichees — sinon l'organe sous-declare son propre silence")
    assert "2 plus ancien(s) omis" in head, "l'omission doit etre NOMMEE"


def test_13779_tail_of_pre_last_commit_stays_bounded():
    """Composer les deux mecanismes ne doit pas rendre la sortie illisible."""
    res = _run([_c("2026-08-30T09:%02d:00Z" % m, PREFLIGHT + str(m))
                for m in range(0, 50, 10)]
               + [_c("2026-08-30T11:00:00Z", LATER)])
    before = [u for u in res["unevaluated"] if not u["after_last_commit"]]
    assert len(before) == 3, "la queue anterieure reste plafonnee a 3"
    assert res["unevaluated_total"] == 6


def test_13779_display_is_chronological():
    """L'anterieur se lit avant le posterieur, comme le fil de la PR."""
    res = _run([_c("2026-08-30T09:30:00Z", PREFLIGHT),
                _c("2026-08-30T11:00:00Z", LATER)])
    ats = [u["at"] for u in res["unevaluated"]]
    assert ats == sorted(ats)


def test_13779_no_posterior_comment_keeps_the_tail_behaviour():
    """Controle de non-regression : sans posterieur, l'ancien comportement."""
    res = _run([_c("2026-08-30T09:%02d:00Z" % m, PREFLIGHT + str(m))
                for m in range(0, 50, 10)])
    assert res["unevaluated_total"] == 5
    assert len(res["unevaluated"]) == 3


def test_13779_surfacing_never_blocks():
    """Rendre visible n'est pas bloquer : `unevaluated` ne touche aucun verdict."""
    res = _run([_c("2026-08-30T09:30:00Z", PREFLIGHT),
                _c("2026-08-30T11:00:00Z", LATER)])
    assert res["blocked"] is False
