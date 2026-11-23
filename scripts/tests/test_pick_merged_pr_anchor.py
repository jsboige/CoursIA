"""La surface « PR MERGEE » distingue une citation d'une enumeration (#24418).

La surface retenait un candidat des qu'un corps de PR contenait `#N`, quelle
que soit la forme de l'ancre. Un bilan de consolidation qui enumere quarante
numeros d'issues -- « …, #18671, #18763, #18770) » -- livrait donc des issues
qu'il ne livrait pas, et le tapis ne les proposait plus jamais.

La mesure qui fonde ce fichier (pool `--belt --json` du 2026-11-03, lane
myia-po-2025:CoursIA) a releve 4 candidats retenus par cette seule surface :
**1 faux positif** (#18763, PR #19232) et **3 livraisons reelles** (#21978,
#21221, #21097). Les trois servent de controle positif -- un detecteur se
valide par ses faux negatifs autant que par ses faux positifs, et un filtre
qui ne retiendrait plus rien passerait le test negatif en trompe-l'oeil.

Les chaines de ce fichier sont verbatim, extraites des corps de PR citees.
"""

import datetime as dt
import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import pick_idle_grain  # noqa: E402
from pick_idle_grain import (  # noqa: E402
    _ENUMERATION_MIN_ANCHORS,
    anchor_is_citation,
    merged_pr_signal,
)

# --- Fixtures verbatim -------------------------------------------------------
# PR #19232 (merged 2026-10-05), corps : deux listes d'issues orphelines.
PR_19232_LINE_1 = (
    "…, #18393, #18408, #18434, #18873), Lean docs (#18286, #18430, "
    "#18624), Lean/docs (#18671, #18763, #18770), Biblio Holistique "
    "(#19267-192"
)
PR_19232_LINE_2 = (
    "… #18423 #18430 #18434 #18545 #18578 #18601 #18624 #18671 #18684 "
    "#18703 #18706 #18731 #18732 #18763 #18770 #18873 #18889 #18898 "
    "#18902 #189"
)
# PR #21985 (merged 2026-10-22) : titre conventionnel + clause de liaison.
PR_21985_TITLE = (
    "Add(ci,#21978): script versionne de creation des slots runner persist "
    "po-2024"
)
# PR #21815 (merged 2026-10-24) : idem.
PR_21815_TITLE = (
    "fix(genai,#21097): Barbie-Schreck -- illustrations ComfyUI restaurees "
    "(sorties reexecutees + une ligne de prose)"
)


# --- Le faux positif mesure --------------------------------------------------

def test_enumeration_only_is_not_a_citation():
    """#18763 dans #19232 : deux listes, aucune forme de liaison."""
    body = PR_19232_LINE_1 + "\n" + PR_19232_LINE_2
    assert anchor_is_citation(body, 18763) is False


def test_enumeration_below_the_threshold_stays_a_citation():
    """Une ligne courte n'est pas une liste : la voie par defaut reste la citation.

    Le filtre ne retire que la forme dont la signature est sans ambiguite.
    Trois numeros dans une phrase restent une citation -- c'est le garde
    contre le faux negatif (livraison reelle transformee en candidat re-servi).
    """
    line = "cette PR livre #21221, #21236 et #21242"
    assert len(pick_idle_grain._ANY_ANCHOR_RE.findall(line)) < (
        _ENUMERATION_MIN_ANCHORS)
    assert anchor_is_citation(line, 21221) is True


# --- Les trois livraisons reelles (controle positif) -------------------------

def test_conventional_title_scope_is_a_citation():
    """`type(scope,#N)` en tete de titre : la forme la plus courante du depot."""
    assert anchor_is_citation(PR_21985_TITLE, 21978) is True
    assert anchor_is_citation(PR_21815_TITLE, 21097) is True


def test_see_clause_is_a_citation():
    """`See #N` en pied de corps, forme canonique de #21236 et #21815."""
    assert anchor_is_citation("…  See #21221\n", 21221) is True
    assert anchor_is_citation("…  See #21097 (passe APP3, volet Barbie-Sc)",
                              21097) is True


def test_linking_clause_wins_inside_a_list_line():
    """Une clause de liaison dans une ligne de liste compte quand meme.

    Une revue de bilan peut citer une issue parmi d'autres en la NOMMANT :
    « voir #N » est une revendication, la liste qui l'entoure n'y change rien.
    """
    line = ("#18001 #18002 #18003 voir #18763 #18004")
    assert len(pick_idle_grain._ANY_ANCHOR_RE.findall(line)) >= (
        _ENUMERATION_MIN_ANCHORS)
    assert anchor_is_citation(line, 18763) is True


def test_closing_keywords_are_citations():
    for form in ("Closes #42", "Fixes #42", "fixed #42", "Resolves #42",
                 "Part of #42", "Refs #42", "Suite de #42"):
        assert anchor_is_citation(form, 42) is True, form


# --- Garde-fous d'ancre ------------------------------------------------------

def test_absent_issue_is_not_a_citation():
    assert anchor_is_citation("aucune ancre ici", 18763) is False


def test_substring_collision_is_ignored():
    """`#1170391` ne cite pas `#11703` (doctrine `#N\\b`, cf #17760)."""
    assert anchor_is_citation("commit #1170391 dans la liste", 11703) is False


# --- Cablage : merged_pr_signal applique bien le filtre ----------------------

def _fake_gh(monkeypatch, prs):
    class _Result:
        def __init__(self, payload):
            self.stdout = json.dumps(payload)
            self.returncode = 0
            self.stderr = ""

    monkeypatch.setattr(pick_idle_grain.subprocess, "run",
                        lambda *a, **k: _Result(prs))


def _recent_merged_at(days_ago=5):
    """`mergedAt` dans la fenetre, pour que le test ne passe pas par peremption.

    Le corps des PRs est verbatim (c'est lui qui est teste) ; seule la date
    est relative, sinon ces deux tests changeraient de sens en janvier.
    """
    stamp = (dt.datetime.now(dt.timezone.utc)
             - dt.timedelta(days=days_ago))
    return stamp.strftime("%Y-%m-%dT%H:%M:%SZ")


def test_merged_pr_signal_ignores_an_enumeration_only_pr(monkeypatch):
    """Controle de bout en bout du cas #18763 : plus de signal de livraison."""
    _fake_gh(monkeypatch, [{
        "number": 19232, "state": "MERGED",
        "mergedAt": _recent_merged_at(),
        "title": "docs(consolidation,#16473): acceptance 2 lots",
        "body": PR_19232_LINE_1 + "\n" + PR_19232_LINE_2,
    }])
    assert merged_pr_signal(18763) is False


def test_merged_pr_signal_keeps_a_real_delivery(monkeypatch):
    """Controle positif : la PR #21985 est une vraie livraison de #21978."""
    _fake_gh(monkeypatch, [{
        "number": 21985, "state": "MERGED",
        "mergedAt": _recent_merged_at(),
        "title": PR_21985_TITLE,
        "body": "See #21978",
    }])
    assert merged_pr_signal(21978) is not False
