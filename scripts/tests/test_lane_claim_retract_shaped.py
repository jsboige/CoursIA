#!/usr/bin/env python3
"""#20128 -- un composite de levee a SYNONYME doit produire l'avertissement.

Rejoue l'incident mesure le 2026-10-09 sur l'issue #20083, verbatim : la lane
`myia-po-2027:CoursIA-2` y a poste `[CLAIMED-RETRACT]` a 12:32:10Z en croyant
rendre le grain. Le token etait **vu** par `_find_suspected_typo_markers`
(`kind='compose'`) mais `is_release_shaped` rendait `False` -- parce que
`RETRACT` n'est pas dans `_CLOSE` -- donc l'avertissement construit par #15982
etait **saute en silence**, et la PR #20084 d'une AUTRE lane est restee bloquee
par un mot absent d'un ensemble de cinq.

Deux garanties que ce fichier epingle, et qui vont ensemble :

1. **le geste est DESORMAIS DIT** -- l'auteur apprend que sa retractation n'a pas
   ete lue, et quelle forme le reduceur lit ;
2. **il n'est toujours PAS ENACTE** -- `[CLAIMED-RETRACT]` ne leve pas le claim,
   la PR reste bloquee. C'est la doctrine #12624 (« on signale, on n'enacte
   pas ») : elargir la RECONNAISSANCE ne doit pas elargir l'ACTION.

Run: python -m pytest scripts/tests/test_lane_claim_retract_shaped.py
"""
import re
import sys
from datetime import datetime, timezone
from pathlib import Path

_HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(_HERE))
sys.path.insert(0, str(_HERE / "ci"))

import check_lane_claim as clc  # noqa: E402
import lane_claim_required as lcr  # noqa: E402


# --- helpers -----------------------------------------------------------------

def comment(body, created_at, author="jsboige"):
    return {
        "body": body,
        "createdAt": created_at,
        "author": {"login": author},
        "url": None,
    }


def payload(*comments, number=20083, title="t"):
    return {"number": number, "title": title, "comments": list(comments)}


# Le fil reel de #20083, dans son ordre. c1 : claim de la lane du demandeur.
# c2 : claim concurrent. c3 : la RETRACTATION, ecrite avec un synonyme.
_C1 = comment(
    "[CLAIMED] lane myia-po-2024:CoursIA-3 -- outil et premiere matrice de "
    "correlation hebdomadaire de la ligue -- paths: scripts/league_correlation.py",
    "2026-10-09T12:03:07Z",
)
_C2 = comment(
    "Grain: DEEP/qc -- lane myia-po-2027:CoursIA-2 -- prev: DEEP/research-code #20044\n\n"
    "[CLAIMED] lane myia-po-2027:CoursIA-2 -- brique 4 : league_correlation.py + tests",
    "2026-10-09T12:31:12Z",
)
_C3_RETRACT = comment(
    "[CLAIMED-RETRACT] lane myia-po-2027:CoursIA-2\n\n"
    "**Retractation -- la brique est deja livree.** PR #20084 livre exactement ce perimetre.",
    "2026-10-09T12:32:10Z",
)

_PR_BODY = (
    "Grain: DEEP/qc -- lane myia-po-2024:CoursIA-3 -- prev: DEEP/qc #20019\n\n"
    "Closes #20083\n"
)

# Horloge fixe : 40 min apres la retractation, soit tres en deca du seuil de
# peremption (48 h) -- le claim concurrent est donc FRAIS et doit bloquer.
_NOW = datetime(2026, 10, 9, 14, 2, 59, tzinfo=timezone.utc)


def _incident_payload():
    return payload(_C1, _C2, _C3_RETRACT)


def _retract_marker():
    """Le quasi-marqueur `[CLAIMED-RETRACT]` tel que le detecteur le rend."""
    found = clc._find_suspected_typo_markers(_incident_payload())
    assert len(found) == 1, f"attendu 1 quasi-marqueur, obtenu {found!r}"
    return found[0]


# --- le geste est DESORMAIS DIT ---------------------------------------------

def test_le_detecteur_voit_deja_le_token_compose():
    # Le detecteur n'etait pas en cause -- il rendait deja `kind='compose'`.
    # Ce test le fige pour que le correctif ne puisse pas etre credite a tort
    # d'une extension de la DETECTION.
    m = _retract_marker()
    assert m["kind"] == "compose"
    assert m["token"] == "CLAIMED-RETRACT"


def test_le_synonyme_est_reconnu_comme_une_levee():
    # C'est le correctif : `RETRACT` ∈ `_CLOSE_SHAPED`, donc le composite est
    # classe « leve » au lieu de tomber dans la branche quasi-PRISE.
    assert clc.is_release_shaped(_retract_marker()) is True


def test_la_forme_recommandee_est_celle_que_le_reduceur_lit():
    # Reconnaitre large ne doit pas faire RECOMMANDER large : conseiller
    # `[RETRACT]` enverrait l'auteur reposter une forme tout aussi invisible
    # que la sienne. Avant le correctif, ce champ valait `CLAIMED` -- soit
    # « reprends le grain que tu viens de rendre ».
    assert _retract_marker()["canonical"] == "RELEASED"
    assert _retract_marker()["canonical"] in clc._CLOSE


def test_le_garde_dit_maintenant_a_la_lane_que_son_geste_n_a_pas_ete_lu():
    """Bout en bout : la condition exacte de `lane_claim_required.py:328-330`."""
    verdict = lcr.check(
        _PR_BODY,
        issue_fetcher=lambda n: _incident_payload(),
        now=_NOW,
        pr_closing_refs={20083},
    )
    # Le blocage subsiste : la retractation n'est PAS enactee (voir plus bas).
    assert verdict["guard_pass"] is False
    assert verdict["blocking_lane"] == "myia-po-2027:CoursIA-2"

    # ... et la lane est desormais INFORMEe. Avant le correctif, `warnings`
    # etait vide pour ce fil : l'auteur ne pouvait pas savoir que son geste
    # avait ete saute, et la seule issue visible etait d'attendre 48 h.
    joined = " || ".join(verdict["warnings"])
    assert "CLAIMED-RETRACT" in joined, verdict["warnings"]
    assert "RELEASED" in joined, verdict["warnings"]


# --- il n'est toujours PAS ENACTE -------------------------------------------

def test_le_reduceur_ne_lit_pas_la_retractation():
    # Le controle negatif qui compte : reconnaitre ne doit pas enacter. Le meme
    # fil, passe au reduceur, garde le claim de po-2027 ACTIF.
    active, _unattrib = clc.compute_active_claims(
        clc._sort_events(_incident_payload())
    )
    assert "myia-po-2027:CoursIA-2" in active
    assert active["myia-po-2027:CoursIA-2"].created_at == "2026-10-09T12:31:12Z"


def test_le_mot_cle_de_retractation_n_est_pas_dans_l_alternation_qui_decide():
    # `_MARKER_RE` est ce qui ENACTE. La ligne de retractation ne doit pas
    # matcher : c'est la preuve que le correctif n'a pas ouvert une levee.
    line = "[CLAIMED-RETRACT] lane myia-po-2027:CoursIA-2"
    assert re.search(clc._MARKER_RE, line) is None


def test_le_vocabulaire_du_reduceur_est_byte_identique():
    # Le cliquet : si quelqu'un « simplifie » un jour en ajoutant RETRACT a
    # `_CLOSE`, ce test rougit -- et c'est voulu, car ce serait enactеr.
    assert clc._CLOSE == {
        "RELEASED", "CANCELLED", "ABANDONED", "DONE", "DELIVERED",
    }
    assert "RETRACT" not in clc._CLOSE
    assert "RETRACTED" not in clc._CLOSE


def test_le_vocabulaire_de_reconnaissance_est_un_sur_ensemble_strict():
    # La relation entre les deux vocabulaires, en une assertion : reconnaitre
    # PLUS, sans jamais changer ce qui est lu.
    assert clc._CLOSE <= clc._CLOSE_SHAPED
    assert clc._CLOSE_SHAPED - clc._CLOSE == {"RETRACT", "RETRACTED"}


def test_le_second_synonyme_est_exerce_pas_seulement_declare():
    # `RETRACTED` est declare dans `_CLOSE_SHAPED` : un mot declare mais jamais
    # parcouru est un mot qui ne protege rien. Les deux formes du synonyme sont
    # donc exercees, jusqu'a la forme recommandee.
    p = payload(comment(
        "[CLAIMED-RETRACTED] lane myia-po-2027:CoursIA-2 -- deja livre",
        "2026-10-09T12:32:10Z",
    ))
    m = clc._find_suspected_typo_markers(p)[0]
    assert clc.is_release_shaped(m) is True
    assert m["canonical"] == "RELEASED"


# --- non-regression des deux cas deja couverts ------------------------------

def test_le_composite_canonique_recommande_toujours_released():
    p = payload(comment(
        "[CLAIMED-RELEASED] lane myia-po-2023:CoursIA -- rendu",
        "2026-10-09T12:00:00Z",
    ))
    m = clc._find_suspected_typo_markers(p)[0]
    assert m["kind"] == "compose"
    assert clc.is_release_shaped(m) is True
    assert m["canonical"] == "RELEASED"


def test_une_quasi_prise_conseille_toujours_de_prendre():
    # Le pendant : une quasi-PRISE (`[CLAGED]`) n'est pas release-shaped, et la
    # forme conseillee reste `CLAIMED`. Le correctif ne doit pas basculer ce cas
    # dans la branche « leve », sinon il conseillerait de rendre un grain que
    # l'auteur n'a jamais pris.
    p = payload(comment(
        "[CLAGED] lane myia-po-2024:CoursIA -- 4 fichiers suivis",
        "2026-10-09T12:00:00Z",
    ))
    m = clc._find_suspected_typo_markers(p)[0]
    assert clc.is_release_shaped(m) is False
    assert m["canonical"] == "CLAIMED"
