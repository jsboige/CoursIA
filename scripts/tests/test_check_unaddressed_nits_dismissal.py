"""Une dismissal ne leve la reserve que si elle vient de son EMETTEUR (#13685).

Le gate portait la premisse ecrite « une dismissal GitHub n'est possible que par
l'auteur de la review (ou un admin) », et faisait donc un `continue`
inconditionnel sur `state == "DISMISSED"`. Cette premisse est FAUSSE : tout
compte disposant du droit d'ecriture peut dismisser la review d'un tiers,
l'auteur de la PR compris. `PUT /pulls/N/reviews/ID/dismissals` etait donc une
trappe : la reserve d'autrui s'eteignait d'un appel d'API.

Mesure du 2026-08-30 sur #13685 : la CHANGES_REQUESTED de clusterManager-Myia
(« 1 defect bloquant trouve ») est dismissee a 18:14:56Z ; `check-navlinks`
passe FAILURE a 18:16:11Z, 75 secondes plus tard. La reserve etait declaree
levee pendant que la propriete qu'elle protege etait encore cassee — #12798
mecanise.

Le second test verrouille le defaut trouve EN COURS de correction : reconnaitre
la dismissal impropre ne suffit pas. La reserve survivante doit reprendre son
etat d'ORIGINE (`CHANGES_REQUESTED`), sinon le signal existe mais retombe en
`review:DISMISSED` — hors de la branche qui force BOT-CONCERN et hors du
durcissement `src == "review:CHANGES_REQUESTED"` en aval. Premiere passe :
`improper_dismissals()` rendait bien `{clusterManager-Myia}` et le gate restait
vert. Un signal hors de sa branche ne bloque rien.
"""
import importlib.util
import sys
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
CHECK_PATH = HERE.parent / "check_unaddressed_nits.py"
spec = importlib.util.spec_from_file_location("cun_dismissal", CHECK_PATH)
mod = importlib.util.module_from_spec(spec)
sys.modules["cun_dismissal"] = mod
spec.loader.exec_module(mod)

MERGED = datetime(2026, 8, 30, 20, 0, tzinfo=timezone.utc)


def _pr(review_state="DISMISSED"):
    return {
        "number": 13685,
        "author": {"login": "jsboige"},
        "commits": [{"committedDate": "2026-08-30T13:00:00Z"}],
        "comments": [],
        "reviews": [{
            "author": {"login": "clusterManager-Myia"},
            "state": review_state,
            "submittedAt": "2026-08-30T14:30:35Z",
            "body": "**[Hermes]** — 1 defect bloquant trouve : les 2 liens sont casses.",
        }],
    }


def test_dismissal_par_un_tiers_ne_leve_pas():
    """Dismissee par quelqu'un d'autre que son emetteur : la reserve SURVIT."""
    res = mod.analyse(_pr(), [], MERGED,
                      dismissed_improperly={"clusterManager-Myia"})
    assert res["blocked"] is True
    assert len(res["blocking"]) == 1
    assert res["blocking"][0]["author"] == "clusterManager-Myia"


def test_reserve_survivante_reprend_letat_changes_requested():
    """Le signal doit porter `review:CHANGES_REQUESTED`, pas `review:DISMISSED`.

    C'est ce qui l'amene dans la branche BOT-CONCERN et sous le durcissement
    anti-extinction-par-commentaire-posterieur. Sans cela le gate reste vert.
    """
    res = mod.analyse(_pr(), [], MERGED,
                      dismissed_improperly={"clusterManager-Myia"})
    assert res["blocking"][0]["src"] == "review:CHANGES_REQUESTED"
    assert res["blocking"][0]["kind"] == "BOT-CONCERN"


def test_dismissal_par_son_emetteur_leve_toujours():
    """Retrait volontaire par l'auteur de la review : extinction legitime (#11222)."""
    res = mod.analyse(_pr(), [], MERGED, dismissed_improperly=set())
    assert res["blocked"] is False


def test_defaut_de_lecture_ne_bloque_jamais_a_tort():
    """Timeline illisible -> `dismissed_improperly=None` -> ancien comportement.

    Un gate qui bloque quand son instrument est muet transforme une panne de
    lecture en refus de merge. Fail-closed sur le comportement anterieur.
    """
    assert mod.analyse(_pr(), [], MERGED)["blocked"] is False
    assert mod.analyse(_pr(), [], MERGED, dismissed_improperly=None)["blocked"] is False


def test_une_review_non_dismissee_est_inchangee():
    """Temoin negatif : le patch ne touche pas le chemin nominal."""
    res = mod.analyse(_pr("CHANGES_REQUESTED"), [], MERGED,
                      dismissed_improperly=set())
    assert res["blocked"] is True
    assert res["blocking"][0]["src"] == "review:CHANGES_REQUESTED"
