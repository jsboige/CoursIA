"""La remise de main BORNEE : un `[RELEASED]` ne bloque que les chemins qu'il nomme (#28899).

Mesure du 27/11 (lot #27133) : un `[RELEASED] -- paths: Search-11` faisait
refuser a sa lane la qualification de quatre autres carnets du meme lot
(`RELACHEE` x4). `tapis_attente.relachee()` ne lisait que le dernier marqueur
du fil et ne consultait jamais sa clause `paths:`.

La regle, desormais : le dernier marqueur du fil QUI CONCERNE les chemins
demandes decide. Chaque test porte son voisin qui n'ecarte pas ; le tirage
(sans chemins) et la pause sont pinnes inchanges.

Deux niveaux : `qualification_grain` (la porte du consommateur, qui ne rend que
HORSFLOTTE, LABEL, GEL et RELACHEE) et `tapis_rapide.etats` (la decision de
l'organe, PAUSE et RECLAMEE compris).

Aucun test ne touche le reseau : les fils sont fabriques.
"""
import sys
from datetime import UTC, datetime, timedelta
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import check_lane_claim as clc
from coordination import gh_bulk, tapis_qualification_fil, tapis_rapide as tr

pytestmark = pytest.mark.usefixtures("forbid_shell_escape")

NOW = datetime(2026, 11, 27, 16, 0, tzinfo=UTC)
LANE = "myia-po-2028:claudish"
AUTRE = "myia-po-2027:CoursIA"
TROIS = "myia-po-2025:CoursIA-2"
DOSSIER = "MyIA.AI.Notebooks/Metaheuristiques"
A, B, C = (f"{DOSSIER}/{nom}.ipynb" for nom in ("MGS-23", "MGS-24", "MGS-26"))


def _h(heures: float) -> str:
    return (NOW - timedelta(hours=heures)).strftime("%Y-%m-%dT%H:%M:%SZ")


def _comment(heures: float, body: str) -> dict:
    return {"createdAt": _h(heures), "author": {"login": "jsboige"}, "body": body}


def _payload(*commentaires: dict) -> dict:
    """Un payload `gh issue view --json` minimal, au fil fabrique."""
    return {"number": 27133, "title": "Lot de portages Rust", "body": "",
            "createdAt": "2026-11-20T00:00:00Z", "labels": [],
            "comments": list(commentaires)}


def _rendue(chemin: str, heures: float = 1, lane: str = TROIS) -> dict:
    """La forme mesuree sur #27133 : le motif du marqueur, puis la clause."""
    return _comment(heures, f"[RELEASED] lane {lane} -- nb_coder: grain ended without a PR "
                            f"(gates-failed) -- paths: {chemin}\n\nLe constat du critique.")


def _qualifie(payload: dict, chemins: list[str] | None) -> tuple[str, str] | None:
    """La porte du consommateur."""
    return tapis_qualification_fil.qualification_grain(payload, LANE, NOW, chemins)


def _etat(*commentaires: dict, chemins: list[str] | None) -> tr.Etat:
    """La decision de l'organe sur le fil."""
    it = {"number": 1, "title": "Grain 1", "body": "", "labels": [],
          "created_at": "2026-10-01T00:00:00Z", "comments_total": len(commentaires),
          "comments": [{"created_at": c["createdAt"], "author": "jsboige", "body": c["body"]}
                       for c in commentaires]}
    return tr.etats(gh_bulk.Lecture(issues=[it], prs=[], citations={}),
                    LANE, NOW, 45, chemins)[0]


# --- les quatre tests de l'issue ----------------------------------------------

def test_rendue_sur_un_chemin_ne_refuse_pas_un_autre():
    """`RELEASED paths=A`, qualification pour `chemins=[B]` : None."""
    assert _qualifie(_payload(_rendue(A)), [B]) is None


def test_rendue_sur_un_chemin_refuse_ce_chemin():
    """`RELEASED paths=A`, qualification pour `chemins=[A]` : RELACHEE."""
    code, motif = _qualifie(_payload(_rendue(A)), [A])
    assert code == "RELACHEE" and f"rendue par {TROIS}" in motif


def test_sans_chemins_la_regle_juge_l_issue_entiere():
    """`RELEASED paths=A`, qualification sans `chemins` : RELACHEE -- le tirage
    garde la regle d'aujourd'hui."""
    assert _qualifie(_payload(_rendue(A)), None)[0] == "RELACHEE"


def test_rendue_sans_clause_paths_reste_globale():
    """`RELEASED` sans `paths:`, qualification pour `chemins=[B]` : RELACHEE."""
    globale = _comment(1, f"[RELEASED] lane {TROIS} -- motif : bloque par X")
    assert _qualifie(_payload(globale), [B])[0] == "RELACHEE"


# --- le faux deblocage ---------------------------------------------------------

def test_un_claim_sur_b_n_efface_pas_la_rendue_sur_a():
    """Le 5e test (coordinateur) : apres `RELEASED paths=A`, un `[CLAIMED]` sur B
    ne doit pas effacer l'etat relache de A."""
    fil = _payload(_rendue(A, heures=3),
                   _comment(1, f"[CLAIMED] lane {LANE} -- paths: {B}"))
    assert _qualifie(fil, [A])[0] == "RELACHEE"
    assert _qualifie(fil, [B]) is None  # B est le mien : rien ne m'y retient


def test_le_claim_d_une_autre_lane_sur_b_n_efface_pas_davantage():
    """Meme fil, claim d'une AUTRE lane : A reste rendue ; la qualification ne
    retient plus B -- c'est le claim qui le retient, pas la remise de main."""
    fil = _payload(_rendue(A, heures=3),
                   _comment(1, f"[CLAIMED] lane {AUTRE} -- paths: {B}"))
    rendue = _qualifie(fil, [A])
    assert rendue[0] == "RELACHEE" and f"rendue par {TROIS}" in rendue[1]
    assert _qualifie(fil, [B]) is None
    assert _etat(*fil["comments"], chemins=[B]).ecart == "RECLAMEE"


def test_deux_rendues_bornees_tiennent_chacune():
    """Mesure du 27/11 (#27133, 7223370965 puis 7223373091) : rendre B APRES A
    rouvrait A -- la regle ne lisait que le dernier marqueur du fil."""
    fil = _payload(_rendue(A, heures=3, lane=TROIS), _rendue(B, heures=1, lane=AUTRE))
    assert _qualifie(fil, [A])[1].startswith(f"rendue par {TROIS}")
    assert _qualifie(fil, [B])[1].startswith(f"rendue par {AUTRE}")
    assert _qualifie(fil, [C]) is None


def test_la_rendue_expiree_ne_tient_plus():
    """La fenetre de trois jours ne change pas : au-dela, le grain revient au pool."""
    fil = _payload(_rendue(A, heures=24 * 4), _rendue(B, heures=1))
    assert _qualifie(fil, [A]) is None
    assert _qualifie(fil, [B])[0] == "RELACHEE"


def test_un_marqueur_global_posterieur_l_emporte_toujours():
    """Un marqueur SANS clause porte sur tout le grain : le dernier marqueur
    gagne, comme avant le correctif."""
    fil = _payload(_rendue(A, heures=3),
                   _comment(1, f"[CLAIMED] lane {AUTRE} -- je reprends le lot"))
    assert _qualifie(fil, [A]) is None
    assert _etat(*fil["comments"], chemins=[A]).ecart == "RECLAMEE"


# --- la clause, lue avec la grammaire des claims --------------------------------

def test_la_clause_se_lit_comme_une_portee():
    """Le glob du marqueur, l'annotation qui le suit, et le glob de l'appelant."""
    dossier = _comment(1, f"[RELEASED] lane {TROIS} -- paths: {DOSSIER}/*.ipynb"
                          " -- pose le 2026-11-27T16:00Z")
    assert _qualifie(_payload(dossier), [A])[0] == "RELACHEE"
    assert _qualifie(_payload(_rendue(A)), [f"{DOSSIER}/**"])[0] == "RELACHEE"
    assert _qualifie(_payload(dossier), ["MyIA.AI.Notebooks/Complexity/X.ipynb"]) is None


def test_une_clause_illisible_est_lue_globale():
    """Conservateur, comme la grammaire des claims (#10597) : une clause qu'on ne
    peut pas lire porte sur tout le grain."""
    brace = _comment(1, f"[RELEASED] lane {TROIS} -- paths: {DOSSIER}/{{a,b-*.ipynb")
    assert _qualifie(_payload(brace), [B])[0] == "RELACHEE"


# --- ce que le correctif ne touche pas ------------------------------------------

def test_une_pause_bornee_reste_une_pause():
    """`attend:` reste une PAUSE, pour tout chemin demande : hors du correctif."""
    pause = _comment(1, f"[RELEASED] lane {TROIS} -- paths: {A} -- attente du GO\n"
                        "attend: Q-c.2344a")
    assert _qualifie(_payload(pause), [B]) is None  # la pause n'est pas un code de qualification
    assert _etat(pause, chemins=[B]).ecart == "PAUSE"
    assert _etat(pause, chemins=[A]).ecart == "PAUSE"


def test_le_tirage_garde_la_regle_du_dernier_marqueur():
    """Le tirage ne demande aucun chemin : pour lui, le `[CLAIMED]` sur B reste
    le dernier marqueur du fil -- comportement d'avant, pinne."""
    commentaires = [_rendue(A, heures=3),
                    _comment(1, f"[CLAIMED] lane {AUTRE} -- paths: {B}")]
    assert _etat(*commentaires, chemins=None).ecart == "RECLAMEE"
    # Le consommateur, lui, voit la remise de main de A.
    assert _etat(*commentaires, chemins=[A]).ecart == "RELACHEE"


def test_la_porte_du_claim_refuse_a_et_laisse_passer_b(capsysbinary, monkeypatch):
    """La porte est sur le chemin du claim (`_run_check` rend 1, donc `[CLAIMED]`
    n'est pas poste) : elle retient A et s'abstient pour B. Le parcours de
    l'arbre est simule : la suite ne lance aucun processus."""
    monkeypatch.setattr(clc, "_git_tracked_files", lambda repo_root=None: [A, B, C])
    payload = _payload(_rendue(A))
    assert clc._run_check(payload, LANE, now=NOW, my_paths=[A]) == 1
    assert "[QUALIFICATION] RELACHEE" in capsysbinary.readouterr().err.decode("utf-8")
    assert clc._run_check(payload, LANE, now=NOW, my_paths=[B]) == 0
    assert "[QUALIFICATION]" not in capsysbinary.readouterr().err.decode("utf-8")
