"""La PORTEE d'un [RELEASED] -- `coordination/tapis_relache.py` (#28114).

Mesure a l'origine du correctif (dispatch `c0035b` du coordinateur, 24/11) :
la garde « `RELEASED` < 3 j » gelait pour **toute** la flotte un grain qu'une
seule lane avait rendu sur un motif d'echec d'OUTIL. Un grain que personne ne
peut servir est un grain perdu.

Ce que ces tests fixent :

- un echec d'outil ne gele que la lane qui l'a rendu ;
- une barriere reelle gele toute la flotte (le comportement d'avant) ;
- un motif inconnu gele toute la flotte (fail-CLOSED) ;
- un [RELEASED] qui porte une condition reste une PAUSE.

Aucun test ne touche le reseau : les lectures sont construites en memoire.
"""
import ast
import sys
from datetime import UTC, datetime, timedelta
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from coordination import gh_bulk
from coordination import tapis_attente, tapis_rapide as tr

pytestmark = pytest.mark.usefixtures("forbid_shell_escape")

NOW = datetime(2026, 11, 24, 20, 0, tzinfo=UTC)
LANE = "myia-po-2024:CoursIA-2"
AUTRE = "myia-po-2027:CoursIA"
DOSSIER_COORD = Path(__file__).resolve().parents[1] / "coordination"


def _h(heures: float) -> str:
    return tr._iso(NOW - timedelta(hours=heures))


def issue(n: int, comments=()) -> dict:
    return {"number": n, "title": f"Grain {n}", "body": "", "labels": [],
            "created_at": "2026-10-01T00:00:00Z", "comments": list(comments),
            "comments_total": len(comments)}


def com(heures: float, body: str) -> dict:
    return {"created_at": _h(heures), "author": "jsboige", "body": body}


def lecture(issues) -> gh_bulk.Lecture:
    return gh_bulk.Lecture(issues=list(issues), prs=[], citations={})


def etat(lec, n: int, lane: str = LANE):
    return next(e for e in tr.etats(lec, lane, NOW) if e.numero == n)


# --- l'echec d'outil ne gele que la lane qui l'a rendu -----------------------

def test_un_echec_d_outil_ne_gele_pas_les_autres_lanes():
    """Le cas mesure : une lane a rendu le grain sur un echec d'outil ; les
    autres lanes n'ont pas le meme outillage -- le grain leur reste
    servable."""
    lec = lecture([issue(1, comments=[com(24, f"[RELEASED] lane {AUTRE} "
                                              "-- motif: stage2-call-failed")])])
    assert etat(lec, 1).ecart is None


def test_un_echec_d_outil_gele_la_lane_qui_l_a_subi():
    """La lane qui a bute ne se ressert pas le grain tout de suite."""
    lec = lecture([issue(1, comments=[com(24, f"[RELEASED] lane {LANE} "
                                              "-- motif: stage2-call-failed")])])
    e = etat(lec, 1)
    assert e.ecart == "RELACHEE"
    assert "echec d'outil" in e.motif and LANE in e.motif


def test_les_cinq_motifs_d_echec_d_outil_sont_recus():
    """Le vocabulaire est ferme et connu : les cinq motifs mesures."""
    from coordination import tapis_relache
    for motif in ("stage2-call-failed", "verify-reject",
                  "refused-revise-trace-mismatch", "built-structure-mismatch",
                  "stage2-unparsed"):
        assert tapis_relache.est_echec_outil(f"lane X -- motif: {motif}"), motif


def test_la_forme_reelle_d_un_rendu_de_production():
    """La forme mesuree (Rust, 22/11) : le marqueur ne dit que « N essais
    consommes », les codes d'echec sont plus loin, et la lane n'est pas nommee
    -- c'est le claim qui precede qui la dit.

    C'est la forme que le coordinateur a signalee : le grain etait gele pour
    toute la flotte alors qu'une seule lane avait consomme ses essais.
    """
    rendu = ("[RELEASED] Coalitions-01-SMT (Rust) -- 2 essais contenu consommes\n"
             "\n"
             "Essais contenu : (1) verify-reject (fouragee w3p, 22/11) ; "
             "(2) built-structure-mismatch (fouragee w3q, 22/11 11:37Z). "
             "Interruptions non comptees : 1x stage2-call-failed (w3r2, 21/11).\n"
             "\n"
             "Consomme : 2 essais contenu -- la lane relache le grain, pas de 3e essai.\n")
    lec = lecture([
        issue(1, comments=[com(72, f"[CLAIMED] lane {AUTRE} -- je prends"),
                           com(24, rendu)]),
        issue(2, comments=[com(72, f"[CLAIMED] lane {LANE} -- je prends"),
                           com(24, rendu)]),
    ])
    # La lane qui a rendu le grain reste gelee par SON echec d'outil...
    e2 = etat(lec, 2)
    assert e2.ecart == "RELACHEE" and "echec d'outil" in e2.motif
    # ... et les autres lanes ne le sont pas.
    assert etat(lec, 1).ecart is None


# --- une barriere reelle gele toute la flotte (comportement inchange) -------

def test_une_barriere_reelle_gele_toute_la_flotte():
    """Le motif d'une barriere reelle (GPU, siege) vaut pour tout le monde."""
    lec = lecture([issue(1, comments=[com(24, f"[RELEASED] lane {AUTRE} "
                                              "-- barriere reelle, mesuree")])])
    e = etat(lec, 1)
    assert e.ecart == "RELACHEE" and AUTRE in e.motif


def test_un_motif_inconnu_gele_toute_la_flotte():
    """Fail-CLOSED : un motif inconnu n'est pas un echec d'outil, donc le
    grain reste gele partout (le comportement d'avant)."""
    lec = lecture([issue(1, comments=[com(24, f"[RELEASED] lane {AUTRE} "
                                              "-- motif: verify-rejected")])])
    assert etat(lec, 1).ecart == "RELACHEE"


def test_au_dela_de_la_fenetre_le_grain_revient():
    """La fenetre reste courte : au-dela de RELACHE_J jours, le grain
    redevient servable, quelle que soit la lane."""
    lec = lecture([issue(1, comments=[com(24 * 4, f"[RELEASED] lane {AUTRE} "
                                                  "-- motif: stage2-call-failed")])])
    assert etat(lec, 1).ecart is None


def test_un_released_qui_porte_une_condition_reste_une_pause():
    """Une remise de main qui porte une condition n'est pas une remise de main
    de trois jours : c'est une pause (#27726)."""
    lec = lecture([issue(1, comments=[com(24, f"[RELEASED] lane {AUTRE} "
                                              "-- attend: #12345")])])
    e = etat(lec, 1)
    assert e.ecart is None or e.ecart != "RELACHEE"


# --- l'organe de la regle, appele directement -------------------------------

def test_le_relachee_ne_depend_plus_de_la_lane_pour_une_barriere():
    """Appele directement : la regle reste la meme pour une barriere."""
    from coordination import tapis_marqueurs
    evts = tapis_marqueurs.evenements([
        {"created_at": _h(24), "body": f"[RELEASED] lane {AUTRE} -- siege"}])
    assert tapis_attente.relachee(evts, NOW, LANE) is not None
    assert tapis_attente.relachee(evts, NOW, AUTRE) is not None


# --- LE MOTIF COURANT, PAS L'HISTORIQUE CITE (review du 25/11, #28440) ----

def test_un_code_historique_ne_degele_pas_le_grain():
    """Barriere **courante** + code **historique** : le gel reste global.

    La lane rend le grain parce que le GPU partage est indisponible, et elle
    rappelle que son essai **precedent** a donne `verify-reject`. Le code
    cite est un souvenir : le motif courant est une barriere reelle, qui
    gele toute la flotte. Avant le correctif, le code d'echec etait lu
    n'importe ou dans le commentaire : le grain etait degele pour les
    autres lanes, sur un motif qui n'etait pas le sien."""
    rendu = (f"[RELEASED] lane {AUTRE} -- le GPU partage est indisponible\n\n"
             "Rappel : l'essai precedent a donne verify-reject "
             "(fournee w3p, 22/11).\n")
    lec = lecture([issue(1, comments=[com(24, rendu)])])
    e = etat(lec, 1)
    assert e.ecart == "RELACHEE", "une barriere reelle gele toute la flotte"
    assert "echec d'outil" not in e.motif, "le code cite n'est pas le motif"


def test_un_code_cite_dans_une_phrase_ne_degele_pas_le_grain():
    """La forme **ordinaire** sur deux lignes (review du 25/11, #28440).

    `[RELEASED] lane X -- GPU partage indisponible`, puis `Essai du 22/11 :
    verify-reject` : aucun jeton de la deuxieme ligne n'est un marqueur
    historique, et la premiere ligne ne porte aucun code. Le code n'est
    pourtant pas le motif courant : il n'est ni au format explicite
    (`motif: <code>`) ni dans la forme Rust mesuree (code suivi de sa
    fournee et de sa date). Le grain ne doit donc pas etre servi aux autres
    lanes : la barriere reelle le gele pour toute la flotte.
    """
    rendu = (f"[RELEASED] lane {AUTRE} -- GPU partage indisponible\n"
             "Essai du 22/11 : verify-reject\n")
    lec = lecture([issue(1, comments=[com(24, rendu)])])
    e = etat(lec, 1)
    assert e.ecart == "RELACHEE", "le grain reste gele pour toute la flotte"
    assert "echec d'outil" not in e.motif, "le code cite n'est pas le motif"
    # ... et la lane voisine n'est pas servie non plus (c'etait le defaut).
    assert etat(lec, 1, lane=LANE).ecart == "RELACHEE"


def test_le_format_explicite_reste_un_echec_d_outil():
    """Le format explicite (`motif: <code>`) est une forme POSITIVEMENT
    identifiee : la portee locale reste la sienne."""
    from coordination import tapis_relache
    assert tapis_relache.est_echec_outil(
        f"[RELEASED] lane {AUTRE} -- motif: stage2-call-failed")


def test_un_melange_de_codes_reste_ambigu():
    """Un code courant et un code historique dans le meme rendu : le motif
    reste ambigu, donc le gel reste global (fail-CLOSED)."""
    rendu = (f"[RELEASED] lane {AUTRE} -- echec d'outil sur l'essai courant\n\n"
             "Essais : (1) verify-reject (fournee w3p, 22/11) ; "
             "l'essai precedent avait donne stage2-call-failed.\n")
    lec = lecture([issue(1, comments=[com(24, rendu)])])
    e = etat(lec, 1)
    assert e.ecart == "RELACHEE", "le melange ne degele rien"
    assert "echec d'outil" not in e.motif


def test_la_forme_rust_mesuree_reste_un_echec_d_outil():
    """Le format Rust mesure (22/11) n'est pas un souvenir : les codes y
    sont listes avec leur fournee et leur date, sans marqueur du passe. Le
    correctif ne doit pas casser cette forme."""
    from coordination import tapis_relache
    rendu = ("[RELEASED] Coalitions-01-SMT (Rust) -- 2 essais contenu consommes\n"
             "\n"
             "Essais contenu : (1) verify-reject (fournee w3p, 22/11) ; "
             "(2) built-structure-mismatch (fournee w3q, 22/11 11:37Z). "
             "Interruptions non comptees : 1x stage2-call-failed (w3r2, 21/11).\n")
    assert tapis_relache.est_echec_outil(rendu)
    assert not tapis_relache.codes_historiques(rendu)


# --- le plafond de l'organe -------------------------------------------------

# La liste des plafonds des organes du tapis vit dans `test_tapis_rapide.py`,
# un fichier **epingle** (810 lignes, `scripts/ci/script_size_ceilings.json`) :
# toute entree ajoutee le fait grossir au-dela de son plafond, et le ratchet
# (`scripts/tests/test_script_size_ratchet.py`) rougit alors la PR qui l'a
# fait grossir. L'entree de cet organe vit donc dans SON module de test,
# qui n'est pas epingle.

@pytest.mark.parametrize(("nom", "plafond"), [("tapis_relache.py", 100),
                                              ("tapis_relache_motif.py", 105),
                                              ("tapis_relache_forme.py", 60)])
def test_plafond_de_lignes(nom, plafond):
    """L'organe tient son plafond de lignes, et aucune de ses fonctions
    n'en depasse 60."""
    texte = (DOSSIER_COORD / nom).read_text(encoding="utf-8")
    assert len(texte.splitlines()) <= plafond
    for noeud in ast.walk(ast.parse(texte)):
        if isinstance(noeud, ast.FunctionDef | ast.AsyncFunctionDef):
            assert noeud.end_lineno - noeud.lineno + 1 <= 60, noeud.name
