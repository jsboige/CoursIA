"""Tests de `coordination/tapis_relache.py` et `tapis_relache_motif.py` (#28440).

La regle : un echec d'OUTIL ne gele que la lane qui l'a subi ; une barriere
reelle gele toute la flotte ; un motif inconnu ou ambigu gele toute la flotte
(fail-CLOSED). Aucun test ne touche le reseau : les lectures sont construites
en memoire, comme dans `test_tapis_rapide.py`.
"""
import sys
from datetime import UTC, datetime, timedelta
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from coordination import gh_bulk
from coordination import tapis_rapide as tr
from coordination import tapis_relache, tapis_relache_motif

pytestmark = pytest.mark.usefixtures("forbid_shell_escape")

NOW = datetime(2026, 11, 13, 12, 0, tzinfo=UTC)
LANE = "myia-po-2024:CoursIA-2"
AUTRE = "myia-po-2028:claudish"
COORD = Path(__file__).resolve().parents[1] / "coordination"

#: La forme reelle d'un rendu de production Rust (22/11) : le motif est ecrit
#: plus loin que la ligne du marqueur, qui ne dit que les essais consommes.
RENDU_RUST = (
    "[RELEASED] Coalitions-01-SMT (Rust) — 2 essais contenu consommés\n\n"
    "Essais contenu : (1) verify-reject (fournee w3p, 22/11) ; "
    "(2) built-structure-mismatch (fournee w3q, 22/11)"
)


def _h(heures: float) -> str:
    return tr._iso(NOW - timedelta(hours=heures))


def issue(n: int, comments=(), labels=()) -> dict:
    return {"number": n, "title": f"Grain {n}", "body": "", "labels": list(labels),
            "created_at": "2026-10-01T00:00:00Z", "comments": list(comments),
            "comments_total": len(comments)}


def com(heures: float, body: str) -> dict:
    return {"created_at": _h(heures), "author": "jsboige", "body": body}


def lecture(issues) -> gh_bulk.Lecture:
    return gh_bulk.Lecture(issues=list(issues), prs=[], citations={})


def etat(lec: gh_bulk.Lecture, n: int, lane: str = LANE) -> tr.Etat:
    return next(e for e in tr.etats(lec, lane, NOW) if e.numero == n)


# --- le vocabulaire ---------------------------------------------------------

@pytest.mark.parametrize("code", sorted(tapis_relache_motif.CODES_OUTIL))
def test_les_cinq_motifs_sont_reconnus(code):
    corps = f"Essais contenu : (1) {code} (fournee w3p, 22/11)"
    assert tapis_relache_motif.code_outil(corps) == code


def test_le_vocabulaire_est_ferme():
    """Cinq codes mesures : un code inconnu n'est jamais un echec d'outil."""
    assert len(tapis_relache_motif.CODES_OUTIL) == 5
    assert tapis_relache_motif.code_outil("(1) stage2-truc-mystere") is None


def test_le_code_est_lu_sans_tenir_la_casse():
    assert tapis_relache_motif.code_outil("(1) VERIFY-REJECT (fournee w3p)") == "verify-reject"


def test_un_melange_de_codes_reste_ambigu():
    """Un essai et un code cite hors essai : l'echec reste ambigu."""
    corps = ("Essais contenu : (1) verify-reject (fournee w3p)\n\n"
             "cf. stage2-call-failed du 20/11, meme cause")
    assert tapis_relache_motif.code_outil(corps) is None


def test_plusieurs_essais_sont_un_echec_d_outillage():
    """La forme Rust mesuree : deux essais, deux codes -- c'est un echec
    d'outillage, pas une barriere."""
    codes = tapis_relache_motif.codes_outil(RENDU_RUST)
    assert codes == {"verify-reject", "built-structure-mismatch"}


def test_un_code_cite_hors_essai_ne_degele_pas():
    """Un code cite (rappel d'un echec ancien) n'est pas un echec de CE rendu."""
    assert tapis_relache_motif.code_outil("cf. verify-reject du 20/11, meme cause") is None


# --- la portee --------------------------------------------------------------

def test_un_echec_d_outillage_ne_gele_pas_les_autres_lanes():
    lec = lecture([issue(1, comments=[com(24, f"[RELEASED] lane {AUTRE} -- 2 essais\n\n"
                                              "Essais contenu : (1) verify-reject (fournee w3p)")])])
    assert etat(lec, 1).ecart is None              # la lane courante est servable
    assert etat(lec, 1, lane=AUTRE).ecart == "RELACHEE"  # celle qui l'a subi est gelee


def test_il_gele_la_lane_qui_l_a_subi():
    lec = lecture([issue(1, comments=[com(24, f"[RELEASED] lane {AUTRE} -- 2 essais\n\n"
                                              "Essais contenu : (1) verify-reject (fournee w3p)")])])
    motif = etat(lec, 1, lane=AUTRE).motif
    assert "verify-reject" in motif and AUTRE in motif


def test_une_barriere_reelle_gele_toute_la_flotte():
    """Le comportement d'avant, intact : une barriere vaut pour tous."""
    lec = lecture([issue(1, comments=[com(24, f"[RELEASED] lane {AUTRE} -- GPU indisponible")])])
    assert etat(lec, 1).ecart == "RELACHEE"
    assert etat(lec, 1, lane=AUTRE).ecart == "RELACHEE"


def test_un_motif_inconnu_gele_toute_la_flotte():
    lec = lecture([issue(1, comments=[com(24, f"[RELEASED] lane {AUTRE} -- Echec\n\n"
                                              "Essais contenu : (1) stage2-truc-mystere")])])
    assert etat(lec, 1).ecart == "RELACHEE"


def test_au_dela_de_la_fenetre_le_grain_revient():
    lec = lecture([issue(1, comments=[com(24 * 4, f"[RELEASED] lane {AUTRE} -- 2 essais\n\n"
                                                   "Essais contenu : (1) verify-reject (w3p)")])])
    assert etat(lec, 1).ecart is None


def test_un_released_qui_porte_une_condition_reste_une_pause():
    lec = lecture([issue(1, comments=[com(24, f"[RELEASED] lane {AUTRE} -- attend: #9\n\n"
                                              "Essais contenu : (1) verify-reject (w3p)")]),
                   issue(9)])
    assert etat(lec, 1).ecart == "PAUSE"


def test_la_forme_reelle_d_un_rendu_de_production():
    """La forme mesuree (production Rust, 22/11) : le motif est plus loin que
    la ligne du marqueur, et le marqueur ne nomme pas sa lane."""
    lec = lecture([issue(1, comments=[com(24, RENDU_RUST),
                                      com(96, f"[CLAIMED] lane {AUTRE} -- je prends")])])
    assert etat(lec, 1).ecart is None                     # servable pour la lane courante
    assert etat(lec, 1, lane=AUTRE).ecart == "RELACHEE"   # gelee chez celle qui l'a subi


def test_un_rendu_sans_lane_nommee_prend_la_lane_du_dernier_claim():
    lec = lecture([issue(1, comments=[com(96, f"[CLAIMED] lane {AUTRE} -- je prends"),
                                      com(2, RENDU_RUST)])])
    assert etat(lec, 1).ecart is None
    assert etat(lec, 1, lane=AUTRE).ecart == "RELACHEE"


def test_l_organe_appele_directement():
    evts = tr.evenements([com(96, f"[CLAIMED] lane {AUTRE} -- je prends"), com(24, RENDU_RUST)])
    ctx = {"maintenant": NOW, "lane": LANE}
    assert tapis_relache.relachee(evts, ctx) is None
    ctx = {"maintenant": NOW, "lane": AUTRE}
    assert "verify-reject" in tapis_relache.relachee(evts, ctx)


def test_sans_lane_nommee_ni_claim_le_gel_reste_global():
    """Fail-CLOSED : personne n'a nomme la lane du rendu -- le gel vaut pour
    tous, comme avant."""
    evts = tr.evenements([com(24, RENDU_RUST)])
    ctx = {"maintenant": NOW, "lane": LANE}
    assert "lire son motif" in tapis_relache.relachee(evts, ctx)


def test_le_corps_du_commentaire_est_lu():
    """`Evt.corps` porte le corps : sans lui, le motif serait invisible."""
    evts = tr.evenements([com(24, RENDU_RUST)])
    assert "Essais contenu" in evts[-1].corps


def test_les_plafonds_des_nouveaux_modules():
    for nom, plafond in (("tapis_relache.py", 100), ("tapis_relache_motif.py", 100)):
        texte = (COORD / nom).read_text(encoding="utf-8")
        assert len(texte.splitlines()) <= plafond, nom
