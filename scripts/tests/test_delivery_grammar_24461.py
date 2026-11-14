"""Tests de la decision #24461 (c) -- la grammaire de la livraison.

Trois points de la decision :

1. un `[DELIVERED] lane X -- PR #N` **avec** clause `paths:` sur la ligne du
   marqueur ne livre qu'une **TRANCHE** : l'issue RESTE servie ; sans clause
   `paths:`, la livraison est epic-wide et l'issue sort du tapis ;
2. un dossier `[CLOSURE PREFLIGHT]` **VIVANT** (verdict KEEP) ecarte l'issue :
   la cloture est en cours ;
3. ce que le tapis ecarte ne disparait pas : le **motif** est nomme.

La grammaire est celle de `scripts/delivery_grammar.py` -- source UNIQUE, lue
par le poseur de label comme par le tapis (#24478, #24482). Ces tests
s'exercent sur le MODULE, pas sur une copie.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import delivery_grammar as dg


TRANCHE = ("[DELIVERED] lane myia-ai-01:CoursIA-2 -- PR #24493 -- "
           "paths: scripts/notebook_tools/twin_pairs.d/search-02b-networkx/**")
EPIC_WIDE = "[DELIVERED] lane myia-ai-01:CoursIA-2 -- PR #24493"
PATHS_LIGNE_SUIVANTE = ("[DELIVERED] lane myia-ai-01:CoursIA-2 -- PR #24493\n"
                        "paths: scripts/x/**")
ATTESTATION = "[INFO] candidate-delivered -- lane myia-ai-01:CoursIA-2"


def _dossier(verdict="KEEP"):
    lines = [
        "[CLOSURE PREFLIGHT]",
        "schema: 1",
        "lane: myia-ai-01:CoursIA-2",
        "issue: 17900",
        f"verdict: {verdict}",
        "acceptance:",
        "  - critere A -> PR #17901",
        "residue: none",
        "open-prs: 0",
        "comments-reviewed: 0",
        "[/CLOSURE PREFLIGHT]",
    ]
    return "\n".join(lines)


# --- 1. la livraison de TRANCHE ne livre pas l'issue ------------------------

def test_une_tranche_nest_pas_epic_wide():
    assert dg.delivery_marker_is_epic_wide(TRANCHE) is False


def test_une_livraison_sans_paths_est_epic_wide():
    assert dg.delivery_marker_is_epic_wide(EPIC_WIDE) is True


def test_une_attestation_est_epic_wide():
    assert dg.delivery_marker_is_epic_wide(ATTESTATION) is True


def test_paths_hors_ligne_du_marqueur_ne_porte_pas_l_evenement():
    """La clause doit etre SUR la ligne du marqueur (c.2816)."""
    assert dg.delivery_marker_is_epic_wide(PATHS_LIGNE_SUIVANTE) is True


def test_is_tranche_marker():
    assert dg.is_tranche_marker(TRANCHE) is True
    assert dg.is_tranche_marker(EPIC_WIDE) is False
    assert dg.is_tranche_marker(ATTESTATION) is False


def test_la_tranche_n_arme_pas_l_etat_du_tapis():
    assert dg.delivery_state([TRANCHE]) == dg.NONE


def test_la_livraison_entiere_arme_l_etat_du_tapis():
    assert dg.delivery_state([EPIC_WIDE]) == dg.ATTESTED


def test_l_attestation_arme_l_etat_du_tapis():
    assert dg.delivery_state([ATTESTATION]) == dg.ATTESTED


def test_une_tranche_ne_desarme_pas_une_livraison_anterieure():
    """Une tranche ne desarme rien : seule une retractation rearme."""
    assert dg.delivery_state([EPIC_WIDE, TRANCHE]) == dg.ATTESTED


def test_la_tranche_n_arme_pas_le_label():
    """Une livraison AVEC clause `paths:` reste une tranche : ni tapis ni label."""
    assert dg.attestation_state([TRANCHE]) == dg.NONE


def test_l_attestation_arme_le_label():
    assert dg.attestation_state([ATTESTATION]) == dg.ATTESTED


# --- 1 bis. residu #24461 (11/11) : la livraison epic-wide arme le LABEL ----
# Le tapis ecartait deja ces issues (`delivery_state`), mais par une sonde
# budgetee -- fail-OPEN, le tirage worker servait le grain quand meme
# (mesure 76/120). Le label, lu gratuitement dans le payload du pool, exige
# la meme grammaire d'arming. La protection d'un marqueur pose a tort reste
# la REVOCATION partagee.

def test_la_livraison_epic_wide_arme_le_label():
    assert dg.attestation_state([EPIC_WIDE]) == dg.ATTESTED


def test_la_livraison_epic_wide_revoquee_ne_l_arme_pas():
    assert dg.attestation_state([EPIC_WIDE, "[NOT-DELIVERED]"]) == dg.REVOKED


def test_la_livraison_epic_wide_rearmee_apres_revocation():
    fil = [EPIC_WIDE, "[NOT-DELIVERED]", EPIC_WIDE]
    assert dg.attestation_state(fil) == dg.ATTESTED


def test_la_tranche_ne_desarme_pas_une_attestation_anterieure():
    assert dg.attestation_state([ATTESTATION, TRANCHE]) == dg.ATTESTED


def test_le_labeler_et_le_tapis_lisent_la_meme_grammaire_hors_dossier():
    """Sur un fil sans dossier, les DEUX organes rendent le meme etat :
    le critere 4 du residu (tirage worker 0 grain a marqueur vivant) exige
    que tout marqueur vivant du tapis soit aussi un marqueur du label."""
    fils = [
        [ATTESTATION],
        [EPIC_WIDE],
        [TRANCHE],
        [EPIC_WIDE, "[NOT-DELIVERED]"],
        [ATTESTATION, TRANCHE],
        ["commentaire ordinaire"],
    ]
    for fil in fils:
        assert dg.attestation_state(fil, dossier=False) \
            == dg.delivery_state(fil, dossier=False), fil


# --- 2. le dossier `[CLOSURE PREFLIGHT]` VIVANT ----------------------------

def test_le_verdict_dun_dossier_vivant_est_keep():
    assert dg.closure_dossier_verdict(_dossier("KEEP")) == "KEEP"


def test_le_verdict_dun_dossier_terminal_est_close():
    assert dg.closure_dossier_verdict(_dossier("CLOSE")) == "CLOSE"


def test_un_dossier_inexistant_n_est_pas_un_signal():
    assert dg.closure_dossier_verdict("rien ici") is None


def test_un_dossier_vivant_arme_l_etat_du_tapis():
    assert dg.delivery_state([_dossier("KEEP")]) == dg.ATTESTED


def test_un_dossier_vivant_n_arme_pas_le_label():
    """Le label reste etroit (attestation dediee seule)."""
    assert dg.attestation_state([_dossier("KEEP")], dossier=False) == dg.NONE


# --- 3. le motif d'ecartement est NOMME ------------------------------------

def test_le_motif_nomme_le_dossier_vivant():
    motif = dg.delivery_motif([_dossier("KEEP")])
    assert motif is not None
    assert "CLOSURE PREFLIGHT" in motif
    assert "VIVANT" in motif


def test_le_motif_nomme_la_livraison_epic_wide():
    motif = dg.delivery_motif([EPIC_WIDE])
    assert motif is not None
    assert "epic-wide" in motif


def test_pas_de_motif_pour_une_tranche():
    assert dg.delivery_motif([TRANCHE]) is None


def test_le_dernier_evenement_decide_du_motif():
    """Le fil est lu a l'envers : c'est le dernier evenement qui decide."""
    motif = dg.delivery_motif([_dossier("KEEP"), EPIC_WIDE])
    assert motif is not None
    assert "epic-wide" in motif


def test_aucun_motif_pour_un_fil_vide():
    assert dg.delivery_motif([]) is None


# --- 4. la CLASSE d'un motif, lue dans une cause rendue -------------------

def test_la_classe_du_dossier_vivant():
    cause = ("LIVRAISON (recent) : marqueur de cloture sur le dernier "
             "commentaire. " + dg.MOTIF_SUFFIX
             + "dossier `[CLOSURE PREFLIGHT]` VIVANT (verdict KEEP) : la "
               "cloture est en cours.")
    assert dg.motif_class(cause) == "living_dossier"


def test_la_classe_de_la_livraison_epic_wide():
    cause = ("LIVRAISON : raison. " + dg.MOTIF_SUFFIX
             + "livraison epic-wide : un `[DELIVERED]` sans clause "
               "`paths:` livre l'issue ENTIERE.")
    assert dg.motif_class(cause) == "epic_wide"


def test_une_cause_sans_motif_nest_pas_classee():
    assert dg.motif_class("LIVRAISON (recent) : marqueur de cloture.") is None


def test_un_dossier_CLOSE_ne_vaut_pas_dossier_vivant():
    """Une cause « dossier CLOSE » porte aussi la chaine `CLOSURE PREFLIGHT` :
    la classe se lit dans le MOTIF, jamais dans toute la cause."""
    cause = ("LIVRAISON (dossier de cloture CLOSE) : le dossier "
             "`[CLOSURE PREFLIGHT]` de cette issue porte un verdict CLOSE "
             "-- elle est resolue.")
    assert dg.motif_class(cause) is None


# --- 5. plusieurs marqueurs dans UN corps -----------------------------------
# Un corps qui porte deux marqueurs de lane se lit comme DEUX evenements :
# le dernier ne l'emporte pas. C'est la meme lecture que pour deux corps
# distincts, ou l'ordre ne change rien (constat de l'adjoint, cycle F).

EPIC_PUIS_TRANCHE = EPIC_WIDE + "\n" + TRANCHE
TRANCHE_PUIS_EPIC = TRANCHE + "\n" + EPIC_WIDE
ATTESTATION_PUIS_TRANCHE = ATTESTATION + "\n" + TRANCHE


def test_une_tranche_apres_une_livraison_entiere_ne_la_desarme_pas():
    """Les deux ordres, dans un corps : l'etat est ATTESTED, comme sur deux corps."""
    assert dg.delivery_state([EPIC_PUIS_TRANCHE]) == dg.ATTESTED
    assert dg.delivery_state([TRANCHE_PUIS_EPIC]) == dg.ATTESTED


def test_un_corps_qui_melange_les_deux_marqueurs_est_epic_wide():
    assert dg.delivery_marker_is_epic_wide(EPIC_PUIS_TRANCHE) is True
    assert dg.delivery_marker_is_epic_wide(TRANCHE_PUIS_EPIC) is True


def test_un_corps_qui_melange_les_deux_marqueurs_nest_pas_une_tranche():
    """« Que des tranches » : un marqueur epic-wide dans le corps suffit a
    disqualifier la tranche -- les deux predicats ne peuvent pas desaccorder."""
    assert dg.is_tranche_marker(EPIC_PUIS_TRANCHE) is False
    assert dg.is_tranche_marker(TRANCHE_PUIS_EPIC) is False
    assert dg.is_tranche_only(TRANCHE_PUIS_EPIC) is False


def test_une_tranche_seule_dans_un_corps_reste_une_tranche():
    assert dg.is_tranche_marker(TRANCHE) is True
    assert dg.is_tranche_only(TRANCHE) is True


def test_une_tranche_apres_une_attestation_ne_desarme_pas_l_attestation():
    assert dg.delivery_state([ATTESTATION_PUIS_TRANCHE]) == dg.ATTESTED


# --- 6. le motif suit l'etat : un fil retracte ne porte pas de motif -------

def test_un_fil_retracte_ne_porte_pas_de_motif_de_livraison():
    """L'etat dit `revoked` (l'issue redevient servable) : nommer un motif
    d'ecarte sur ce fil serait annoncer une ecarte qui n'a plus lieu."""
    assert dg.delivery_state([EPIC_WIDE, "[NOT-DELIVERED]"]) == dg.REVOKED
    assert dg.delivery_motif([EPIC_WIDE, "[NOT-DELIVERED]"]) is None


def test_un_fil_retracte_puis_rearme_reporte_le_motif():
    assert dg.delivery_state([EPIC_WIDE, "[NOT-DELIVERED]", EPIC_WIDE]) == dg.ATTESTED
    motif = dg.delivery_motif([EPIC_WIDE, "[NOT-DELIVERED]", EPIC_WIDE])
    assert motif is not None
    assert "epic-wide" in motif

def test_chronologie_du_fil_et_tranches():
    lane = '[DELIVERED] lane po:CoursIA -- PR #1'
    tranche = lane + ' -- paths: scripts/**'
    neutral = 'Une question de suivi.'
    revoke = '[NOT-DELIVERED] partiel'
    assert not dg.recent_delivery_state([tranche, neutral])
    assert dg.recent_delivery_state([lane, tranche, neutral])
    assert not dg.recent_delivery_state([lane, revoke, tranche])
    assert dg.recent_delivery_state([revoke, lane, neutral])
    assert not dg.delivered_state(['```\n' + lane + '\n```'])
    assert dg.delivered_state([lane, '```\n' + revoke + '\n```'])


def test_chronologie_conteneur():
    attestation = '[INFO] candidate-delivered -- termine'
    tranche = '[DELIVERED] lane po:CoursIA -- PR #1 -- paths: scripts/**'
    assert dg.container_delivery_state([attestation, tranche, 'neutre'])
    assert not dg.container_delivery_state([attestation, '[NOT-DELIVERED]'])
    assert not dg.container_delivery_state(['```\n' + attestation + '\n```'])


def test_dossier_keep_survit_aux_neutres_et_aux_tranches():
    assert dg.recent_delivery_state([_dossier("KEEP"), TRANCHE, "suivi"])
    assert not dg.recent_delivery_state([_dossier("KEEP"), "[NOT-DELIVERED]", TRANCHE])


def test_tranche_sans_lane_ne_change_pas_l_etat_du_fil():
    for tranche in ("[DELIVERED] -- paths: a.py", "[DELIVERED] paths: a.py"):
        assert not dg.recent_delivery_state([tranche, "suivi"])
        assert dg.recent_delivery_state([EPIC_WIDE, tranche])
        assert not dg.recent_delivery_state([EPIC_WIDE, "[NOT-DELIVERED]", tranche])
    assert dg.recent_delivery_state(["[DELIVERED] -- travail termine"])
    assert dg.recent_delivery_state(["[DELIVERED] -- travail termine\npaths: a.py"])


def test_tranche_insensible_a_la_casse_avec_et_sans_lane():
    assert dg.is_tranche_marker("[delivered] lane myia-ai-01:CoursIA -- PaThS: a.py")
    assert dg.is_tranche_marker("[delivered] -- PATHS: a.py")
    assert not dg.is_tranche_marker("[delivered] lane myia-ai-01:CoursIA\nPaThS: a.py")
