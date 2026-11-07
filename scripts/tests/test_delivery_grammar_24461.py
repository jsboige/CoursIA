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
    """Le label reste etroit : une attestation dediee seule l'arme."""
    assert dg.attestation_state([TRANCHE]) == dg.NONE


def test_l_attestation_arme_le_label():
    assert dg.attestation_state([ATTESTATION]) == dg.ATTESTED


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
