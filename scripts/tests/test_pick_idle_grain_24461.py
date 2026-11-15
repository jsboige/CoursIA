"""Tests pour la decision #24461 (c) -- la grammaire de la livraison,
au niveau du REDUCTEUR et du FILTRE RECENT du tapis.

Ce fichier est le successor de celui porte par la branche superseded
`feature/24461-belt-delivery-grammar` : il est conserve tel quel, parce
que ses assertions portent sur le reducteur (`_delivery_event_from_comments`)
et sur le filtre recent (`has_recent_delivery_marker`) -- deux surfaces que
les tests de grammaire du MODULE ne couvrent pas. La grammaire elle-meme
est verifiee dans `test_delivery_grammar_24461.py`.

Deux points de la decision :

1. un `[DELIVERED] lane X -- PR #N` **avec** clause `paths:` sur la ligne du
   marqueur ne livre qu'une **TRANCHE** (semantique v2 du claim) : l'issue
   RESTE servie ; sans clause `paths:`, la livraison est epic-wide et l'issue
   sort du tapis comme avant ;
2. un dossier `[CLOSURE PREFLIGHT]` **VIVANT** (verdict KEEP) ecarte l'issue :
   la cloture est en cours.

Aucun appel reseau : la reouverture (#24250) est neutralisee, le filtre RECENT
lit un dernier commentaire injecte.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import pick_idle_grain as pig

TRANCHE = ("[DELIVERED] lane myia-ai-01:CoursIA-2 -- PR #24493 -- "
           "paths: scripts/notebook_tools/twin_pairs.d/search-02b-networkx/**")
EPIC_WIDE = "[DELIVERED] lane myia-ai-01:CoursIA-2 -- PR #24493"
PATHS_LIGNE_SUIVANTE = ("[DELIVERED] lane myia-ai-01:CoursIA-2 -- PR #24493\n"
                        "paths: scripts/x/**")
CANDIDATE_DELIVERED = ("[INFO] candidate-delivered -- lane myia-ai-01:CoursIA-2")


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


def _comment(body, created="2026-11-03T10:00:00Z"):
    return {"body": body, "createdAt": created}


def _event(body, created="2026-11-03T10:00:00Z"):
    return pig._delivery_event_from_comments([_comment(body, created)])


# --- 1. la livraison de TRANCHE ne livre pas l'issue -----------------------

def test_tranche_avec_paths_ne_livre_pas_l_issue():
    recent, state, stamp = _event(TRANCHE)
    assert state is False, "un [DELIVERED] avec clause paths: livre une tranche"
    assert recent is False
    assert stamp is None


def test_livraison_sans_paths_livre_l_issue():
    recent, state, stamp = _event(EPIC_WIDE)
    assert state is True
    assert recent is True
    assert stamp == "2026-11-03T10:00:00Z"


def test_paths_hors_ligne_du_marqueur_ne_porte_pas_l_evenement():
    """La clause doit etre SUR la ligne du marqueur (c.2816)."""
    recent, state, _ = _event(PATHS_LIGNE_SUIVANTE)
    assert state is True, "une clause paths: ailleurs ne porte pas l'evenement"


def test_candidate_delivered_reste_epic_wide():
    recent, state, _ = _event(CANDIDATE_DELIVERED)
    assert state is True


def test_une_tranche_puis_une_livraison_entiere_livre_l_issue():
    """Le DERNIER marqueur tranche l'etat."""
    comments = [_comment(TRANCHE), _comment(EPIC_WIDE, "2026-11-03T11:00:00Z")]
    _recent, state, _stamp = pig._delivery_event_from_comments(comments)
    assert state is True


def test_une_tranche_ne_desarme_pas_une_livraison_anterieure():
    """Une livraison ENTIERE reste armee : seule une `[NOT-DELIVERED]` rearme."""
    comments = [_comment(EPIC_WIDE), _comment(TRANCHE, "2026-11-03T11:00:00Z")]
    _recent, state, _stamp = pig._delivery_event_from_comments(comments)
    assert state is True


# --- 2. le dossier `[CLOSURE PREFLIGHT]` VIVANT ----------------------------

def test_dossier_keep_vivant_arme_l_etat():
    recent, state, stamp = _event(_dossier("KEEP"))
    assert state is True, "un dossier de cloture vivant ecarte l'issue"
    assert recent is True
    assert stamp == "2026-11-03T10:00:00Z"


def test_dossier_close_reste_terminal():
    _recent, state, stamp = _event(_dossier("CLOSE"))
    assert state is True
    assert stamp is None, "un dossier CLOSE n'expire pas (terminal)"


# --- 3. le filtre RECENT --------------------------------------------------

def _recent(body, monkeypatch):
    """Le filtre RECENT lit le FIL par `_issue_comments` (#24523 : le gel vit
    dans le corps de l'issue et le balayage porte tout le fil, pas la queue).

    Le seam patche est donc `_issue_comments` -- l'ancien seam
    (`_last_comment`) ne porte plus le filtre apres ce refactor.
    """
    monkeypatch.setattr(pig, "_issue_comments",
                        lambda _n: ([_comment(body)], ""))
    monkeypatch.setattr(pig, "_issue_body", lambda _n: None)
    monkeypatch.setattr(pig, "_reopen_events", lambda _n: [])
    return pig.has_recent_delivery_marker(17900)


def test_filtre_recent_ignore_une_tranche(monkeypatch):
    assert _recent(TRANCHE, monkeypatch) is False


def test_attestation_et_tranche_dans_un_meme_corps(monkeypatch):
    """L'attestation prime la tranche sur les trois surfaces du tapis."""
    body = TRANCHE + "\n" + CANDIDATE_DELIVERED
    recent, state, stamp = _event(body)
    assert (recent, state, stamp) == (True, True, "2026-11-03T10:00:00Z")
    assert _recent(body, monkeypatch) is True


def test_filtre_recent_ecsarte_une_livraison_epic_wide(monkeypatch):
    assert _recent(EPIC_WIDE, monkeypatch) is True


def test_filtre_recent_ecsarte_un_dossier_vivant(monkeypatch):
    assert _recent(_dossier("KEEP"), monkeypatch) is True


def test_filtre_recent_ecsarte_un_frozen(monkeypatch):
    assert _recent("[FROZEN] lane myia-ai-01:CoursIA-2", monkeypatch) is True


# --- 4. le motif d'ecartement est NOMME (point 4 de la decision) -----------

def _motif(body, monkeypatch):
    monkeypatch.setattr(pig, "_snapshot_comments", lambda _n: [_comment(body)])
    return pig._delivery_motif(17900)


def test_motif_nomme_le_dossier_vivant(monkeypatch):
    motif = _motif(_dossier("KEEP"), monkeypatch)
    assert motif is not None
    assert "VIVANT" in motif


def test_motif_nomme_la_livraison_epic_wide(monkeypatch):
    motif = _motif(EPIC_WIDE, monkeypatch)
    assert motif is not None
    assert "epic-wide" in motif


def test_pas_de_motif_pour_une_tranche(monkeypatch):
    assert _motif(TRANCHE, monkeypatch) is None


def test_motif_absent_sans_instantane(monkeypatch):
    monkeypatch.setattr(pig, "_snapshot_comments", lambda _n: None)
    assert pig._delivery_motif(17900) is None
