"""Le garde de fraicheur du rejeu DWELL (`scripts/ci/replay_dwell_floors.py`).

Le rejeu est un geste **irreversible** : un run part. Entre l'inventaire
qui a decide, et le geste, la PR peut avoir change d'etat. Ce que la
relecture doit prouver, c'est que la PR est **encore rejouable** :

- elle n'est pas devenue **brouillon** (un brouillon n'est pas mergeable ;
  `decide` l'exclut par construction, le balayeur aussi) ;
- elle n'est pas devenue **dispensee** (le label de derogation la retire
  du minuteur) ;
- le controle `PR gate` rejoue est **bien celui de l'inventaire** : un
  identifiant absent d'un seul cote ne prouve rien (fail-CLOSED).

Hors reseau : les fonctions testees sont PURES.
"""

from __future__ import annotations

import sys
from pathlib import Path

CI_DIR = Path(__file__).resolve().parents[1]
if str(CI_DIR) not in sys.path:
    sys.path.insert(0, str(CI_DIR))

from merge_dwell import WAIVER_LABEL  # noqa: E402


def _inv(**extra):
    """Un inventaire minimal : l'etat de depart du rejeu."""
    base = {"head_sha": "abc123", "gate_id": 1, "draft": False,
            "derogation": False}
    base.update(extra)
    return base


def _frais(**extra):
    """Un etat relu minimal, identique a l'inventaire."""
    base = {"sha": "abc123", "state": "open", "gate_id": 1,
            "status": "completed", "conclusion": "failure",
            "draft": False, "derogation": False}
    base.update(extra)
    return base

# ---------------------------------------------------------------------------
# Le garde de fraicheur : brouillon, dispense, identifiant non prouve
# ---------------------------------------------------------------------------

def test_le_geste_est_refuse_si_la_pr_est_devenue_brouillon():
    """Une PR peut devenir BROUILLON entre l'inventaire et le geste.

    Un brouillon n'est pas mergeable : `decide` l'exclut par construction,
    et le balayeur `pr-gate-stale-sweep.yml` l'exclut aussi. La relecture
    doit donc le relire -- sans quoi le rejeu partirait sur une PR que
    personne ne peut merger.
    """
    import replay_dwell_floors

    ok, motif = replay_dwell_floors.verifie_fraicheur(_inv(), _frais(draft=True))
    assert ok is False
    assert "brouillon" in motif


def test_le_geste_est_refuse_si_la_pr_est_devenue_dispensee():
    """Une PR peut gagner le label de derogation entre les deux lectures.

    Une dispense n'est pas soumise au minuteur : la rejouer ne sert a rien.
    """
    import replay_dwell_floors

    ok, motif = replay_dwell_floors.verifie_fraicheur(
        _inv(), _frais(derogation=True))
    assert ok is False
    assert "dispense" in motif


def test_un_etat_relu_sans_le_champ_draft_est_un_refus():
    """Fail-CLOSED : un etat relu qui ne porte pas le champ ne prouve pas
    que la PR n'est pas devenue brouillon."""
    import replay_dwell_floors

    frais = _frais()
    del frais["draft"]
    ok, motif = replay_dwell_floors.verifie_fraicheur(_inv(), frais)
    assert ok is False
    assert "draft" in motif


def test_un_identifiant_de_controle_absent_d_un_cote_est_un_refus():
    """Un identifiant de controle **absent d'un seul cote** ne prouve pas
    l'egalite : c'est un identifiant non prouve. Les deux sens sont refuses."""
    import replay_dwell_floors

    inv = _inv()
    del inv["gate_id"]
    ok, motif = replay_dwell_floors.verifie_fraicheur(inv, _frais())
    assert ok is False
    assert "gate_id" in motif or "identifiant de controle" in motif

    frais = _frais()
    del frais["gate_id"]
    ok, motif = replay_dwell_floors.verifie_fraicheur(_inv(), frais)
    assert ok is False
    assert "identifiant de controle" in motif


def test_relit_etat_rend_le_brouillon_et_la_derogation(monkeypatch):
    """La relecture rend l'etat de BROUILLON et la DEROGATION : ils ne sont
    plus lus puis jetes."""
    import replay_dwell_floors

    def faux_pr_info(repo, number):
        return {"sha": "abc123", "state": "open", "draft": True,
                "labels": [WAIVER_LABEL], "labels_lus": True}

    monkeypatch.setattr(replay_dwell_floors, "pr_info", faux_pr_info)
    monkeypatch.setattr(replay_dwell_floors, "gate_check_run",
                        lambda *a, **k: {"id": 7, "status": "completed",
                                         "conclusion": "failure"})
    relu = replay_dwell_floors.relit_etat("jsboige/CoursIA", 27273)
    assert relu["draft"] is True
    assert relu["derogation"] is True
    assert relu["labels_lus"] is True


def test_le_rejeu_ne_part_pas_si_la_pr_est_devenue_brouillon(monkeypatch):
    """Le geste ne part pas : `gh run rerun` n'est pas appele, et la
    commande sort en rc 1 (geste rate)."""
    import replay_dwell_floors

    appele = {"gh": False}
    monkeypatch.setattr(replay_dwell_floors, "inspect_pr", lambda *a, **k: {
        "pr": 1, "action": "rejouer", "motif": "plancher brut passe",
        "run_id": "42", "job_id": "43", "draft": False, "state": "open",
        "head_sha": "abc123", "gate_id": 1, "derogation": False})

    monkeypatch.setattr(replay_dwell_floors, "relit_etat", lambda *a, **k: {
        "sha": "abc123", "state": "open", "gate_id": 1, "status": "completed",
        "conclusion": "failure", "draft": True, "derogation": False,
        "labels_lus": True})

    def faux_gh_rerun(*a, **k):
        appele["gh"] = True
        return 0, ""

    monkeypatch.setattr(replay_dwell_floors, "gh_rerun", faux_gh_rerun)
    monkeypatch.setattr(sys, "argv",
                        ["replay_dwell_floors.py", "--pr", "1", "--apply", "--json"])
    assert replay_dwell_floors.main() == 1
    assert appele["gh"] is False
