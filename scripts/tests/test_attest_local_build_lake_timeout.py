"""Temoins du budget de temps par lake de l'organe d'attestation Lean.

Deux defauts distincts, deux temoins (dispatch du coordinateur du 15/11) :

1. **le defaut general coupait le build de `conway`** : a 900 s, le lake
   rend `exit 124` **sans** que le code soit en faute -- mesure sur ai-01 :
   #25585, `exit 124` a 904 s, 8 752 / 8 802 modules construits ; #26282,
   `exit 124` a 903 s, 8 773 / 8 804. Le budget propre du lake (2 400 s)
   porte ce lake la ou les autres gardent 900 s ;
2. **un timeout se lisait comme un echec de compilation** : le champ
   `reason` portait « lake build a echoue (exit_code=...) » la ou
   `builds[].status` disait `timeout`. Le diagnostic renvoyait a une faute
   de code la ou le defaut etait un budget de temps.

Les fonctions testees sont **pures** (aucun Lake, aucun toolchain, aucun
appel reseau) : le temoin ne depend pas de l'etat de la machine.

Run : python -m pytest scripts/tests/test_attest_local_build_lake_timeout.py -q
"""

from __future__ import annotations

import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "scripts" / "lean"))

import attest_local_build as alb  # noqa: E402


# --- 1. le budget de temps par lake ---------------------------------------

def test_le_defaut_general_reste_900_s():
    """Le defaut general ne bouge pas : un lake ordinaire garde 900 s."""
    assert alb.DEFAULT_LAKE_TIMEOUT == 900.0


def test_conway_beneficie_du_budget_propre():
    """Le lake `conway` ne se fait plus couper a 900 s.

    Temoin du defaut : sur le code casse, `conway` recevait le defaut
    general, et le build rendait `exit 124` a 903-904 s avec 8 7xx / 8 8xx
    modules construits -- une attestation impossible, sur un code sain.
    """
    assert alb.LAKE_TIMEOUTS["conway"] == 2400.0
    assert alb.lake_timeout({"lake": "conway"}) == 2400.0


def test_un_lake_ordinaire_garde_le_defaut_general():
    """Les autres lakes ne payent pas le budget de `conway`."""
    assert alb.lake_timeout({"lake": "sudoku"}) == 900.0
    assert alb.lake_timeout({"lake": "decisiontheory"}) == 900.0
    assert alb.lake_timeout({"lake": "conwaycgt"}) == 900.0


def test_la_surcharge_explicite_prime_sur_le_budget_propre():
    """Une surcharge de la ligne de commande prime toujours.

    C'est le contrat du dispatch du coordinateur : il relance #25585 et
    #26282 avec `--timeout 2400` en attendant ; cette valeur doit rester
    Prioritaire sur le budget propre du lake.
    """
    assert alb.lake_timeout({"lake": "conway"}, 2400.0) == 2400.0
    assert alb.lake_timeout({"lake": "conway"}, 120.0) == 120.0
    assert alb.lake_timeout({"lake": "sudoku"}, 2400.0) == 2400.0


def test_le_timeout_est_porte_par_le_nom_du_lake():
    """Le budget se resout sur le NOM du lake, pas sur son chemin.

    Le chemin du lake change avec les renommages de serie (`conway_lean`
    passe de `GOL/` a `JeuDeLaVie/`) : une table indexee sur le chemin
    deviendrait fausse au premier renommage, silencieusement.
    """
    assert alb.lake_timeout("conway") == 2400.0
    assert alb.lake_timeout("sudoku") == 900.0
    assert alb.lake_timeout({"lake": "conway"}) == 2400.0


# --- 2. timeout et echec de compilation se distinguent -----------------------

def test_le_timeout_est_nomme_dans_la_raison():
    """Un timeout porte un motif qui le dit.

    Temoin du defaut : la raison valait « lake build a echoue
    (exit_code=124) » -- le lecteur y cherche une faute de code, la ou le
    defaut est un budget de temps.
    """
    payload = {"exit_code": 124, "status": "timeout"}
    raison = alb.build_failure_reason(payload)
    assert "timeout" in raison
    assert "exit_code=124" in raison


def test_un_echec_de_compilation_reste_un_echec_de_compilation():
    """Un `failure` n'est pas un timeout : les deux motifs doivent differer."""
    payload = {"exit_code": 1, "status": "failure"}
    raison = alb.build_failure_reason(payload)
    assert "timeout" not in raison
    assert "echoue" in raison
    assert "exit_code=1" in raison


def test_la_violation_de_budget_prime_sur_le_motif_de_timeout():
    """La violation de concurrence reste nommee en premier.

    `lean_exec` presente une violation de budget comme un `timeout` : si le
    motif de budget disparait, le defaut se lit comme un manque de temps
    (#26480).
    """
    payload = {"exit_code": 124, "status": "timeout"}
    raison = alb.build_failure_reason(payload, "4 compilations lean > parallélisme accordée 3")
    assert "violation du budget de concurrence" in raison
    assert "timeout" not in raison
