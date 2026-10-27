#!/usr/bin/env python3
"""Tests du gate GPU du picker (#22747).

Le protocole (`docs/coordination/gpu-reservation.md`, section « Liaison
picker <-> file #1454 ») prescrit depuis c.257 que le picker consulte
`scripts/coordination/debt_ledger.py check_pending` AVANT de proposer un
grain GPU-bound. Le protocole l'annoncait ; le CODE ne le faisait pas
(mesure 2026-10-27 : `git grep -n check_pending scripts/` ne renvoie que le
ledger, ses tests et la documentation).

Ce fichier couvre les cas d'acceptation nommes par #22747 :

  - grain GPU propose sur device libre -> propose ;
  - grain GPU propose sur device tenu  -> ecarte avec motif ;
  - gate indisponible                  -> ecarte avec motif ;

et les deux non-regressions qui les rendent verifiables :

  - le verdict est lu dans le JSON, PAS dans le code de sortie (`NO_OBS`
    sort 0 et doit pourtant ecarter ; `STALE` et une erreur d'usage
    sortent tous deux 2) ;
  - un grain qui n'est pas GPU-borne ne consulte JAMAIS le gate.

Fichiers : ce module est distinct de `test_pick_idle_grain.py` pour que la
PR qui touche le picker (#22677, triage des contributions publiques) et
celle-ci ne se recouvrent pas sur le meme fichier de test.
"""

import json
import random
import subprocess
import sys
import types
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import pick_idle_grain as pig  # noqa: E402


@pytest.fixture(autouse=True)
def _no_shell_escape(forbid_shell_escape, monkeypatch):
    """Sentinelle armee pour tout le module (meme contrat que le module
    `test_pick_idle_grain.py`) : un test qui lancerait un vrai processus
    passerait sur l'etat chaud de la machine -- un vert qui ne mesure rien.
    Les tests qui ont besoin d'un faux ledger patchent eux-memes
    `pig.subprocess.run`.
    """
    monkeypatch.setenv("GH_TOKEN", "tok-fake-picker-gpu-gate")
    return forbid_shell_escape


class _FakeCompleted:
    """Stand-in de `CompletedProcess` (meme forme que celui du module
    `test_pick_idle_grain.py` : `_run_bounded` relit `.stdout` en repli)."""

    def __init__(self, stdout, returncode=0, stderr=""):
        self.stdout = stdout
        self.returncode = returncode
        self.stderr = stderr


def _item(number=5001, genre="training", body=""):
    return {
        "number": number, "title": "grain de test", "labels": [],
        "genre": genre, "body": body, "klass": "grain", "age": 10, "idle": 1,
    }


def _args(lane="myia-ai-01:CoursIA-2", gpu_entity=None):
    return types.SimpleNamespace(lane=lane, gpu_entity=list(gpu_entity or []))


# --- Le gate n'est appele QUE pour un grain GPU-borne -----------------------


def test_grain_non_gpu_borne_ne_consulte_jamais_le_gate():
    calls = []

    def probe(item, args):
        calls.append(item["number"])
        return ("HOLD", "inattendu")

    assert pig.gpu_gate_reason(_item(genre="guard"), _args(), probe) is None
    assert pig.gpu_gate_reason(_item(genre="docs"), _args(), probe) is None
    assert calls == [], "un grain non GPU-borne ne doit pas toucher le gate"


def test_sonde_inerte_ne_produit_aucun_verdict():
    """La sonde INERTE (test sans injection) ne mesure rien : le grain
    reste servable. C'est le fail-OPEN de la SONDE -- l'inverse du
    fail-CLOSED du GATE, qui ne vaut que pour une mesure REELLE."""
    assert pig.gpu_gate_reason(_item(), _args(), pig.gpu_gate_probe_inert) is None


# --- Les cinq verdicts du gate --------------------------------------------


def test_device_libre_le_grain_est_servable():
    for verdict in ("RELEASED", "OK_TO_RUN"):
        reason = pig.gpu_gate_reason(
            _item(), _args(),
            lambda i, a, v=verdict: (v, "myia-ai-01#gpu2 : " + v + " -- libre"))
        assert reason is None, verdict + " doit laisser passer le grain"


def test_device_tenu_le_grain_est_ecarte_avec_motif_nomme():
    reason = pig.gpu_gate_reason(
        _item(), _args(),
        lambda i, a: ("HOLD",
                       "myia-ai-01#gpu2 : HOLD -- held by myia-po-2024:CoursIA"))
    assert reason is not None
    assert "[DEFER gpu-reservation hold]" in reason
    assert "myia-ai-01#gpu2" in reason
    assert "myia-po-2024:CoursIA" in reason


def test_observation_absente_le_grain_est_ecarte_avec_motif_nomme():
    reason = pig.gpu_gate_reason(
        _item(), _args(),
        lambda i, a: ("NO_OBS",
                       "myia-ai-01#gpu2 : NO_OBS -- no record for myia-ai-01#gpu2"))
    assert reason is not None
    assert "[SKIP gpu-reservation missing]" in reason


@pytest.mark.parametrize("verdict,marker", [
    ("STALE", "[DEFER gpu-reservation stale]"),
    ("UNPOSTED", "[DEFER gpu-reservation unposted]"),
    ("GATE_UNREAD", "[DEFER gpu-reservation gate-unreadable]"),
    ("TARGET_UNRESOLVED", "[DEFER gpu-reservation target-unresolved]"),
])
def test_chaque_verdict_non_servable_a_son_marqueur(verdict, marker):
    reason = pig.gpu_gate_reason(
        _item(), _args(), lambda i, a: (verdict, "myia-ai-01#gpu2 : " + verdict))
    assert reason is not None
    assert marker in reason
    assert "myia-ai-01#gpu2" in reason


# --- La resolution de la cible -------------------------------------------


def test_cible_resolue_par_le_corps_puis_par_l_option():
    assert pig.gpu_target_entities(
        _item(body="la campagne tourne sur myia-ai-01#gpu2"), _args()
    ) == ["myia-ai-01#gpu2"]
    assert pig.gpu_target_entities(
        _item(), _args(gpu_entity=["myia-po-2024#gpu1"])
    ) == ["myia-po-2024#gpu1"]
    # Le corps d'abord : c'est la cible ecrite par l'auteur du grain.
    assert pig.gpu_target_entities(
        _item(body="myia-ai-01#gpu2"), _args(gpu_entity=["myia-po-2024#gpu1"])
    )[0] == "myia-ai-01#gpu2"


def test_cible_non_resolue_nomme_le_verdict_sans_consulter_le_ledger():
    """Aucun `<machine>#gpu<n>` dans le corps, aucune option : le verdict
    TARGET_UNRESOLVED est rendu SANS lancer de processus (la sentinelle du
    module le prouverait si le code essayait)."""
    verdict, reason = pig.gpu_gate_probe(_item(), _args())
    assert verdict == "TARGET_UNRESOLVED"
    assert "gpu-entity" in reason


# --- Le verdict est lu dans le JSON, pas dans le code de sortie ------------


def test_verdict_lu_dans_le_json_pas_dans_le_code_de_sortie(monkeypatch):
    """`NO_OBS` sort 0 et doit pourtant ecarter ; `STALE` et une erreur
    d'usage sortent tous deux 2. Le code de sortie ne decide donc rien --
    seul le champ `verdict` du JSON decide."""
    payload = json.dumps({"verdict": "NO_OBS",
                           "reason": "no snapshot at /tmp/snapshot.json",
                           "entity": "myia-ai-01#gpu2"})
    monkeypatch.setattr(pig.subprocess, "run",
                        lambda cmd, **kw: _FakeCompleted(payload, returncode=0))
    verdict, reason = pig.gpu_gate_probe(
        _item(body="myia-ai-01#gpu2"), _args())
    assert verdict == "NO_OBS"
    assert "no snapshot" in reason


def test_stale_sort_2_mais_le_verdict_prime(monkeypatch):
    payload = json.dumps({"verdict": "STALE",
                           "reason": "last state=stale at 2026-10-27T09:00:00Z",
                           "entity": "myia-ai-01#gpu2"})
    monkeypatch.setattr(pig.subprocess, "run",
                        lambda cmd, **kw: _FakeCompleted(payload, returncode=2))
    verdict, reason = pig.gpu_gate_probe(
        _item(body="myia-ai-01#gpu2"), _args())
    assert verdict == "STALE"
    assert "stale" in reason


def test_reponse_illisible_est_un_gate_illisible(monkeypatch):
    monkeypatch.setattr(pig.subprocess, "run",
                        lambda cmd, **kw: _FakeCompleted("pas du json",
                                                         returncode=0))
    verdict, reason = pig.gpu_gate_probe(
        _item(body="myia-ai-01#gpu2"), _args())
    assert verdict == "GATE_UNREAD"
    assert "myia-ai-01#gpu2" in reason


def test_gate_qui_echoue_est_un_gate_illisible(monkeypatch):
    def _boom(cmd, **kw):
        raise OSError("permission denied")

    monkeypatch.setattr(pig.subprocess, "run", _boom)
    verdict, reason = pig.gpu_gate_probe(
        _item(body="myia-ai-01#gpu2"), _args())
    assert verdict == "GATE_UNREAD"
    assert "myia-ai-01#gpu2" in reason


def test_le_gate_recoit_bien_le_mandat_du_ledger(monkeypatch):
    """La commande lancee est la sous-commande documentee, avec l'entite et
    la lane du tirage -- pas un appel libre."""
    seen = {}

    def _capture(cmd, **kw):
        seen["cmd"] = cmd
        return _FakeCompleted(json.dumps({"verdict": "RELEASED",
                                           "reason": "libre",
                                           "entity": "myia-ai-01#gpu2"}))

    monkeypatch.setattr(pig.subprocess, "run", _capture)
    verdict, _reason = pig.gpu_gate_probe(
        _item(body="myia-ai-01#gpu2"), _args(lane="myia-ai-01:CoursIA-2"))
    cmd = seen["cmd"]
    assert verdict == "RELEASED"
    assert cmd[1].endswith("debt_ledger.py")
    assert "check_pending" in cmd
    assert "--ledger" in cmd and "gpu-reservation" in cmd
    assert cmd[cmd.index("--entity") + 1] == "myia-ai-01#gpu2"
    assert cmd[cmd.index("--my-lane") + 1] == "myia-ai-01:CoursIA-2"
    assert "--json" in cmd


# --- Le gate agit sur les DEUX chemins de tirage --------------------------


def test_tirage_pondere_ecarte_un_grain_gpu_tenu(monkeypatch):
    monkeypatch.setattr(pig, "has_recent_delivery_marker", lambda n: False)
    candidates = [
        {"number": 5001, "title": "Add(training): campagne GPU", "age": 30,
         "idle": 1, "idle_since_delivery": 1, "genre": "training",
         "body": "tourne sur myia-ai-01#gpu2", "klass": "grain", "labels": []},
        {"number": 5002, "title": "Fix(docs): relecture", "age": 25,
         "idle": 1, "idle_since_delivery": 1, "genre": "docs",
         "body": "", "klass": "grain", "labels": []},
    ]
    by_class = {"grain": candidates, "umbrella": [], "delivered": []}

    class _A:
        grains = 4
        umbrellas = 0
        delivered = 0
        prev_genre = None
        lane = "myia-ai-01:CoursIA-2"
        check_claims = False

    picks, claims, conflicts = pig.draw_unclaimed(
        by_class, _A(), random.Random(42), {}, {}, {},
        delivered_state={"failures": [], "budget_hit": False,
                         "recent_filtered": 0},
        gpu_probe=lambda i, a: ("HOLD",
                                 "myia-ai-01#gpu2 : HOLD -- held by "
                                 "myia-po-2024:CoursIA"))
    assert [c["number"] for c in picks] == [5002]
    holds = [c for c in conflicts
             if c[0]["number"] == 5001 and "[DEFER gpu-reservation hold]" in c[1]]
    assert len(holds) == 1, "le grain GPU tenu doit etre ecarte AVEC son motif"


def test_tapis_ecarte_un_grain_gpu_tenu():
    """Le tapis (`--belt`) est le chemin que le cycle `/continue` emprunte :
    il porte le meme gate, le meme fail-CLOSED et le meme motif nomme."""
    args = types.SimpleNamespace(grains=1, include_delivered=True,
                                 lane="myia-ai-01:CoursIA-2", gpu_entity=[])
    picks, withheld, state = pig.belt_pick_with_replacements(
        [{"number": 6001, "klass": "grain", "genre": "training",
          "body": "myia-ai-01#gpu2"}],
        {6001: (pig.CLAIM_CODE_FREE, "libre")}, args, probe_budget=4,
        gpu_probe=lambda i, a: ("HOLD",
                                 "myia-ai-01#gpu2 : HOLD -- held by "
                                 "myia-po-2024:CoursIA"))
    assert picks == []
    assert len(withheld) == 1
    assert "[DEFER gpu-reservation hold]" in withheld[0][1]
    assert "myia-ai-01#gpu2" in withheld[0][1]
