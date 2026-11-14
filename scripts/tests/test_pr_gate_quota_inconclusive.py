#!/usr/bin/env python3
"""La famille QUOTA d'installation ne doit pas rendre un FAIL de contenu.

Mesure (fenetre 2026-11-14 12:00Z-14:00Z, 40 runs du PR gate, 35 echecs) :
**6 des 35 echecs du gate** portaient la signature
`rate limit exceeded for installation` -- des rouges que la lane lisait comme
des defauts de code, et qui n'etaient pas des defauts de code. Les 29 autres
etaient 14 DWELL (minuteur), 10 vrais rouges et 2 STARVED.

Ce que ces tests tiennent :

1. **Controle positif** -- un 403 de quota simule rend un verdict
   INCONCLUSIVE (code 3), rejouable, et NON un FAIL (code 1) ;
2. **Controle negatif** -- un vrai rouge de check reste un FAIL (code 1) avec
   son annotation `::error::` ;
3. **Repli borne** -- quand l'heure de reinitialisation du quota tient dans le
   budget restant du job, le gate ATTEND cette heure au lieu de conclure ;
4. Quand elle ne tient pas, le verdict est INCONCLUSIVE -- jamais un FAIL ;
5. La legende du code 3 est un `::warning::` (ce n'est pas une erreur de
   code), et la conclusion de check-run correspondante est `neutral`.

Run: python -m pytest scripts/tests/test_pr_gate_quota_inconclusive.py
"""
from __future__ import annotations

import itertools
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import pr_gate  # noqa: E402

QUOTA_SIGNATURE = "gh: API rate limit exceeded for installation. (HTTP 403)"

#: Instant mural fixe : les tests comparent l'epoch de reinitialisation du
#: quota a une horloge murale injectee, jamais a l'heure reelle.
WALL_NOW = 1_700_000_000.0


def quota_error(reset_at: int | None = None) -> pr_gate.GateError:
    """L'erreur que `_gh_api` leve sur un 403 de quota d'installation."""
    message = f"gh api repos/o/r/check-runs failed (exit 1, HTTP 403): {QUOTA_SIGNATURE}"
    if reset_at is not None:
        message += f", quota reset {reset_at}"
    return pr_gate.GateError(message)


def _clock(step=10):
    counter = itertools.count(0, step)
    return lambda: next(counter)


def _run(name, conclusion, status="completed"):
    return {
        "name": name,
        "status": status,
        "conclusion": conclusion,
        "started_at": "2026-08-07T00:00:00Z",
        "details_url": "https://example.invalid/run/1",
    }


# --- 1. controlespositif et negatif sur le VERDICT --------------------------


def test_un_403_de_quota_rend_un_verdict_inconclusive(monkeypatch):
    """CONTROLE POSITIF : le quota epuise donne le code 3, pas 1."""
    def fetch(_repo, _sha):
        raise quota_error()

    with pytest.raises(pr_gate.GateInconclusive):
        pr_gate.wait_and_decide(
            "o/r", "sha", "PR gate", timeout_min=0, poll_sec=0,
            settle_polls=2, sleep=lambda _s: None, fetch=fetch,
            now=_clock(), wall_now=lambda: WALL_NOW,
        )


def test_le_verdict_inconclusive_sort_par_le_code_3(monkeypatch):
    """Le code 3 est DISTINCT de 1 : c'est lui que le chainer reconnait
    comme rejouable. Un FAIL de contenu reste 1."""
    assert pr_gate.INSTALLATION_QUOTA_EXIT == 3
    assert pr_gate.INSTALLATION_QUOTA_EXIT != 1


def test_un_vrai_rouge_reste_un_fail(monkeypatch):
    """CONTROLE NEGATIF : un vrai rouge de check ne bouge pas."""
    def fetch(_repo, _sha):
        return [_run("Lean CI", "failure")]

    code, msg = pr_gate.wait_and_decide(
        "o/r", "sha", "PR gate", timeout_min=90, poll_sec=0,
        settle_polls=2, sleep=lambda _s: None, fetch=fetch, now=_clock(),
    )
    assert code == 1
    assert "Lean CI" in msg


# --- 2. le repli borne : attendre la reinitialisation du quota --------------


def test_le_repli_borne_attend_la_reinitialisation_du_quota():
    """Quand l'heure de reinitialisation tient dans le budget restant, le gate
    ATTEND cette heure et rejoue sa lecture -- il ne conclut pas en FAIL sur
    une infra qui redeviendra lisible dans une minute."""
    polls = []
    sleeps = []

    def fetch(_repo, _sha):
        polls.append(1)
        if len(polls) == 1:
            raise quota_error(reset_at=int(WALL_NOW) + 30)
        return []

    code, msg = pr_gate.wait_and_decide(
        "o/r", "sha", "PR gate", timeout_min=10, poll_sec=0,
        settle_polls=2, sleep=lambda s: sleeps.append(s), fetch=fetch,
        now=_clock(), wall_now=lambda: WALL_NOW,
    )
    assert code == 0, msg
    # L'attente de 30 s (le delai avant reinitialisation) a bien eu lieu.
    assert 30 in sleeps, sleeps
    assert len(polls) == 3, "la lecture est rejouee apres l'attente"


def test_le_repli_borne_ne_conclut_pas_en_inconclusive():
    """Le chemin d'attente aboutit a un verdict, pas a une exception."""
    polls = []

    def fetch(_repo, _sha):
        polls.append(1)
        if len(polls) == 1:
            raise quota_error(reset_at=int(WALL_NOW) + 5)
        return []

    code, msg = pr_gate.wait_and_decide(
        "o/r", "sha", "PR gate", timeout_min=10, poll_sec=0,
        settle_polls=2, sleep=lambda _s: None, fetch=fetch,
        now=_clock(), wall_now=lambda: WALL_NOW,
    )
    assert code == 0 and "PASS" in msg


def test_un_reset_au_dela_du_budget_donne_inconclusive():
    """Quand l'heure de reinitialisation est HORS du budget restant, le gate
    ne peut pas attendre : le verdict est INCONCLUSIVE (rejouable), jamais un
    FAIL de contenu."""
    def fetch(_repo, _sha):
        raise quota_error(reset_at=int(WALL_NOW) + 100_000)

    with pytest.raises(pr_gate.GateInconclusive):
        pr_gate.wait_and_decide(
            "o/r", "sha", "PR gate", timeout_min=0.01, poll_sec=0,
            settle_polls=2, sleep=lambda _s: None, fetch=fetch,
            now=_clock(), wall_now=lambda: WALL_NOW,
        )


def test_un_403_sans_heure_de_reinitialisation_ne_bloque_pas():
    """Sans l'en-tete `x-ratelimit-reset`, l'erreur reste sur le chemin
    transitoire ordinaire : pas d'attenteale, pas d'exception INCONCLUSIVE
    prematuree -- mais le verdict final reste INCONCLUSIVE s'il est toujours
    illisible."""
    def fetch(_repo, _sha):
        raise quota_error()

    with pytest.raises(pr_gate.GateInconclusive):
        pr_gate.wait_and_decide(
            "o/r", "sha", "PR gate", timeout_min=0.5, poll_sec=0,
            settle_polls=2, sleep=lambda _s: None, fetch=fetch,
            now=_clock(), wall_now=lambda: WALL_NOW,
        )


# --- 3. la lecture de l'en-tete ---------------------------------------------


def test_l_en_tete_reset_est_lu():
    header = (
        "HTTP/2.0 403 Forbidden\r\n"
        "x-ratelimit-limit: 1000\r\n"
        "x-ratelimit-remaining: 0\r\n"
        "x-ratelimit-reset: 1700003600\r\n"
        "content-type: application/json\r\n"
    )
    assert pr_gate._gh_rate_limit_reset(header) == 1700003600


def test_un_en_tete_absent_ne_donne_pas_d_epoch():
    assert pr_gate._gh_rate_limit_reset("HTTP/2.0 403 Forbidden\r\n") is None
    assert pr_gate._gh_rate_limit_reset("") is None


def test_l_epoch_est_relu_depuis_le_message():
    exc = quota_error(reset_at=1700003600)
    assert pr_gate._quota_reset_epoch(exc) == 1700003600
    assert pr_gate._quota_reset_epoch(pr_gate.GateError("boom")) is None


# --- 4. la surface du verdict (main) ---------------------------------------


def test_main_rend_le_code_3_sur_un_quota(capsys, monkeypatch):
    """Le verdict INCONCLUSIVE sort par le code 3, avec un message qui le
    nomme."""
    def boom(*_args, **_kwargs):
        raise pr_gate.GateInconclusive("quota partage epuise")

    monkeypatch.setattr(pr_gate, "wait_and_decide", boom)
    assert pr_gate.main(["--repo", "o/r", "--sha", "deadbeef"]) == 3
    captured = capsys.readouterr()
    assert "INCONCLUSIVE" in captured.out
    assert "REJOUABLE" in captured.out


def test_main_annonce_le_code_3_en_warning_pas_en_error(capsys, monkeypatch):
    """La famille quota n'est pas une erreur de code : l'annotation dit
    `::warning::`, et surtout PAS `::error::`."""
    def boom(*_args, **_kwargs):
        raise pr_gate.GateInconclusive("quota partage epuise")

    monkeypatch.setattr(pr_gate, "wait_and_decide", boom)
    pr_gate.main(["--repo", "o/r", "--sha", "deadbeef"])
    captured = capsys.readouterr()
    assert "::warning::[pr-gate] INCONCLUSIVE" in captured.err
    assert "::error::" not in captured.err


def test_main_annonce_un_vrai_rouge_en_error(capsys, monkeypatch):
    """CONTROLE NEGATIF de la surface : un FAIL de contenu reste un
    `::error::`."""
    def boom(*_args, **_kwargs):
        raise pr_gate.GateError("gh api exploded")

    monkeypatch.setattr(pr_gate, "wait_and_decide", boom)
    assert pr_gate.main(["--repo", "o/r", "--sha", "deadbeef"]) == 1
    captured = capsys.readouterr()
    assert "::error::[pr-gate] FAIL -- cannot establish check state" in captured.err


def test_la_legende_inconclusive_annule_la_legende_rouge(monkeypatch):
    """Une jambe INCONCLUSIVE s'annule elle-meme, comme STARVED : la PR reste
    BLOQUEE sans rouge de code, et le balayage la rejoue."""
    cancelled = []

    def boom(*_args, **_kwargs):
        raise pr_gate.GateInconclusive("quota partage epuise")

    monkeypatch.setattr(pr_gate, "wait_and_decide", boom)
    monkeypatch.setattr(
        pr_gate, "cancel_own_run", lambda repo, run_id: cancelled.append(run_id) or True
    )
    monkeypatch.setattr(pr_gate, "CANCEL_GRACE_SEC", 0.0)
    code = pr_gate.main([
        "--repo", "o/r", "--sha", "deadbeef", "--run-id", "4242",
    ])
    assert code == 3
    assert cancelled == ["4242"], cancelled


# --- 5. la conclusion de check-run ------------------------------------------


def test_la_conclusion_de_check_run_neutre_pour_le_code_3():
    assert pr_gate._conclusion_for(0) == "success"
    assert pr_gate._conclusion_for(1) == "failure"
    assert pr_gate._conclusion_for(pr_gate.INSTALLATION_QUOTA_EXIT) == "neutral"


def test_le_code_3_ne_se_poste_pas_en_failure(monkeypatch):
    """Un `failure` POSTE serait un rouge inamovible (#21543) pour un verdict
    qui n'est pas un verdict."""
    posted = {}

    def poster(path, fields):
        posted.update(fields)
        return {}

    pr_gate.post_check_run("o/r", "sha", "PR gate", 3, "INCONCLUSIVE -- quota", poster=poster)
    assert posted["conclusion"] == "neutral"

    posted.clear()
    pr_gate.post_check_run("o/r", "sha", "PR gate", 1, "FAIL -- Lean CI", poster=poster)
    assert posted["conclusion"] == "failure"
