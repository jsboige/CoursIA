"""T-H (#25510) -- publication des check-runs : idempotence, relance, compte.

Le quota d'ecriture de l'API Checks se consomme PAR POST. La voie rapide
emet un check-run par garde (~74 sur le registre courant), et le
declencheur `edited` (tranche T-C/2) fait revenir la voie rapide sur la
MEME tete : republier un verdict identique coute une ecriture pour rien.

Trois proprietes sont verifiees ici :
  - un verdict **identique** (meme nom, meme conclusion, meme titre) deja
    publie sur la tete n'est **pas** republie ;
  - une publication refusee par le **quota** est relancee **une seule fois**,
    et une erreur qui n'est pas un quota n'est **pas** relancee ;
  - le **compte** des publications (publiees / identiques / refusees) est
    dans le journal du job -- sans lui, une publication refusee disparait
    dans le stderr d'un garde.
"""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "scripts" / "ci"))

import fast_lane  # noqa: E402
import fast_lane_registry  # noqa: E402


def _guard_absorbe() -> object:
    """Un garde `absorbed` : son nom rendu est son nom canonique.

    Un garde absorbe ne porte pas le prefixe d'ombre : le nom de check-run
    qu'il publie est donc lisible tel quel dans le test.
    """
    for tranche in (fast_lane_registry.PILOT,):
        for guard in tranche:
            if guard.absorbed:
                return guard
    for attr in dir(fast_lane_registry):
        if not attr.startswith("TRANCHE"):
            continue
        for guard in getattr(fast_lane_registry, attr):
            if guard.absorbed:
                return guard
    raise AssertionError("aucun garde absorbe dans le registre")


def _run_engine(monkeypatch, tmp_path, existing, published):
    """Fait tourner la voie rapide sur UN garde, et rend son nom rendu."""
    guard = _guard_absorbe()
    monkeypatch.setenv("RUNNER_TEMP", str(tmp_path))
    monkeypatch.setattr(fast_lane, "changed_files", lambda _ref: ["x.ipynb"])
    monkeypatch.setattr(fast_lane, "guard_applies", lambda g, c: True)
    monkeypatch.setattr(fast_lane, "run_argv", lambda argv, ctx: (0, "{}"))
    monkeypatch.setattr(fast_lane, "run_iter",
                        lambda argv, paths, ctx, warn_rc=(),
                        fail_on_all_warn=False: (0, "{}"))
    monkeypatch.setattr(fast_lane, "git",
                        lambda *a: subprocess.CompletedProcess(a, 0, "", ""))
    monkeypatch.setattr(fast_lane, "latest_check_runs",
                        lambda repo, sha: existing)
    monkeypatch.setattr(fast_lane, "emit_check_run",
                        lambda *a, **k: (published.append(a), True)[1])
    rc = fast_lane.main(["--only", guard.name, "--base-ref", "main",
                          "--base-sha", "dead" * 10, "--head-sha", "beef" * 10,
                          "--pr-number", "1", "--repo", "jsboige/CoursIA"])
    return rc, guard


def test_un_verdict_identique_nest_pas_republie(monkeypatch, tmp_path):
    """Le cas de la tranche : republier un verdict identique coute du quota."""
    published = []
    guard = _guard_absorbe()
    name = guard.name
    title = f"{guard.name} -- OK"
    rc, guard = _run_engine(
        monkeypatch, tmp_path, {name: ("success", title)}, published)

    assert rc == 0
    assert published == [], (
        "un verdict identique (meme nom, meme conclusion, meme titre) doit "
        "etre laisse en place -- le POST coute une ecriture de quota")


def test_un_verdict_de_conclusion_differente_est_republie(monkeypatch, tmp_path):
    """Un verdict qui a change doit etre republie : le skip est porte par
    le couple (conclusion, titre), pas par le seul nom."""
    published = []
    guard = _guard_absorbe()
    name = guard.name
    rc, guard = _run_engine(
        monkeypatch, tmp_path, {name: ("failure", f"{guard.name} -- echec")},
        published)

    assert rc == 0
    assert len(published) == 1, (
        "un verdict de conclusion differente doit etre republie -- sinon la "
        "PR garderait un verdict perime")


def test_un_titre_different_donne_a_la_meme_conclusion_est_republie(
        monkeypatch, tmp_path):
    """Meme conclusion, titre different : le signal a change, on republie."""
    published = []
    guard = _guard_absorbe()
    rc, guard = _run_engine(
        monkeypatch, tmp_path,
        {guard.name: ("success", f"{guard.name} -- autre chose")}, published)

    assert rc == 0
    assert len(published) == 1


def test_une_lecture_echouee_ne_saute_aucune_publication(monkeypatch, tmp_path):
    """L'optimisation ne doit jamais fabriquer un verdict : si la lecture
    des verdicts existants echoue, on republie tout (et on perd du quota,
    ce qui est le prix d'un verdict sur)."""
    published = []
    rc, guard = _run_engine(monkeypatch, tmp_path, {}, published)

    assert rc == 0
    assert len(published) == 1


def test_une_publication_refusee_par_le_quota_est_relancee_une_fois(
        monkeypatch):
    """Un 403 de quota se relance UNE fois ; un succes suit."""
    calls = []

    def _fake_run(cmd, **kwargs):
        calls.append(cmd)
        if len(calls) == 1:
            return subprocess.CompletedProcess(
                cmd, 1, "",
                "gh: HTTP 403: API rate limit exceeded for installation")
        return subprocess.CompletedProcess(cmd, 0, '{"id": 1}', "")

    slept = []
    monkeypatch.setattr(fast_lane.subprocess, "run", _fake_run)
    monkeypatch.setattr(fast_lane.time, "sleep", lambda s: slept.append(s))

    ok = fast_lane.emit_check_run("jsboige/CoursIA", "beef" * 10, "garde",
                                  "success", "titre", "resume", False)

    assert ok is True
    assert len(calls) == 2, "une seule relance est autorisee"
    assert slept == [fast_lane.CHECK_RUN_RETRY_S]


def test_une_erreur_qui_nest_pas_un_quota_nest_pas_relancee(monkeypatch):
    """Une erreur de droit ou de payload ne se relance pas : la republier
    ne la ferait pas disparaitre."""
    calls = []

    def _fake_run(cmd, **kwargs):
        calls.append(cmd)
        return subprocess.CompletedProcess(
            cmd, 1, "", "gh: HTTP 422: Validation Failed")

    monkeypatch.setattr(fast_lane.subprocess, "run", _fake_run)
    monkeypatch.setattr(fast_lane.time, "sleep",
                        lambda s: pytest.fail("pas de relance sans quota"))

    ok = fast_lane.emit_check_run("jsboige/CoursIA", "beef" * 10, "garde",
                                  "success", "titre", "resume", False)

    assert ok is False
    assert len(calls) == 1


def test_un_quota_refuse_deux_fois_est_signale_sans_boucle(monkeypatch):
    """Deux refus de quota : le verdict est perdu, mais l'appel s'arrete."""
    calls = []

    def _fake_run(cmd, **kwargs):
        calls.append(cmd)
        return subprocess.CompletedProcess(
            cmd, 1, "", "gh: HTTP 403: API rate limit exceeded")

    monkeypatch.setattr(fast_lane.subprocess, "run", _fake_run)
    monkeypatch.setattr(fast_lane.time, "sleep", lambda s: None)

    ok = fast_lane.emit_check_run("jsboige/CoursIA", "beef" * 10, "garde",
                                  "success", "titre", "resume", False)

    assert ok is False
    assert len(calls) == 2


def test_le_compte_des_publications_est_dans_le_journal(monkeypatch, tmp_path,
                                                        capsys):
    """Le compte est la seule mesure qui rend le quota lisible."""
    published = []
    rc, guard = _run_engine(monkeypatch, tmp_path, {}, published)

    out = capsys.readouterr().out
    assert "publications :" in out, (
        "le journal du job doit porter le compte des publications")
    assert "1 publiee(s)" in out
    assert "0 identique(s)" in out
    assert "0 refusee(s)" in out


def test_lis_le_plus_recent_check_run_de_chaque_nom(monkeypatch):
    """`latest_check_runs` lit le PLUS RECENT de chaque nom.

    L'API rend les entrees du plus recent au plus ancien : la premiere
    occurrence d'un nom est donc son check-run le plus recent.
    """
    payload = {
        "check_runs": [
            {"name": "garde A", "status": "completed",
             "conclusion": "success", "output": {"title": "garde A -- OK"}},
            {"name": "garde B", "status": "completed",
             "conclusion": "failure", "output": {"title": "garde B -- echec"}},
            {"name": "garde A", "status": "completed",
             "conclusion": "neutral", "output": {"title": "garde A -- neutre"}},
        ],
    }
    monkeypatch.setattr(
        fast_lane.subprocess, "run",
        lambda cmd, **kw: subprocess.CompletedProcess(
            cmd, 0, __import__("json").dumps(payload), ""))

    latest = fast_lane.latest_check_runs("jsboige/CoursIA", "beef" * 10)

    assert latest == {
        "garde A": ("success", "garde A -- OK"),
        "garde B": ("failure", "garde B -- echec"),
    }


def test_une_jambe_skipped_ne_remplace_pas_un_verdict(monkeypatch):
    """Une jambe `skipped` n'a rien mesure : elle ne peut pas servir de
    reference de skip (regle du repli, cf #26255)."""
    payload = {
        "check_runs": [
            {"name": "garde A", "status": "completed",
             "conclusion": "skipped", "output": {"title": "garde A -- skip"}},
        ],
    }
    monkeypatch.setattr(
        fast_lane.subprocess, "run",
        lambda cmd, **kw: subprocess.CompletedProcess(
            cmd, 0, __import__("json").dumps(payload), ""))

    assert fast_lane.latest_check_runs("jsboige/CoursIA", "beef" * 10) == {}
