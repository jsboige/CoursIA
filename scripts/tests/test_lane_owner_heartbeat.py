#!/usr/bin/env python3
r"""Tests du battement `.lane-owner` (#19010, suite #18494).

Pinent les trois bornes de `scripts/ci/lane_owner_heartbeat.py` et
l'acceptance de l'issue :

- un agent vivant en lecture seule au-dela de la fenetre **n'est plus
  retirable tant qu'il bat** -- verifie sur le predicat REEL du pruner
  (`prune_merged_worktrees.recent_activity_age_hours`, celui que
  `prune_merged_worktrees.py` appelle avant tout retrait) ;
- a sa mort (plus aucun battement), **la fenetre reprend son cours** --
  protection auto-expirante inchangee ;
- le battement ne CREE jamais de marqueur (pas d'attribution fabriquee),
  ne touche pas au contenu, et ne recule jamais le mtime.

Run : python -m pytest scripts/tests/test_lane_owner_heartbeat.py
"""
from __future__ import annotations

import hashlib
import os
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import lane_owner_heartbeat as loh  # noqa: E402
import prune_merged_worktrees as pmw  # noqa: E402

WINDOW_H = 6.0
MARKER_TEXT = "myia-po-2026:CoursIA\nworktree 19010\n"


def _aged_worktree(tmp_path: Path, age_h: float, with_marker: bool = True) -> Path:
    """Worktree simule : dossier et marqueur vieillis de `age_h` heures."""
    wt = tmp_path / "CoursIA-19010"
    (wt / "sub").mkdir(parents=True)
    (wt / "sub" / "f.txt").write_text("x", encoding="utf-8")
    t = time.time() - age_h * 3600.0
    if with_marker:
        marker = wt / loh.MARKER_NAME
        marker.write_text(MARKER_TEXT, encoding="utf-8")
        os.utime(marker, (t, t))
    os.utime(wt, (t, t))
    os.utime(wt / "sub", (t, t))
    return wt


def _sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


class TestRefresh:
    def test_avance_le_mtime_sans_toucher_au_contenu(self, tmp_path):
        wt = _aged_worktree(tmp_path, age_h=10.0)
        marker = wt / loh.MARKER_NAME
        before = _sha(marker)
        assert loh.marker_age_hours(wt) > 9.0

        ok, message = loh.refresh(wt)

        assert ok, message
        assert _sha(marker) == before, "le contenu du marqueur ne doit jamais changer"
        assert loh.marker_age_hours(wt) < 0.01

    def test_refuse_marqueur_absent_et_ne_cree_rien(self, tmp_path):
        wt = _aged_worktree(tmp_path, age_h=10.0, with_marker=False)
        marker = wt / loh.MARKER_NAME

        ok, message = loh.refresh(wt)

        assert not ok
        assert "absent" in message
        assert not marker.exists(), "un battement ne fabrique jamais d'attribution de lane"

    def test_ne_recule_jamais_un_mtime_deja_frais(self, tmp_path):
        wt = _aged_worktree(tmp_path, age_h=1.0)
        marker = wt / loh.MARKER_NAME
        future = time.time() + 3600.0
        os.utime(marker, (future, future))

        ok, message = loh.refresh(wt)

        assert ok
        assert "inchange" in message
        assert marker.stat().st_mtime == future, "jamais de recul de protection"


class TestAcceptanceSurLePredicatDuPruner:
    """L'acceptance de #19010, mesuree sur la fonction que le pruner appelle."""

    def test_agent_vivant_au_dela_de_la_fenetre_reste_protege(self, tmp_path):
        # 10 h sans ecriture : le predicat brut dit "retirable"...
        wt = _aged_worktree(tmp_path, age_h=10.0)
        assert pmw.recent_activity_age_hours(str(wt)) > WINDOW_H

        # ... et un battement le protege a nouveau, sans commit ni ecriture.
        ok, _ = loh.refresh(wt)
        assert ok

        assert pmw.recent_activity_age_hours(str(wt)) < WINDOW_H

    def test_fenetre_reprise_a_la_mort_de_l_agent(self, tmp_path):
        # Meme worktree, marqueur vieilli de 8 h : plus personne ne bat.
        wt = _aged_worktree(tmp_path, age_h=8.0)
        assert pmw.recent_activity_age_hours(str(wt)) > WINDOW_H, (
            "sans battement, la protection doit expirer -- #18494 n'est pas affaibli"
        )

    def test_le_dossier_n_est_pas_touche(self, tmp_path):
        # Le predicat prend le PLUS RECENT des deux marqueurs : battre le seul
        # marqueur suffit, et le dossier doit rester intact (aucun effet de bord).
        wt = _aged_worktree(tmp_path, age_h=10.0)
        dir_mtime = wt.stat().st_mtime

        ok, _ = loh.refresh(wt)

        assert ok
        assert wt.stat().st_mtime == dir_mtime


class TestCli:
    def test_once_rc0_et_marqueur_battu(self, tmp_path, capsys):
        wt = _aged_worktree(tmp_path, age_h=7.0)
        assert loh.main([str(wt)]) == loh.EXIT_OK
        assert "battu" in capsys.readouterr().out
        assert loh.marker_age_hours(wt) < 0.01

    def test_once_refuse_rc2_sur_marqueur_absent(self, tmp_path):
        wt = _aged_worktree(tmp_path, age_h=7.0, with_marker=False)
        assert loh.main([str(wt)]) == loh.EXIT_REFUSED

    def test_status_n_ecrit_rien(self, tmp_path, capsys):
        wt = _aged_worktree(tmp_path, age_h=1.0)
        mtime = (wt / loh.MARKER_NAME).stat().st_mtime

        assert loh.main([str(wt), "--status"]) == loh.EXIT_OK

        assert "protege" in capsys.readouterr().out
        assert (wt / loh.MARKER_NAME).stat().st_mtime == mtime

    def test_loop_sous_le_plancher_refuse(self, tmp_path):
        wt = _aged_worktree(tmp_path, age_h=1.0)
        assert loh.main([str(wt), "--loop", "1"]) == loh.EXIT_USAGE

    def test_loop_borne_bat_le_nombre_demande(self, tmp_path, capsys):
        wt = _aged_worktree(tmp_path, age_h=7.0)
        code = loh.main([str(wt), "--loop", str(loh.MIN_LOOP_SECONDS), "--beats", "2"])
        assert code == loh.EXIT_OK
        assert capsys.readouterr().out.count("battu") == 2
        assert loh.marker_age_hours(wt) < 0.01

    def test_dossier_inexistant_rc3(self, tmp_path):
        assert loh.main([str(tmp_path / "pas-la")]) == loh.EXIT_USAGE
