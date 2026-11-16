#!/usr/bin/env python3
r"""Temoins comportementaux du predicat 7 ``preserved_on_origin`` (#26805).

La classe ``no_pr_match`` confondait deux situations :

- (a) une branche **jamais poussee** : le worktree est la seule copie du
  travail, le refus est juste ;
- (b) une branche **entierement poussee**, dont le tip distant est
  exactement la tete locale : ``origin`` detient deja tout le contenu, et
  ``git worktree remove`` ne supprime ni la branche locale ni la branche
  distante. Le refus y protegeait une copie redondante, a perpetuite.

Le predicat 7 rend REMOVE sur (b), et **fail-closed** sur tout le reste.

Cinq conditions exigees toutes les cinq :

1. la branche existe sur le **distant** (mesuree en direct, jamais sur la
   seule ref de tracking locale, qui peut etre perimee) ;
2. le tip distant est **egal** a la tete locale (ni en avance, ni en
   retard, ni divergent) ;
3. la ref de tracking locale existe et designe la tete locale (temoin
   d'un fetch effectif) ;
4. le worktree est propre ;
5. aucune activite dans la fenetre, et le worktree n'est pas le courant.

Les six cas REFUSE demandes par l'issue sont temoins ici :

- branche absente de ``origin`` ;
- tete en avance d'un commit ;
- tete divergente ;
- fichier suivi modifie ;
- activite recente ;
- ref distant absent faute de fetch.

Plus deux temoins de contrat : le mode degrade gh n'essaie aucun appel
reseau, et le champ ``content_on_main`` reste **faux** (le contenu n'est
pas sur main : c'est origin qui le porte).
"""
from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import prune_merged_worktrees as pmw  # noqa: E402


# ---------------------------------------------------------------------------
# harnais git jetable
# ---------------------------------------------------------------------------

def _git(cwd, *args: str, check: bool = True) -> str:
    proc = subprocess.run(
        ["git", *args],
        cwd=str(cwd),
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        timeout=120,
    )
    if check and proc.returncode != 0:
        raise AssertionError(
            f"git {' '.join(args)} -> rc={proc.returncode}: {proc.stderr}"
        )
    return proc.stdout.strip()


def _commit(repo: Path, path: str, content: str, msg: str) -> str:
    (repo / path).write_text(content, encoding="utf-8")
    _git(repo, "add", path)
    _git(repo, "commit", "-q", "-m", msg)
    return _git(repo, "rev-parse", "HEAD")


class _Fixture:
    """origin (bare) + clone + les branches des six cas.

    Historique :

      main : A -- B -- C              (pousse)
      feat/pushed      : B -- p1      (poussee, ref locale presente)
      feat/nofetch     : B -- n1      (poussee par un AUTRE clone -> la
                                       ref de tracking locale est absente)
      feat/avance      : B -- a1 (poussee) puis a2 local (tete en avance)
      feat/divergent   : B -- d1 (poussee) puis d2 local divergent
    """

    def __init__(self, tmp_path: Path):
        origin = tmp_path / "origin.git"
        origin.mkdir()
        _git(origin, "init", "--bare", "-b", "main")

        seed = tmp_path / "seed"
        seed.mkdir()
        _git(seed, "init", "-b", "main")
        _git(seed, "config", "user.name", "T")
        _git(seed, "config", "user.email", "t@example.invalid")
        _commit(seed, "a.txt", "a\n", "A")
        sha_b = _commit(seed, "b.txt", "b\n", "B")
        _commit(seed, "c.txt", "c\n", "C")
        _git(seed, "remote", "add", "origin", str(origin))
        _git(seed, "push", "origin", "main")

        clone = tmp_path / "clone"
        _git(tmp_path, "clone", str(origin), "clone")
        _git(clone, "config", "user.name", "T")
        _git(clone, "config", "user.email", "t@example.invalid")

        # --- branche poussee, ref de tracking locale presente -------------
        _git(clone, "checkout", "-q", "-b", "feat/pushed", sha_b)
        self.sha_pushed = _commit(clone, "p.txt", "p\n", "p1")
        _git(clone, "push", "-q", "origin", "feat/pushed")

        # --- branche poussee, ref de tracking locale ABSENTE ---------------
        # La branche existe sur origin, mais ce clone ne l'a jamais
        # fetchee : la ref `refs/remotes/origin/feat/nofetch` n'existe pas
        # ici. C'est le cas « ref distant absent faute de fetch ».
        _git(clone, "checkout", "-q", "-b", "feat/nofetch", sha_b)
        self.sha_nofetch = _commit(clone, "n.txt", "n\n", "n1")
        _git(clone, "push", "-q", "origin", "feat/nofetch")
        _git(clone, "update-ref", "-d", "refs/remotes/origin/feat/nofetch")

        # --- branche en avance d'un commit -------------------------------
        _git(clone, "checkout", "-q", "-b", "feat/avance", sha_b)
        self.sha_avance_pousse = _commit(clone, "a.txt", "a1\n", "a1")
        _git(clone, "push", "-q", "origin", "feat/avance")
        self.sha_avance = _commit(clone, "a.txt", "a2\n", "a2")

        # --- branche divergente -----------------------------------------
        _git(clone, "checkout", "-q", "-b", "feat/divergent", sha_b)
        self.sha_div_pousse = _commit(clone, "d.txt", "d1\n", "d1")
        _git(clone, "push", "-q", "origin", "feat/divergent")
        _git(clone, "reset", "-q", "--hard", sha_b)
        self.sha_divergent = _commit(clone, "d.txt", "d2\n", "d2")

        _git(clone, "checkout", "-q", "--detach")

        self.clone = clone
        self.wts = {}
        for name in ("feat/pushed", "feat/nofetch", "feat/avance",
                     "feat/divergent"):
            wt = tmp_path / ("wt-" + name.replace("/", "-"))
            _git(clone, "worktree", "add", "-q", str(wt), name)
            self.wts[name] = wt


@pytest.fixture(autouse=True)
def _no_gh_degraded(monkeypatch):
    """Le singleton de resolution ne doit pas se croire en mode degrade."""
    pmw.reset_pr_resolution()


def _sans_pr(monkeypatch):
    """Aucune PR attribuable : le grain est la cible du predicat 7."""
    monkeypatch.setattr(pmw, "lookup_pr_for_branch",
                        lambda branch, head_sha=None: None)
    monkeypatch.setattr(pmw, "remote_head_for_head",
                        lambda wt_path, branch, head_sha: None)


def _tip_distant(monkeypatch, etat: str, sha=None):
    """Injecte la mesure du tip distant (voie REST de l'organe)."""
    monkeypatch.setattr(pmw, "_remote_branch_tip",
                        lambda branch: (etat, sha))
    monkeypatch.setattr(pmw, "_REMOTE_TIP_MEMO", {})


# ---------------------------------------------------------------------------
# Le cas REMOVE
# ---------------------------------------------------------------------------

class TestCasRemove:
    def test_branche_poussee_propre_et_inactive_donne_remove(self, tmp_path,
                                                              monkeypatch):
        fx = _Fixture(tmp_path)
        wt = fx.wts["feat/pushed"]
        _sans_pr(monkeypatch)
        _tip_distant(monkeypatch, "ok", fx.sha_pushed)

        st = pmw.diagnose_worktree(str(wt), str(fx.clone),
                                   activity_window_h=0.0)
        assert st.decision == "REMOVE", st.refusal_reason
        assert st.refusal_reason is None
        assert st.content_preserved_by == "origin_branch"
        # Le contenu n'est PAS sur main : `content_on_main` reste faux, et
        # `content_on_main_by` reste vide. Confondre les deux ferait lire
        # une ascendance de main la ou il n'y a qu'une branche distante.
        assert st.content_on_main is False
        assert st.content_on_main_by is None

    def test_le_rapport_json_porte_la_preuve(self, tmp_path, monkeypatch):
        fx = _Fixture(tmp_path)
        wt = fx.wts["feat/pushed"]
        _sans_pr(monkeypatch)
        _tip_distant(monkeypatch, "ok", fx.sha_pushed)

        st = pmw.diagnose_worktree(str(wt), str(fx.clone),
                                   activity_window_h=0.0)
        charge = st.to_dict()
        assert charge["content_preserved_by"] == "origin_branch"

    def test_le_texte_annonce_la_preservation(self, tmp_path, monkeypatch):
        """Le lecteur du dry-run doit voir *pourquoi* le retrait est sur."""
        fx = _Fixture(tmp_path)
        wt = fx.wts["feat/pushed"]
        _sans_pr(monkeypatch)
        _tip_distant(monkeypatch, "ok", fx.sha_pushed)

        st = pmw.diagnose_worktree(str(wt), str(fx.clone),
                                   activity_window_h=0.0)
        rendu = pmw.render_text([st], dry_run=True)
        assert "preserved_on_origin(origin_branch)" in rendu, rendu


# ---------------------------------------------------------------------------
# Les six cas REFUSE
# ---------------------------------------------------------------------------

class TestSixCasRefuse:
    def test_branche_absente_de_origin(self, tmp_path, monkeypatch):
        """Le distant ne porte plus la branche : il ne peut rien
        preserver. Le refus terminal est conserve."""
        fx = _Fixture(tmp_path)
        wt = fx.wts["feat/pushed"]
        _sans_pr(monkeypatch)
        _tip_distant(monkeypatch, "absent", None)

        st = pmw.diagnose_worktree(str(wt), str(fx.clone),
                                   activity_window_h=0.0)
        assert st.decision == "REFUSE"
        assert st.refusal_reason == "no_pr_match"
        assert st.content_preserved_by is None

    def test_tete_en_avance_d_un_commit(self, tmp_path, monkeypatch):
        """Le local a un commit de plus que le distant : le distant ne
        preserve pas le local."""
        fx = _Fixture(tmp_path)
        wt = fx.wts["feat/avance"]
        _sans_pr(monkeypatch)
        _tip_distant(monkeypatch, "ok", fx.sha_avance_pousse)

        assert pmw.content_preserved_on_origin_branch(
            str(wt), "feat/avance", fx.sha_avance) is False
        st = pmw.diagnose_worktree(str(wt), str(fx.clone),
                                   activity_window_h=0.0)
        assert st.decision == "REFUSE"
        assert st.content_preserved_by is None

    def test_tete_divergente(self, tmp_path, monkeypatch):
        """Tete divergente : ni egalite, ni ancetre commun -> refus."""
        fx = _Fixture(tmp_path)
        wt = fx.wts["feat/divergent"]
        _sans_pr(monkeypatch)
        _tip_distant(monkeypatch, "ok", fx.sha_div_pousse)

        assert pmw.content_preserved_on_origin_branch(
            str(wt), "feat/divergent", fx.sha_divergent) is False
        st = pmw.diagnose_worktree(str(wt), str(fx.clone),
                                   activity_window_h=0.0)
        assert st.decision == "REFUSE"
        assert st.content_preserved_by is None

    def test_fichier_suivi_modifie(self, tmp_path, monkeypatch):
        """Un worktree sale n'est pas retirable : le predicat 2a refuse
        en amont, le predicat 7 ne s'atteint pas."""
        fx = _Fixture(tmp_path)
        wt = fx.wts["feat/pushed"]
        _sans_pr(monkeypatch)
        _tip_distant(monkeypatch, "ok", fx.sha_pushed)
        (wt / "p.txt").write_text("modifie\n", encoding="utf-8")

        st = pmw.diagnose_worktree(str(wt), str(fx.clone),
                                   activity_window_h=0.0)
        assert st.decision == "REFUSE"
        assert st.refusal_reason == "uncommitted_source_changes"
        assert st.content_preserved_by is None

    def test_activite_recente(self, tmp_path, monkeypatch):
        """Fenetre « agent vivant » : le worktree frais est protege."""
        fx = _Fixture(tmp_path)
        wt = fx.wts["feat/pushed"]
        _sans_pr(monkeypatch)
        _tip_distant(monkeypatch, "ok", fx.sha_pushed)

        st = pmw.diagnose_worktree(str(wt), str(fx.clone),
                                   activity_window_h=6.0)
        assert st.decision == "REFUSE"
        assert st.refusal_reason.startswith("recent_activity:"), \
            st.refusal_reason
        assert st.content_preserved_by == "origin_branch", (
            "la preservation est mesuree, mais l'activite recente "
            "l'empeche : la preuve reste lisible dans le rapport"
        )

    def test_ref_distant_absent_faute_de_fetch(self, tmp_path, monkeypatch):
        """Branche poussee par un autre clone : la ref de tracking locale
        n'existe pas. Aucune fetch n'est tentee par l'organe -> refus."""
        fx = _Fixture(tmp_path)
        wt = fx.wts["feat/nofetch"]
        _sans_pr(monkeypatch)
        _tip_distant(monkeypatch, "ok", fx.sha_nofetch)

        assert pmw.content_preserved_on_origin_branch(
            str(wt), "feat/nofetch", fx.sha_nofetch) is False
        st = pmw.diagnose_worktree(str(wt), str(fx.clone),
                                   activity_window_h=0.0)
        assert st.decision == "REFUSE"
        assert st.refusal_reason == "no_pr_match"
        assert st.content_preserved_by is None


# ---------------------------------------------------------------------------
# Contrat : fail-closed, aucun canal reseau nouveau, mode degrade
# ---------------------------------------------------------------------------

class TestContrat:
    def test_mode_degrade_gh_aucun_appel_reseau(self, tmp_path, monkeypatch):
        """En mode degrade (#21753), aucun appel gh n'est tente : la
        preservation n'est pas mesuree, le refus est conserve."""
        fx = _Fixture(tmp_path)
        wt = fx.wts["feat/pushed"]
        _sans_pr(monkeypatch)

        appels = []
        monkeypatch.setattr(
            pmw, "_remote_branch_tip",
            lambda branch: appels.append(branch) or ("ok", fx.sha_pushed),
        )
        st = pmw.diagnose_worktree(str(wt), str(fx.clone),
                                   activity_window_h=0.0,
                                   gh_unavailable_reason="gh absent (temoin)")
        assert appels == []
        assert st.decision == "REFUSE"
        assert st.content_preserved_by is None

    def test_tip_distant_indetermmable_conserve_le_refus(self, tmp_path,
                                                          monkeypatch):
        """Une API muette ne prouve rien : fail-CLOSED."""
        fx = _Fixture(tmp_path)
        wt = fx.wts["feat/pushed"]
        _sans_pr(monkeypatch)
        _tip_distant(monkeypatch, "unknown", None)

        assert pmw.content_preserved_on_origin_branch(
            str(wt), "feat/pushed", fx.sha_pushed) is None
        st = pmw.diagnose_worktree(str(wt), str(fx.clone),
                                   activity_window_h=0.0)
        assert st.decision == "REFUSE"
        assert st.content_preserved_by is None

    def test_aucun_canal_reseau_nouveau(self):
        """L'organe n'introduit pas de second canal reseau : la voie REST
        deja utilisee (#23330) suffit. Ni `ls-remote`, ni `git fetch`."""
        source = Path(pmw.__file__).read_text(encoding="utf-8")
        assert re.findall(r"""["']ls-remote""", source) == []
        # Aucun `git fetch` declenche par l'organe : la ref de tracking
        # locale est un TEMOIN, pas une garantie de fraicheur. On cherche
        # l'ARGUMENT git, pas le mot (la prose en parle).
        assert re.findall(r"""["']fetch["']""", source) == []

    def test_le_champ_jumeau_est_additif(self):
        """`content_on_main_by` garde sa liste de jambes : le predicat 7
        n'y touche pas (le contenu n'est pas sur main)."""
        source = Path(pmw.__file__).read_text(encoding="utf-8")
        assert 'content_on_main_by="origin_branch"' not in source
        assert 'content_preserved_by="origin_branch"' in source
