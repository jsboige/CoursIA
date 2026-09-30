# -*- coding: utf-8 -*-
"""Tests du garde de la publication quotidienne du catalogue.

Les controles positifs viennent en premier : un garde qui ne peut pas echouer
ne prouve rien quand il rend vert. Le cas nominal de ce garde est justement un
vert -- il faut donc d'abord prouver qu'il sait mordre.
"""
import datetime as dt
import json
import sys

from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from ci import check_catalog_freshness as mod  # noqa: E402
from ci.check_catalog_freshness import (  # noqa: E402
    delivery_state,
    divergence,
    notebooks_on_disk,
)


def _tree(tmp_path, names):
    root = tmp_path / "nb"
    root.mkdir(exist_ok=True)
    for name in names:
        target = root / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text("{}", encoding="utf-8")
    return str(root)


# --- controles positifs : le garde DOIT mordre --------------------------------

def test_un_chemin_fantome_est_compte(tmp_path):
    """Une entree dont le fichier n'existe pas : le catalogue promet un
    notebook que le lecteur ne trouvera pas."""
    root = _tree(tmp_path, ["A/present.ipynb"])
    cat = [{"path": "A/present.ipynb"}, {"path": "A/disparu.ipynb"}]
    out = divergence(cat, {"A/present.ipynb"}, root=root)
    assert out["phantom"] == ["A/disparu.ipynb"]
    assert out["phantom_count"] == 1
    assert out["missing_count"] == 0


def test_un_notebook_absent_du_catalogue_est_compte(tmp_path):
    root = _tree(tmp_path, ["A/vu.ipynb", "A/invisible.ipynb"])
    cat = [{"path": "A/vu.ipynb"}]
    out = divergence(cat, {"A/vu.ipynb", "A/invisible.ipynb"}, root=root)
    assert out["missing"] == ["A/invisible.ipynb"]
    assert out["phantom_count"] == 0
    assert out["coverage_pct"] == 50.0


def test_les_deux_divergences_sont_independantes(tmp_path):
    """Elles cassent separement -- un catalogue peut etre complet ET fantome."""
    root = _tree(tmp_path, ["A/vu.ipynb", "A/invisible.ipynb"])
    cat = [{"path": "A/vu.ipynb"}, {"path": "A/disparu.ipynb"}]
    out = divergence(cat, {"A/vu.ipynb", "A/invisible.ipynb"}, root=root)
    assert out["phantom_count"] == 1
    assert out["missing_count"] == 1


# --- controle negatif : un catalogue exact ne declenche rien ------------------

def test_un_catalogue_exact_ne_declenche_rien(tmp_path):
    root = _tree(tmp_path, ["A/un.ipynb", "B/deux.ipynb"])
    cat = [{"path": "A/un.ipynb"}, {"path": "B/deux.ipynb"}]
    out = divergence(cat, {"A/un.ipynb", "B/deux.ipynb"}, root=root)
    assert out["phantom_count"] == 0
    assert out["missing_count"] == 0
    assert out["coverage_pct"] == 100.0


# --- le corpus scanne exclut ce qui n'en fait pas partie ----------------------

def test_les_worktrees_et_artefacts_sont_hors_corpus(tmp_path):
    root = _tree(tmp_path, [
        "A/vrai.ipynb",
        "A/run_output.ipynb",
        ".claude/worktrees/agent-x/A/copie.ipynb",
        "A/_archive/vieux.ipynb",
        "A/.ipynb_checkpoints/vrai-checkpoint.ipynb",
    ])
    assert notebooks_on_disk(root) == {"A/vrai.ipynb"}


# --- livraison : le run GARE est le signal que rien ne portait ----------------

class _Gh:
    """Remplace `gh` : rend les charges utiles que le vrai binaire rendrait."""

    def __init__(self, prs, runs):
        self.prs, self.runs = prs, runs

    def __call__(self, args):
        if args[0] == "pr":
            return json.dumps(self.prs)
        return json.dumps(self.runs)


def test_les_runs_action_required_sont_comptes_comme_gares(monkeypatch):
    """Un run `action_required` n'est ni vert ni rouge : il n'a jamais tourne.
    C'est exactement ce que le rollup de la PR ne sait pas dire."""
    monkeypatch.setattr(mod, "_gh", _Gh(
        prs=[{"number": 15942, "createdAt": "2026-09-13T08:33:00Z", "headRefOid": "abc",
              "updatedAt": "2026-09-21T09:24:00Z", "mergeStateStatus": "BLOCKED"}],
        runs=[{"databaseId": 1, "conclusion": "action_required",
               "headSha": "abc", "workflowName": "Secret Scan"},
              {"databaseId": 2, "conclusion": "action_required",
               "headSha": "abc", "workflowName": "Always-on guards"},
              {"databaseId": 3, "conclusion": "success",
               "headSha": "abc", "workflowName": "CodeQL"}],
    ))
    out = mod.delivery_state("o/r", now=dt.datetime(2026, 9, 21, tzinfo=dt.timezone.utc))
    assert out["pr"] == 15942
    assert out["parked_runs"] == 2
    assert out["parked_workflows"] == ["Always-on guards", "Secret Scan"]
    assert out["age_days"] == 7.6


def test_sans_pr_de_livraison_rien_n_est_reproche(monkeypatch):
    """Pas de PR ouverte = le cron n'a pas detecte de derive. Ce n'est pas un
    defaut, et le confondre avec un blocage sur-accuserait."""
    monkeypatch.setattr(mod, "_gh", _Gh(prs=[], runs=[]))
    out = mod.delivery_state("o/r")
    assert out == {"pr": None, "parked_runs": 0, "age_days": None}


def test_un_run_gare_sur_un_head_perime_n_est_pas_impute(monkeypatch):
    """Le controle qui empeche l'organe de rester rouge pour toujours.

    Une PR longue duree accumule les heads : chaque regeneration quotidienne
    en pousse un neuf, et les runs gares des anciens ne disparaissent pas.
    Les compter ferait un organe qui ne peut plus verdir une fois la panne
    reparee -- indiscernable d'un organe debranche. Seul le head courant
    porte les checks requis de la PR telle qu'elle est.
    """
    monkeypatch.setattr(mod, "_gh", _Gh(
        prs=[{"number": 15942, "createdAt": "2026-09-13T08:33:00Z", "headRefOid": "neuf",
              "updatedAt": "2026-09-21T09:24:00Z", "mergeStateStatus": "BLOCKED"}],
        runs=[{"databaseId": 1, "conclusion": "action_required",
               "headSha": "vieux", "workflowName": "Secret Scan"},
              {"databaseId": 2, "conclusion": "action_required",
               "headSha": "vieux2", "workflowName": "Always-on guards"},
              {"databaseId": 3, "conclusion": "success",
               "headSha": "neuf", "workflowName": "CodeQL"}],
    ))
    out = mod.delivery_state("o/r", now=dt.datetime(2026, 9, 21, tzinfo=dt.timezone.utc))
    assert out["parked_runs"] == 0, "un head perime ne bloque rien"
    assert out["parked_stale_heads"] == 2, "ils restent comptes, sans etre imputes"
