"""Tests du perimetre local de la voie rapide (#27012, point 2).

Le module `scripts/ci/fast_lane_scope.py` pilote `fast_lane.main` sans
modifier `fast_lane.py`. Ces tests pinnent trois garanties :

  1. la selection reste CELLE du moteur (une garde declenchee par un chemin
     demande est dans le plan, une garde declenchee par un autre chemin
     n'y est pas) ;
  2. rien n'est publie (le moteur tourne en `--dry-run`, `emit_check_run` est
     neutralise pendant la passe) ;
  3. une garde executee deux fois est signalee (le defaut mesure dans la
     chaine du moteur).
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import fast_lane  # noqa: E402
import fast_lane_scope  # noqa: E402

# Deux chemins synthetiques : l'un declenche le garde « testpaths vs CI
# coverage » (il declare `scripts/check_testpaths_coverage.py`), l'autre
# declenche les gardes de carnets.
SYNTHETIC = [
    "scripts/check_testpaths_coverage.py",
    "MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/p5_tts.py",
]


@pytest.fixture
def engine(monkeypatch, tmp_path):
    """Moteur factice : la liste des fichiers modifies est synthetique."""
    monkeypatch.setenv("RUNNER_TEMP", str(tmp_path))
    monkeypatch.setattr(fast_lane, "changed_files",
                        lambda _base: list(SYNTHETIC))
    return fast_lane


@pytest.fixture
def no_exec(monkeypatch):
    """Aucune garde reelle ne s'execute : les moteurs d'execution sont simules.

    Sans cette fixture, un test en mode passe lancerait les gardes sans
    `paths` (toujours dans le perimetre) -- mesure du 28/11 : 104 s pour la
    classe, contre quelques secondes avec la simulation.
    """
    calls: list[tuple[str, ...]] = []

    def fake_argv(argv, ctx):
        calls.append(tuple(argv))
        return 0, "simule"

    monkeypatch.setattr(fast_lane, "run_argv", fake_argv)
    monkeypatch.setattr(fast_lane, "run_iter",
                        lambda argv, paths, ctx, warn_rc=(),
                        fail_on_all_warn=False: (0, "simule"))
    return calls


def test_restrict_changed_garde_un_chemin_exact():
    changed = ["scripts/check_testpaths_coverage.py", "a.ipynb"]
    kept = fast_lane_scope.restrict_changed(
        changed, ["scripts/check_testpaths_coverage.py"])
    assert kept == ["scripts/check_testpaths_coverage.py"]


def test_restrict_changed_accepte_un_motif():
    changed = ["MyIA.AI.Notebooks/GenAI/a.ipynb", "scripts/x.py"]
    kept = fast_lane_scope.restrict_changed(changed, ["**/*.ipynb"])
    assert kept == ["MyIA.AI.Notebooks/GenAI/a.ipynb"]


def test_restrict_changed_sans_motif_ne_change_rien():
    changed = ["a.ipynb", "b.py"]
    assert fast_lane_scope.restrict_changed(changed, []) == changed


def test_plan_ne_selectionne_que_les_gardes_du_perimetre(engine):
    """La selection est celle du moteur, restreinte aux chemins demandes."""
    report = fast_lane_scope.scoped_pass(
        ["scripts/check_testpaths_coverage.py"], "origin/main", execute=False)
    names = [g["name"] for g in report["guards_evaluated"]]
    assert "testpaths vs CI coverage" in names
    # Une garde de carnets n'est pas declenchee par un fichier de scripts.
    assert "cell-source-parses" not in names
    assert report["files_kept"] == 1
    assert report["files_dropped"] == 1


def test_plan_ne_publie_rien(engine, no_exec, monkeypatch):
    """Contrôle positif : aucun check-run n'est ecrit, meme en mode passe."""
    published: list[tuple] = []
    monkeypatch.setattr(fast_lane, "emit_check_run",
                        lambda *a, **k: published.append(a) or True)
    fast_lane_scope.scoped_pass(["scripts/check_testpaths_coverage.py"],
                                "origin/main", execute=True)
    assert published == [], "le perimetre local ne doit publier aucun verdict"


def test_la_passe_execute_les_gardes_du_perimetre(engine, no_exec):
    """En mode passe, les gardes selectionnees s'executent (ici : simulees)."""
    report = fast_lane_scope.scoped_pass(
        ["scripts/check_testpaths_coverage.py"], "origin/main", execute=True)
    names = [g["name"] for g in report["guards_evaluated"]]
    assert "testpaths vs CI coverage" in names
    assert all(rc == 0 for rc in (g["rc"] for g in report["guards_evaluated"]))
    # Chaque execution simulee est chronometree et attribuee a sa garde.
    assert "testpaths vs CI coverage" in report["durations_s"]


def test_le_moteur_tourne_toujours_en_dry_run(engine, no_exec, monkeypatch):
    """Le moteur ne doit jamais etre appele sans `--dry-run`."""
    captured: list[list[str]] = []
    real_main = fast_lane.main

    def spy(argv):
        captured.append(list(argv))
        return real_main(argv)

    monkeypatch.setattr(fast_lane, "main", spy)
    fast_lane_scope.scoped_pass(["scripts/check_testpaths_coverage.py"],
                                "origin/main", execute=True)
    assert captured and "--dry-run" in captured[0]


def test_emit_check_run_est_retabli_apres_la_passe(engine, no_exec, monkeypatch):
    """La couture du moteur est rendue a l'identique apres le passage."""
    before = fast_lane.emit_check_run
    fast_lane_scope.scoped_pass(["scripts/check_testpaths_coverage.py"],
                                "origin/main", execute=True)
    assert fast_lane.emit_check_run is before


def test_aucun_fichier_retenu_echoue_ferme(engine):
    """Un motif qui ne selectionne rien ne doit pas rendre un plan vide vert."""
    with pytest.raises(SystemExit) as exc:
        fast_lane_scope.scoped_pass(["jamais/vu.py"], "origin/main",
                                    execute=False)
    assert "aucun fichier modifie" in str(exc.value)


def test_parse_engine_output_reconnait_les_lignes_du_moteur():
    text = "\n".join([
        "[fast-lane] phase 1 garde A : exit 0",
        "[fast-lane] phase 1 garde B (iter sur 3 fichier(s)) : exit 1",
        "[fast-lane] phase 1 (HEAD) garde C : scan capture",
        "[fast-lane] hors perimetre (filtre paths) : garde D",
    ])
    evaluated, out = fast_lane_scope.parse_engine_output(text)
    assert [n for n, _ in evaluated] == ["garde A", "garde B", "garde C"]
    assert [rc for _, rc in evaluated] == [0, 1, None]
    assert out == ["garde D"]


def test_une_garde_executee_deux_fois_est_signalee():
    text = "\n".join([
        "[fast-lane] phase 1 garde A : exit 0",
        "[fast-lane] phase 1 garde A : exit 0",
        "[fast-lane] phase 1 garde B : exit 0",
    ])
    evaluated, _out = fast_lane_scope.parse_engine_output(text)
    counts: dict[str, int] = {}
    for name, _rc in evaluated:
        counts[name] = counts.get(name, 0) + 1
    assert [n for n, c in counts.items() if c > 1] == ["garde A"]


@pytest.mark.xfail(strict=False, reason=(
    "Defaut mesure le 28/11 : TRANCHE52 est chainee DEUX fois dans "
    "`fast_lane.main` (l.924 et l.948) -- la garde « Prose-numbers vs outputs "
    "ratchet » s'execute donc deux fois par passe (45,7 s puis 41,2 s sur la "
    "branche fix/23384-canon-3-13-sk8-mcp). La correction est la suppression "
    "d'une ligne dans `fast_lane.py`, fichier occupe par les PRs ouvertes "
    "#28769 et #28126 : elle attend que ces PRs soient passees. Le test "
    "devient vert quand la ligne dupliquee a disparu."))
def test_la_chaine_du_moteur_ne_liste_pas_de_garde_en_double(engine):
    """La chaine du moteur ne doit lister aucune garde deux fois."""
    from pathlib import Path

    source = Path(engine.__file__).read_text(encoding="utf-8")
    occurrences = [
        line.strip() for line in source.splitlines()
        if "TRANCHE52" in line and "+" in line and "import" not in line
    ]
    assert len(occurrences) == 1, (
        "TRANCHE52 doit apparaitre UNE seule fois dans la chaine des gardes "
        f"(trouve {len(occurrences)} : {occurrences})")
