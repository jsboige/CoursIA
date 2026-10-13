"""Tests de scripts/lean/lake_matrix_dispatch.py et
scripts/ci/check_lake_matrix_paths.py (#13751 pilote).

Charge les modules par importlib depuis le worktree (pattern maison des
tests de scripts), construit des manifestes/workflows de fixture MINIMAUX,
et verifie les trois contrats :

  1. selection par fnmatch (un chemin change -> un lake) ;
  2. self-cover GATE_SELF_COVER -> TOUS les lakes (lecon #8712) ;
  3. garde fail-CLOSED : chemin de manifeste absent de l'union ->
     exit 1 ; dispatcher historique encore present -> exit 1.

La garde est aussi testee CONTRE LES VRAIS FICHIERS du depot (manifeste +
workflow reels) : c'est le contrat qui protege le merge.
"""

from __future__ import annotations

import importlib.util
import json
import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
DISPATCH = REPO_ROOT / "scripts" / "lean" / "lake_matrix_dispatch.py"
GUARD = REPO_ROOT / "scripts" / "ci" / "check_lake_matrix_paths.py"


def _load(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


@pytest.fixture(scope="module")
def dispatch_mod():
    return _load(DISPATCH, "lake_matrix_dispatch_under_test")


@pytest.fixture(scope="module")
def manifest():
    return json.loads(
        (REPO_ROOT / "scripts" / "lean" / "ci_lakes.json")
        .read_text(encoding="utf-8"))


# --- Selection -----------------------------------------------------------


def test_one_changed_file_selects_its_lake(dispatch_mod, manifest):
    lakes = dispatch_mod.changed_lakes(
        ["MyIA.AI.Notebooks/Sudoku/sudoku_lean/src/Sudoku.lean"], manifest)
    assert [l["lake"] for l in lakes] == ["sudoku"]


def test_nested_lean_file_matches_glob(dispatch_mod, manifest):
    lakes = dispatch_mod.changed_lakes(
        ["MyIA.AI.Notebooks/GameTheory/minimax_lean/Nim/Core.lean"], manifest)
    assert [l["lake"] for l in lakes] == ["minimax"]


def test_lakefile_toml_triggers(dispatch_mod, manifest):
    lakes = dispatch_mod.changed_lakes(
        ["MyIA.AI.Notebooks/Search/discrepancy_lean/lakefile.toml"], manifest)
    assert [l["lake"] for l in lakes] == ["discrepancy"]


def test_two_lakes_selected_in_manifest_order(dispatch_mod, manifest):
    lakes = dispatch_mod.changed_lakes(
        ["MyIA.AI.Notebooks/Search/search_lean/lakefile.lean",
         "MyIA.AI.Notebooks/QuantConnect/kelly_lean/lean-toolchain"],
        manifest)
    # Ordre du manifeste (kelly avant search), pas l'ordre des fichiers.
    assert [l["lake"] for l in lakes] == ["kelly", "search"]


def test_unrelated_file_selects_nothing(dispatch_mod, manifest):
    assert dispatch_mod.changed_lakes(
        ["docs/reference/whatever.md"], manifest) == []


def test_self_cover_file_selects_all(dispatch_mod, manifest):
    lakes = dispatch_mod.changed_lakes(
        ["scripts/lean/ci_lakes.json"], manifest)
    assert [l["lake"] for l in lakes] == [l["lake"] for l in manifest["lakes"]]


def test_every_self_cover_entry_selects_all(dispatch_mod, manifest):
    for f in dispatch_mod.GATE_SELF_COVER:
        lakes = dispatch_mod.changed_lakes([f], manifest)
        assert len(lakes) == len(manifest["lakes"]), f(
            "self-cover {f} ne declenche pas tous les lakes")


def test_dedup_when_glob_and_literal_both_match(dispatch_mod, manifest):
    # Un commit qui touche lakefile.lean ET un .lean profond du meme lake :
    # le lake n'apparait qu'une fois.
    lakes = dispatch_mod.changed_lakes(
        ["MyIA.AI.Notebooks/Sudoku/sudoku_lean/lakefile.lean",
         "MyIA.AI.Notebooks/Sudoku/sudoku_lean/src/Deep.lean"],
        manifest)
    assert [l["lake"] for l in lakes] == ["sudoku"]


# --- CLI : format outputs-file --------------------------------------------


def test_outputs_file_format(tmp_path, manifest):
    changed = tmp_path / "changed.txt"
    changed.write_text(
        "MyIA.AI.Notebooks/GameTheory/assignment_lean/A.lean\n", encoding="utf-8")
    out = tmp_path / "gh_outputs.txt"
    rc = subprocess.call(
        [sys.executable, str(DISPATCH),
         "--changed-file", str(changed), "--outputs-file", str(out)])
    assert rc == 0
    text = out.read_text(encoding="utf-8")
    lines = dict(l.split("=", 1) for l in text.strip().splitlines())
    assert lines["any"] == "true"
    payload = json.loads(lines["lake-set"])
    assert [e["lake"] for e in payload["include"]] == ["assignment"]
    # Chaque entree porte les cles que la matrice consomme.
    entry = payload["include"][0]
    for k in ("lake", "project-path", "display-name",
              "sorry-baseline", "sorry-filter-mode"):
        assert k in entry, f"cle matrice manquante: {k}"


def test_outputs_file_empty_intersection_any_false(tmp_path):
    changed = tmp_path / "changed.txt"
    changed.write_text("README.md\n", encoding="utf-8")
    out = tmp_path / "gh_outputs.txt"
    subprocess.call([sys.executable, str(DISPATCH),
                     "--changed-file", str(changed),
                     "--outputs-file", str(out)])
    lines = dict(l.split("=", 1)
                 for l in out.read_text(encoding="utf-8").strip().splitlines())
    assert lines["any"] == "false"
    assert json.loads(lines["lake-set"])["include"] == []


# --- Garde : fail-CLOSED ---------------------------------------------------


def _write_workflow(path: Path, push_paths: list[str], pr_paths: list[str]):
    doc = {
        "on": {
            "push": {"branches": ["main"], "paths": push_paths},
            "pull_request": {"branches": ["main"],
                             "types": ["opened", "synchronize"],
                             "paths": pr_paths},
        },
        "jobs": {"changes": {"runs-on": "ubuntu-latest"}},
    }
    import yaml
    path.write_text(yaml.safe_dump(doc, sort_keys=False), encoding="utf-8")
    return path


def _materialize_gate_files(root: Path, paths: list[str]):
    """Le garde verifie l'existence sur disque des self-covers ``.github/`` et
    ``scripts/`` references par l'union. Depuis #17374 le manifeste lui-meme
    porte de tels chemins (gate certifie de gametheory) : une fixture dont
    l'union derive du manifeste doit les materialiser, sinon le rouge vient
    du mauvais contrat."""
    for p in paths:
        if p.startswith((".github/", "scripts/")):
            f = root / p
            f.parent.mkdir(parents=True, exist_ok=True)
            f.write_text("", encoding="utf-8")


def test_guard_green_on_repo_files():
    rc = subprocess.call([sys.executable, str(GUARD)])
    assert rc == 0, "le garde doit etre vert sur l'etat livre du depot"


def test_guard_red_when_manifest_path_missing_from_push(tmp_path, manifest):
    wf = _write_workflow(
        tmp_path / "wf.yml",
        push_paths=[],  # push vide -> chaque chemin manque
        pr_paths=[p for l in manifest["lakes"] for p in l["paths"]],
    )
    rc = subprocess.call(
        [sys.executable, str(GUARD),
         "--manifest", str(REPO_ROOT / "scripts" / "lean" / "ci_lakes.json"),
         "--workflow", str(wf), "--repo-root", str(REPO_ROOT)])
    assert rc == 1


def test_guard_red_when_only_pr_block_covers(tmp_path, manifest):
    """Le push couvre, le pull_request oublie un lake -> fail-CLOSED."""
    all_paths = [p for l in manifest["lakes"] for p in l["paths"]]
    pr_paths = [p for p in all_paths if not p.startswith(
        "MyIA.AI.Notebooks/Sudoku/")]
    wf = _write_workflow(tmp_path / "wf.yml", all_paths, pr_paths)
    rc = subprocess.call(
        [sys.executable, str(GUARD),
         "--manifest", str(REPO_ROOT / "scripts" / "lean" / "ci_lakes.json"),
         "--workflow", str(wf), "--repo-root", str(REPO_ROOT)])
    assert rc == 1


def test_guard_red_when_legacy_dispatcher_still_present(tmp_path, manifest):
    all_paths = [p for l in manifest["lakes"] for p in l["paths"]]
    _materialize_gate_files(tmp_path, all_paths)
    wf = _write_workflow(tmp_path / "wf.yml", all_paths, all_paths)
    legacy = tmp_path / ".github" / "workflows" / "lean-sudoku.yml"
    legacy.parent.mkdir(parents=True)
    legacy.write_text("name: legacy\n", encoding="utf-8")
    rc = subprocess.call(
        [sys.executable, str(GUARD),
         "--manifest", str(REPO_ROOT / "scripts" / "lean" / "ci_lakes.json"),
         "--workflow", str(wf), "--repo-root", str(tmp_path)])
    assert rc == 1


def test_guard_red_on_path_overlap_with_foreign_filename(tmp_path, manifest):
    """Lecon #17336 : le check par nom rate les wrappers dont le nom ne
    derive PAS du lake (lean-serre.yml couvrait serre100_lean). Le critere
    effectif = recroisement des on.paths, independant du nom de fichier."""
    all_paths = [p for l in manifest["lakes"] for p in l["paths"]]
    _materialize_gate_files(tmp_path, all_paths)
    wf = _write_workflow(tmp_path / "wf.yml", all_paths, all_paths)
    serre_path = next(p for l in manifest["lakes"]
                      if l["lake"] == "serre100" for p in l["paths"])
    # Nom de fichier volontairement ETANGER au lake : "lean-serre.yml" != serre100
    wrapper = tmp_path / ".github" / "workflows" / "lean-serre.yml"
    wrapper.parent.mkdir(parents=True, exist_ok=True)
    wrapper.write_text(
        "name: Lean CI (serre100_lean)\n"
        "on:\n"
        "  push:\n"
        f"    paths: ['{serre_path}']\n"
        "  pull_request:\n"
        f"    paths: ['{serre_path}']\n",
        encoding="utf-8")
    rc = subprocess.call(
        [sys.executable, str(GUARD),
         "--manifest", str(REPO_ROOT / "scripts" / "lean" / "ci_lakes.json"),
         "--workflow", str(wf), "--repo-root", str(tmp_path)])
    assert rc == 1


def test_guard_red_on_tranched_pair_since_17374(tmp_path, manifest):
    """#17374 a tranche les deux paires historiques : l'allowlist est VIDE et
    le garde est strict -- le recroisement qui etait tolere (wrapper
    asymmetric x gamedefsext) rougit maintenant."""
    all_paths = [p for l in manifest["lakes"] for p in l["paths"]]
    _materialize_gate_files(tmp_path, all_paths)
    wf = _write_workflow(tmp_path / "wf.yml", all_paths, all_paths)
    gamedefsext = next(l for l in manifest["lakes"]
                       if l["lake"] == "gamedefsext")
    wrapper = tmp_path / ".github" / "workflows" / "lean-asymmetric-information.yml"
    wrapper.parent.mkdir(parents=True, exist_ok=True)
    wrapper.write_text(
        "name: Lean Asymmetric Information CI\n"
        "on:\n"
        "  push:\n"
        f"    paths: ['{gamedefsext['paths'][0]}']\n"
        "  pull_request:\n"
        f"    paths: ['{gamedefsext['paths'][0]}']\n",
        encoding="utf-8")
    rc = subprocess.call(
        [sys.executable, str(GUARD),
         "--manifest", str(REPO_ROOT / "scripts" / "lean" / "ci_lakes.json"),
         "--workflow", str(wf), "--repo-root", str(tmp_path)])
    assert rc == 1


def test_guard_allowlist_mechanism_silences_a_declared_pair(
        tmp_path, manifest, monkeypatch):
    """L'allowlist est vide depuis #17374, mais le MECANISME demeure : une
    paire declaree (dette temporaire citee par son issue) ne rougit pas le
    garde. La constante est patchee in-process -- sur disque elle reste vide
    (pinned par test_axiom_matrix_wiring)."""
    all_paths = [p for l in manifest["lakes"] for p in l["paths"]]
    _materialize_gate_files(tmp_path, all_paths)
    wf = _write_workflow(tmp_path / "wf.yml", all_paths, all_paths)
    gamedefsext = next(l for l in manifest["lakes"]
                       if l["lake"] == "gamedefsext")
    wrapper = tmp_path / ".github" / "workflows" / "lean-asymmetric-information.yml"
    wrapper.parent.mkdir(parents=True, exist_ok=True)
    wrapper.write_text(
        "name: Lean Asymmetric Information CI\n"
        "on:\n"
        "  push:\n"
        f"    paths: ['{gamedefsext['paths'][0]}']\n"
        "  pull_request:\n"
        f"    paths: ['{gamedefsext['paths'][0]}']\n",
        encoding="utf-8")
    guard = _load(GUARD, "check_lake_matrix_paths_under_test")
    monkeypatch.setattr(
        guard, "KNOWN_DOUBLE_TRIGGERS",
        {("lean-asymmetric-information.yml", "gamedefsext")})
    rc = guard.main([
        "--manifest", str(REPO_ROOT / "scripts" / "lean" / "ci_lakes.json"),
        "--workflow", str(wf), "--repo-root", str(tmp_path)])
    assert rc == 0


def test_guard_green_on_full_coverage_with_fake_repo(tmp_path, manifest):
    all_paths = [p for l in manifest["lakes"] for p in l["paths"]]
    _materialize_gate_files(tmp_path, all_paths)
    wf = _write_workflow(tmp_path / "wf.yml", all_paths, all_paths)
    # Pas de dispatcher legacy ; les self-covers .github/scripts references
    # par l'union (le manifeste en porte depuis #17374) sont materialises
    # par la fixture : vert.
    rc = subprocess.call(
        [sys.executable, str(GUARD),
         "--manifest", str(REPO_ROOT / "scripts" / "lean" / "ci_lakes.json"),
         "--workflow", str(wf), "--repo-root", str(tmp_path)])
    assert rc == 0


def test_guard_red_on_dead_self_cover_path(tmp_path, manifest):
    all_paths = [p for l in manifest["lakes"] for p in l["paths"]]
    wf = _write_workflow(
        tmp_path / "wf.yml",
        all_paths + ["scripts/lean/does_not_exist.py"],
        all_paths + ["scripts/lean/does_not_exist.py"],
    )
    rc = subprocess.call(
        [sys.executable, str(GUARD),
         "--manifest", str(REPO_ROOT / "scripts" / "lean" / "ci_lakes.json"),
         "--workflow", str(wf), "--repo-root", str(REPO_ROOT)])
    assert rc == 1
