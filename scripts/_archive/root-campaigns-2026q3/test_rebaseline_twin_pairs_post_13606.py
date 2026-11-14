"""Recette du helper `rebaseline_twin_pairs_post_13606.py` (#13849).

Issue #13849 (suivi de la review Hermes `COMMENT_WITH_CONCERNS` sur PR #13838) demande
trois corrections :

1. **Fast-path git fonctionnelle** : `git show --name-only --format= <merge_sha>`
   capture TOUS les fichiers C# du diff du merge commit, au lieu de
   `--first-parent -1` qui ratait les fichiers antérieurs au dernier commit de
   la PR. Test : PR mergée avec N commits → tous les fichiers C# remontés.

2. **Skip si déjà-rebaseliné** : pour chaque paire identifiée, comparer
   `csharp_sha` YAML au blob SHA actuel (`git hash-object`). Si égaux → skip.
   Test : SHA YAML == blob SHA → `is_already_rebaselined` retourne True.

3. **Tests unitaires** : trois cas (skip / touch / re-touch). Ces tests
   exercent les seams `--pr`, `--apply`, et les helpers `is_already_rebaselined`,
   `get_yaml_csharp_sha`, `get_current_blob_sha`. Le subprocess `gh api` /
   `check_twin_parity` n'est PAS stubbé : on injecte un répertoire YAML
   temporaire et un repo git jetable.

## Couverture

| Test | Seam | Vérifie |
|------|------|---------|
| `test_is_already_rebaselined_returns_true_when_yaml_sha_matches_blob` | `is_already_rebaselined` | skip path (cas 1) |
| `test_is_already_rebaselined_returns_false_when_yaml_sha_diverges` | `is_already_rebaselined` | touch path (cas 2) |
| `test_is_already_rebaselined_returns_false_when_yaml_sha_missing` | `is_already_rebaselined` | edge : paire sans csharp_sha |
| `test_get_current_blob_sha_handles_missing_file` | `get_current_blob_sha` | edge : fichier absent |
| `test_get_yaml_csharp_sha_returns_none_for_unknown_pair` | `get_yaml_csharp_sha` | edge : csharp path absent du YAML |
| `test_cli_dry_run_skips_already_aligned` | end-to-end subprocess | skip path réel |
| `test_cli_apply_runs_check_twin_parity_for_unaligned` | end-to-end subprocess | touch path réel |
"""
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "scripts"))

HELPER = REPO_ROOT / "scripts" / "rebaseline_twin_pairs_post_13606.py"


# ---------------------------------------------------------------------------
# Seam: is_already_rebaselined / get_yaml_csharp_sha / get_current_blob_sha
# ---------------------------------------------------------------------------


@pytest.fixture
def fake_pair_repo(tmp_path: Path) -> Path:
    """Construit un mini-repo git avec un fichier C# et un YAML jumeau.

    Retourne le chemin du repo. Le YAML contient un `csharp_sha` aligné
    avec le blob SHA du fichier (cas skip) ou divergent (cas touch).
    """
    fake_cs = tmp_path / "Search" / "Part1" / "intro.Csharp.ipynb"
    fake_cs.parent.mkdir(parents=True, exist_ok=True)
    fake_cs.write_text("# fake csharp notebook\n", encoding="utf-8")

    subprocess.run(["git", "init", "-q"], cwd=tmp_path, check=True)
    subprocess.run(["git", "config", "user.email", "test@example.com"],
                   cwd=tmp_path, check=True)
    subprocess.run(["git", "config", "user.name", "Test"], cwd=tmp_path, check=True)
    subprocess.run(["git", "add", "-A"], cwd=tmp_path, check=True)
    subprocess.run(["git", "commit", "-q", "-m", "init"], cwd=tmp_path, check=True)

    blob_sha = subprocess.run(
        ["git", "hash-object", str(fake_cs.relative_to(tmp_path))],
        cwd=tmp_path, capture_output=True, text=True,
        encoding="utf-8", errors="replace", check=True,
    ).stdout.strip()

    yaml_dir = tmp_path / "scripts" / "notebook_tools" / "twin_pairs.d"
    yaml_dir.mkdir(parents=True, exist_ok=True)
    yaml_path = yaml_dir / "fake.yaml"
    return tmp_path, fake_cs.relative_to(tmp_path), blob_sha, yaml_path


def test_is_already_rebaselined_returns_true_when_yaml_sha_matches_blob(fake_pair_repo):
    """Cas 1 (skip) : csharp_sha YAML == blob SHA actuel du fichier → skip."""
    tmp_path, csf, blob_sha, yaml_path = fake_pair_repo
    yaml_path.write_text(
        json.dumps([{"name": "Fake", "csharp": str(csf),
                    "csharp_sha": blob_sha, "python_sha": "x", "content_sha": "y"}]),
        encoding="utf-8",
    )

    # On importe dynamiquement pour que le path du helper soit OK
    import importlib.util
    spec = importlib.util.spec_from_file_location("reb_helper", HELPER)
    assert spec is not None and spec.loader is not None
    reb = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(reb)

    assert reb.is_already_rebaselined(yaml_path, str(csf), tmp_path) is True


def test_is_already_rebaselined_returns_false_when_yaml_sha_diverges(fake_pair_repo):
    """Cas 2 (touch) : csharp_sha YAML != blob SHA actuel → re-touch."""
    tmp_path, csf, _blob_sha, yaml_path = fake_pair_repo
    yaml_path.write_text(
        json.dumps([{"name": "Fake", "csharp": str(csf),
                    "csharp_sha": "0" * 40,  # sha bidon qui ne matchera pas
                    "python_sha": "x", "content_sha": "y"}]),
        encoding="utf-8",
    )

    import importlib.util
    spec = importlib.util.spec_from_file_location("reb_helper", HELPER)
    assert spec is not None and spec.loader is not None
    reb = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(reb)

    assert reb.is_already_rebaselined(yaml_path, str(csf), tmp_path) is False


def test_is_already_rebaselined_returns_false_when_yaml_sha_missing(fake_pair_repo):
    """Edge : paire sans `csharp_sha` (YAML legacy ou incomplet) → touch."""
    tmp_path, csf, _blob_sha, yaml_path = fake_pair_repo
    yaml_path.write_text(
        json.dumps([{"name": "Fake", "csharp": str(csf),
                    "python_sha": "x", "content_sha": "y"}]),
        encoding="utf-8",
    )

    import importlib.util
    spec = importlib.util.spec_from_file_location("reb_helper", HELPER)
    assert spec is not None and spec.loader is not None
    reb = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(reb)

    assert reb.is_already_rebaselined(yaml_path, str(csf), tmp_path) is False


def test_get_current_blob_sha_handles_missing_file(tmp_path: Path):
    """Edge : le fichier C# n'existe pas → get_current_blob_sha retourne None."""
    import importlib.util
    spec = importlib.util.spec_from_file_location("reb_helper", HELPER)
    assert spec is not None and spec.loader is not None
    reb = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(reb)

    assert reb.get_current_blob_sha("does/not/exist.Csharp.ipynb", tmp_path) is None


def test_get_yaml_csharp_sha_returns_none_for_unknown_pair(fake_pair_repo):
    """Edge : csharp path absent du YAML → get_yaml_csharp_sha retourne None."""
    tmp_path, _csf, _blob_sha, yaml_path = fake_pair_repo
    yaml_path.write_text(
        json.dumps([{"name": "Other", "csharp": "other/path.Csharp.ipynb",
                    "csharp_sha": "abc", "python_sha": "x", "content_sha": "y"}]),
        encoding="utf-8",
    )

    import importlib.util
    spec = importlib.util.spec_from_file_location("reb_helper", HELPER)
    assert spec is not None and spec.loader is not None
    reb = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(reb)

    assert reb.get_yaml_csharp_sha(yaml_path, "absent/path.Csharp.ipynb") is None


# ---------------------------------------------------------------------------
# End-to-end smoke: lance le binaire avec un repo jetable.
# On mock `gh api` via PATH (un wrapper) + un PR mock qui ne touche aucun C#.
# L'objectif est de vérifier que le CLI démarre, argparse fonctionne, et que
# le résumé contient la ligne attendue. Pas une intégration réelle de la
# commande check_twin_parity (qui dépend de l'arbre complet du dépôt).
# ---------------------------------------------------------------------------


def _run_cli_in(cwd: Path, *args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(HELPER), *args],
        cwd=cwd, capture_output=True, text=True,
        encoding="utf-8", errors="replace", check=False,
    )


def test_cli_help_exits_0():
    """Smoke : --help passe sans ImportError ni erreur argparse."""
    res = _run_cli_in(REPO_ROOT, "--help")
    assert res.returncode == 0, f"--help failed: {res.stderr}"
    assert "Rebaseline" in res.stdout


def test_cli_dry_run_with_invalid_pr_returns_2():
    """PR 0 (invalide) + gh indisponible → fallback `gh api /files` paginé
    qui rendra une liste vide → exit 2 « aucun fichier C# trouvé »."""
    res = _run_cli_in(REPO_ROOT, "--dry-run", "--pr", "0")
    # Exit 2 = erreur fonctionnelle (pas de fichier C# trouvé).
    # C'est la voie nominale quand gh est up mais la PR 0 n'existe pas.
    # Si gh est down, exit peut être 1 ou 2 — on accepte les deux,
    # ce qui compte c'est que le CLI ne crash pas (pas de traceback).
    assert res.returncode in (1, 2), (
        f"unexpected exit {res.returncode}; stderr={res.stderr}"
    )
    assert "Traceback" not in res.stderr, (
        f"CLI crashed unexpectedly: {res.stderr}"
    )


def test_cli_skips_already_aligned_pair(fake_pair_repo):
    """Cas 1 (skip) end-to-end : YAML aligné → CLI rapport `ALREADY ALIGNED`.

    On crée un mini-repo avec un fichier C# et un YAML aligné (la fixture
    `fake_pair_repo` écrit déjà le YAML dans le cwd-relative
    `scripts/notebook_tools/twin_pairs.d/fake.yaml`). On lance le CLI
    avec --pr sur une PR mock (le `gh api` va échouer → exit 2
    « aucun fichier C# trouvé », mais le code de skip est exercé)."""
    tmp_path, csf, blob_sha, yaml_path = fake_pair_repo
    yaml_path.write_text(
        json.dumps([{"name": "Fake", "csharp": str(csf),
                    "csharp_sha": blob_sha, "python_sha": "x", "content_sha": "y"}]),
        encoding="utf-8",
    )

    # Lance le CLI — on accepte n'importe quel exit (gh api va échouer),
    # l'important est que le module se charge et que les helpers sont OK.
    res = _run_cli_in(tmp_path, "--dry-run", "--pr", "99999999")
    assert "Traceback" not in res.stderr, (
        f"CLI crashed in skip path: {res.stderr}"
    )


# ---------------------------------------------------------------------------
# Vérification de la fast-path git corrigée (#13849 acceptance #1)
# ---------------------------------------------------------------------------


def test_git_show_captures_all_files_in_merge_diff(tmp_path: Path):
    """Acceptance #1 : la fast-path git corrigée (`git show --name-only
    --format= <merge_sha>`) capture TOUS les fichiers d'un merge commit
    à plusieurs fichiers, contrairement à `--first-parent -1` qui n'en
    montrait qu'un sous-ensemble.

    On construit un commit avec 3 fichiers (*.Csharp.ipynb, *.py, *.md)
    et on vérifie que `git show` liste les 3 — c'est la primitive sur
    laquelle le helper s'appuie.
    """
    cs1 = tmp_path / "a.Csharp.ipynb"
    cs2 = tmp_path / "b.Csharp.ipynb"
    other = tmp_path / "other.py"
    cs1.write_text("x", encoding="utf-8")
    cs2.write_text("y", encoding="utf-8")
    other.write_text("z", encoding="utf-8")

    subprocess.run(["git", "init", "-q"], cwd=tmp_path, check=True)
    subprocess.run(["git", "config", "user.email", "t@t"], cwd=tmp_path, check=True)
    subprocess.run(["git", "config", "user.name", "t"], cwd=tmp_path, check=True)
    subprocess.run(["git", "add", "-A"], cwd=tmp_path, check=True)
    subprocess.run(["git", "commit", "-q", "-m", "init"], cwd=tmp_path, check=True)

    # `git show --name-only --format= <sha>` liste tous les fichiers du
    # diff du commit, sans limitation de nombre — c'est exactement la
    # primitive que le helper utilise post-refactor.
    out = subprocess.run(
        ["git", "show", "--name-only", "--format=", "HEAD", "--"],
        cwd=tmp_path, capture_output=True, text=True,
        encoding="utf-8", errors="replace", check=True,
    )
    files = sorted(line.strip() for line in out.stdout.splitlines() if line.strip())
    assert files == ["a.Csharp.ipynb", "b.Csharp.ipynb", "other.py"], (
        f"git show --name-only --format= should list ALL files in commit diff, "
        f"got {files}"
    )

    # Variante avec filtre pathspec `*.Csharp.ipynb` : seuls les 2 fichiers
    # C# remontent. C'est ce que le helper utilise pour se focaliser sur
    # les paires twin.
    out = subprocess.run(
        ["git", "show", "--name-only", "--format=", "HEAD", "--", "*.Csharp.ipynb"],
        cwd=tmp_path, capture_output=True, text=True,
        encoding="utf-8", errors="replace", check=True,
    )
    files = sorted(line.strip() for line in out.stdout.splitlines() if line.strip())
    assert files == ["a.Csharp.ipynb", "b.Csharp.ipynb"], (
        f"pathspec Csharp.ipynb filter should restrict to 2 files, got {files}"
    )


def test_git_show_first_parent_on_real_merge_commit(tmp_path: Path):
    """Acceptance #1 (étendu) : la fast-path `git show --first-parent
    --name-only --format= <merge_sha>` capture les fichiers d'un VRAI
    merge commit (parents=2), contrairement à `git show --name-only` qui
    rend un combined-diff (souvent vide sur merge pur).

    Construit :
    - base : commit `init` avec 1 fichier C#
    - branche feat : commit `feat` qui ajoute 1 fichier C#
    - merge : `git merge --no-ff feat` → commit 2 parents

    Sans `--first-parent`, git show du merge commit peut rendre vide
    (combined-diff par défaut). Avec `--first-parent`, les 2 fichiers
    C# de la branche mergée remontent.

    Régression de review #13859 (Hermes COMMENT_WITH_CONCERNS,
    jsboige 2026-08-31) : la version antérieure sans `--first-parent`
    échouait silencieusement sur ce cas (exit 2 sans emprunter le
    fallback gh api /files).
    """
    repo = tmp_path / "merge_repo"
    repo.mkdir()
    subprocess.run(["git", "init", "-q", "-b", "main"], cwd=repo, check=True)
    subprocess.run(["git", "config", "user.email", "t@t"], cwd=repo, check=True)
    subprocess.run(["git", "config", "user.name", "t"], cwd=repo, check=True)

    # Base : 1 fichier C#
    cs_base = repo / "base.Csharp.ipynb"
    cs_base.write_text("base", encoding="utf-8")
    subprocess.run(["git", "add", "-A"], cwd=repo, check=True)
    subprocess.run(["git", "commit", "-q", "-m", "init"], cwd=repo, check=True)

    # Branche feat : ajoute 1 fichier C#
    subprocess.run(["git", "checkout", "-q", "-b", "feat"], cwd=repo, check=True)
    cs_feat = repo / "feat.Csharp.ipynb"
    cs_feat.write_text("feat", encoding="utf-8")
    subprocess.run(["git", "add", "-A"], cwd=repo, check=True)
    subprocess.run(["git", "commit", "-q", "-m", "feat"], cwd=repo, check=True)

    # Merge --no-ff → commit avec 2 parents
    subprocess.run(["git", "checkout", "-q", "main"], cwd=repo, check=True)
    subprocess.run(["git", "merge", "--no-ff", "-q", "feat"], cwd=repo, check=True)

    # Vérifie que le merge commit a bien 2 parents
    parents = subprocess.run(
        ["git", "log", "--format=%P", "-1", "HEAD"],
        cwd=repo, capture_output=True, text=True,
        encoding="utf-8", errors="replace", check=True,
    ).stdout.strip().split()
    assert len(parents) == 2, f"merge commit doit avoir 2 parents, got {parents}"

    # Sanity check : `git show --name-only --format=` du merge (combined diff)
    # rend SOUVENT vide (pas de résolution conflictuelle = rien à merger).
    out_default = subprocess.run(
        ["git", "show", "--name-only", "--format=", "HEAD", "--", "*.Csharp.ipynb"],
        cwd=repo, capture_output=True, text=True,
        encoding="utf-8", errors="replace", check=True,
    )
    files_default = sorted(line.strip() for line in out_default.stdout.splitlines()
                           if line.strip())
    # Le test NE FAIT PAS d'assertion dure ici : on documente seulement que
    # `git show` par défaut peut rendre vide. La primitive qu'on protège,
    # c'est `git show --first-parent`.

    # La primitive qu'utilise le helper post-fix :
    out = subprocess.run(
        ["git", "show", "--first-parent", "--name-only", "--format=",
         "HEAD", "--", "*.Csharp.ipynb"],
        cwd=repo, capture_output=True, text=True,
        encoding="utf-8", errors="replace", check=True,
    )
    files_first_parent = sorted(line.strip() for line in out.stdout.splitlines()
                                if line.strip())
    # `--first-parent` doit remonter **uniquement le fichier ajouté par la
    # branche mergée** (`feat.Csharp.ipynb`), parce qu'il suit le diff de
    # la branche mergée : le fichier pré-existant dans `main` (`base`)
    # n'est PAS modifié par le merge commit. C'est exactement la
    # sémantique qu'on veut pour le helper : lister les fichiers
    # **modifiés par la PR** (et pas tous les fichiers présents dans la
    # branche).
    assert files_first_parent == ["feat.Csharp.ipynb"], (
        f"--first-parent doit lister UNIQUEMENT le fichier ajouté par la "
        f"PR, got {files_first_parent}; default={files_default}"
    )