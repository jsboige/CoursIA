"""Contrat du workflow markdown-claims-output-advisory (#22564 D1/D2).

Le workflow advisory de prose/output construit son lot de carnets par
`git diff --name-only --diff-filter=... $BASE HEAD -- '*.ipynb'`. Deux
defauts y etaient mesures (#22564) :

- D1 : le filtre `--diff-filter=MR` exclut les carnets AJOUTES -- une PR
  qui n'ouvre que des carnets neufs scanne un lot vide.
- D2 : le lot vide empruntait `exit=0`, le meme verdict que « scanne, rien
  trouve » -- le commentaire sticky vert ne distinguait pas « rien regarde »
  de « regarde, propre ».

Ce test ne teste pas du code Python isole : il extrait la commande reelle
DU WORKFLOW parse et la REJOUE sur un depot temporaire ou un carnet vient
d'etre ajoute (meme philosophie que les contract tests de workflows, p. ex.
`test_action_cache_seed_guard.py` : on mesure ce qui sera execute, pas une
copie du geste). Un retour a `--diff-filter=MR` fait disparaitre le carnet
ajoute du lot -- et rougit le test.
"""

from __future__ import annotations

import re
import subprocess
from pathlib import Path

import yaml

REPO_ROOT = Path(__file__).resolve().parents[2]
WORKFLOW = REPO_ROOT / ".github" / "workflows" / "markdown-claims-output-advisory.yml"

DETECTOR_IDS = ("run", "stale", "mislabel")

# La commande exacte presente dans les trois blocs detecteur : elle est
# extraite du workflow (pas recopiee) pour que le test mesure le workflow.
DIFF_CMD_RE = re.compile(
    r"git diff --name-only --diff-filter=(?P<filter>\S+) (?P<renames>\S+) "
    r'"\$BASE" HEAD -- \'\*\.ipynb\''
)


def _load_workflow() -> dict:
    return yaml.safe_load(WORKFLOW.read_text(encoding="utf-8"))


def _detector_run_script(job: dict, step_id: str) -> str:
    for step in job["steps"]:
        if step.get("id") == step_id:
            return step["run"]
    raise AssertionError(f"step id={step_id!r} absent du workflow")


def _make_repo_with_added_notebook(tmp_path: Path) -> tuple[Path, str]:
    """Deport temporaire : un commit de base, puis l'ajout d'un carnet."""
    repo = tmp_path / "repo"
    repo.mkdir()

    def git(*args: str) -> str:
        out = subprocess.run(
            ["git", "-C", str(repo), *args],
            check=True,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
        )
        return out.stdout

    git("init", "-q", "-b", "main")
    git("config", "user.email", "contract-test@example.invalid")
    git("config", "user.name", "Contract Test")
    git("config", "core.autocrlf", "false")
    (repo / "README.md").write_text("base\n", encoding="utf-8")
    git("add", "-A")
    git("commit", "-q", "-m", "base")
    base = git("rev-parse", "HEAD").strip()

    series = repo / "MyIA.AI.Notebooks" / "Search"
    series.mkdir(parents=True)
    (series / "New-Series.ipynb").write_text("{}", encoding="utf-8")
    git("add", "-A")
    git("commit", "-q", "-m", "add notebook")
    return repo, base


def _replay_lot(repo: Path, base: str, diff_filter: str, renames: str) -> list[str]:
    """Rejoue la commande du workflow (meme forme, memes arguments)."""
    out = subprocess.run(
        [
            "git", "-C", str(repo), "diff", "--name-only",
            f"--diff-filter={diff_filter}", renames,
            base, "HEAD", "--", "*.ipynb",
        ],
        check=True,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    return [line for line in out.stdout.splitlines() if line.strip()]


def test_workflow_parses_and_exposes_the_three_detectors() -> None:
    job = _load_workflow()["jobs"]["claims-output-advisory"]
    for step_id in DETECTOR_IDS:
        script = _detector_run_script(job, step_id)
        assert DIFF_CMD_RE.search(script), (
            f"{step_id}: la commande git diff du lot a change de forme -- "
            "maj de DIFF_CMD_RE requise"
        )


def test_added_notebook_reaches_the_scan_lot(tmp_path: Path) -> None:
    """D1 : un carnet AJOUTE doit figurer dans le lot de chacun des trois
    detecteurs. Controle negatif : avec l'ancien filtre MR il en disparaît --
    c'est le defaut mesure, le test est fait pour le voir."""
    job = _load_workflow()["jobs"]["claims-output-advisory"]
    repo, base = _make_repo_with_added_notebook(tmp_path)
    expected = "MyIA.AI.Notebooks/Search/New-Series.ipynb"
    for step_id in DETECTOR_IDS:
        match = DIFF_CMD_RE.search(_detector_run_script(job, step_id))
        assert match, f"{step_id}: commande git diff introuvable"
        lot = _replay_lot(repo, base, match["filter"], match["renames"])
        assert expected in lot, (
            f"{step_id}: le carnet AJOUTE manque du lot (filtre "
            f"{match['filter']}) -- regression D1"
        )
        assert expected not in _replay_lot(repo, base, "MR", match["renames"])


def test_empty_lot_is_none_not_a_clean_zero() -> None:
    """D2 : le lot vide rend exit=none, jamais exit=0."""
    job = _load_workflow()["jobs"]["claims-output-advisory"]
    for step_id in DETECTOR_IDS:
        script = _detector_run_script(job, step_id)
        assert 'echo "exit=none" >> "$GITHUB_OUTPUT"' in script
        assert 'echo "exit=0" >> "$GITHUB_OUTPUT"' not in script, (
            f"{step_id}: le lot vide repasse a exit=0 -- regression D2"
        )


def test_sticky_comments_distinguish_none_from_clean() -> None:
    """D2 : chaque commentaire sticky porte une branche 'none' distincte du
    vert '0' (⚪ rien a scanner vs ✅ scanne et propre)."""
    job = _load_workflow()["jobs"]["claims-output-advisory"]
    for step in job["steps"]:
        message = step.get("with", {}).get("message")
        if not isinstance(message, str):
            continue
        for step_id in DETECTOR_IDS:
            if f"steps.{step_id}.outputs.exit" not in message:
                continue
            assert f"steps.{step_id}.outputs.exit == 'none'" in message, (
                f"sticky de {step_id}: la branche 'none' a disparu"
            )
            assert "⚪" in message
