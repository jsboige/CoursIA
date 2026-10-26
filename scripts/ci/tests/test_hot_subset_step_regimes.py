"""Regimes du step `hot_subset` de `always-on-guards.yml` (#22435).

Le code retour de pytest n'est pas un booleen : `1` dit que des tests ont
echoue -- le seul regime qui dise quelque chose du contenu --, tandis que
`2` (execution interrompue : erreur de collecte ou `ImportError`), `3`
(erreur interne), `4` (usage) et `5` (aucun test collecte) disent que la
mesure n'a pas eu lieu.

Le step imprimait le verdict de contenu `SRC_DRIFT` sur tout RC non nul. Une
PR verte sur son contenu portait donc un rouge qui affirmait une derive de
traduction jamais mesuree : #22130 (tete `402871d9cc`) et #22264 (tete
`07885aafc8`), `2 passed` localement sur les deux tetes.

Ce test execute le **vrai** bloc `run:` du workflow, avec des `python`,
`pip` et `git` factices : c'est le shell du workflow qui est mesure, pas une
reecriture de sa logique dans le test.

Apres le merge de #22472 sur `main`, l'implementation porteuse des regimes
est celle de ce cote (main) : vocabulaire `MESURE-VERT` / `VERDICT-CONTENU`
/ `NON-MESURE` / `NON-MESURE-ATTRIBUABLE` exporte vers `outputs.regime`,
double lecture du diff (`origin/BASE` puis `PR_BASE_SHA`), perimetre
d'attribution `ORGANE_RE` sous `--no-renames`. La resolution du conflit de
#22436 a pris le cote de main pour le workflow (subsomption : l'intention
#22435 y est reprise et etendue) ; ce fichier en epingle desormais les
attendus SUR cette implementation, pas sur la version intervenue de la
branche -- le vocabulaire asserted ci-dessous est celui de #22472.
"""

from __future__ import annotations

import os
import pathlib
import shutil
import stat
import subprocess

import pytest

yaml = pytest.importorskip("yaml")

REPO = pathlib.Path(__file__).resolve().parents[3]
WORKFLOW = REPO / ".github" / "workflows" / "always-on-guards.yml"
VERDICT_LINE = "::error::Hot-subset ratchet : regime VERDICT DE CONTENU"


def _hot_subset_run_block() -> str:
    doc = yaml.safe_load(WORKFLOW.read_text(encoding="utf-8"))
    # Nit NanoClaw (rev. #22436) : `next(iter(doc["jobs"].values()))` casse en
    # rouge trompeur si un job est un jour prefixe au fichier. On cherche le
    # job qui PORTE le step, pas le premier du fichier.
    for job in doc["jobs"].values():
        step = next((s for s in job.get("steps", []) if s.get("id") == "hot_subset"), None)
        if step is not None:
            return step["run"]
    raise AssertionError("step hot_subset introuvable dans always-on-guards.yml")


def _shim(directory: pathlib.Path, name: str, body: str) -> None:
    path = directory / name
    path.write_text("#!/bin/sh\n" + body + "\n", encoding="utf-8", newline="\n")
    path.chmod(path.stat().st_mode | stat.S_IEXEC)


# Shim git : journalise ses arguments (reserve 2 NanoClaw -- le test doit
# pouvoir voir CE QUE la commande d'attribution lit), echoue sur commande si
# FAKE_GIT_RC=1, echoue sur la seule lecture par origin/ si
# FAKE_GIT_ORIGIN_FAIL=1 (pour piner le chemin de repli PR_BASE_SHA), et
# sinon imprime les fichiers de la PR.
_GIT_SHIM = r'''
printf '%s\n' "$*" >> "$GIT_ARGS_LOG"
if [ "${FAKE_GIT_RC:-}" = "1" ]; then exit 1; fi
if [ "${FAKE_GIT_ORIGIN_FAIL:-}" = "1" ] && printf '%s' "$*" | grep -q 'origin/'; then
  exit 1
fi
printf '%s\n' "$FAKE_FILES"
'''


def _run_step(
    tmp_path: pathlib.Path,
    rc: str,
    files: str,
    extra_env: dict[str, str] | None = None,
) -> subprocess.CompletedProcess:
    bin_dir = tmp_path / "bin"
    bin_dir.mkdir()
    _shim(bin_dir, "python", 'exit "$FAKE_RC"')
    _shim(bin_dir, "pip", "exit 0")
    _shim(bin_dir, "git", _GIT_SHIM)
    script = tmp_path / "step.sh"
    script.write_text(_hot_subset_run_block(), encoding="utf-8", newline="\n")
    env = dict(os.environ)
    env["PATH"] = str(bin_dir) + os.pathsep + env["PATH"]
    env["FAKE_RC"] = rc
    env["FAKE_FILES"] = files
    env["GIT_ARGS_LOG"] = str(tmp_path / "git-args.log")
    env.update(extra_env or {})
    return subprocess.run(
        ["bash", str(script)],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        env=env,
    )


# (id, rc pytest, fichiers touches par la PR, exit attendu, texte attendu)
CASES = [
    ("vert", "0", "", 0, None),
    ("contenu", "1", "", 1, VERDICT_LINE),
    ("collecte-hors-organe", "2", "docs/README.md", 0, "regime NON MESURE"),
    ("collecte-notebook-hors-organe", "5", "MyIA.AI.Notebooks/x.ipynb", 0, "regime NON MESURE"),
    ("interne-hors-organe", "3", "", 0, "regime NON MESURE"),
    ("collecte-touche-organe", "2", "scripts/translation/foo.py", 1, "attribuable"),
    ("collecte-touche-outils", "2", "scripts/notebook_tools/bar.py", 1, "attribuable"),
    # Reserve 2 NanoClaw : les deux lectures du diff peuvent ECHOUER -- le
    # regime INDECISE doit se dire, pas retomber en "hors organe" (reserve 1).
    ("git-indisponible", "2", "scripts/translation/foo.py", 0, "ATTRIBUTION INDECISE"),
    # Chemin de repli #22472 : origin/BASE illisible, base de l'evenement
    # lisible -> l'attribution s'applique quand meme.
    ("fallback-pr-base-sha", "2", "scripts/translation/foo.py", 1, "diff lu par PR_BASE_SHA"),
]

# Environnement supplementaire par cas (les FAIL_* pilotent le shim git).
EXTRA_ENV: dict[str, dict[str, str]] = {
    "git-indisponible": {"FAKE_GIT_RC": "1"},
    "fallback-pr-base-sha": {"FAKE_GIT_ORIGIN_FAIL": "1", "PR_BASE_SHA": "f" * 40},
}


@pytest.mark.skipif(shutil.which("bash") is None, reason="shell bash requis pour executer le step")
@pytest.mark.parametrize("case_id,rc,files,want_rc,want_text", CASES, ids=[c[0] for c in CASES])
def test_hot_subset_regime(tmp_path, case_id, rc, files, want_rc, want_text):
    proc = _run_step(tmp_path, rc, files, EXTRA_ENV.get(case_id))
    output = proc.stdout + proc.stderr
    assert proc.returncode == want_rc, output
    if want_text is not None:
        assert want_text in output, output
    if rc != "1":
        # garde-fou : la LIGNE DE VERDICT ne doit jamais sortir hors du rc 1.
        # On cherche la ligne emise, pas le token nu -- l'avertissement doit
        # pouvoir nommer SRC_DRIFT pour dire qu'il ne l'est pas.
        assert VERDICT_LINE not in output, output


@pytest.mark.skipif(shutil.which("bash") is None, reason="shell bash requis pour executer le step")
def test_hot_subset_attribution_lit_une_plage_reelle(tmp_path):
    """Reserve 2 NanoClaw : l'attribution doit lire une PLAGE, pas un point.

    Un shim git qui repond quoi qu'on lui demande ne peut pas distinguer
    ``origin/main...HEAD`` (plage) de ``HEAD...HEAD`` (point, toujours vide).
    Le journal d'arguments du shim epingle la plage : si un futur changement
    degenere la commande d'attribution, ce test devient rouge alors que les
    cas de regime resteraient verts.
    """
    proc = _run_step(tmp_path, "2", "docs/README.md")
    output = proc.stdout + proc.stderr
    assert proc.returncode == 0, output
    args_log = pathlib.Path(tmp_path, "git-args.log")
    recorded = args_log.read_text(encoding="utf-8") if args_log.exists() else ""
    assert "diff" in recorded, recorded
    assert "...HEAD" in recorded, recorded
    assert "origin/main...HEAD" in recorded, recorded
