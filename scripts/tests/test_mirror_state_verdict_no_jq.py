#!/usr/bin/env python3
"""Non-regression: le verdict du miroir ne depend plus d'un outil absent (#28504).

Le job `Miroir d'objets (hote)` de `mirror-state-pr-advisory.yml` lisait le
resume de l'organe avec `jq`, sous le `set -e` qui suit la capture du code de
retour. Sur les slots auto-heberges ou `jq` n'est pas installe, l'etape mourait
en 127 (`jq: command not found`) et le job passait au rouge **alors que
l'organe avait conclu « etat non lisible »** -- exactement le cas que l'en-tete
du workflow decide de traiter en NOTE, jamais en rouge (mesure de l'issue :
19 echecs du 16 au 25/11, dont 12 en cinq heures le 24-25/11).

Les deux tests ci-dessous gardent le correctif par les deux bouts :

1. `test_..._sans_jq` : statique -- le bloc `run:` de l'etape ne contient plus
   d'invocation de `jq`.
2. `test_..._retombe_sur_les_defauts` : dynamique -- les lignes de lecture
   **extraites du workflow** (pas recopiees) sont jouees dans un vrai `bash`
   sur trois formes de `mirror.json` : resume valide, cles absentes, fichier
   illisible. Les deux dernieres doivent rendre les memes defauts qu'avant
   (`inconnu` / `?`), sans code de sortie non nul.

Run:
    python -m pytest scripts/tests/test_mirror_state_verdict_no_jq.py
"""
from __future__ import annotations

import re
import subprocess
from pathlib import Path

import pytest

from ._bash_resolution import resolve_bash

WORKFLOW = (
    Path(__file__).resolve().parents[2]
    / ".github"
    / "workflows"
    / "mirror-state-pr-advisory.yml"
)
STEP_NAME = "Verdict de l'etat du miroir"
# Une invocation de jq : debut de commande, ou apres un separateur de shell.
JQ_INVOCATION = re.compile(r"(^|[|;&(]\s*)(?:command\s+)?jq\b", re.MULTILINE)


def _step_run_block() -> str:
    """Le texte du `run:` de l'etape de verdict, tel que le shell le lit."""
    import yaml

    data = yaml.safe_load(WORKFLOW.read_text(encoding="utf-8"))
    for job in data["jobs"].values():
        for step in job.get("steps", []):
            if step.get("name") == STEP_NAME:
                return step["run"]
    raise AssertionError(f"etape introuvable dans {WORKFLOW.name} : {STEP_NAME!r}")


def _read_lines() -> str:
    """Les lignes qui calculent `fails` et `seuil`, extraites du bloc.

    Extrait de `cat mirror.json` exclu jusqu'au `if` du verdict exclu : c'est la
    portion exacte qui doit rester jouable sans `jq`.
    """
    block = _step_run_block().splitlines()
    try:
        start = next(i for i, line in enumerate(block) if line.strip() == "cat mirror.json")
        end = next(i for i, line in enumerate(block) if line.strip().startswith('if [ "$rc"'))
    except StopIteration as exc:  # pragma: no cover - garde de structure
        raise AssertionError(f"bloc de lecture introuvable dans l'etape {STEP_NAME!r}") from exc
    lines = block[start + 1 : end]
    return "\n".join(lines)


def test_le_verdict_du_miroir_ne_lit_plus_par_jq():
    """Le defaut mesure : `jq` absent du slot tue l'etape sous `set -e`."""
    assert not JQ_INVOCATION.search(_step_run_block()), (
        "l'etape de verdict appelle jq : sur un slot sans jq, `set -e` la tue en 127 "
        "alors que l'organe a conclu « etat non lisible » (#28504)"
    )


@pytest.mark.parametrize(
    ("contenu", "attendu"),
    [
        ('{"mirror": {"fails": 3, "threshold": 5}}', "3|5"),
        ('{"mirror": {}}', "inconnu|?"),
        ('{"status": "OK", "note": "etat non lisible ici"}', "inconnu|?"),
        ("pas du json du tout", "inconnu|?"),
    ],
)
def test_la_lecture_retombe_sur_les_defauts(tmp_path, contenu, attendu):
    """Un etat illisible reste une NOTE : memes defauts, jamais un code non nul."""
    (tmp_path / "mirror.json").write_text(contenu, encoding="utf-8")
    script = _read_lines() + "\nprintf '%s|%s' \"$fails\" \"$seuil\"\n"
    result = subprocess.run(
        [resolve_bash(), "-e", "-c", script],
        cwd=tmp_path,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        timeout=60,
    )
    assert result.returncode == 0, result.stderr
    assert result.stdout == attendu, f"stdout={result.stdout!r} stderr={result.stderr!r}"
