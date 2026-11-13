"""T-L (#25510) -- le slot RESERVE de la verification de `main`.

Le job CPU de `main` est un job REQUIS : tant qu'il n'a pas de verdict,
`main` n'est pas verifie. Il etait route sur le meme pool que les PRs
(`coursia-ephemeral`), et il a donc attendu derriere elles -- mesure du
2026-11-12 : plus de 27 minutes en file, avec 31 runners sur 31 occupes.

Ce test porte la MOITIE INFRA de la tranche : le slot reserve lui-meme.
Il est verifie **par son comportement** : le `--dry-run` est execute (c'est
le seul mode qui ne demande ni docker ni token, donc le seul verifiable
partout, CI comprise), et le refus d'un label interdit est mesure.

La MOITIE ROUTING (le job CPU qui vise ce slot sur un push `main`) n'est pas
dans cette PR : elle demande une forme auditee de `runs-on` que la politique
des runners n'admet pas encore (`scripts/ci/check_self_hosted_runner_policy.py`
rend `VIOLATION DYNAMIC_RUNS_ON` / `RUNNER_LABELS`). L'arbitrage est pose au
coordinateur ; le detail est dans le corps de la PR.
"""
from __future__ import annotations

import os
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
SCRIPT = (REPO_ROOT / "scripts" / "ci" / "docker" / "linux-runner" / "persist"
          / "ai-01" / "create-main-slot.sh")

RESERVED_LABELS = "self-hosted,coursia-main,coursia-linux"
EPHEMERAL_LABEL = "coursia-ephemeral"


def _bash() -> str:
    bash = shutil.which("bash")
    if bash is None:
        pytest.skip("bash absent : le script de creation est un script bash")
    return bash


def _run(*args: str, env: dict[str, str] | None = None) -> subprocess.CompletedProcess:
    environment = dict(os.environ)
    if env:
        environment.update(env)
    return subprocess.run(
        [_bash(), str(SCRIPT), *args],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
        env=environment, timeout=120,
    )


def test_le_script_de_creation_existe():
    assert SCRIPT.is_file(), f"le script de creation du slot reserve est absent : {SCRIPT}"


def test_le_dry_run_porte_les_labels_du_slot_reserve():
    proc = _run("--dry-run")
    assert proc.returncode == 0, f"le dry-run doit aboutir : {proc.stderr}"
    out = proc.stdout
    assert f"ACTIONS_RUNNER_INPUT_LABELS={RESERVED_LABELS}" in out, (
        "le dry-run doit porter les labels du slot reserve")
    assert "DRY-RUN" in out and "Aucun conteneur n'a ete cree" in out


def test_le_dry_run_ne_porte_pas_le_label_du_pool_pr():
    """Le slot reserve ne doit JAMAIS redevenir un client du pool PR."""
    proc = _run("--dry-run")
    assert proc.returncode == 0
    assert EPHEMERAL_LABEL not in proc.stdout, (
        f"le slot reserve ne doit pas porter '{EPHEMERAL_LABEL}'")


def test_un_label_ephemere_est_refuse():
    """CONTROLE NEGATIF : un slot reserve qui porterait le label du pool PR
    ne resoudrait pas le probleme -- le script doit refuser, pas creer."""
    proc = _run("--dry-run", env={
        "COURSIA_MAIN_LABELS": f"self-hosted,{EPHEMERAL_LABEL},coursia-linux",
    })
    assert proc.returncode != 0, (
        "un label ephemere doit etre refuse (fail-closed)")
    assert EPHEMERAL_LABEL in proc.stderr, (
        "le refus doit nommer le label fautif")


def test_un_label_sans_coursia_main_est_refuse():
    """Sans `coursia-main`, le slot ne serait vise par aucun job."""
    proc = _run("--dry-run", env={
        "COURSIA_MAIN_LABELS": "self-hosted,coursia-linux",
    })
    assert proc.returncode != 0


def test_le_repli_ecrit_est_dans_le_script():
    """Le repli doit etre ECRIT, dans le fichier que l'operateur ouvre quand
    le runner tombe : la commande de rejeu de la verification de `main`."""
    text = SCRIPT.read_text(encoding="utf-8")
    assert "gh workflow run scripts-tests.yml" in text, (
        "la commande de repli doit etre ecrite dans le script du slot")
    assert "runner_override" in text, (
        "le repli doit nommer l'entree qu'il utilise")


def test_le_check_signale_un_slot_absent():
    """`--check` est l'organe de l'etat VIVANT : sans slot, il sort en
    erreur (fail-closed). Sans docker, il sort deja en erreur -- les deux
    cas sont une derive a corriger, jamais un succes muet."""
    if shutil.which("docker") is None:
        pytest.skip("docker absent : --check ne peut pas lire l'etat vivant")
    proc = _run("--check")
    assert proc.returncode != 0, (
        "un slot absent doit etre signale comme une derive")


if __name__ == "__main__":  # pragma: no cover
    sys.exit(pytest.main([__file__]))
