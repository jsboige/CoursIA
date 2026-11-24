# -*- coding: utf-8 -*-
"""Controle de la resolution du jeton REST : App GitHub si le secret existe,
sinon `GITHUB_TOKEN` (volet D de #26739).

Le contrat demande est precis : « `create-github-app-token` quand le secret
existe, `github.token` sinon, avec le test de retombee sans secret ». Ce test
execute donc **le script du depot** -- pas une reimplementation de sa logique
dans le test -- et verifie les trois branches :

- le repli **sans secret** (le cas demande) : `token=<GITHUB_TOKEN>` et
  `source=github-token`, code retour 0 ;
- le jeton d'App present : `token=<jeton d'App>` et `source=app` ;
- aucun jeton du tout : echec **nomme**, et surtout **aucune** ligne
  `token=` ecrite (fail-CLOSED : un job qui croit avoir un jeton et n'en a
  pas echoue plus tard, ailleurs, sans cause).

Il verifie aussi que le mecanisme n'est pas un artefact mort : l'etape App de
l'action composite est bien **conditionnee** par la presence des deux
entrees, et **continue-on-error** (une App desinstallee ne doit pas faire
echouer le job), et le consommateur cable dans le workflow du controleur
passe bien la sortie `token` dans `GH_TOKEN`.

Le jeton d'App a un seau de quota distinct de celui de `GITHUB_TOKEN`
(~630 appels/h pour un seul cron horaire d'apres le recensement du volet B) :
c'est ce deplacement de depense que le mecanisme opere, et rien d'autre --
en l'absence de secret, le comportement est celui d'aujourd'hui.
"""

import os
import subprocess
from pathlib import Path

import pytest
import yaml

from ._bash_resolution import resolve_bash

ROOT = Path(__file__).resolve().parents[2]
ACTION_DIR = ROOT / ".github" / "actions" / "gh-app-token"
ACTION = ACTION_DIR / "action.yml"
SCRIPT = ACTION_DIR / "resolve_token.sh"
CONTROLLER = ROOT / ".github" / "workflows" / "ci-overflow-controller.yml"

BASH = resolve_bash()

FALLBACK = "gh-token-repli-test"
APP_TOKEN = "gh-token-app-test"


def _action() -> dict:
    return yaml.safe_load(ACTION.read_text(encoding="utf-8"))


def _steps() -> list:
    return _action()["runs"]["steps"]


def _step(step_id: str) -> dict:
    for step in _steps():
        if step.get("id") == step_id:
            return step
    raise AssertionError("pas d'etape d'id {} dans {}".format(step_id, ACTION))


def _run(env: dict, tmp_path: Path) -> subprocess.CompletedProcess:
    """Execute le script du depot avec un GITHUB_OUTPUT temporaire."""
    sortie = tmp_path / "github_output.txt"
    sortie.write_text("", encoding="utf-8")
    # Chemin en barres obliques : un chemin Windows `C:\...` passe dans un
    # `>> "$OUTPUT"` sous bash et lu comme un nom relatif (`C:Users...`).
    env = dict(env)
    env["GITHUB_OUTPUT"] = str(sortie).replace("\\", "/")
    proc = subprocess.run(
        [BASH, str(SCRIPT).replace("\\", "/")],
        env={**os.environ, **env},
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        timeout=30,
    )
    proc.stdout = proc.stdout or ""
    proc.stderr = proc.stderr or ""
    proc.sortie = sortie.read_text(encoding="utf-8")
    return proc


def _lignes(sortie: str) -> dict:
    out = {}
    for ligne in sortie.splitlines():
        if "=" in ligne:
            cle, valeur = ligne.split("=", 1)
            out[cle] = valeur
    return out


# --- le contrat du script ---------------------------------------------------


@pytest.mark.skipif(BASH is None, reason="no sane bash available (#17201)")
def test_repli_sans_secret(tmp_path):
    """Le cas demande : pas de secret -> le jeton du job, et rien d'autre."""
    proc = _run({"APP_TOKEN": "", "FALLBACK_TOKEN": FALLBACK}, tmp_path)
    assert proc.returncode == 0, proc.stderr
    lignes = _lignes(proc.sortie)
    assert lignes.get("token") == FALLBACK
    assert lignes.get("source") == "github-token"
    assert "api-quota:" in proc.stdout


@pytest.mark.skipif(BASH is None, reason="no sane bash available (#17201)")
def test_jeton_app_prioritaire(tmp_path):
    """Secret present -> jeton d'App, et le repli n'est pas utilise."""
    proc = _run({"APP_TOKEN": APP_TOKEN, "FALLBACK_TOKEN": FALLBACK}, tmp_path)
    assert proc.returncode == 0, proc.stderr
    lignes = _lignes(proc.sortie)
    assert lignes.get("token") == APP_TOKEN
    assert lignes.get("source") == "app"


@pytest.mark.skipif(BASH is None, reason="no sane bash available (#17201)")
def test_aucun_jeton_echoue_sans_ecrire_de_token(tmp_path):
    """Fail-CLOSED : pas de jeton -> echec nomme, et AUCUNE ligne `token=`."""
    proc = _run({"APP_TOKEN": "", "FALLBACK_TOKEN": ""}, tmp_path)
    assert proc.returncode != 0
    assert "token=" not in proc.sortie
    assert proc.stderr.strip() != ""


@pytest.mark.skipif(BASH is None, reason="no sane bash available (#17201)")
def test_sortie_absente_est_nommee(tmp_path):
    """Pas de GITHUB_OUTPUT -> echec nomme, pas un silence."""
    env = dict(os.environ)
    env.pop("GITHUB_OUTPUT", None)
    env["APP_TOKEN"] = ""
    env["FALLBACK_TOKEN"] = FALLBACK
    proc = subprocess.run(
        [BASH, str(SCRIPT).replace("\\", "/")],
        env=env,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        timeout=30,
    )
    assert proc.returncode != 0
    assert "GITHUB_OUTPUT" in (proc.stderr or "")


# --- le cablage de l'action composite ---------------------------------------


def test_etape_app_conditionnee_par_les_deux_entrees():
    """Une entree seule ne suffit pas : l'etape doit s'ignorer."""
    etape = _step("app")
    condition = str(etape.get("if", ""))
    assert "app-id" in condition and "private-key" in condition
    assert "!=" in condition or "!= ''" in condition


def test_etape_app_ne_fait_pas_echouer_le_job():
    """App desinstallee ou secret expire -> repli, pas de job rouge."""
    assert _step("app").get("continue-on-error") is True


def test_etape_app_bien_cablee_sur_create_github_app_token():
    etape = _step("app")
    assert str(etape.get("uses", "")).startswith("actions/create-github-app-token@")
    with_ = etape.get("with", {})
    assert "app-id" in with_ and "private-key" in with_


def test_sorties_declarees():
    sorties = _action()["outputs"]
    assert "token" in sorties and "source" in sorties
    assert "steps.resolve.outputs.token" in sorties["token"]["value"]
    assert "steps.resolve.outputs.source" in sorties["source"]["value"]


def test_etape_resolution_lit_le_jeton_du_job_en_repli():
    env = _step("resolve")["env"]
    assert "github.token" in str(env.get("FALLBACK_TOKEN", ""))
    assert "steps.app.outputs.token" in str(env.get("APP_TOKEN", ""))


# --- le consommateur cable ---------------------------------------------------


def test_controleur_cable_le_jeton_resolu():
    """Le mecanisme n'est pas un artefact mort : le controleur l'utilise."""
    texte = CONTROLLER.read_text(encoding="utf-8")
    assert "actions/gh-app-token" in texte
    assert "steps.gh-token.outputs.token" in texte
    # L'ANCIEN câblage ne doit plus porter la mesure : le jeton du job
    # reste disponible en repli, mais la mesure passe par l'action.
    assert "GH_TOKEN: ${{ steps.gh-token.outputs.token }}" in texte
    assert "GH_TOKEN: ${{ github.token }}" not in texte


def test_controleur_checkout_le_repertoire_de_l_action():
    """Un appel local exige `.github/actions` dans le sparse-checkout."""
    texte = CONTROLLER.read_text(encoding="utf-8")
    assert ".github/actions" in texte


def test_le_sparse_checkout_ne_contient_aucun_commentaire():
    """Une ligne `#` DANS le bloc `sparse-checkout` n'est pas un commentaire.

    Le bloc est un scalaire litteral (`|`) : YAML y range la ligne telle
    quelle, `#` compris. actions/checkout en mode cone passe alors chaque
    ligne comme un nom de repertoire a `git sparse-checkout set`, et l'erreur
    n'apparait qu'a l'execution planifiee -- pas dans la CI de la PR, qui
    n'exerce pas le job (review 5912895910 sur #26792).

    Le test lit la valeur **resolue** par `yaml.safe_load`, pas le texte :
    c'est la valeur resolue que l'action recoit.
    """
    donnees = yaml.safe_load(CONTROLLER.read_text(encoding="utf-8"))
    etapes = donnees["jobs"]["control"]["steps"]
    checkout = next(e for e in etapes if e.get("name") == "Checkout")
    valeur = checkout["with"]["sparse-checkout"]
    lignes = [l.strip() for l in valeur.splitlines() if l.strip()]
    assert not [l for l in lignes if l.startswith("#")], (
        f"commentaire dans la valeur sparse-checkout : {lignes}"
    )
    assert ".github/actions" in lignes, lignes

