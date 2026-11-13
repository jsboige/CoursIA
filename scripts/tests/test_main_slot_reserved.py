"""T-L (#25510) -- le slot RESERVE de la verification de `main`.

Le job CPU de `main` est un job REQUIS : tant qu'il n'a pas de verdict,
`main` n'est pas verifie. Il etait route sur le meme pool que les PRs
(`coursia-ephemeral`), et il a donc attendu derriere elles -- mesure du
2026-11-12 : plus de 27 minutes en file, avec 31 runners sur 31 occupes.

Ce test porte la MOITIE INFRA de la tranche : le slot reserve lui-meme.
Il est verifie **par son comportement** : le `--dry-run` est execute (c'est
le seul mode qui ne demande ni docker ni token, donc le seul verifiable
partout, CI comprise), et le refus d'un label interdit est mesure.

Trois garde-fous viennent de la revue du coordinateur (13/11) :

1. le **repli ecrit** doit designer un workflow et des entrees qui
   EXISTENT -- une entree morte (`runner_override`) fait echouer la
   commande de repli elle-meme ;
2. le `--dry-run` ne doit laisser **aucune trace** sur le disque : le
   `mkdir` du repertoire de base est un geste d'`--apply` ;
3. les tests du dry-run doivent etre **independant de l'etat vivant** :
   un prefixe de slot jetable, pour que l'existence -- ou l'absence --
   du slot reel de ai-01 ne fasse pas rougir la suite en local.

La MOITIE ROUTING (le job CPU qui vise ce slot sur un push `main`) n'est pas
dans cette PR : elle demande une forme auditee de `runs-on` que la politique
des runners n'admet pas encore (`scripts/ci/check_self_hosted_runner_policy.py`
rend `VIOLATION_DYNAMIC_RUNS_ON` / `RUNNER_LABELS`). L'arbitrage est pose au
coordinateur ; le detail est dans le corps de la PR.
"""
from __future__ import annotations

import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

import pytest
import yaml

REPO_ROOT = Path(__file__).resolve().parents[2]
SCRIPT = (REPO_ROOT / "scripts" / "ci" / "docker" / "linux-runner" / "persist"
          / "ai-01" / "create-main-slot.sh")

RESERVED_LABELS = "self-hosted,coursia-main,coursia-linux"
EPHEMERAL_LABEL = "coursia-ephemeral"

#: `gh workflow run <fichier> [-f cle=valeur] ...`
REPLI_RE = re.compile(
    r"gh\s+workflow\s+run\s+(?P<file>[\w./-]+\.ya?ml)"
    r"(?P<suite>(?:\s+-\S+\s+\S+)*)"
)


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


@pytest.fixture
def prefix_jetable(tmp_path) -> str:
    """Un prefixe de slot JETABLE.

    Le dry-run interroge l'etat vivant (docker inspect) : sans prefixe
    jetable, le test dependrait du conteneur du slot de ai-01 -- il
    rougirait en local le jour ou ce conteneur existe, alors que rien
    n'a change au script.
    """
    return f"coursia-test-jetable-{tmp_path.name}"


def test_le_script_de_creation_existe():
    assert SCRIPT.is_file(), f"le script de creation du slot reserve est absent : {SCRIPT}"


def test_le_dry_run_porte_les_labels_du_slot_reserve(prefix_jetable):
    proc = _run("--dry-run", env={"COURSIA_MAIN_PREFIX": prefix_jetable})
    assert proc.returncode == 0, f"le dry-run doit aboutir : {proc.stderr}"
    out = proc.stdout
    assert f"ACTIONS_RUNNER_INPUT_LABELS={RESERVED_LABELS}" in out, (
        "le dry-run doit porter les labels du slot reserve")
    assert "DRY-RUN" in out and "Aucun conteneur n'a ete cree" in out


def test_le_dry_run_ne_porte_pas_le_label_du_pool_pr(prefix_jetable):
    """Le slot reserve ne doit JAMAIS redevenir un client du pool PR."""
    proc = _run("--dry-run", env={"COURSIA_MAIN_PREFIX": prefix_jetable})
    assert proc.returncode == 0
    assert EPHEMERAL_LABEL not in proc.stdout, (
        f"le slot reserve ne doit pas porter '{EPHEMERAL_LABEL}'")


def test_un_label_ephemere_est_refuse(prefix_jetable):
    """CONTROLE NEGATIF : un slot reserve qui porterait le label du pool PR
    ne resoudrait pas le probleme -- le script doit refuser, pas creer."""
    proc = _run("--dry-run", env={
        "COURSIA_MAIN_PREFIX": prefix_jetable,
        "COURSIA_MAIN_LABELS": f"self-hosted,{EPHEMERAL_LABEL},coursia-linux",
    })
    assert proc.returncode != 0, (
        "un label ephemere doit etre refuse (fail-closed)")
    assert EPHEMERAL_LABEL in proc.stderr, (
        "le refus doit nommer le label fautif")


def test_un_label_sans_coursia_main_est_refuse(prefix_jetable):
    """Sans `coursia-main`, le slot ne serait vise par aucun job."""
    proc = _run("--dry-run", env={
        "COURSIA_MAIN_PREFIX": prefix_jetable,
        "COURSIA_MAIN_LABELS": "self-hosted,coursia-linux",
    })
    assert proc.returncode != 0


def test_le_dry_run_ne_cree_aucun_repertoire(tmp_path, prefix_jetable):
    """Le `--dry-run` ne doit laisser AUCUNE trace sur le disque.

    Le `mkdir` du repertoire de base est un geste d'`--apply` : un
    dry-run qui cree un dossier est un dry-run qui a des effets de bord
    (mesure : la suite de tests creeait `$HOME/CoursIA-runners-main`).
    """
    base = tmp_path / "repertoire-de-base"
    assert not base.exists()
    proc = _run("--dry-run", env={
        "COURSIA_MAIN_PREFIX": prefix_jetable,
        "COURSIA_MAIN_BASE": str(base),
    })
    assert proc.returncode == 0, proc.stderr
    assert not base.exists(), (
        f"le dry-run a cree {base} : le mkdir appartient a la branche --apply")


def test_le_token_ne_passe_pas_dans_l_argv(prefix_jetable):
    """Le token d'enregistrement ne doit PAS figurer dans l'argv.

    Un `-e ACTIONS_RUNNER_INPUT_TOKEN=<valeur>` porte la valeur dans
    l'argv de `docker run` : elle est lisible par `ps` pendant
    l'execution. Le token passe par `--env-file`, fichier en mode 600
    supprime apres la creation.
    """
    proc = _run("--dry-run", env={"COURSIA_MAIN_PREFIX": prefix_jetable})
    assert proc.returncode == 0, proc.stderr
    assert "-e ACTIONS_RUNNER_INPUT_TOKEN=" not in proc.stdout, (
        "le token ne doit pas etre passe par `-e` (argv lisible par `ps`)")
    assert "--env-file" in proc.stdout, (
        "le token doit etre passe par `--env-file`")


def test_le_repli_ecrit_est_dans_le_script():
    """Le repli doit etre ECRIT, dans le fichier que l'operateur ouvre quand
    le runner tombe : la commande de rejeu de la verification de `main`."""
    text = SCRIPT.read_text(encoding="utf-8")
    assert "gh workflow run scripts-tests.yml" in text, (
        "la commande de repli doit etre ecrite dans le script du slot")


def test_le_repli_designe_un_workflow_et_des_entrees_qui_existent():
    """Le repli doit designer un workflow et des entrees REELS.

    Une entree morte (`runner_override`, absente de `workflow_dispatch`)
    fait echouer la commande elle-meme : le repli doit etre verifie
    CONTRE le workflow, pas contre une chaine de caracteres.
    """
    text = SCRIPT.read_text(encoding="utf-8")
    commandes = list(REPLI_RE.finditer(text))
    assert commandes, (
        "le script doit ecrire au moins une commande `gh workflow run` "
        "(le repli quand le runner tombe)")
    for match in commandes:
        nom = match.group("file")
        chemin = REPO_ROOT / ".github" / "workflows" / nom
        assert chemin.is_file(), (
            f"le repli designe `{nom}`, qui n'est pas un workflow du depot : "
            f"{chemin}")
        data = yaml.safe_load(chemin.read_text(encoding="utf-8")) or {}
        # PyYAML lit la cle `on:` comme le booleen `True` (YAML 1.1) :
        # la section des evenements est donc sous `data[True]`, pas
        # sous `data["on"]`.
        declencheurs = data.get("on", data.get(True)) or {}
        # `workflow_dispatch:` sans `inputs:` se parse en None : c'est
        # la PRESENCE de la cle qui compte, pas sa valeur.
        assert "workflow_dispatch" in declencheurs, (
            f"`{nom}` ne declare pas `workflow_dispatch` : la commande de "
            "repli serait refusee")
        dispatch = declencheurs.get("workflow_dispatch") or {}
        entrees = dispatch.get("inputs") or {}
        for cle in re.findall(r"-f\s+([\w-]+)=", match.group("suite")):
            assert cle in entrees, (
                f"le repli passe `-f {cle}=...` mais `{nom}` ne declare pas "
                f"cette entree (`workflow_dispatch.inputs` = "
                f"{sorted(entrees)}) : la commande serait refusee par GitHub")


def test_le_help_affiche_l_entete_du_script():
    """`--help` doit afficher l'en-tete du script.

    L'en-tete porte le repli : c'est le premier reflexe de l'operateur
    quand le runner tombe. Le corte de l'en-tete ne doit donc pas
    dependre de son nombre de lignes.
    """
    proc = _run("--help")
    assert proc.returncode == 0
    assert "gh workflow run scripts-tests.yml" in proc.stdout, (
        "`--help` doit afficher l'en-tete, repli compris")
    assert "set -u" not in proc.stdout, (
        "`--help` ne doit pas laisser fuir la premiere ligne de code")


def test_le_check_signale_un_slot_absent(prefix_jetable):
    """`--check` est l'organe de l'etat VIVANT : sans slot, il sort en
    erreur (fail-closed). Sans docker, il sort deja en erreur -- les deux
    cas sont une derive a corriger, jamais un succes muet."""
    if shutil.which("docker") is None:
        pytest.skip("docker absent : --check ne peut pas lire l'etat vivant")
    proc = _run("--check", env={"COURSIA_MAIN_PREFIX": prefix_jetable})
    assert proc.returncode != 0, (
        "un slot absent doit etre signale comme une derive")


def _faux_binaires(tmp_path) -> tuple[Path, Path]:
    """Faux `docker` et faux `gh` sur le PATH du test.

    `docker inspect` repond comme si le slot EXISTAIT deja -- c'est le cas
    qui ne doit pas mint de token. `gh` note chaque appel dans un fichier :
    un appel = un token d'enregistrement mint.
    """
    bin_dir = tmp_path / "bin"
    bin_dir.mkdir(parents=True, exist_ok=True)
    marqueur_gh = tmp_path / "gh-appele"

    docker = bin_dir / "docker"
    docker.write_text(
        "#!/bin/sh\n"
        "if [ \"$1\" = \"inspect\" ]; then\n"
        "  if [ \"$2\" = \"--format\" ]; then\n"
        "    printf '4294967296 512 3000000000 true\\n'\n"
        "  else\n"
        "    printf 'CONTAINER\\n'\n"
        "  fi\n"
        "  exit 0\n"
        "fi\n"
        "exit 0\n",
        encoding="utf-8")
    gh = bin_dir / "gh"
    gh.write_text(
        "#!/bin/sh\n"
        f"printf 'appel\\n' >> '{marqueur_gh}'\n"
        "printf 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA\\n'\n",
        encoding="utf-8")
    docker.chmod(0o755)
    gh.chmod(0o755)
    return bin_dir, marqueur_gh


def test_le_mint_ne_se_produit_pas_si_le_slot_existe_deja(tmp_path):
    """Un slot deja present ne doit MINT aucun token d'enregistrement.

    Constat du coordinateur (13/11) : en `--apply`, le token etait mint et
    son fichier LAISSE dans `$BASE`, car seule la branche de creation le
    supprimait. Un jeton d'enregistrement valide, ecrit en clair, pour un
    slot qui n'est meme pas cree : c'est un secret laisse sur le disque.
    """
    bin_dir, marqueur_gh = _faux_binaires(tmp_path)
    base = tmp_path / "base"
    proc = _run("--apply", env={
        "PATH": f"{bin_dir}{os.pathsep}{os.environ.get('PATH', '')}",
        "COURSIA_MAIN_BASE": str(base),
        "COURSIA_MAIN_PREFIX": "coursia-test-jetable-token",
    })
    assert proc.returncode == 0, f"{proc.stdout}\n{proc.stderr}"
    assert "[EXISTANT]" in proc.stdout, proc.stdout
    assert not marqueur_gh.exists(), (
        "aucun token ne doit etre mint quand le slot existe deja")
    residus = list(base.glob(".token-registration.*")) if base.exists() else []
    assert not residus, (
        f"un fichier de token a ete laisse sur le disque : {residus}")


if __name__ == "__main__":  # pragma: no cover
    sys.exit(pytest.main([__file__]))
