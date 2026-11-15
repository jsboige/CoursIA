# -*- coding: utf-8 -*-
"""Controle du soin d'arbre chaud, extrait en action composite (#23287).

Plusieurs choses sont verifiees ici, et deux d'entre elles n'etaient mesurees
nulle part avant l'extraction :

- **controle positif** (critere 4 de l'issue) : sur un arbre volontairement
  pollue par un fichier non suivi, le soin rapporte la salissure ET dit qu'il ne
  l'a pas retiree ;
- **silence en echec** (critere 3) : un `git status` qui echoue produit une
  ligne `::warning::`, jamais un silence qui se lit « arbre propre » ;
- **anti-divergence** (le motif de l'issue) : le corps du script reste
  byte-identique au bloc que les workflows portent encore, pour que la
  factorisation ne se defasse pas en silence d'ici le basculement des appelants.

Le raccordement **distant** des workflows a l'action composite est explicitement
ecarte : l'etape de soin tourne AVANT `actions/checkout`, donc une action
locale n'existe pas encore dans l'espace de travail ; l'appel distant
(`jsboige/CoursIA/.github/actions/heal-worktree@main`) oblige en revanche
GitHub a telecharger l'archive codeload du depot ENTIER a l'etape « Set up
job » -- de quoi faire tomber la totalite des workflows qui l'utilisent. Les
copies inline restent donc en place, et c'est ce test qui porte l'objectif de
source unique (#23287) : chaque copie doit etre byte-identique au script.

Depuis #23512, l'identite n'est plus seulement **verifiee**, elle est
**maintenue** : `scripts/ci/sync_heal_worktree_copies.py` regenere les copies
depuis le script source, donc corriger le soin demande une edition et une
commande, non vingt-six editions synchrones. Ce test couvre le generateur
(mode `--check` sans desync, controle positif de reparation, idempotence) et
la fermeture de la couverture : un workflow qui porterait le bloc sans etre
inscrit dans `EXPECTED_WORKFLOWS` est signale.
"""

import io
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

from ._bash_resolution import resolve_bash

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / ".github" / "actions" / "heal-worktree" / "heal_worktree.sh"
ACTION = ROOT / ".github" / "actions" / "heal-worktree" / "action.yml"
WORKFLOWS = ROOT / ".github" / "workflows"
STEP_NAME = "Restore the warm work tree before the sparse checkout"
MARKER = "# --- corps extrait : byte-identique au bloc des workflows (#23287) ---"
REMOTE_REF = "jsboige/CoursIA/.github/actions/heal-worktree"

# Les workflows qui portent le soin d'arbre chaud. La liste est explicite :
# une garde qui compte les occurrences passe aussi quand une seule en porte
# une -- c'etait le trou du controle d'identite, qui verifiait la copie sans
# verifier la couverture.
#
# La liste a ete completee le 2026-11-04 (#23512) : elle portait 12 noms
# alors que 26 workflows du pool portaient deja le bloc (28 occurrences). La
# couverture ne verifiait que les 12 premiers -- un workflow qui perdait son
# soin passait inapercu.
EXPECTED_WORKFLOWS = (
    "adjacency-stale-sweep.yml",
    "candidate-delivered-advisory.yml",
    "concurrency-conj-guard.yml",
    "degenerate-figure-gate.yml",
    "epic-charter-advisory.yml",
    "epic-neglect-sweep.yml",
    "grain-orphans-sweep.yml",
    "harness-coauthor-guard.yml",
    "hooks-parity.yml",
    "lane-claim-guard.yml",
    "linux-runner-version-pin-advisory.yml",
    "markdown-table-guard.yml",
    "orphaned-delivery-scan.yml",
    "pr-gate-rerun.yml",
    "pr-gate-sweep-health-advisory.yml",
    "regression-guard.yml",
    "slides-composition-pr-relay.yml",
    "stale-base-warning.yml",
    "stale-guard-red-sweep.yml",
    "svg-broken-geometry-gate.yml",
    "svg-decimal-comma-gate.yml",
    "svg-empty-display-gate.yml",
    "svg-offscreen-flat-gate.yml",
    "translation-guard.yml",
    "unique-check-run-names-guard.yml",
    "variation-light-genre.yml",
)

# Pas `shutil.which("bash")` : sous le PATH d'une tache planifiee Windows,
# il rend le lanceur WSL de System32, qui avale le chemin Windows du script
# (exit 127) -- c'est ce qui faisait rougir l'arbre fusionne de merge_ready
# sur toutes les PRs approuvees (#17201, mesure du 2026-11-06).
BASH = resolve_bash()


def run_heal(workspace, extra_path=None):
    """Execute le script tel que l'action composite l'appelle."""
    env = dict(os.environ)
    env["GITHUB_WORKSPACE"] = workspace
    if extra_path:
        env["PATH"] = extra_path + os.pathsep + env.get("PATH", "")
    return subprocess.run(
        [BASH, str(SCRIPT)],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        env=env,
        timeout=120,
    )


def _git(cwd, *args):
    return subprocess.run(
        ["git", "-C", str(cwd)] + list(args),
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        check=True,
    )


@pytest.fixture()
def warm_repo(tmp_path):
    """Un depot git minimal, avec un fichier suivi commite."""
    repo = tmp_path / "warm"
    repo.mkdir()
    _git(repo, "init", "--quiet")
    _git(repo, "config", "user.email", "test@example.invalid")
    _git(repo, "config", "user.name", "test")
    (repo / "tracked.txt").write_text("contenu initial\n", encoding="utf-8")
    _git(repo, "add", "tracked.txt")
    _git(repo, "commit", "--quiet", "-m", "init")
    return repo


def _workspace(path):
    """Chemin au format POSIX : Git Bash lit `D:/...` sans conversion."""
    return Path(path).resolve().as_posix()


@pytest.mark.skipif(BASH is None, reason="bash absent de cet hote")
def test_controle_positif_arbre_pollue(warm_repo):
    """Critere 4 : la salissure est rapportee, et le non-suivi n'est pas retire."""
    (warm_repo / "tracked.txt").write_text("modifie\n", encoding="utf-8")
    (warm_repo / "residu.txt").write_text("laisse\n", encoding="utf-8")

    res = run_heal(_workspace(warm_repo))

    assert res.returncode == 0, res.stderr
    assert "::notice::[heal-worktree] reset --hard effectue" in res.stdout
    assert "1 entree(s) non suivie(s) laissee(s) en place" in res.stdout
    # le message separe ce qui est traite de ce qui ne l'est pas : la ligne sale
    # citee est celle qui a ete remise en etat, le non-suivi est compte a part
    assert "M tracked.txt" in res.stdout, "le message doit nommer l'etat remis en etat"
    assert (warm_repo / "residu.txt").exists(), "le soin ne doit pas nettoyer les caches"
    assert (warm_repo / "tracked.txt").read_text(encoding="utf-8") == "contenu initial\n"


@pytest.mark.skipif(BASH is None, reason="bash absent de cet hote")
def test_arbre_propre_ne_dit_rien(warm_repo):
    """Sur un arbre propre, le soin se tait : aucune ligne de diagnostic."""
    res = run_heal(_workspace(warm_repo))

    assert res.returncode == 0, res.stderr
    assert "[heal-worktree]" not in res.stdout


@pytest.mark.skipif(BASH is None, reason="bash absent de cet hote")
def test_probe_muet_emet_un_warning(warm_repo, tmp_path):
    """Critere 3 : `git status` en echec ne doit pas se lire « arbre propre »."""
    shim_dir = tmp_path / "shim"
    shim_dir.mkdir()
    shim = shim_dir / "git"
    # delegue tout, sauf `status`, qui echoue comme un index illisible. Le shim
    # recoit `-C <ws> -c safe.directory=<ws> status --porcelain` : `status` n'est
    # pas un argument fixe, on le cherche donc dans la ligne d'arguments.
    shim.write_text(
        "#!/usr/bin/env bash\n"
        'for a in "$@"; do if [ "$a" = "status" ]; then exit 128; fi; done\n'
        'exec "' + shutil.which("git").replace("\\", "/") + '" "$@"\n',
        encoding="utf-8",
        newline="\n",
    )
    shim.chmod(0o755)
    # Le wrapper Git `bin\bash.exe` (repli de resolve_bash hors PATH Git)
    # replace `/mingw64/bin:/usr/bin` DEVANT le PATH herite : le shim serait
    # contourne et le test rougirait sans que le soin soit en cause. On mesure
    # la propriete plutot que de deviner l'hote.
    probe_env = dict(os.environ)
    probe_env["PATH"] = shim_dir.as_posix() + os.pathsep + probe_env.get("PATH", "")
    probe = subprocess.run(
        [BASH, "-c", "command -v git"],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
        # Meme budget que `run_heal` ci-dessus (120 s) : la sonde est triviale,
        # mais sous le job `Scripts Tests (CPU)` quatre workers xdist se
        # partagent le runner et un sous-processus peut etre affame bien
        # au-dela de son cout nominal (job 131005200449, 2026-11-12).
        env=probe_env, timeout=120,
    )
    if "shim" not in probe.stdout:
        pytest.skip("ce bash reordonne le PATH (wrapper Git bin\\bash.exe) : "
                    "un shim prepose y est contourne")

    res = run_heal(_workspace(warm_repo), extra_path=shim_dir.as_posix())

    assert res.returncode == 0, res.stderr
    assert "::warning::[heal-worktree] probe git status muet" in res.stdout


@pytest.mark.skipif(BASH is None, reason="bash absent de cet hote")
def test_sans_depot_git_le_soin_ne_fait_rien(tmp_path):
    """Un espace de travail sans `.git` (pool froid) n'est pas une erreur."""
    empty = tmp_path / "vide"
    empty.mkdir()

    res = run_heal(_workspace(empty))

    assert res.returncode == 0, res.stderr
    assert "[heal-worktree]" not in res.stdout


def _workflow_bodies():
    """Corps (`run: |` dedente) de chaque occurrence du bloc dans les workflows."""
    bodies = []
    for path in sorted(WORKFLOWS.glob("*.yml")):
        text = io.open(path, encoding="utf-8", newline="").read()
        idx = 0
        while True:
            i = text.find(STEP_NAME, idx)
            if i < 0:
                break
            start = text.rfind("\n", 0, text.rfind("\n", 0, i) + 1) + 1
            rest = text[i:]
            m = re.search(r"\n      - ", rest[1:])
            end = i + 1 + (m.start() if m else len(rest) - 1)
            lines = text[start:end].splitlines()
            assert lines[1].strip() == "run: |", path
            # une ligne vide du script reste vide dans le workflow : la
            # dedentition ne doit pas presumer d'une longueur minimale
            bodies.append((path.name, [ln[10:] if len(ln) >= 10 else "" for ln in lines[2:]]))
            idx = i + len(STEP_NAME)
    return bodies


def test_le_script_est_le_corps_des_workflows():
    """Anti-divergence : le corps sous le marqueur reste byte-identique au bloc.

    Le controle porte DEUX choses : l'identite de chaque copie (le script est
    la source), et la COUVERTURE (chacun des workflows attendus porte bien une
    copie). La couverture etait absente : la garde passait avec une seule
    occurrence dans l'ensemble du pool.
    """
    text = SCRIPT.read_text(encoding="utf-8")
    assert MARKER in text, "le marqueur de corps a disparu : garde sans objet"
    script_body = text.split(MARKER + "\n", 1)[1].splitlines()
    bodies = _workflow_bodies()

    assert bodies, "aucune occurrence du bloc dans les workflows : garde sans objet"
    for name, body in bodies:
        assert body == script_body, (
            "le script a diverge du bloc porte par %s : la factorisation se defait "
            "avant meme le basculement des appelants" % name
        )

    portraits = {name for name, _ in bodies}
    manquants = [name for name in EXPECTED_WORKFLOWS if name not in portraits]
    assert not manquants, (
        "workflow(s) du pool sans copie du soin : %s -- le soin d'arbre chaud "
        "manque a ces run(s), la source unique n'y est pas portee"
        % ", ".join(manquants)
    )


def test_aucun_workflow_n_appelle_l_action_distante():
    """Controle negatif : l'appel distant a l'action composite est exclu.

    L'action composite existe, mais l'appeler a distance (`...@main`) force
    GitHub a telecharger l'archive codeload du depot ENTIER (~3,5 Go) a
    l'etape « Set up job » -- avant meme le checkout. Chaque workflow qui
    l'appelle fait tomber son propre run ; l'action locale est exclue par la
    position de l'etape (avant le checkout). Le soin reste donc inline, et ce
    test interdit qu'on reintroduise l'appel distant.
    """
    for path in sorted(WORKFLOWS.glob("*.yml")):
        text = io.open(path, encoding="utf-8", newline="").read()
        assert REMOTE_REF not in text, (
            "%s appelle l'action composite a distance : le run telechargera "
            "l'archive du depot entier avant le checkout" % path.name
        )


def test_action_reference_le_script():
    """L'action composite appelle bien le script, sans recopier son corps."""
    text = ACTION.read_text(encoding="utf-8")
    assert "using: composite" in text
    assert "${{ github.action_path }}/heal_worktree.sh" in text
    assert "reset --hard" not in text, "le corps doit vivre dans le script, pas dans l'action"


# --- generateur des copies (#23512) -----------------------------------------
#
# Le bloc est porte par 26 workflows ; sans generateur, le corriger demandait
# 26 editions synchrones a la main. Le generateur retire la main de l'edition :
# on modifie le script source, on le regenere, les copies suivent.

GENERATOR = ROOT / "scripts" / "ci" / "sync_heal_worktree_copies.py"


def _load_generator():
    """Charge le generateur comme module (chemin relatif au depot)."""
    import importlib.util

    spec = importlib.util.spec_from_file_location("sync_heal_worktree_copies", GENERATOR)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_la_couverture_est_complete_et_fermee():
    """Aucun workflow en dehors de la liste ne porte le bloc (croiture).

    La liste est la declaration de qui porte le soin. Un workflow qui
    copierait le bloc sans y etre inscrit passerait la garde d'identite
    (qui ne verifie que l'egalite) sans jamais etre signale : la duplication
    pourrait croitre en silence. La direction fermee rattrape ce cas.
    """
    bodies = _workflow_bodies()
    portraits = {name for name, _ in bodies}
    hors_liste = sorted(portraits - set(EXPECTED_WORKFLOWS))
    assert not hors_liste, (
        "workflow(s) portant le soin d'arbre chaud sans etre inscrits dans "
        "EXPECTED_WORKFLOWS : %s -- inscrire le nom, sinon la duplication "
        "croit sans controle" % ", ".join(hors_liste)
    )


def test_le_generateur_ne_reecrit_rien_en_mode_check():
    """Mode `--check` : le depot est deja synchronise, donc exit 0."""
    module = _load_generator()
    assert module.main(["--check"]) == 0, "les copies inline ont derive du script source"


def test_le_generateur_repare_une_copie_divergente():
    """Controle positif : une copie alteree est regeneree a l'identique.

    Sans ce controle, un generateur qui ne regenere rien passerait tous les
    tests : il suffit de le rendre idempotent pour qu'il paraisse correct.
    """
    module = _load_generator()
    body = module.script_body()
    source = (WORKFLOWS / "adjacency-stale-sweep.yml").read_text(encoding="utf-8")

    # on alterre le bloc : une ligne du corps est remplacee
    altere = source.replace("set -u\n", "set -u\n", 1)
    altere = altere.replace("reset --hard --quiet", "reset --hard --quiet ; exit 0", 1)
    assert altere != source, "la fixture n'a pas reellement ete alteree"

    regenere, count = module.sync_text(altere, body)
    assert count == 1, "le generateur n'a pas vu la derive"
    assert regenere == source, "la copie regeneree n'est pas revenue a l'identique"

    # et le generateur est idempotent : une seconde passe ne change rien
    encore, count2 = module.sync_text(regenere, body)
    assert count2 == 0
    assert encore == regenere


def test_le_generateur_repare_une_copie_crlf(tmp_path):
    """Un checkout CRLF n'est plus un no-op silencieux du generateur.

    Controle POSITIF : le chemin d'ecriture (`sync_file`) repare une copie
    CRLF alteree, et les fins de ligne CRLF sont preservees a l'ecriture.

    Controle NEGATIF : ce test est rouge sur une tete ou `sync_file` ne
    normalise pas le texte avant la synchronisation (mesure sur ai-01 :
    `STEP_RE` exige `run: |\n`, le fichier CRLF porte `run: |\r\n`, donc
    `_blocks()` rend 0 et rien n'est ecrit). C'est donc la preuve que le
    chemin d'ecriture -- et non seulement `sync_text` -- est exerce.
    """
    module = _load_generator()
    body = module.script_body()
    source = (WORKFLOWS / "adjacency-stale-sweep.yml").read_text(encoding="utf-8")

    altere = source.replace("reset --hard --quiet", "reset --hard --quiet ; exit 0", 1)
    assert altere != source, "la fixture n'a pas reellement ete alteree"

    cible = tmp_path / "copie-crlf.yml"
    cible.write_bytes(altere.replace("\n", "\r\n").encode("utf-8"))

    count = module.sync_file(cible, body)

    assert count == 1, (
        "le generateur n'a pas vu la derive d'une copie CRLF : `sync_file` "
        "normalise-t-il le texte avant la synchronisation ?"
    )
    brut = cible.read_bytes()
    assert b"\r\n" in brut, "les fins de ligne CRLF n'ont pas ete preservees"
    assert b"\n" not in brut.replace(b"\r\n", b""), (
        "une fin de ligne LF s'est glisee dans un fichier CRLF"
    )
    # le bloc est revenu a l'identique du script source, une fois les fins de
    # ligne normalisees
    relu = brut.decode("utf-8").replace("\r\n", "\n")
    assert relu == source, "la copie CRLF regeneree n'est pas revenue a l'identique"


def test_main_signale_un_ecart_entre_le_compte_detecte_et_le_compte_ecrit(
    tmp_path, monkeypatch
):
    """`main()` ne peut plus annoncer « regenere » quand rien n'a ete ecrit.

    Le desync silencieux (compte detecte != compte ecrit) est une erreur, pas
    une reussite : la sortie doit etre non nulle, pour que la commande ne
    passe jamais pour une regeneration reussie.
    """
    module = _load_generator()
    body = module.script_body()
    source = (WORKFLOWS / "adjacency-stale-sweep.yml").read_text(encoding="utf-8")

    altere = source.replace("reset --hard --quiet", "reset --hard --quiet ; exit 0", 1)
    assert altere != source, "la fixture n'a pas reellement ete alteree"

    pool = tmp_path / "workflows"
    pool.mkdir()
    (pool / "copie.yml").write_text(altere, encoding="utf-8", newline="\n")
    monkeypatch.setattr(module, "WORKFLOWS", pool)
    # on simule un generateur qui n'ecrit rien : l'ecart doit etre signale
    monkeypatch.setattr(module, "sync_file", lambda path, body: 0)

    with pytest.raises(module.Desync):
        module.main([])
