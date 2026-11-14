"""Tests hors ligne du heal shallow propre au job Scripts Tests (#24986).

Contrat du HEAL **depuis T-K (#25510)** : le HEAL ne tire **plus rien**.

Avant T-K, le HEAL tentait `git fetch --unshallow origin` **sans refspec** sur
un work dir SHALLOW reutilise : cette commande tire `+refs/heads/*`, c'est-a-dire
l'historique complet des 1 606 branches du depot -- 19 min mesurees sur
`75e21a7fac` (job 131524893709). L'historique utile (tete + base) est tire
apres coup par l'etape T-K, **bornee** (deux refspec explicites).

Le contrat du HEAL est donc reduit a deux verites :

1. un work dir SHALLOW est **conserve tel quel** (profondeur conservee) --
   l'elargissement borne suit ;
2. un work dir dont le graphe **n'est pas lisible** est **purge** (il faut un
   clone neuf).

Ces deux tests sont hors ligne : ils rejouent le snippet HEAL sur un depot
synthetique, dans un `tmp_path`.
"""

import os
import subprocess
from pathlib import Path

import pytest

from ._bash_resolution import resolve_bash

ROOT = Path(__file__).resolve().parents[2]
WORKFLOW = ROOT / ".github" / "workflows" / "scripts-tests.yml"
STEP = '      - name: "Purger un work dir reutilise au graphe incomplet (#15387)"\n'
BASH = resolve_bash()

# Budget du sous-processus qui rejoue le snippet HEAL. C'est une garde
# anti-blocage, PAS une assertion de latence : depuis T-K le snippet ne fait
# plus aucun `git fetch` (il ne lit que le depot local), mais il tourne sur
# un runner self-hosted partage par quatre workers xdist.
#
# 30 s ne suffisait pas sous le job `Scripts Tests (CPU)`, ou jusqu'a quatre
# workers xdist se partagent le runner : job 131005200449 du 2026-11-12, le
# snippet a depasse 30 s de famine alors que le reste de la suite rendait
# 1 failed / 26551 passed (`subprocess.TimeoutExpired` a 06:35:03Z). Le
# defaut n'etait pas dans le snippet mais dans le budget, et il rougissait
# une jambe REQUISE pour toutes les PRs du depot.
#
# 120 s laisse un facteur ~30 au-dessus du besoin mesure tout en bornant un
# vrai blocage a deux minutes.
HEAL_TIMEOUT_S = 120


def _git(cwd, *args, check=True):
    return subprocess.run(
        ["git", "-C", str(cwd), *args], check=check, capture_output=True,
        text=True, encoding="utf-8",
    )


def _heal_script():
    text = WORKFLOW.read_text(encoding="utf-8")
    block = text.split(STEP, 1)[1].split("\n      - uses: actions/checkout@v4", 1)[0]
    lines = block.splitlines()
    assert lines[0].strip() == "shell: bash"
    assert lines[1].strip() == "run: |"
    return "\n".join(line[10:] if line.startswith("          ") else line for line in lines[2:]) + "\n"


@pytest.fixture
def shallow_repo(tmp_path):
    source = tmp_path / "source"
    source.mkdir()
    _git(source, "init", "--quiet", "-b", "main")
    _git(source, "config", "user.email", "test@example.invalid")
    _git(source, "config", "user.name", "test")
    for index in range(4):
        (source / "history.txt").write_text(f"commit {index}\n", encoding="utf-8")
        _git(source, "add", "history.txt")
        _git(source, "commit", "--quiet", "-m", f"commit {index}")
    bare = tmp_path / "origin.git"
    _git(tmp_path, "clone", "--quiet", "--bare", str(source), str(bare))
    clone = tmp_path / "clone"
    subprocess.run(
        ["git", "clone", "--quiet", "--depth=1", "--branch", "main", bare.as_uri(), str(clone)],
        check=True, capture_output=True, text=True,
        encoding="utf-8", errors="replace",
    )
    assert _git(clone, "rev-parse", "--is-shallow-repository").stdout.strip() == "true"
    return clone, bare


def _run_heal(clone, tmp_path):
    script = tmp_path / "heal.sh"
    script.write_text(_heal_script(), encoding="utf-8")
    env = dict(os.environ, GITHUB_WORKSPACE=str(clone))
    return subprocess.run(
        [BASH, str(script)], env=env, capture_output=True,
        text=True, encoding="utf-8", errors="replace",
        timeout=HEAL_TIMEOUT_S,
    )


@pytest.mark.skipif(BASH is None, reason="bash absent de cet hote")
def test_le_heal_ne_tire_plus_rien(shallow_repo, tmp_path):
    """Aucun `git fetch` dans le HEAL : c'est l'objet meme de T-K (#25510).

    Le geste retire (`git fetch --unshallow origin` sans refspec) tirait
    l'historique des 1 606 branches ; son retour dans le snippet re-rougirait
    silencieusement la jambe longue.
    """
    clone, _ = shallow_repo
    snippet = _heal_script()
    assert "git fetch" not in snippet, (
        "le HEAL ne doit plus lancer de `git fetch` : l'historique utile est "
        "tire par l'etape T-K, bornee a la tete et a la base"
    )


@pytest.mark.skipif(BASH is None, reason="bash absent de cet hote")
def test_work_dir_shallow_reutilise_profondeur_conservee(shallow_repo, tmp_path):
    """Un work dir SHALLOW est conserve tel quel : la profondeur n'est pas
    touchee par le HEAL, l'elargissement borne suit (etape T-K)."""
    clone, _ = shallow_repo
    result = _run_heal(clone, tmp_path)
    assert result.returncode == 0, result.stderr
    assert "profondeur conservee" in result.stdout
    assert "graphe d'objets incomplet" not in result.stdout
    assert "unshallow explicite reussi" not in result.stdout
    assert (clone / ".git").is_dir()
    # Le work dir reste SHALLOW : c'est l'etape T-K (bornée) qui elargit.
    assert (clone / ".git" / "shallow").exists()


@pytest.mark.skipif(BASH is None, reason="bash absent de cet hote")
def test_graphe_illisible_purge_le_work_dir(shallow_repo, tmp_path):
    """Un graphe que git ne sait pas lire est purge (il faut un clone neuf).

    Le cas historique du test d'origine -- "l'origin est absent, donc le
    unshallow echoue" -- ne declenche plus rien : le HEAL ne tire plus rien,
    donc une remote absente ne le concerne plus. Le cas de purge qui reste
    est la **lecture** du graphe, pas sa profondeur : un `HEAD` qui pointe
    un objet absent fait echouer `git rev-list --all --count` (verifie :
    `fatal: bad object HEAD`), et c'est exactement ce que la branche
    "graphe d'objets incomplet" doit attraper.
    """
    clone, _ = shallow_repo
    head = clone / ".git" / "HEAD"
    head.write_text("deadbeefdeadbeefdeadbeefdeadbeefdeadbeef\n", encoding="utf-8")
    assert _git(clone, "rev-list", "--all", "--count", check=False).returncode != 0

    result = _run_heal(clone, tmp_path)
    assert result.returncode == 0, result.stderr
    assert "graphe d'objets incomplet" in result.stdout
    assert not (clone / ".git").exists()
