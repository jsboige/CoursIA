"""T-K (#25510) : le checkout des deux jambes ne tire plus les 1 606 branches.

`fetch-depth: 0` fait tirer `+refs/heads/*` + les tags : l'historique
complet de TOUTES les branches. L'entree `refspec` de checkout v4 ne peut
PAS resoudre cela -- elle est IGNOREE par le code de l'action
(`src/git-source-provider.ts` appelle `getRefSpecForAllHistory`, qui
construit `+refs/heads/*:refs/remotes/origin/*` + `tagsRefSpec` ;
`settings.refspec` n'apparait nulle part dans la source de l'action).

Mesure de reference : 19 min de checkout sur 75e21a7fac (job 131524893709,
`curl 28` apres 22:12-22:31Z) et 2 425 s sur le run 43318043479.

Ces tests verrouillent la FORME : profondeur 1 au checkout, puis UN fetch
borne (tete + base) qui approfondit l'historique, puis un controle qui
prouve que l'historique est vraiment lu. Ils rougissent si quelqu'un
reintroduit `fetch-depth: 0` dans ces deux workflows.
"""

from __future__ import annotations

from pathlib import Path

import pytest
import yaml

REPO_ROOT = Path(__file__).resolve().parents[2]
WORKFLOWS = {
    "scripts-tests.yml": "scripts-tests",
    "always-on-guards.yml": "always-on-guards",
}


def _load(name: str) -> dict:
    path = REPO_ROOT / ".github" / "workflows" / name
    return yaml.safe_load(path.read_text(encoding="utf-8"))


def _steps(workflow: str, job: str) -> list[dict]:
    data = _load(workflow)
    return list(data["jobs"][job].get("steps") or [])


def _checkouts(steps: list[dict]) -> list[dict]:
    return [s for s in steps if str(s.get("uses") or "").startswith("actions/checkout")]


def _fetch_steps(steps: list[dict]) -> list[dict]:
    """Les etapes dont le script lance un `git fetch`."""
    out = []
    for step in steps:
        run = str(step.get("run") or "")
        if "git fetch" in run:
            out.append(step)
    return out


@pytest.mark.parametrize("workflow,job", sorted(WORKFLOWS.items()))
def test_checkout_ne_tire_plus_toutes_les_branches(workflow: str, job: str) -> None:
    """Aucun `fetch-depth: 0` : c'est lui qui tire `+refs/heads/*`."""
    steps = _steps(workflow, job)
    checkouts = _checkouts(steps)
    assert checkouts, "le workflow ne doit pas perdre son checkout"
    for step in checkouts:
        depth = (step.get("with") or {}).get("fetch-depth")
        assert depth is not None, f"{workflow}: checkout sans fetch-depth explicite"
        assert str(depth) != "0", (
            f"{workflow}: `fetch-depth: 0` fait tirer l'historique complet de "
            "TOUTES les branches (1606) -- le fetch borne le remplace"
        )
        # Le clone partiel (blobs laisses en paresseux) reste : les organes
        # metadata n'ont besoin que de l'arbre, pas des blobs.
        assert str((step.get("with") or {}).get("filter")) == "blob:none"


@pytest.mark.parametrize("workflow,job", sorted(WORKFLOWS.items()))
def test_un_fetch_borne_approfondit_la_tete_et_la_base(workflow: str, job: str) -> None:
    """Un fetch elargit l'historique a la TETE et a la BASE, et a rien d'autre."""
    steps = _steps(workflow, job)
    bounded = []
    for step in _fetch_steps(steps):
        run = str(step.get("run") or "")
        if "+refs/heads/main:refs/remotes/origin/main" in run:
            bounded.append(run)
    assert bounded, (
        f"{workflow}: aucun fetch de `refs/heads/main` -- sans la base, le "
        "fast-lane ne calcule pas de merge-base"
    )
    for run in bounded:
        assert "--unshallow" in run, (
            f"{workflow}: le fetch doit etre `--unshallow` (ou l'historique "
            "reste superficiel et le walk des ancetres est tronque)"
        )
        assert "refs/remotes/origin/tete" in run, (
            f"{workflow}: le fetch doit couvrir la tete (ascendance complete)"
        )
        # Le piege que la forme doit eviter : un fetch SANS refspec tire
        # `+refs/heads/*` -- c'est-a-dire les 1606 branches.
        assert "+refs/heads/*" not in run


@pytest.mark.parametrize("workflow,job", sorted(WORKFLOWS.items()))
def test_un_controle_prouve_que_l_historique_est_lu(workflow: str, job: str) -> None:
    """Un controle explicite verifie la base ET la profondeur de l'historique."""
    steps = _steps(workflow, job)
    controls = [
        str(s.get("run") or "")
        for s in steps
        if "git merge-base origin/main HEAD" in str(s.get("run") or "")
    ]
    assert controls, f"{workflow}: aucun controle de la base (merge-base)"
    for run in controls:
        assert "git rev-list --count" in run, (
            f"{workflow}: le controle doit compter les commits de l'ascendance "
            "de la base -- une base presente mais tronquee ne suffit pas"
        )
        assert "exit 1" in run, f"{workflow}: le controle doit etre bloquant"


def test_scripts_tests_ne_fait_plus_de_unshallow_de_toutes_les_branches() -> None:
    """Le HEAL ne doit plus lancer `git fetch --unshallow origin` SANS refspec.

    C'etait le chemin des 19 min sur 75e21a7fac : le work dir reutilise etait
    superficiel, et le HEAL elargissait le depot entier avant le checkout.
    """
    steps = _steps("scripts-tests.yml", "scripts-tests")
    for step in _fetch_steps(steps):
        run = str((step.get("with") or {}).get("run") or "")
        for line in run.splitlines():
            stripped = line.strip()
            if stripped.startswith("git fetch --unshallow") and "+" not in stripped:
                pytest.fail(
                    "scripts-tests.yml : `git fetch --unshallow origin` sans "
                    "refspec tire l'historique des 1606 branches -- la tranche "
                    "T-K le remplace par un fetch borne"
                )
