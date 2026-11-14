"""T-K (#25510) : le checkout du job Scripts Tests ne tire plus les 1 606 branches.

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
reintroduit `fetch-depth: 0` dans le job `scripts-tests`.

**Perimetre restreint au job `scripts-tests` (arbitrage coordinateur du
2026-11-13).** La jambe `always-on-guards` garde son `fetch-depth: 0` :
elle tourne sur `ubuntu-latest` avec un work dir NEUF (116 s mesurees
contre 58 s de mediane avant sur le pool self-hosted partage), et
`always-on-guards.yml` n'est pas dans le scope de cette PR. Le contrat
borne porte donc sur `scripts-tests.yml` seul -- et le test
`test_la_jambe_always_on_guards_garde_son_fetch_depth_0` verrouille
l'exception, pour qu'elle soit visible et non silencieuse.
"""

from __future__ import annotations

from pathlib import Path

import pytest
import yaml

REPO_ROOT = Path(__file__).resolve().parents[2]
WORKFLOW = "scripts-tests.yml"
JOB = "scripts-tests"
#: L'etape HEAL : c'est la que le geste `git fetch --unshallow` SANS
#: refspec avait ete installe (le chemin des 19 min).
HEAL_NAME = "Purger un work dir reutilise au graphe incomplet"


def _load(name: str) -> dict:
    path = REPO_ROOT / ".github" / "workflows" / name
    return yaml.safe_load(path.read_text(encoding="utf-8"))


def _steps(workflow: str, job: str) -> list[dict]:
    data = _load(workflow)
    return list(data["jobs"][job].get("steps") or [])


def _checkouts(steps: list[dict]) -> list[dict]:
    return [s for s in steps if str(s.get("uses") or "").startswith("actions/checkout")]


def _fetch_steps(steps: list[dict]) -> list[dict]:
    """Les etapes dont le script lance un `git fetch`.

    `run` est une CLE de l'etape, pas une entree de `with` : chercher
    `with.run` lit toujours vide et le detecteur devient muet.
    """
    out = []
    for step in steps:
        run = str(step.get("run") or "")
        if "git fetch" in run:
            out.append(step)
    return out


def _unbounded_unshallow_lines(steps: list[dict]) -> list[str]:
    """Les lignes de fetch `--unshallow` SANS refspec, dans tout le workflow.

    Un `git fetch --unshallow origin` sans refspec tire `+refs/heads/*` :
    l'historique complet des 1 606 branches. C'est le geste que la
    tranche T-K retire, et que ce detecteur doit etre capable de
    retrouver -- y compris quand on le REINJECTE (controle negatif).
    """
    out: list[str] = []
    for step in steps:
        run = str(step.get("run") or "")
        for line in run.splitlines():
            stripped = line.strip()
            if stripped.startswith("git fetch --unshallow") and "+" not in stripped:
                out.append(stripped)
    return out


def test_checkout_ne_tire_plus_toutes_les_branches() -> None:
    """Aucun `fetch-depth: 0` : c'est lui qui tire `+refs/heads/*`."""
    steps = _steps(WORKFLOW, JOB)
    checkouts = _checkouts(steps)
    assert checkouts, "le workflow ne doit pas perdre son checkout"
    for step in checkouts:
        depth = (step.get("with") or {}).get("fetch-depth")
        assert depth is not None, f"{WORKFLOW}: checkout sans fetch-depth explicite"
        assert str(depth) != "0", (
            f"{WORKFLOW}: `fetch-depth: 0` fait tirer l'historique complet de "
            "TOUTES les branches (1606) -- le fetch borne le remplace"
        )
        # Le clone partiel (blobs laisses en paresseux) reste : les organes
        # metadata n'ont besoin que de l'arbre, pas des blobs.
        assert str((step.get("with") or {}).get("filter")) == "blob:none"


def test_un_fetch_borne_approfondit_la_tete_et_la_base() -> None:
    """Un fetch elargit l'historique a la TETE et a la BASE, et a rien d'autre."""
    steps = _steps(WORKFLOW, JOB)
    bounded = []
    for step in _fetch_steps(steps):
        run = str(step.get("run") or "")
        if "+refs/heads/main:refs/remotes/origin/main" in run:
            bounded.append(run)
    assert bounded, (
        f"{WORKFLOW}: aucun fetch de `refs/heads/main` -- sans la base, le "
        "fast-lane ne calcule pas de merge-base"
    )
    for run in bounded:
        assert "--unshallow" in run, (
            f"{WORKFLOW}: le fetch doit etre `--unshallow` (ou l'historique "
            "reste superficiel et le walk des ancetres est tronque)"
        )
        assert "refs/remotes/origin/tete" in run, (
            f"{WORKFLOW}: le fetch doit couvrir la tete (ascendance complete)"
        )
        # Le piege que la forme doit eviter : un fetch SANS refspec tire
        # `+refs/heads/*` -- c'est-a-dire les 1606 branches.
        assert "+refs/heads/*" not in run


def test_un_controle_prouve_que_l_historique_est_lu() -> None:
    """Un controle explicite verifie la base ET la profondeur de l'historique."""
    steps = _steps(WORKFLOW, JOB)
    controls = [
        str(s.get("run") or "")
        for s in steps
        if "git merge-base origin/main HEAD" in str(s.get("run") or "")
    ]
    assert controls, f"{WORKFLOW}: aucun controle de la base (merge-base)"
    for run in controls:
        assert "git rev-list --count" in run, (
            f"{WORKFLOW}: le controle doit compter les commits de l'ascendance "
            "de la base -- une base presente mais tronquee ne suffit pas"
        )
        assert "exit 1" in run, f"{WORKFLOW}: le controle doit etre bloquant"


def test_le_heal_ne_declenche_plus_de_fetch_sans_refspec() -> None:
    """Le HEAL ne doit plus lancer `git fetch --unshallow origin` SANS refspec.

    C'etait le chemin des 19 min sur 75e21a7fac : le work dir reutilise etait
    superficiel, et le HEAL elargissait le depot entier avant le checkout.
    """
    assert _unbounded_unshallow_lines(_steps(WORKFLOW, JOB)) == []


def test_le_controle_negatif_detecte_le_geste_reinjecte() -> None:
    """CONTROLE NEGATIF : le detecteur voit le geste quand on le REINJECTE.

    Sans ce test, le detecteur pourrait etre vide par construction (un
    motif qui ne matche jamais) et le test precedent resterait vert
    pour la mauvaise raison. On rejoue donc le geste historique
    (`git fetch --unshallow origin`, sans refspec) dans le HEAL, sur une
    COPIE des etapes, et on exige que le detecteur le retrouve.
    """
    steps = _steps(WORKFLOW, JOB)
    mutes = [dict(s) for s in steps]
    touche = 0
    for step in mutes:
        if HEAL_NAME in str(step.get("name") or ""):
            step["run"] = str(step.get("run") or "") + "\ngit fetch --unshallow origin\n"
            touche += 1
    assert touche == 1, f"{WORKFLOW}: etape HEAL introuvable ({touche} trouvee(s))"
    assert _unbounded_unshallow_lines(mutes) == ["git fetch --unshallow origin"]


def test_la_jambe_always_on_guards_garde_son_fetch_depth_0() -> None:
    """L'EXCEPTION est visible : `always-on-guards` garde `fetch-depth: 0`.

    Arbitrage coordinateur du 2026-11-13 : la jambe `always-on-guards`
    tourne sur `ubuntu-latest` avec un work dir NEUF (116 s mesurees contre
    58 s de mediane avant sur le pool self-hosted partage) ; elle n'est pas
    dans le scope de la tranche T-K. Ce test verrouille l'exception, pour
    qu'un jour ou l'on elargit le contrat a cette jambe, ce soit une
    decision mesuree et non un effet de bord.
    """
    steps = _steps("always-on-guards.yml", "always-on-guards")
    checkouts = _checkouts(steps)
    assert checkouts, "always-on-guards.yml ne doit pas perdre son checkout"
    depths = [str((s.get("with") or {}).get("fetch-depth")) for s in checkouts]
    assert "0" in depths, (
        "always-on-guards.yml : le `fetch-depth: 0` fait partie de l'arbitrage "
        "coordinateur du 2026-11-13 -- sa suppression doit etre une decision "
        "mesuree (duree de la jambe sur ubuntu-latest), pas un effet de bord"
    )
