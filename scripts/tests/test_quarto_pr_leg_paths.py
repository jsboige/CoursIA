"""P4 #25510 (fournée 1) : la validation Quarto par-PR ne couvre plus le contenu.

Deux invariants, une seule classe de correction -- retirer les re-executions
redondantes de la voie par-PR, sign-off mainteneur du 2026-11-14 :

1. ``quarto-pages-deploy.yml`` : la voie ``pull_request`` ne se déclenche
   plus sur les surfaces de CONTENU du site (``MyIA.AI.Notebooks/**/*.ipynb``,
   ``**/_output.ipynb``, ``**/README.md``, ``docs/**``). Mesure du
   2026-11-14 sur 24 h : 237 runs ``pull_request`` pour un rendu que le push
   de merge rejoue en complet sur l'arbre reel. Les surfaces qui PILOTENT le
   rendu (``_quarto.yml``, scripts, ce workflow, catalogue) gardent leur
   validation par-PR (#14391, #15490, #14429).

2. ``site-links-post-deploy.yml`` : le garde des liens du site publié ne se
   déclenche que sur les DÉPLOIEMENTS réels (``workflow_run.event == 'push'``).
   Mesure du 2026-11-14 sur 24 h : 300 runs, dont 105 échecs, tirés par des
   complétions de jambes PR qui ne déploient rien.

Ces tests verrouillent la forme : ils rougissent si un path de contenu
revient dans le filtre PR de Quarto, ou si la porte événement de site-links
disparaît. Le verrou sur les chemins conservés (#14391 etc.) est tout aussi
important : une suppression du filtre entier (voire du trigger) casserait
l'auto-couverture mesurée par ces issues.
"""

from __future__ import annotations

from pathlib import Path

import yaml

REPO_ROOT = Path(__file__).resolve().parents[2]
WORKFLOWS = REPO_ROOT / ".github" / "workflows"

#: Paths de CONTENU : présents dans le filtre `push` (le rendu complet du
#: merge les vérifie), interdits dans le filtre `pull_request` depuis P4.
CONTENT_PATHS = [
    "MyIA.AI.Notebooks/**/*.ipynb",
    "MyIA.AI.Notebooks/**/_output.ipynb",
    "MyIA.AI.Notebooks/**/README.md",
    "docs/**",
]

#: Paths PILOTANTS : le retrait de l'un d'eux rouvrirait l'incident que la
#: ligne cite (#14391 auto-couverture, #15490 catalog-cron, #14429 smoke).
PILOTING_PATHS = [
    "_quarto.yml",
    "**.qmd",
    "MyIA.AI.Notebooks/**/index.qmd",
    ".github/workflows/quarto-pages-deploy.yml",
    "scripts/ci/quarto_yaml_safe.py",
    "COURSE_CATALOG.generated.md",
    "scripts/ci/quarto_render_scope.py",
    "scripts/ci/quarto_site_link_targets.py",
    "scripts/ci/quarto_readme_titles.py",
    "scripts/ci/tests/test_quarto_readme_titles.py",
]


def _quarto() -> dict:
    return yaml.safe_load(
        (WORKFLOWS / "quarto-pages-deploy.yml").read_text(encoding="utf-8")
    )


def _site_links() -> dict:
    return yaml.safe_load(
        (WORKFLOWS / "site-links-post-deploy.yml").read_text(encoding="utf-8")
    )


# ---------------------------------------------------------------------------
# 1. Quarto : la voie PR ne couvre plus le contenu, elle garde les pilotes.
# ---------------------------------------------------------------------------


def test_la_voie_pr_ne_declenche_plus_sur_le_contenu():
    """Chaque path de contenu retiré rouvrirait ~230 runs/jour (mesure 14/11)."""
    # yaml.safe_load lit `on:` comme la clé booléenne True (YAML 1.1).
    on = _quarto()[True]
    pr_paths = on["pull_request"]["paths"]
    for path in CONTENT_PATHS:
        assert path not in pr_paths, (
            f"le path de contenu {path!r} est revenu dans le filtre "
            f"pull_request de quarto-pages-deploy.yml : c'est la surface "
            f"que P4 #25510 a retiree (237 runs/24 h mesures le 2026-11-14), "
            f"verifiee depuis par le rendu complet du push main."
        )


def test_les_surfaces_pilotantes_gardent_la_voie_pr():
    """Le filtre PR garde config, scripts, workflow et catalogue (#14391...)."""
    on = _quarto()[True]
    pr_paths = on["pull_request"]["paths"]
    for path in PILOTING_PATHS:
        assert path in pr_paths, (
            f"le path pilotant {path!r} a disparu du filtre pull_request : "
            f"une PR qui ne touche QUE ce fichier ne validerait plus son "
            f"propre rendu (auto-couverture #14391/#15490/#14429)."
        )


def test_la_voie_push_garde_le_contenu():
    """Le rendu complet du merge reste le vérificateur du contenu."""
    on = _quarto()[True]
    push_paths = on["push"]["paths"]
    for path in [
        "MyIA.AI.Notebooks/**/*.ipynb",
        "MyIA.AI.Notebooks/**/README.md",
        "docs/**",
    ]:
        assert path in push_paths, (
            f"le path {path!r} a disparu du filtre push : le contenu ne "
            f"serait plus verifie nulle part."
        )


# ---------------------------------------------------------------------------
# 2. site-links : la garde ne se déclenche que sur un déploiement réel.
# ---------------------------------------------------------------------------


def test_la_garde_site_links_exige_un_deploiement():
    """Le if du job porte la porte événement `workflow_run.event == 'push'`.

    On lit le texte du workflow, pas l'AST de l'expression : la condition est
    une expression GitHub Actions que yaml.safe_load rend comme une chaîne --
    le test verrouille les DEUX membres (event push, conclusion success) et
    le repli workflow_dispatch.
    """
    text = (WORKFLOWS / "site-links-post-deploy.yml").read_text(encoding="utf-8")
    assert "github.event.workflow_run.event == 'push'" in text, (
        "la porte evenement du garde site-links a disparu : le declencheur "
        "workflow_run tire sur chaque completion de Quarto Pages Deploy, "
        "jambes PR comprises, qui ne deploient rien (300 runs/24 h dont 105 "
        "echecs, mesures le 2026-11-14)."
    )
    assert "github.event.workflow_run.conclusion == 'success'" in text, (
        "la porte de conclusion a disparu : tester un ancien site apres un "
        "deploy echoue produirait un verdict qui ne parle pas de la sortie "
        "reelle."
    )
    assert "github.event_name == 'workflow_dispatch'" in text, (
        "le repli manuel (re-mesure volontaire du site publie) a disparu."
    )


def test_le_trigger_site_links_reste_workflow_run():
    """L'organe reste un observateur post-déploiement, pas une garde de PR."""
    on = _site_links()[True]
    assert "workflow_run" in on, "le declencheur workflow_run a disparu"
    assert "pull_request" not in on and "push" not in on, (
        "site-links-post-deploy est advisory PAR CONSTRUCTION : aucun "
        "declencheur de PR ne doit apparaitre."
    )
