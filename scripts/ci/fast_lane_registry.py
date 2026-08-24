"""Registre des gardes de la VOIE RAPIDE (#11835).

Motivation mesuree (2026-08-19) : dans les workflows de garde de ce depot,
`actions/checkout` represente **89 a 99 %** du temps d'execution, et l'analyse
elle-meme 1 a 5 secondes -- parce que le depot pese 2,1 Go et que 46 workflows
le clonent avec `fetch-depth: 0`. Chaque garde qui lit trois lignes de diff
paie donc un clone integral.

    Cell-order gate        checkout 225,5 s   travail  ~1 s   99,1 %
    Notebook Navlink       checkout 172,0 s   travail   3 s   98,0 %
    prose-counts-guard     checkout 122,0 s   travail   1 s   98,4 %
    banner-guard           checkout 121,5 s   travail   2 s   97,2 %
    perimeter-review       checkout  64,0 s   travail   2 s   94,8 %
    solution-leak          checkout  63,5 s   travail 5,5 s   89,4 %

La voie rapide paie **un** checkout puis enchaine les analyses dans le meme
job, en emettant **un check-run nomme par garde** via l'API Checks : la
granularite visible sur la PR est preservee (protection de branche, surfaces
de review B.0), seule l'infrastructure est mutualisee.

Ce module ne contient QUE des donnees : la mecanique est dans `fast_lane.py`,
ce qui rend le registre lisible et testable sans executer quoi que ce soit.
"""

from __future__ import annotations

from dataclasses import dataclass, field


@dataclass(frozen=True)
class Guard:
    """Un garde de la voie rapide.

    name        Nom EXACT du check-run emis. En phase pilote il est prefixe
                par `shadow_prefix` (cf fast_lane.py) pour cohabiter avec le
                workflow d'origine sans lui voler son nom.
    paths       Globs (syntaxe fnmatch, evaluee sur des chemins POSIX
                relatifs a la racine). Vide = le garde tourne toujours.
                Reproduit le bloc `paths:` du workflow d'origine -- la
                difference est qu'ici c'est du code, donc testable.
                Si `iterates_paths=True`, le garde recoit la liste des
                fichiers qui matchent ces globs et est execute UNE FOIS PAR
                fichier (le placeholder `{changed_paths}` dans `argv` est
                alors substitue par un chemin a la fois).
    argv        Commande a executer, deja decoupee (pas de shell : un shell
                introduirait une seconde couche de quoting sur des chemins
                qui viennent du diff).
    blocking    True  -> un echec doit rougir la PR (conclusion `failure`).
                False -> advisory : le verdict est publie, jamais bloquant
                (conclusion `neutral`), conformement au caractere annonce du
                workflow d'origine. Neutraliser un advisory en `success`
                effacerait le signal ; le rendre `failure` mentirait sur son
                statut.
    needs_base  Le garde compare HEAD a la base : le runner lui garantit que
                `origin/<base_ref>` est joignable.
    delta_argv  Present => le garde est un DELTA en trois temps : `argv` est
                execute sur HEAD (sa sortie standard est capturee comme
                `head.json`), puis sur l'arbre bascule a la base
                (`base.json`), puis `delta_argv` compare les deux. Le
                placeholder `{base_json}` / `{head_json}` y est substitue.
    swap_paths  Sous-arbres a basculer a la base pour la phase 2. Le
                basculement est MUTANT : c'est le seul danger propre a la
                mutualisation d'un job, puisqu'un garde pourrait lire l'arbre
                d'un autre. Le runner y repond par trois mesures -- les
                gardes non-mutants passent tous AVANT, la bascule est faite
                UNE fois pour tous les gardes delta (au lieu d'une par garde
                aujourd'hui), et la restauration est **verifiee** avant de
                rendre le moindre verdict.
    source      Workflow d'origine, pour que la correspondance reste tracable
                quand on retirera le workflow unitaire.
    """

    name: str
    argv: list[str]
    source: str
    paths: list[str] = field(default_factory=list)
    blocking: bool = True
    needs_base: bool = False
    delta_argv: list[str] = field(default_factory=list)
    swap_paths: list[str] = field(default_factory=list)
    iterates_paths: bool = False  # voir `run_iter` dans fast_lane.py
    absorbed: bool = False  # tranche d'absorption #12567 : nom canonique + conclusion reelle, meme en lane ombre
    # Codes de retour traites comme SUCCES au-dela de 0. Les detecteurs de
    # la serie figure/texte rendent rc=1 sur defaut et rc=2 sur fichier
    # INTROUVABLE (mesure firsthand : un JSON corrompu rend rc=0 avec une
    # NOTE "unreadable"). Leur workflow d'origine ne voit jamais ce cas --
    # il saute les fichiers supprimes (`[ -f "$nb" ] || continue`) -- et le
    # moteur reproduit ce skip ; `warn_rc` est la seconde defense si un
    # chemin echappe au filtre (checkout partiel). Sans lui, la lane serait
    # PLUS stricte que le workflow qu'elle absorbe.
    warn_rc: tuple[int, ...] = ()
    # Commande de PRE-CONTROLE executee avant `argv` (phase 1). Un rc non
    # nul devient le verdict du garde et `argv` n'est PAS execute. Cas
    # d'usage : le self-test du ratchet output-failure, qui dans son
    # workflow d'origine etait un step distinct AVANT le scan -- un
    # detecteur qui ne peut pas prouver qu'il tire est indiscernable d'un
    # detecteur debranche (lecon #11685/#12817). Pas de `bash -c ... &&` :
    # le shell n'est pas resolu pareil selon l'hote (127 mesuré en local
    # Windows) et le registre interdit la seconde couche de quoting.
    pre_argv: list[str] = field(default_factory=list)


# Valeur de `source` pour un garde NE dedoublant aucun workflow unitaire : il
# est ne dans la voie rapide. La distinction compte parce que `source` sert a
# tracer quel workflow pourra etre retire quand la voie rapide sortira de
# l'ombre -- un garde natif n'a pas de jumeau a retirer. Le test qui verifie
# la tracabilite reste STRICT pour les autres : une faute de frappe dans un
# nom de workflow doit continuer d'echouer, seule cette valeur exacte est
# admise comme "pas de workflow d'origine".
FAST_LANE_NATIVE = "(garde natif de la voie rapide : aucun workflow d'origine)"

NOTEBOOK_GLOBS = ["**/*.ipynb"]

# ---------------------------------------------------------------------------
# Lot pilote (#11835). Dix gardes choisis pour couvrir les formes que le
# moteur doit savoir traiter, et non pour leur nombre :
#
#   - banner-guard        : bloquant, scan global, sans base
#   - pip-leak-guard      : bloquant, delta HEAD-vs-base
#   - solution-leak-guard : ADVISORY, delta HEAD-vs-base (verifie qu'un
#                           advisory ne peut pas rougir par accident)
#   - prose-counts-guard  : advisory, diff-range direct
#   - perimeter-review    : bloquant, appelle l'API GitHub (a besoin de
#                           GH_TOKEN, pas seulement de l'arbre)
#   - bare-cross-dir-load-gate : bloquant, EXECUTION PAR FICHIER (Pattern 1)
#   - notebook-navlink-check   : bloquant, scan global
#   - notebook-interp-positioning-guard : bloquant, scan global baselined
#   - markdown-rendering-guard : bloquant, scan global baselined
#   - self-hosted-runner-policy : bloquant, scan statique des workflows
#   - duplicate-notebook-index-guard : bloquant, delta base-vs-head sur
#                           les fichiers AJOUTES (#12753)
#
# Un lot homogene aurait valide le moteur sur un seul cas de figure -- et un
# lot entierement vert serait indiscernable d'un moteur debranche.
# ---------------------------------------------------------------------------
PILOT: list[Guard] = [
    Guard(
        name="banner-guard",
        source="banner-guard.yml",
        paths=NOTEBOOK_GLOBS + [
            "scripts/notebook_tools/strip_probe_banner.py",
            ".github/workflows/banner-guard.yml",
        ],
        argv=[
            "python", "scripts/notebook_tools/strip_probe_banner.py",
            "--scan-all", "--check", "--exclude-submodules",
        ],
        blocking=True,
    ),
    Guard(
        name="pip-leak-guard",
        source="pip-leak-guard.yml",
        paths=NOTEBOOK_GLOBS,
        argv=["python", "scripts/notebook_tools/audit_pip_install_cells.py",
              "--scan-all", "--json"],
        delta_argv=["python", "scripts/notebook_tools/pip_leak_delta.py",
                    "{base_json}", "{head_json}"],
        swap_paths=["MyIA.AI.Notebooks"],
        blocking=True,
        needs_base=True,
    ),
    Guard(
        name="solution-leak-guard",
        source="solution-leak-guard.yml",
        paths=NOTEBOOK_GLOBS,
        argv=["python", "scripts/notebook_tools/audit_solution_leaks.py", "--json"],
        delta_argv=["python", "scripts/notebook_tools/solution_leak_delta.py",
                    "{base_json}", "{head_json}"],
        swap_paths=["MyIA.AI.Notebooks"],
        blocking=False,          # WARN phase (#8053) -- ne rougit jamais
        needs_base=True,
    ),
    Guard(
        name="prose-counts-guard",
        source="prose-counts-guard.yml",
        paths=["**/*.ipynb", "**/*.md"],
        argv=["python", "scripts/notebook_tools/check_prose_quantitative_claims.py",
              "--diff", "{base_ref}...HEAD"],
        blocking=False,          # ADVISORY tant que #9377 n'est pas resorbe
        needs_base=True,
    ),
    Guard(
        name="perimeter-review-guard",
        source="perimeter-review-guard.yml",
        paths=[],                # sans filtre : porte sur le corps de la PR
        argv=["python", "scripts/check_pr_perimeter.py", "{pr_number}",
              "--scan-thread"],
        blocking=True,
    ),
    # -- extension pilote (5 -> 9) ------------------------------------------
    # Pattern 1 : execute une fois par chemin matchant (boucle bash d'origine
    # absorbee). Le placeholder `{changed_paths}` est substitue par un chemin
    # a la fois ; le verdict agrege est failure si l'une des iterations
    # echoue avec un code `failure` (rc=1 pour les detecteurs deterministes).
    Guard(
        name="bare-cross-dir-load-gate",
        source="bare-cross-dir-load-gate.yml",
        paths=NOTEBOOK_GLOBS + [
            "scripts/notebook_tools/detect_bare_cross_dir_load.py",
            ".github/workflows/bare-cross-dir-load-gate.yml",
        ],
        argv=[
            "python", "scripts/notebook_tools/detect_bare_cross_dir_load.py",
            "{changed_paths}", "--check",
        ],
        blocking=True,
        iterates_paths=True,
    ),
    Guard(
        name="notebook-navlink-check",
        source="notebook-navlink-check.yml",
        paths=NOTEBOOK_GLOBS + [
            "scripts/notebook_tools/check_notebook_navlinks.py",
            "scripts/tests/baseline_nb_navlinks.json",
            ".github/workflows/notebook-navlink-check.yml",
        ],
        argv=["python", "scripts/notebook_tools/check_notebook_navlinks.py",
              "--check"],
        blocking=True,
    ),
    Guard(
        name="notebook-interp-positioning-guard",
        source="notebook-interp-positioning.yml",
        paths=NOTEBOOK_GLOBS + [
            "scripts/notebook_tools/check_interp_positioning.py",
            "scripts/notebook_tools/interp_positioning_baseline.json",
            ".github/workflows/notebook-interp-positioning.yml",
        ],
        argv=["python", "scripts/notebook_tools/check_interp_positioning.py",
              "--check",
              "--baseline", "scripts/notebook_tools/interp_positioning_baseline.json"],
        blocking=True,
    ),
    Guard(
        name="markdown-rendering-guard",
        source="markdown-rendering-guard.yml",
        paths=[
            "**/*.ipynb",
            "_quarto.yml",
            "scripts/notebook_tools/detect_markdown_rendering.py",
            "scripts/notebook_tools/scan_md_hierarchy.py",
            "scripts/notebook_tools/markdown_rendering_baseline.json",
            ".github/workflows/markdown-rendering-guard.yml",
        ],
        argv=["python", "scripts/notebook_tools/detect_markdown_rendering.py",
              "--check",
              "--baseline",
              "scripts/notebook_tools/markdown_rendering_baseline.json"],
        blocking=True,
    ),
    Guard(
        name="self-hosted-runner-policy",
        source="fast-lane-shadow.yml",
        paths=[
            ".github/workflows/*.yml",
            ".github/workflows/*.yaml",
            "scripts/ci/check_self_hosted_runner_policy.py",
            "scripts/tests/test_check_self_hosted_runner_policy.py",
            "scripts/ci/fast_lane_registry.py",
        ],
        argv=["python", "scripts/ci/check_self_hosted_runner_policy.py",
              "--check"],
        blocking=True,
    ),
    # -- extension c.1339 (10 -> 11) ----------------------------------------
    # Ferme un angle mort du merge-gate mesure le 2026-08-24 (#12753) : aucun
    # garde ne demandait si le contenu AJOUTE existe deja sur la base sous un
    # AUTRE nom de fichier. Deux notebooks `3.1-*` de la meme lane, cites par
    # la meme issue, ont ete merges a 29 minutes d'intervalle sans qu'aucune
    # des cinq portes (nits, perimetre, H.4, tag de grain, cap de variation)
    # n'ait de quoi le voir : chacune juge la PR en elle-meme, aucune ne la
    # confronte a ce que la base porte deja.
    #
    # Porte aux fichiers AJOUTES seulement. C'est ce qui le rend vert sur le
    # `main` d'aujourd'hui -- qui porte deja deux collisions (index 3.1 et
    # index 22, cf #12753) -- tout en empechant la recurrence. Un garde qui
    # accuserait la dette pre-existante serait rouge des sa naissance et
    # ferait echouer toutes les PR sans qu'aucune ne l'ait causee.
    Guard(
        name="duplicate-notebook-index-guard",
        source=FAST_LANE_NATIVE,
        paths=NOTEBOOK_GLOBS + [
            "scripts/notebook_tools/check_duplicate_notebook_index.py",
        ],
        argv=["python", "scripts/notebook_tools/check_duplicate_notebook_index.py",
              "--base", "{base_ref}", "--head", "HEAD"],
        blocking=True,
        needs_base=True,
    ),
]


# ---------------------------------------------------------------------------
# TRANCHE 1 d'absorption (#12567) -- le basculement, second geste announce
# par la phase pilote : ces gardes passent DIRECTEMENT en mode canonique
# (nom exact du check-run d'origine, conclusion reelle qui peut rougir), et
# leurs workflows dedis perdent le declenchement `pull_request` dans la meme
# PR -- le fichier source reste pour push/dispatch.
#
# `absorbed=True` est ce qui distingue la tranche du pilote : le moteur
# emet le nom SANS prefixe ombre et la conclusion NON neutralisee, meme quand
# le reste de la lane tourne en ombre. Le check-run portant le nom original,
# le rollup de la PR est identique a ce que produisait le workflow dedie.
#
# Contrainte de design tranchee par ai-01 (DM 2026-08-26T05:04Z) : chaque
# garde absorbe CONSERVE son nom de check-run, et `PR gate` -- seul check
# requis -- reste non filtre.
#
# Choix de la tranche : trois formes moteur distinctes (scan global simple,
# scan globs serie, delta base-vs-head), aucun besoin d'ecriture PR, aucune
# dependance au-dela de python stdlib -- le pip install pyyaml/Pillow du job
# couvre deja tout ce que ces trois gardes demandent.
# ---------------------------------------------------------------------------
TRANCHE1: list[Guard] = [
    # Forme 1 : scan global simple, sans base. Source : docs-link-check.yml
    # (job `check-links`). Le nom du garde est le nom du JOB, pas celui du
    # workflow -- c'est lui que le rollup affichait.
    Guard(
        name="check-links",
        source="docs-link-check.yml",
        paths=[
            "CLAUDE.md", "index.md", "PARCOURS.md",
            ".claude/rules/**", "docs/**", "**/README.md",
            "scripts/check_docs_links.py",
        ],
        argv=["python", "scripts/check_docs_links.py", "--check"],
        blocking=True,
        absorbed=True,
    ),
    # Forme 2 : scan globs, bloque sur convention zero-pad GameTheory
    # (#11840/#12586). Source : series-naming-gate.yml (job affiche
    # `zero-pad guard (GameTheory serie)`).
    Guard(
        name="zero-pad guard (GameTheory serie)",
        source="series-naming-gate.yml",
        paths=[
            "MyIA.AI.Notebooks/GameTheory/**",
            "scripts/notebook_tools/check_series_zero_pad.py",
            ".github/workflows/series-naming-gate.yml",
        ],
        argv=["python", "scripts/notebook_tools/check_series_zero_pad.py"],
        blocking=True,
        absorbed=True,
    ),
    # Forme 3 : delta base-vs-head -- meme motif que pip-leak-guard pilote :
    # scan HEAD capture, bascule MyIA.AI.Notebooks vers la base, scan BASE,
    # restauration verifyee, puis delta. Source : exercise-leak-ci.yml (job
    # `Exercice-solution HIGH delta guard (#8053)`). Rouge seulement sur les
    # NOUVEAUX leaks HIGH -- les herites sont tolere's (#8053).
    Guard(
        name="Exercice-solution HIGH delta guard (#8053)",
        source="exercise-leak-ci.yml",
        paths=[
            "MyIA.AI.Notebooks/**/*.ipynb",
            "scripts/notebook_tools/detect_solution_leaks.py",
            "scripts/notebook_tools/exercise_leak_delta.py",
            ".github/workflows/exercise-leak-ci.yml",
        ],
        argv=["python", "scripts/notebook_tools/detect_solution_leaks.py",
              "--scan-all"],
        delta_argv=["python",
                    "scripts/notebook_tools/exercise_leak_delta.py",
                    "{base_json}", "{head_json}"],
        swap_paths=["MyIA.AI.Notebooks"],
        blocking=True,
        needs_base=True,
        absorbed=True,
    ),
]


# ---------------------------------------------------------------------------
# TRANCHE 2 d'absorption (#12567) -- meme contrat que la tranche 1 (nom
# canonique, conclusion reelle, workflow d'origine retire de pull_request),
# trois formes moteur nouvelles par rapport a la tranche 1 :
#
#   - ratchet AUTONOME : le script fait lui-meme son diff base...HEAD, la lane
#     ne fournit que {base_ref}. Son self-test est un PRE-CONTROLE (`pre_argv`)
#     qui gate le garde comme le step distinct du workflow d'origine -- sans
#     shell, resolu identiquement sur tout hote.
#   - iter_paths + warn_rc : boucle par notebook change, rc=1 defaut / rc=2
#     introuvable (skip dans l'original, donc warn_rc=(2,) en defense
#     seconde, cf docstring du champ).
#   - iter_paths + dependance Pillow : deja installee par le job lane.
#
# Fidelite aux boucles d'origine : les fichiers SUPPRIMES par la PR sont
# sautes (`[ -f "$nb" ] || continue` dans l'original) -- le moteur filtre
# les arg_paths inexistants.
# ---------------------------------------------------------------------------
TRANCHE2: list[Guard] = [
    # Forme 1 : ratchet autonome binaire (exit 0/1), PRE-CONTROLE self-test
    # (les deux steps du workflow d'origine, sans shell).
    # Source : notebook-output-failure-ratchet.yml (job `ratchet`).
    Guard(
        name="Output-failure ratchet (base vs PR)",
        source="notebook-output-failure-ratchet.yml",
        paths=[
            "**.ipynb",
            "scripts/notebook_tools/check_output_failure_text.py",
            ".github/workflows/notebook-output-failure-ratchet.yml",
        ],
        pre_argv=[
            "python", "scripts/notebook_tools/check_output_failure_text.py",
            "--self-test",
        ],
        argv=[
            "python", "scripts/notebook_tools/check_output_failure_text.py",
            "{base_ref}",
        ],
        blocking=True,
        needs_base=True,
        absorbed=True,
    ),
    # Forme 2 : iter par notebook change, rc=1 defaut / rc=2 illisible.
    # Source : fabricated-output-gate.yml (job `fabricated-output`).
    Guard(
        name="No fabricated text output in changed notebooks",
        source="fabricated-output-gate.yml",
        paths=[
            "MyIA.AI.Notebooks/**/*.ipynb",
            "scripts/notebook_tools/detect_fabricated_outputs.py",
            ".github/workflows/fabricated-output-gate.yml",
        ],
        argv=[
            "python", "scripts/notebook_tools/detect_fabricated_outputs.py",
            "--check", "{changed_paths}",
        ],
        blocking=True,
        iterates_paths=True,
        absorbed=True,
        warn_rc=(2,),
    ),
    # Forme 3 : iter par notebook change + Pillow (deja dans le job lane).
    # Source : degenerate-figure-gate.yml (job `degenerate-figure`).
    Guard(
        name="No degenerate figure in changed notebooks",
        source="degenerate-figure-gate.yml",
        paths=[
            "MyIA.AI.Notebooks/**/*.ipynb",
            "scripts/notebook_tools/detect_blank_figures.py",
            ".github/workflows/degenerate-figure-gate.yml",
        ],
        argv=[
            "python", "scripts/notebook_tools/detect_blank_figures.py",
            "--check", "{changed_paths}",
        ],
        blocking=True,
        iterates_paths=True,
        absorbed=True,
        warn_rc=(2,),
    ),
]
