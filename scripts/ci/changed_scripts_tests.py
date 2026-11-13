#!/usr/bin/env python3
"""Portee du job Scripts Tests (CPU) : suites liees aux chemins modifies (#22468 tranche 4).

Mesure de l'issue (levier 6 de l'audit CI #22461) : le job Scripts Tests
(CPU) joue ses ~38 suites (~21 000 tests, 15,8-17,4 min mesures sur main le
2026-11-11) sur TOUTE PR qui touche un chemin de son filtre -- y compris la
PR qui edite un seul organe d'une seule suite. Les suites non modifiees ont
deja leur verdict vert sur main : le rejouer ne produit aucune information
nouvelle et consomme un slot du pool auto-heberge partage.

## Ce que cet organe rend

Un JSON sur stdout : ``{"mode": "restricted"|"full", "suites": [...],
"reason": "..."}``. ``suites`` est TOUJOURS une sous-liste ordonnee de la
liste du workflow (mode full = la liste entiere) : le pas CI consomme
``suites`` tel quel. La raison est toujours nommee -- un repli muet vers la
pleine suite annulerait le gain sans laisser de trace lisible.

## Contrat : fail-OPEN vers la pleine suite

Toute incertitude rend la **pleine suite** : lecteur de diff en echec, PR
introuvable, portee restreinte vide, delegation hors table en echec. Se
tromper dans ce sens coute du calcul ; se tromper dans l'autre valide moins
que declenche.

## Chemins hors table : delegation a l'organe natif (#25510)

Un chemin hors de toute aire de veille ne rend plus la pleine suite : la
selection est deleguee a ``select_tests.select`` (P2, #25520), dont la regle
R4 (portee depot) couvre par construction tout changement. Le filet qui
borne les trous de la delegation est le lot quatre fois par jour (P3,
``slow-lane.yml``), qui joue la liste complete sur l'arbre d'integration --
le controle positif #25510 en est le temoin.

Seule exception, assumee bruyante (rc 2, meme semantique que guard_test_root
#19026) : le bloc pytest du workflow illisible -- l'organe ne peut meme plus
enumerer la pleine suite, un repli silencieux serait une liste INVENTEE.

## Ou vivent les listes (source unique)

- **La liste des suites** est lue depuis le workflow par
  ``guard_test_root.parse_collected_paths`` -- le meme parseur que la garde
  anti-recidive #18888. Une suite ajoutee au workflow est automatiquement
  couverte ici (aire de veille derivee, ci-dessous) sans edition de cet
  organe.
- **L'aire de veille** de chaque suite ``X/tests`` est son dossier parent
  ``X/`` (naturel : la suite de ``scripts/sudoku`` veille ``scripts/sudoku``).
  Les suites fichiers (carnets de contrat isoles) et la suite racine
  ``tests`` portent des aires explicites dans ``WATCH_OVERRIDES``.

## Ce qui force la pleine suite (garde-fou de la tranche)

Un vert restreint ne vaut que si la clee couvre tout ce qui influe sur le
verdict (#22468) : le workflow lui-meme, ``pytest.ini``, tout ``conftest.py``,
le script d'install, le chien de garde xdist et cet organe. Le registre
``arxiv_attributions_registry.yaml`` est relu par la suite generique
``scripts/tests`` (#17850) : il la selectionne.

## Organ-first : lecteurs herites de #22548

Les lecteurs de chemins modifies viennent de ``codeql_changed_languages``
(diff local primaire sur le checkout de fusion, API en repli paginee) --
meme heritage que la tranche 2 (``changed_notebooks``). Pas de duplication.

## workflow_dispatch reste pleine suite (intentionnel)

Le declencheur manuel existe pour revalider l'ensemble apres un lot de
fusions : le restreindre casserait sa raison d'etre.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
from pathlib import Path
from typing import Callable

try:
    from codeql_changed_languages import (  # type: ignore[attr-defined]
        _api_pr_paths,
        _describe,
        _local_diff_paths,
    )
    from guard_test_root import parse_collected_paths
    from select_tests import select as _select_native
except ImportError:  # chargement par spec_from_file_location (tests)
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from codeql_changed_languages import (  # noqa: E402
        _api_pr_paths,
        _describe,
        _local_diff_paths,
    )
    from guard_test_root import parse_collected_paths  # noqa: E402
    from select_tests import select as _select_native  # noqa: E402

Reader = Callable[[str], list[str]]

REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_WORKFLOW = REPO_ROOT / ".github" / "workflows" / "scripts-tests.yml"

# Garde-fou de la tranche : tout chemin qui influence le verdict SANS passer
# par une suite precise force la pleine suite. Prefixes (dossiers) et chemins
# exacts.
FULL_TRIGGERS: tuple[str, ...] = (
    ".github/workflows/",   # le verdict produit par le workflow lui-meme
    "scripts/ci/install_scripts_tests_deps.sh",  # l'env du verdict
    "scripts/ci/xdist_watchdog.py",             # le chien de garde du run
    "scripts/ci/changed_scripts_tests.py",      # cet organe (auto-veille)
    "scripts/ci/guard_test_root.py",            # lit ce workflow : derive = verdict derive
    "scripts/ci/select_tests.py",               # organe de la delegation hors table (#25510)
)
FULL_BASENAMES: frozenset[str] = frozenset({"conftest.py", "pytest.ini"})

# Aires de veille explicites pour les suites que la derivation parent-dir ne
# couvre pas : la suite racine ``tests`` (son parent serait le depot entier)
# et les suites fichiers (carnets de contrat isoles par env, #22735/#15058).
AGENT_TESTS = "MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests"
V4 = "MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4"
WATCH_OVERRIDES: dict[str, tuple[str, ...]] = {
    "tests": ("tests/",),
    f"{AGENT_TESTS}/tests/test_bg_tree_lock.py": (f"{AGENT_TESTS}/",),
    f"{AGENT_TESTS}/tests/test_prover_guards.py": (f"{AGENT_TESTS}/",),
    f"{AGENT_TESTS}/tests/test_lean_utils.py": (f"{AGENT_TESTS}/",),
    f"{AGENT_TESTS}/tests/test_prover_forensic_guards.py": (f"{AGENT_TESTS}/",),
    f"{AGENT_TESTS}/tests/test_provider_gate_18709.py": (f"{AGENT_TESTS}/",),
    f"{V4}/prosody_lab/test_bake_bank.py": (f"{V4}/",),
    f"{V4}/tests/test_p5_narrator_routing.py": (f"{V4}/",),
    f"{V4}/tests/test_p5_customvoice_narrator.py": (f"{V4}/",),
    f"{V4}/tests/test_qwen_tts_client.py": (f"{V4}/",),
    f"{V4}/tests/test_p2_segment_dedup.py": (f"{V4}/",),
    f"{V4}/tests/test_narration.py": (f"{V4}/",),
    "MyIA.AI.Notebooks/GameTheory/gateway/test_openspiel_cfr_core.py": (
        "MyIA.AI.Notebooks/GameTheory/",),
    "MyIA.AI.Notebooks/SymbolicAI/SMT/Z3-API/gateway/test_z3_sudoku_core.py": (
        "MyIA.AI.Notebooks/SymbolicAI/SMT/Z3-API/",),
    "MyIA.AI.Notebooks/SymbolicAI/SMT/Z3-API/gateway/test_run_gateway.py": (
        "MyIA.AI.Notebooks/SymbolicAI/SMT/Z3-API/",),
}

# Selecteurs additionnels : chemins relus par une suite sans en etre le
# dossier parent (registre #17850 relu par la suite generique scripts/tests).
#
# Aretes inter-dossiers (review 5867133827) : suites qui testent un module
# d'un AUTRE dossier via un chemin construit depuis ``__file__``. La
# derivation parent-dir ne les voit pas -- la garde
# ``scripts/ci/tests/test_watch_area_edges.py`` mesure ces aretes (borne
# basse : ancres ``__file__`` et ``parents[N] / "seg"`` uniquement) et
# verifie la reciproque : chaque entree repertoirique doit correspondre a
# une arete relue, sinon elle rougit.
EXTRA_SELECTORS: dict[str, tuple[str, ...]] = {
    # registre #17850 + modules prosody_lab relus via ancres __file__ par la
    # generique (garde #22468 : test_bakeoff_small_import, test_syllable_pitch_verdict)
    "scripts/tests": (
        "arxiv_attributions_registry.yaml",
        f"{V4}/prosody_lab/",
        # arete #25360 : test_setup_native_lean4_import.py relit le script
        # d'install WSL de GameTheory via une ancre __file__
        "MyIA.AI.Notebooks/GameTheory/scripts/setup_wsl_lean4.sh",
    ),
    "tests": ("scripts/ci/", "scripts/notebook_tools/"),
    "scripts/lean/tests": ("scripts/ci/",),
    "scripts/translation/tests": ("scripts/ci/",),
}


def watch_areas(suite: str) -> tuple[str, ...]:
    """Aire de veille d'une suite : parent des ``X/tests``, override sinon.

    ``scripts/sudoku/tests`` veille ``scripts/sudoku/`` -- et la derivation
    fait de ``scripts/tests`` la suite GENERIQUE de tout ``scripts/``
    (intentionnel : les organes exposes a la racine de scripts/ sont testes
    par elle). Les suites dossiers non-``tests`` (ArgumentAnalysis,
    GradeBookApp) veillent leur propre arbre.
    """
    if suite in WATCH_OVERRIDES:
        return WATCH_OVERRIDES[suite] + EXTRA_SELECTORS.get(suite, ())
    if suite.endswith("/tests"):
        parent = suite[: -len("/tests")]
        return (parent + "/",) + EXTRA_SELECTORS.get(suite, ())
    return (suite + "/",) + EXTRA_SELECTORS.get(suite, ())


def _norm(path: str) -> str:
    return path.replace("\\", "/").lstrip("/")


def _selects(area: str, path: str) -> bool:
    """Vrai si ``path`` tombe dans l'aire ``area`` (prefixe ou egalite)."""
    trimmed = area.rstrip("/")
    return path == trimmed or path.startswith(area)


def suites_for_paths(
    changed: list[str], suite_list: list[str]
) -> tuple[list[str], list[str]]:
    """Rend (suites, chemins_non_mappe) dans l'ordre du workflow.

    Tout chemin hors de toute aire de veille est rendu separemment :
    l'appelant en fait un repli pleine suite (fail-open), pas un silence.
    """
    selected: dict[str, None] = {}
    areas = [(suite, watch_areas(suite)) for suite in suite_list]
    unmapped: list[str] = []
    for raw in changed:
        path = _norm(raw)
        if not path:
            continue
        hit = False
        for suite, suites_areas in areas:
            if any(_selects(area, path) for area in suites_areas):
                selected[suite] = None
                hit = True
        if not hit:
            unmapped.append(path)
    return [s for s in suite_list if s in selected], unmapped


def _suites_via_native(
    unmapped: list[str], suite_list: list[str], repo_root: Path | None = None
) -> list[str]:
    """Suites du lot couvrant les chemins hors table, par l'organe natif.

    select_tests.py (P2, #25520) selectionne, pour les chemins donnes, les
    tests que le depot rattache a ces chemins : la regle R4 (portee depot)
    couvre par construction tout changement, les regles R1-R3 les citations
    et conventions de nom. Les fichiers selectionnes sont rabattus sur les
    entrees du lot par contenance : une suite dossier couvre son sous-arbre
    (``X`` couvre ``X/tests/t.py``), une suite fichier ne couvre qu'elle-meme.
    Une seconde table de correspondance serait une derive de plus -- ici la
    carte vient du depot, pas d'une ecriture a la main.
    """
    root = (repo_root or REPO_ROOT).resolve()
    selection = _select_native(root, unmapped)
    picked: set[str] = set()
    for test_rel in selection.selected:
        for entry in suite_list:
            trimmed = entry.rstrip("/")
            if test_rel == entry or test_rel.startswith(trimmed + "/"):
                picked.add(entry)
    return [s for s in suite_list if s in picked]


def _is_full_trigger(path: str) -> bool:
    if any(path.startswith(prefix) or path == prefix.rstrip("/")
           for prefix in FULL_TRIGGERS):
        return True
    return path.rsplit("/", 1)[-1] in FULL_BASENAMES


def scope(
    event: str,
    suite_list: list[str],
    repo: str = "",
    pr_number: int = 0,
    token: str | None = None,
    readers: list[tuple[str, Reader]] | None = None,
    repo_root: Path | None = None,
) -> tuple[str, list[str], str]:
    """Rend (mode, suites, raison). Fail-OPEN : pleine suite en cas de doute.

    ``readers`` chaine les lecteurs de diff (etiquette, lecteur) pour les
    tests ; en production, PR = diff local puis API, push = diff HEAD~1.
    ``repo_root`` surcharge la racine de la delegation hors table (#25510)
    pour les tests sur depot synthetique.
    """
    if event == "workflow_dispatch":
        return "full", list(suite_list), (
            "workflow_dispatch : revalidation complete apres batch (#13861)"
        )
    if event == "push":
        # Revue ai-01 5867133827, point 1 : le push sur main reste en PLEINE
        # suite. Le filet -- la casse arrive sur main sans y rougir, et ne
        # se voit qu'a la PR suivante qui touche la suite du test -- ne vaut
        # que si le push joue tout. Le gain de la tranche porte sur les PRs.
        #
        # Le push joue le diff HEAD~1 : sur main, ce sont les chemins du
        # commit qui vient d'atterrir, donc la portee restreinte y limiterait
        # la suite au strict necessaire -- et la casse qu'elle laisse passer
        # ne serait vue qu'au push suivant, sur un commit sans rapport.
        return "full", list(suite_list), (
            "push sur main : pleine suite (filet -- une erreur de portee "
            "serait imputee a ce seul commit, jamais rattrapee)"
        )
    if event not in ("pull_request", "push"):
        return "full", list(suite_list), (
            f"evenement {event or '?'} non restreint : pleine suite"
        )

    paths: list[str] | None = None
    source = ""
    failures: list[str] = []
    if event == "pull_request":
        chain = readers or [
            ("diff HEAD^1", lambda _base: _local_diff_paths("HEAD^1")),
            ("api", lambda _base: _api_pr_paths(repo, pr_number, token)),
        ]
    else:
        chain = readers or [("diff HEAD~1", lambda _base: _local_diff_paths("HEAD~1"))]
    for label, reader in chain:
        try:
            paths = reader("HEAD^1" if event == "pull_request" else "HEAD~1")
        except Exception as exc:  # noqa: BLE001 - fail-open documente en tete
            failures.append(f"{label}: {_describe(exc)}")
            continue
        source = label
        break

    if paths is None:
        return "full", list(suite_list), (
            "portee illisible (" + "; ".join(failures) + ") : pleine suite"
        )
    full_paths = [_norm(p) for p in paths if _norm(p)]
    triggers = sorted({p for p in full_paths if _is_full_trigger(p)})
    if triggers:
        return "full", list(suite_list), (
            "producteur du verdict modifie (" + ", ".join(triggers[:3])
            + ("..." if len(triggers) > 3 else "") + ") : pleine suite"
        )

    suites, unmapped = suites_for_paths(paths, suite_list)
    if unmapped:
        # #25510 : un chemin hors table ne rend PLUS la pleine suite. La
        # selection est deleguee a l'organe natif P2 (select_tests.py, #25520) :
        # ses regles R1-R6 derivent du depot (noms, citations, parcours
        # d'arborescence), donc un chemin que rien ne cite tombe sous la
        # regle R4 (portee depot) -- le plancher de selection, pas la totalite.
        # Mesure #25510 : les PRs du marathon II (carnets + twin_pairs.d/)
        # rendaient 37/37 suites par ce repli ; la delegation en retient 13
        # a 14, et la pleine suite reste au lot quatre fois par jour (P3,
        # slow-lane.yml). Fail-OPEN preserve : si l'organe natif est
        # indisponible (import, race de checkout) la pleine suite revient.
        try:
            delegated = _suites_via_native(unmapped, suite_list, repo_root)
        except Exception as exc:  # noqa: BLE001 - fail-open documente en tete
            return "full", list(suite_list), (
                f"chemins hors table ({', '.join(unmapped[:3])}"
                + ("..." if len(unmapped) > 3 else "")
                + f") : pleine suite (delegation en echec : {_describe(exc)})"
            )
        suites = [s for s in suite_list if s in set(suites) | set(delegated)]
        if delegated:
            return "restricted", suites, (
                f"{len(suites)} suite(s) sur {len(suite_list)} [source {source}"
                f" + R4 native sur {len(unmapped)} chemin(s) hors table]"
            )
        return "full", list(suite_list), (
            f"chemins hors table ({', '.join(unmapped[:3])}"
            + ("..." if len(unmapped) > 3 else "")
            + ") : aucune suite native couvrante : pleine suite"
        )
    if not suites:
        return "full", list(suite_list), (
            "aucune suite correspond aux chemins modifies : pleine suite"
        )
    return "restricted", suites, (
        f"{len(suites)} suite(s) sur {len(suite_list)} [source {source}]"
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--event", default="",
                        help="github.event_name (pull_request, push, workflow_dispatch...)")
    parser.add_argument("--repo", default="",
                        help="owner/repo — pour le repli API (PR)")
    parser.add_argument("--pr", type=int, default=0,
                        help="numero de PR — pour le repli API")
    parser.add_argument("--workflow", type=Path, default=DEFAULT_WORKFLOW,
                        help="chemin du workflow portant la liste des suites")
    args = parser.parse_args(argv)

    try:
        suite_list = parse_collected_paths(args.workflow)
    except Exception as exc:  # noqa: BLE001 - bruyant par contrat (rc 2)
        print(f"FAIL: workflow illisible {args.workflow}: {exc}", file=sys.stderr)
        return 2
    if suite_list is None:
        print(
            "FAIL: bloc pytest introuvable dans " + str(args.workflow)
            + " -- mettre a jour guard_test_root.PYTEST_BLOCK_RE (meme derive"
            + " que la garde #19026, jamais de liste inventee)",
            file=sys.stderr,
        )
        return 2

    # Revue ai-01 11/11 (job 130763938091) : le jeton n'est PLUS un argument de
    # ligne de commande. Il est lu dans l'ENVIRONNEMENT, la ou le pas de
    # workflow dedie le pose (`env: GH_TOKEN`) -- un jeton sur la ligne de
    # commande fuit dans le diff des invocations citees, et surtout le pas
    # `Run tests` avait fini par heriter du jeton au niveau du step entier :
    # deux tests de la suite mesuraient ce jeton ambiant (test_gh_identity
    # restaurait `***` au lieu de None ; test_gh_comment_fetcher_no_repo_env_raises
    # n'obtenait plus FetchError). Le contrat d'environnement est explicite et
    # testé (test_main_lit_le_jeton_dans_l_environnement).
    token = os.environ.get("GH_TOKEN") or os.environ.get("GITHUB_TOKEN") or None
    mode, suites, reason = scope(
        args.event, suite_list, repo=args.repo, pr_number=args.pr,
        token=token,
    )
    print(reason, file=sys.stderr)
    json.dump({"mode": mode, "suites": suites, "reason": reason},
              sys.stdout, indent=1)
    print()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
