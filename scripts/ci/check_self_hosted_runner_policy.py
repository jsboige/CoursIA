#!/usr/bin/env python3
"""Enforce the isolation policy for future self-hosted Actions jobs (#12704).

The repository is public. A self-hosted job that can receive a fork payload can
execute untrusted code next to the cluster's credentials. This scanner therefore
fails closed: every self-hosted job must belong to an explicitly allowed
workflow, use the exact dedicated label set, and avoid runner groups (unavailable
for this personal-account repository). Every pull_request job must also carry
the exact same-repository guard. A self-hosted job is gated on a trigger
allowlist (pull_request, push, schedule, workflow_dispatch): these only run
repository-owned refs, and are checked for the same-repo guard when
pull_request is present. Any other trigger is rejected fail-closed -- the
known-dangerous ones carry specific codes (pull_request_target, workflow_run,
issue_comment, pull_request_review, pull_request_review_comment), and anything
unlisted (e.g. check_run / check_suite, whose payload can name a fork pull
request) is refused by default. Dynamic ``runs-on`` expressions are rejected
because their target cannot be proved statically.

A ratchet (#23053) additionally refuses any job of a ``pull_request`` workflow
left on a naked ``ubuntu-latest`` -- it never reads the overflow variable, so
it queues on the hosted pool while local slots sit idle -- unless its workflow
is named in ``HOSTED_PR_JOB_EXCEPTIONS`` with a motive. That list is a subset
of a frozen baseline and only shrinks: naming a new exception is itself a
violation.

Exit codes:
  0  policy satisfied (including the explicit baseline of zero self-hosted jobs)
  1  policy violation
  2  broken instrument or unreadable workflow
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any

EXIT_OK = 0
EXIT_VIOLATION = 1
EXIT_BROKEN = 2

REQUIRED_LABELS = {
    "self-hosted",
    "coursia-ephemeral",
    "coursia-fast-guards",
}
# Dedicated label set for the containerized Linux runner (mission #13378,
# dispatch ai-01 2026-08-31, po-2024): routes ONLY to the Docker container,
# never to the Windows fast-guards runners -- the distinct label is the
# routing guarantee (a windows dispatch must not land on Linux).
LINUX_RUNNER_LABELS = {
    "self-hosted",
    "coursia-ephemeral",
    "coursia-linux",
}
# Dedicated label set for the PR-gate waiter pool (#13363 jambe A, po-2024):
# 24 slots deployed via `supervise.sh waiters` (1 vCPU / 1 GiB / 128 pids,
# coursia-waiters.service). A waiter never carries coursia-linux -- the
# distinct label is what lets the gate WAIT without holding a work slot
# (arbitrage ai-01 2026-09-02: "attendre ne coute pas de CPU").
WAITER_LABELS = {
    "self-hosted",
    "coursia-waiter",
}
# Dedicated label set for the specialised Lean pool (#14337, po-2024): elan +
# toolchain baked in a dedicated image (Dockerfile.lean), .lake kept warm in
# the per-slot work volume. A lean slot never carries coursia-linux -- the
# distinct label is the routing guarantee (a pure-Python guard must not land
# on a lean slot, and a lake build must not land on the minimal image).
LEAN_RUNNER_LABELS = {
    "self-hosted",
    "coursia-ephemeral",
    "coursia-lean",
}
DEDICATED_LABEL_SETS = (REQUIRED_LABELS, LINUX_RUNNER_LABELS, WAITER_LABELS, LEAN_RUNNER_LABELS)
# Owner-approved additions must cite the lane that owns the runner deployment:
# - pr-gate-stale-sweep.yml: schedule-mutualized re-aggregation (pre-existing).
# - windows-self-hosted-tests.yml: workflow_dispatch-ONLY vehicle for the 9
#   @requires_windows confinement tests (#13063 skip surface), zero fan-out
#   (#13097), executed on an --ephemeral runner (#12704, po-2024, #13135).
# - linux-self-hosted-tests.yml: workflow_dispatch-ONLY pilot vehicle for the
#   containerized Linux runner (#13378, po-2024, dispatch ai-01 2026-08-31),
#   zero fan-out, --ephemeral inside a capped Docker container.
# - tranche 1 (#13378, decision ai-01 2026-09-01, owner myia-po-2024:CoursIA):
#   pure-Python guards, no secret, no GITHUB_TOKEN use, universal same-repo
#   guard (#13874) at job level so fork PRs are skipped (pr_gate.py counts
#   `skipped` as OK). Routed to the containerized Linux leg to relieve the
#   GitHub-hosted queue. Rollback = revert of the routing PR.
SELF_HOSTED_WORKFLOW_ALLOWLIST = {
    # tranche 3d (#14283) : premier consommateur GitHub-hosted du depot une
    # fois secret-scan bascule -- 2650 runs same-repo du 2026-08-28 au
    # 2026-09-02, timeout 25 min, aucun filtre `paths:`.
    #
    # 2026-10-27 (PR #22820, lane myia-ai-01:CoursIA) : always-on-guards.yml et
    # always-on-guards-body.yml MIGRENT vers ubuntu-latest par Q35 etape 2
    # (#17397) -- l'organe `scripts/ci/audit_self_hosted_needs.py` les certifie
    # sans aucun besoin local, et le parc local etait sature PAR SES CHECKOUTS
    # (mesure 00:45Z : 11 des 12 slots occupes dans `actions/checkout`). Sortis
    # de SELF_HOSTED_WORKFLOW_ALLOWLIST dans le meme commit. Precedent :
    # repeated-prose-advisory.yml (#17443).
    "pr-gate-stale-sweep.yml",
    "windows-self-hosted-tests.yml",
    "linux-self-hosted-tests.yml",
    "banner-guard.yml",
    "prose-counts-guard.yml",
    "notebook-interp-positioning.yml",
    "cell-order-gate.yml",
    "pip-leak-guard.yml",
    "hooks-parity.yml",
    # 2026-10-27 (lane myia-ai-01:CoursIA, lot 2 de l'extension Q35 etape 2) :
    #   ces 11 workflows MIGRENT vers ubuntu-latest -- l'organe
    #   `scripts/ci/audit_self_hosted_needs.py` les certifie sans aucun besoin
    #   local, et le parc local etait sature PAR SES CHECKOUTS (mesure 00:45Z :
    #   11 des 12 slots occupes dans `actions/checkout`, 614 runs en file). La
    #   garde anti-fork est conservee dans chaque fichier. Sortis de
    #   SELF_HOSTED_WORKFLOW_ALLOWLIST dans le meme commit. Precedent :
    #   repeated-prose-advisory.yml (#17443).
    "notebook-navlink-check.yml",
    "notebook-nav-chain-guard.yml",
    # tranche 3b (#14283, meme decision, meme owner) : suite des gardes PR
    #   pure-Python. Fondue dans la meme PR que 3a -- les scinder aurait produit
    #   un conflit sur cette meme ancre pour zero benefice de relecture.
    "markdown-claims-output-advisory.yml",
    "slides-composition-pr-relay.yml",
    "source-output-ratchet.yml",
    "translation-guard.yml",
    "validation-matrix.yml",
    # tranche 3a (#14283, decision ai-01 2026-09-02, owner myia-ai-01:CoursIA) :
    #   gardes PR pure-Python, garde same-repo au niveau job, runs-on STATIQUE.
    #   Exclus deliberement : pr-gate.yml (agregateur qui poll -- il tiendrait le
    #   slot quil attend), owui-playwright-check.yml (navigateurs hors image),
    #   always-on-guards.yml (trigger pull_request_review = FORK_REACHABLE).
    #   Rollback = revert de la PR de routage.
    # 2026-10-27 (lane myia-ai-01:CoursIA, lot 1 de l'extension Q35 etape 2) :
    #   ces 13 workflows MIGRENT vers ubuntu-latest -- l'organe
    #   `scripts/ci/audit_self_hosted_needs.py` les certifie sans aucun besoin
    #   local, et le parc local etait sature PAR SES CHECKOUTS (mesure 00:45Z :
    #   11 des 12 slots occupes dans `actions/checkout`, 614 runs en file). La
    #   garde anti-fork est conservee dans chaque fichier. Sortis de
    #   SELF_HOSTED_WORKFLOW_ALLOWLIST dans le meme commit. Precedent :
    #   repeated-prose-advisory.yml (#17443).
    "consecutive-code-cells-advisory.yml",
    "ict-tests.yml",
    "lean-conway.yml",
    "lean-i18n-drift.yml",
    "lean-knot.yml",
    # tranche 3c (#14283, meme decision, meme owner) : jobs individuels d'un
    #   workflow dont les autres jobs restent sur ubuntu-latest.
    #   Exclus deliberement : ml-tests (torch retelecharge a chaque run, pas de
    #   cache persistant), lean-social-
    #   choice/build (merite un pool a cache Mathlib chaud, cf #14337),
    #   notebook-execution-required/golden-set-execute (execution lourde).
    "bash-syntax-advisory.yml",
    # #10643 item 3 (owner myia-po-2024:CoursIA, 2026-10-05) : garde
    #   pure-Python de couverture compagnons bi-OS (.ps1 -> .sh, README
    #   croise, carnets Setup). Trigger pull_request paths + garde same-repo
    #   au niveau job + runs-on STATIQUE -- meme profil que ses voisins 3c.
    #   Rollback = revert de la PR (l'entree disparait de l'allowlist).
    "lean-social-choice.yml",
    "notebook-execution-required.yml",
    "secret-scan.yml",
    # secret-scan/gitleaks : exclu en 3c pour la socket Docker, LEVE depuis --
    #   le job scanner n'utilise plus `docker run` mais le binaire epingle
    #   (meme release, meme ${GITLEAKS_VERSION}), forme deja eprouvee sur ce
    #   pool par son job positive-controls. La jambe fork reste GitHub-hosted
    #   sous la forme docker : `gitleaks-fork`.
    # always-on-metadata-guards.yml : routable (triggers pull_request +
    #   workflow_dispatch seulement). Son jumeau always-on-guards.yml ne l'est
    #   PAS -- il porte pull_request_review, classe FORK_REACHABLE (#14294).
    "always-on-metadata-guards.yml",
    # #22937 (volet (d), 2026-10-28, lane myia-ai-01:CoursIA-2) : la garde
    #   des waivers de chemins locaux REJOINT LA COHORTE (forme hybride
    #   auditee #22461). Declencheurs `pull_request` (opened/synchronize/
    #   reopened) + `workflow_dispatch` -- les DEUX sont dans
    #   SAFE_SELF_HOSTED_TRIGGERS ; la jambe `issue_comment` avait ete
    #   RETIREE (#23044, et son trigger est FORK_REACHABLE). Le job est
    #   pure-Python, sparse-checkout de 2 fichiers, lecture seule des
    #   commentaires de PR (`permissions: issues: read`,
    #   `pull-requests: read`) : aucun besoin heberge specifique.
    #   Rollback = remettre `runs-on: ubuntu-latest` + retirer l'entry.
    "local-path-waiver-guard.yml",
    # tranche 4 (#14283, meme decision, meme owner) : balayages cron pur-Python.
    #   Declencheur `schedule` seul -- pas de contexte pull_request, donc aucune
    #   garde same-repo requise. 33 creneaux distincts, au plus 2 simultanes
    #   (mesure 2026-09-02) : ils ne peuvent pas affamer les gardes de PR.
    #   Exclus : markdown-table-guard / render-volume-delta-advisory (lourds),
    #   slides-composition-advisory (navigateurs hors image).
    # #15347 (owner myia-po-2026:CoursIA) : cablage de l'organe G-VAR-3
    #   refresh_stale_adjacency.py -- sur main + tests, aucun workflow ne
    #   l'appelait (organe inerte, 24 h de blocage mesurees sur #15165).
    #   Balayage cron horaire (schedule + workflow_dispatch) pur-Python +
    #   gh bootstrap toolcache : simule le garde contre la sequence de merges
    #   courante et appose le marqueur `<!-- refresh-adj -->` idempotent qui
    #   re-declenche `pull_request: edited` -- jamais d'override (le garde
    #   reste l'autorite, la simulation doit passer). Advisory by
    #   construction : exit 0 toujours, rc=2 logge ::warning::, aucun secret,
    #   GITHUB_TOKEN lecture seule + pull-requests: write (body edit).
    #   Aucun trigger pull_request -> aucune garde same-repo requise (tranche
    #   4 #14283, meme profil que pr-gate-stale-sweep). Rollback = revert de
    #   la PR (l'entree disparait de l'allowlist).
    "ascii-flowchart-advisory.yml",
    "candidate-delivered-advisory.yml",
    "catalog-cron.yml",
    "check-resync-only.yml",
    "cjk-residue-advisory.yml",
    "degraded-mode-advisory.yml",
    "detect-dup-selftest.yml",
    "dotnet-nuget-block-advisory.yml",
    "epic-charter-advisory.yml",
    "epic-neglect-sweep.yml",
    "exercises-advisory.yml",
    "grain-orphans-sweep.yml",
    "h1-hygiene-advisory.yml",
    # #12156 piste 1 (owner myia-po-2024:CoursIA) : advisory epic-wide-sur-
    #   umbrella. Balayage cron hebdomadaire (schedule + workflow_dispatch)
    #   pur-Python, GH_TOKEN lecture seule + issues: write. Aucun trigger
    #   pull_request -> aucune garde same-repo requise (tranche 4 #14283,
    #   meme profil que candidate-delivered-advisory). Rollback = revert de
    #   la PR (l'entree disparait de l'allowlist).
    "lane-claim-epic-wide-advisory.yml",
    # leaky-fixture-sweep.yml : RETIREE le 2026-09-14 (#16141). Elle etait
    #   entree ici avec la tranche 4 (#14283) comme ses sœurs `schedule`-only,
    #   mais son profil n'est PAS celui des autres : elle installe
    #   `libfaketime` par `sudo apt-get`, donc elle exige root/apt que le pool
    #   ne fournit pas (uid 1001, no-new-privileges, sans sudo ni dpkg).
    #   C'est la meme exclusion que slides-composition-advisory
    #   (`playwright --with-deps` exige root) et pr-gate.yml. Cout mesure de
    #   l'erreur : 12 runs, 12 `failure`, du 2026-09-03 au 2026-09-14, zero
    #   balayage effectif. Le job est repasse sur `ubuntu-latest`.
    "machine-dep-timing-advisory.yml",
    "machine-dep-timing-inventory.yml",
    "mermaid-fill-color-advisory.yml",
    "orphan-branch-scan.yml",
    "outputs-text-fragmentation-advisory.yml",
    "pedagogy-density-advisory.yml",
    # pr-gate-missing-advisory.yml : supprime par #14477 -- sa detection est
    # repliee comme etape du sweep ci-dessous (design-gate ai-01 : "meme
    # population, meme requete ; seule la branche de remediation differe.
    # Ne pas creer un troisieme organe").
    # pr-path-collision-advisory.yml : migre ubuntu-latest par Q35 etape 2
    # (#17397, PR dediee myia-ai-01:CoursIA-2 c.206, 5 workflows agregateurs,
    # 2026-10-06). Sorti de SELF_HOSTED_WORKFLOW_ALLOWLIST dans le meme
    # commit. Precedent : #17443 (po-2023, 4 agregateurs).

    # queue-ghost-watch.yml (#14367, owner myia-po-2023:CoursIA-2) : sonde cron
    #   04:17 UTC (offset anti-stampede, hors-:00) sur les 18 zombies QUEUED
    #   du 2026-08-19. Meme profil que runner-starvation-advisory : advisory
    #   schedule + workflow_dispatch UNIQUEMENT (doctrine #12817), runs-on
    #   statique [self-hosted, coursia-ephemeral, coursia-linux], aucun
    #   trigger pull_request. Pur-Python stdlib + gh binaire de l'image ;
    #   permissions contents:read + issues:write + actions:read (ouvre
    #   issue labellee `queue-ghost-watch` sur DRIFT). Aucun GITHUB_TOKEN
    #   cote job pour les operations de decision -- uniquement pour ouvrir
    #   l'issue (token du runner, scope contenu par les permissions).
    #   Rollback = revert de la PR (l'entree disparait de l'allowlist).
    "queue-ghost-watch.yml",
    "qc-research-monitor.yml",
    # repo-size-advisory.yml : migre ubuntu-latest par Q35 etape 2 (#17397,
    # PR dediee myia-ai-01:CoursIA-2 c.206, 5 workflows agregateurs,
    # 2026-10-06). Sorti de SELF_HOSTED_WORKFLOW_ALLOWLIST dans le meme
    # commit. Precedent : #17443 (po-2023, 4 agregateurs).
    "review-coverage-advisory.yml",
    "slides-build-advisory.yml",
    "slow-lane.yml",
    "translation-parity.yml",
    "twin-parity-cron.yml",
    "twin-parity-drift-audit.yml",
    "workflow-path-filter-audit.yml",

    # - tranche 5 (#13378/#14283, decision ai-01 2026-09-02) : le solde des
    #   gardes routables. Exclus et pourquoi : pr-gate.yml (agregateur qui
    #   poll jusqu'a 45 min -- le router reproduirait la famine mesuree en
    #   #11405), lean-axiom/lean-build (builds Lean sans cache mathlib, cf
    #   #14337 pools specialises), slides-composition-advisory (playwright
    #   --with-deps exige root, le conteneur tourne en uid 1001).
    #   quarto-pages-deploy : jobs build/validate-pr routes en fin de chantier
    #   (tarball, voir l'entree dediee) ; seul `deploy` reste exclu (Pages/OIDC).
    "bare-cross-dir-load-gate.yml",
    "base-not-main-advisory.yml",
    # concurrency-conj-guard.yml : migre ubuntu-latest par Q35 etape 2
    # (#17397, PR dediee myia-ai-01:CoursIA-2 c.206, 5 workflows
    # agregateurs, 2026-10-06). Sorti de SELF_HOSTED_WORKFLOW_ALLOWLIST
    # dans le meme commit. Precedent : #17443 (po-2023, 4 agregateurs).
    "degenerate-figure-gate.yml",
    "docs-link-check.yml",
    "exercise-leak-ci.yml",
    "fabricated-output-gate.yml",
    "fast-lane-shadow.yml",
    "lane-claim-guard.yml",
    # linux-runner-version-pin-advisory.yml (#15201, owner
    #   myia-po-2023:CoursIA) : organe cron schedule+workflow_dispatch
    #   UNIQUEMENT (advisory par construction, doctrine #12817), runs-on
    #   statique [self-hosted, coursia-ephemeral, coursia-linux], garde
    #   same-repo au niveau job malgre l'absence de trigger pull_request.
    #   Pur-Python stdlib + gh binaire de l'image ; le GITHUB_TOKEN du run
    #   ne sert qu'a LIRE releases/latest (permissions: contents: read).
    #   Cron 23,53 -- offset des sweeps 13,43 et du starvation 19,49.
    #   Rollback = revert de la PR (l'entree disparait de l'allowlist).
    "linux-runner-version-pin-advisory.yml",
    "linux-runner-starvation-advisory.yml",
    # #22946 (owner myia-ai-01:CoursIA-2, review ai-01 du 2026-10-27) :
    #   controleur du debordement CI_OVERFLOW_LOCAL (phase B de #22937). Meme
    #   profil que les deux advisories ci-dessus : `schedule` +
    #   `workflow_dispatch` UNIQUEMENT (advisory par construction, doctrine
    #   #12817), runs-on STATIQUE [self-hosted, coursia-ephemeral,
    #   coursia-linux], garde same-repo au niveau job malgre l'absence de
    #   trigger `pull_request`. Pur-Python stdlib + `gh` binaire de l'image ;
    #   le job est en LECTURE SEULE (aucun secret, aucune ecriture de
    #   variable -- l'ecriture reste un geste d'operateur ai-01 en local,
    #   arbitrage (b) du 2026-10-27), `permissions: actions: read` +
    #   `contents: read` -- `variables` n'est PAS une portee admise sous
    #   `permissions:` (une cle hors liste invalide le fichier entier).
    #   La bascule vers le pool est le POINT 1 de la review : le job mesurait
    #   la file hebergee en y faisant la queue (17 des 23 jobs en cours
    #   etaient heberges). Rollback = revert de la PR (l'entree disparait de
    #   l'allowlist, et le garde fail-closed refuse alors le runs-on).
    "ci-overflow-controller.yml",
    # runner-starvation-advisory.yml (#14846, owner myia-po-2027:CoursIA-2) :
    #   jumeau de linux-runner-starvation-advisory.yml (#13378) etendu aux
    #   2 labels waiter + lean (matrice GitHub Actions, 2 entrees include).
    #   coursia-linux reste couvert par le workflow dedie
    #   linux-runner-starvation-advisory.yml -- la sonde n'oberve pas
    #   linux. Meme profil : advisory cron schedule+workflow_dispatch
    #   UNIQUEMENT (doctrine #12817), runs-on STATIQUE [self-hosted,
    #   coursia-ephemeral, coursia-linux] -- l'observateur tourne sur la jambe
    #   Linux containerisee, pas sur les labels qu'il observe (un observateur
    #   qui tournerait sur le label garde mourrait avec lui). Pur-Python
    #   stdlib + gh binaire de l'image ; RUNNERS_READ_PAT secret read-only
    #   pose 2026-09-02T08:26Z (Administration:read, incapable de minter un
    #   registration-token, par design). Cron 23,53 (offset disjoint du cron
    #   linux 19,49 et des sweeps 13,43). trigger workflow_dispatch sans
    #   input (matrice executee in extenso -- l'input `label` declare
    #   precedemment a ete retire c.1065 car chaque job matriciel porte
    #   matrix.label truthy et shadowait inputs.label). ZERO job self-hosted
    #   sur pull_request : aucun risque d'atteindre un job de fork. Rollback
    #   = revert de la PR (l'entree disparait de l'allowlist).
    "runner-starvation-advisory.yml",
    "markdown-rendering-guard.yml",
    "markdown-table-guard.yml",
    "md-content-loss-gate.yml",
    "ml-tests.yml",
    "notebook-output-failure-ratchet.yml",
    # jumeau output-flood (#14959, meme forme moteur que le failure-ratchet
    #   ci-dessus : garde Python pur stdlib, garde same-repo au niveau job,
    #   shell workflow_dispatch-only absorbe par fast-lane TRANCHE2).
    "notebook-output-flood-ratchet.yml",
    # jumeau output-collapse (#15327, owner myia-po-2023:CoursIA) : verdict
    #   BLOQUANT depuis T2 de #21424, rendu par fast-lane TRANCHE2 (entree 5,
    #   check-run `Output-collapse ratchet (base vs PR)`), shell
    #   workflow_dispatch-ONLY pour re-run manuel -- meme profil que les deux
    #   jumeaux ci-dessus. Detecteur check_output_collapse.py, stdlib-only,
    #   garde same-repo au niveau job, aucun GITHUB_TOKEN cote job. L'organe a
    #   recu l'approval design (Hermes 02:29Z) ; la review ai-01 03:33Z a
    #   demande la voie 2 : allowlist canonique + test de politique rejoue
    #   (test_current_repository_self_hosted_jobs_satisfy_isolation_policy,
    #   scan du repo courant -- aucune autre liste a synchroniser).
    #   Rollback = revert de la PR (l'entree disparait de l'allowlist).
    "notebook-output-collapse-ratchet.yml",
    "notebook-validation.yml",
    "perimeter-review-guard.yml",
    "regression-guard.yml",
    "render-volume-delta-advisory.yml",
    # registre TRANCHE7 (demande user 2026-09-05, owner myia-po-2023:CoursIA)
    #   : vehicule workflow_dispatch-ONLY servant de cible d'identite au
    #   check-run absorbe par fast-lane (registre TRANCHE7) et de re-run
    #   manuel self-test sur main. Detecteur de prose repetee
    #   intra-notebook (detect_repeated_prose.py), advisory pur-Python
    #   stdlib-only, label signe, jamais exit != 0, aucun secret.
    #   Rollback = revert de la PR (l'entree disparait de l'allowlist).
    # repeated-prose-advisory.yml : migre ubuntu-latest par Q35 etape 2
    # (#17397, PR dediee myia-ai-01:CoursIA-2 c.206, 5 workflows
    # agregateurs, 2026-10-06). Sorti de SELF_HOSTED_WORKFLOW_ALLOWLIST
    # dans le meme commit. Precedent : #17443 (po-2023, 4 agregateurs).
    # scripts-tests.yml : RESTE sur le parc local (PR #22820, lane
    # myia-ai-01:CoursIA, 2026-10-27). La migration vers ubuntu-latest a ete
    # tentee puis ANNULEE sur une MESURE, pas sur une preference :
    # `Scripts Tests (CPU)` y echoue (run 40427418743 -- 4 echecs sur 20950
    # tests). Les deux causes sont couplees a la FORME du runner :
    #   (a) `scripts/lean/tests/test_lean_exec.py` -- `compute_granted` derive
    #       `jobs_cpu` de `os.cpu_count()` (2 sur ubuntu-latest, >= 4 sur le
    #       parc local) ; le test exige `granted == 4` ;
    #   (b) `scripts/tests/test_setup_shared_mathlib_scan.py` -- le script
    #       `scripts/lean/setup_shared_mathlib.ps1` convertit la racine du
    #       depot en chemins Windows (`$RepoRoot -replace '/', '\'`), ce qui
    #       invalide `Test-Path` sur un runner POSIX -> « Aucun projet Lake
    #       avec mathlib trouve. ».
    # Un job dont la suite de tests est couplee a la forme de l'hote a un
    # besoin local REEL : l'organe `audit_self_hosted_needs.py` ne le voit pas
    # (il classifie le workflow, pas la suite qu'il execute).
    "scripts-tests.yml",
    "series-naming-gate.yml",
    # registre TRANCHE14 (issue #16762, owner myia-po-2023:CoursIA) : meme
    #   profil que repeated-prose-advisory.yml (TRANCHE7) ci-dessus --
    #   vehicule workflow_dispatch-ONLY servant de cible d'identite au
    #   check-run absorbe par fast-lane (registre TRANCHE14) et de re-run
    #   manuel du recensement sur main. Detecteur de paires de cellules de
    #   lecture scindees (check_split_reading_cells.py), pur-Python
    #   stdlib-only, aucun secret. Promu en cliquet BLOQUANT par #17044 : le
    #   verdict de PR est rendu par le garde absorbe, PAS par ce workflow, qui
    #   ne tourne jamais sur un pull_request (dispatch-only) -- l'entree reste
    #   justifiee telle quelle. Rollback = revert de la PR (l'entree
    #   disparait de l'allowlist).
    "split-reading-advisory.yml",
    "stale-base-warning.yml",
    # fin de chantier #14283 (feu vert ai-01 2026-09-02) : les jobs
    #   quarto-pages-deploy `build` et `validate-pr` passent au pool — le
    #   setup Quarto se fait par tarball auto-contenu (l'action canonique
    #   exige sudo apt + dpkg, absents de l'image no-new-privileges, mesure
    #   issuecomment-5516335275). Le job `deploy` RESTE ubuntu-latest :
    #   deploy-pages + OIDC/env github-pages, question separee.
    "quarto-pages-deploy.yml",
    "svg-broken-geometry-gate.yml",
    "svg-decimal-comma-gate.yml",
    "svg-empty-display-gate.yml",
    "svg-offscreen-flat-gate.yml",
    # testpaths-coverage-guard.yml : migre ubuntu-latest par Q35 etape 2
    # (#17397, PR dediee myia-ai-01:CoursIA-2 c.206, 5 workflows
    # agregateurs, 2026-10-06). Sorti de SELF_HOSTED_WORKFLOW_ALLOWLIST
    # dans le meme commit. Precedent : #17443 (po-2023, 4 agregateurs).
    "translation-sync.yml",
    "variation-light-genre.yml",
    # tranche 6 (c.903, owner myia-po-2026:CoursIA-2) : garde advisory pur-Python
    #   declenchee sur pull_request filtrant les `MyIA.AI.Notebooks/**/README.md`,
    #   scan delta-PR vs main (merge-base), pose un label signe (jamais exit != 0).
    #   Meme profil que machine-dep-timing-advisory / pr-path-collision-advisory /
    #   exercises-advisory / catalog-drift : stdlib-only, lecture seule du repo,
    #   aucun GITHUB_TOKEN cote job. Le job porte la garde universelle parenthe-
    #   seee (cf. test_universal_guard_with_combined_target_is_accepted, #13874)
    #   pour les forks PRs qui se font skipper proprement par pr_gate.
    #   Rollback = revert de cette PR (l'entree disparait de l'allowlist).
    # tranche 7 (acceptance 3 #11703, owner myia-po-2027:CoursIA) : garde
    #   advisory pur-Python declenchee sur pull_request filtrant les
    #   `**/*_lean/**/*.lean`, mode --pr-base de l'organe canonique
    #   scan_lake_notebook_visibility.py (diff 3-points, DECL_RE partage --
    #   aucune reimplementation), pose une paire de labels signes (drift /
    #   unmeasured), jamais exit != 0. Meme profil que la tranche 6 :
    #   stdlib-only, aucun GITHUB_TOKEN hors gh label/pr edit, garde same-repo
    #   au niveau job pour les forks. Rollback = revert de la PR (l'entree
    #   disparait de l'allowlist).
    "lean-visibility-advisory.yml",
    # registre TRANCHE6 (#14325, owner myia-po-2023:CoursIA) : vehicule
    #   workflow_dispatch-ONLY servant de cible d'identite au check-run absorbe
    #   par fast-lane (scripts/ci/fast_lane_registry.py) et de re-run manuel
    #   sur main ; l'analyse per-PR elle-meme tourne dans le slot fast-lane.
    #   Advisory pur-Python (detect_markdown_deaccent.py, durci #14064) :
    #   label signe, exit 0 toujours, aucun secret, GITHUB_TOKEN en lecture
    #   seule pour l'API Checks/labels. Garde same-repo parenthesee au niveau
    #   job (#13874) pour les forks. Rollback = revert de cette PR.
    "markdown-deaccent-advisory.yml",
    # #13363 jambe B (arbitrage ai-01 2026-09-02, owner myia-po-2024:CoursIA) :
    #   pr-gate.yml routes its pull_request leg to the waiter pool via the ONE
    #   audited hybrid runs-on form (_hybrid_runs_on) -- the same-repo guard
    #   lives inside the expression itself, forks and workflow_dispatch fall
    #   back to ubuntu-latest. Excluded until now because the polling
    #   aggregator must not hold the work slot it waits for (#11405); the
    #   waiter pool (1 vCPU / 1 GiB, #14303) is exactly the third term that
    #   removes the objection. Rollback = revert of the routing PR.
    "pr-gate.yml",
    # #14859 (owner myia-po-2026:CoursIA) : garde advisory pur-Python sur les
    #   caracteres de controle ayant mange un escape LaTeX dans les portees
    #   math des notebooks. pull_request/push filtrant **.ipynb + detecteur +
    #   workflow ; scan PR-diff (check_latex_control_chars.py, stdlib-only) ;
    #   occurrences = ::warning:: + exit 0 (jamais bloquant), exit 2 (notebook
    #   illisible) = warning UNKNOWN nomme + exit 1 (#14849). Aucun secret,
    #   aucun GITHUB_TOKEN cote job, garde same-repo universelle parenthesee
    #   au niveau job (#13874). Runner = jambe Linux containerisee
    #   (LINUX_RUNNER_LABELS, meme profil que notebook-cell-source-parses.yml
    #   tranche 1 #13378). Rollback = revert de la PR (l'entree disparait de
    #   l'allowlist).
    # #17380 (owner myia-po-2023:CoursIA) : garde advisory sur la syntaxe
    #   math non rendable des cellules markdown -- 4 classes (delimiteurs
    #   LaTeX purs \(..\)/\[..\], dollars impairs par paragraphe, commandes
    #   LaTeX nues hors scopes, scopes que KaTeX refuse). Reponse au
    #   commentaire user du 2026-09-22 sur IIT-06 : le notebook mesurait
    #   propre (62/62 scopes rendables), la cause etait le visualiseur --
    #   l'organe rend la question mesurable a l'echelle du corpus.
    #   pull_request/push filtrant **.ipynb + detecteur + workflow ; jambe
    #   KaTeX active en CI via npm install katex --no-save (node requis par
    #   le runner ephemeral, saut dite a voix haute sinon, #14849) ;
    #   occurrences = ::warning:: + exit 0 (jamais bloquant), exit 2 =
    #   warning UNKNOWN nomme + exit 1. Aucun secret, aucun GITHUB_TOKEN
    #   cote job, garde same-repo parenthesee au niveau job (#13874).
    #   Runner = jambe Linux containerisee (LINUX_RUNNER_LABELS, meme
    #   profil que notebook-latex-control-chars). Rollback = revert de la
    #   PR (l'entree disparait de l'allowlist).
    # #14532 item 1 (owner myia-po-2026:CoursIA-2) : garde PR pure-Python sur
    #   les disparitions de section au plan des notebooks pedagogiques.
    #   workflow_dispatch-only ce cycle (anti-panic-deploiement, idem
    #   md-content-loss-gate a sa creation -- absorption fast-lane-shadow
    #   differee a un cycle ulterieur si le pattern tient). Detecteur
    #   `scripts/notebook_tools/detect_notebook_plan_loss.py` (3 passes de
    #   substance + normalisation accents/numerals, complement structurel de
    #   md-content-loss : axe PLAN vs axe VOLUME), stdlib-only, 28 tests verts.
    #   Aucun secret, aucun GITHUB_TOKEN cote job, garde same-repo universelle
    #   parenthesee au niveau job (#13874) pour les forks PRs qui se font
    #   skipper proprement par pr_gate. Runner = jambe Linux containerisee
    #   (LINUX_RUNNER_LABELS, meme profil que md-content-loss-gate tranche 5
    #   #13378). Rollback = revert de la PR (l'entree disparait de l'allowlist).
    "notebook-plan-loss-gate.yml",
    # #15322 (owner myia-po-2023:CoursIA) : vehicule workflow_dispatch-ONLY
    #   servant de cible d'identite au check-run absorbe par fast-lane
    #   (registre TRANCHE2) et de re-run manuel du self-test sur main.
    #   Detecteur check_pr_translation_drift.py (attribution par merge-base,
    #   predicat REUTILISE de check_translation_sync.check_csv -- aucune
    #   reimplementation), advisory pur-Python stdlib-only, conclusion neutre,
    #   jamais exit != 0 sur le verdict, aucun secret, aucun GITHUB_TOKEN cote
    #   job. Runner = jambe Linux containerisee (LINUX_RUNNER_LABELS, meme
    #   profil que repeated-prose-advisory.yml / markdown-deaccent-
    #   advisory.yml). Rollback = revert de la PR (l'entree disparait de
    #   l'allowlist).
    "translation-hot-drift-advisory.yml",
    # #15405 (decision ai-01 2026-09-11, owner myia-ai-01:CoursIA) : garde
    #   advisory pur-Python sur les paragraphes markdown depassant 2000
    #   caracteres (detect_paragraph_length.py, stdlib-only). Declencheur
    #   pull_request filtrant `**/*.md` + auto-couverture du workflow (#8822,
    #   sans quoi le poseur de label ne peut plus retirer son propre label une
    #   fois les chemins sortis du diff). Pose un label signe, jamais exit != 0.
    #   `pull-requests: write` + GITHUB_TOKEN limites a l'API labels -- meme
    #   profil que markdown-deaccent-advisory.yml / repeated-prose-advisory.yml,
    #   deja admis a ce titre. Garde same-repo au niveau job (#13874) : les PRs
    #   de fork se font skipper proprement par pr_gate. Runner = jambe Linux
    #   containerisee (LINUX_RUNNER_LABELS). Rollback = revert de la PR
    #   (l'entree disparait de l'allowlist).
    # #14598 sous-grain (owner myia-po-2025:CoursIA, claim c. issue) : sonde
    #   TEMPORAIRE de mesure non censuree de tests/ (55) -- le plafond
    #   production 30 min d'ict-tests.yml censure a droite les runs coupes
    #   (6/11 des 30 derniers). Workflow diagnostique separe : pull_request
    #   self-cover (declenche seulement par son propre fichier) +
    #   workflow_dispatch, concurrency FIXE sans cancel-in-progress (une
    #   mesure ne doit pas etre interrompue), timeout 90 min, pytest
    #   --durations=25, venv per-job #14571, garde same-repo universelle au
    #   niveau job, runs-on STATIQUE. Pur test pytest, aucun secret, aucun
    #   GITHUB_TOKEN cote job, aucun label pose. Retirer ce workflow ET cette
    #   entree dans la PR qui re-calibre le plafond d'apres la mesure
    #   (acceptance reprise #14598). Rollback = revert de la PR (l'entree
    #   disparait de l'allowlist).
    "ict-tests-profile.yml",
    # #16081 / c.559 (owner myia-po-2023:CoursIA-2, PR #16082) : kernel-drift
    #   guard -- detecte la re-execution d'un notebook sous un kernel Python
    #   ou une signature float-repr differente de la base. Pure-Python, pas
    #   de secret, pas de GITHUB_TOKEN cote job. Garde same-repo universelle
    #   au niveau job (#13874) -- fork PRs skipped. Pull-request filtre par
    #   paths `**.ipynb` + 3 fichiers du garde (auto-couverture) + workflow
    #   lui-meme : declenche seulement quand un notebook est touche OU le
    #   garde evolue. workflow_dispatch pour re-run manuel avec base_ref
    #   parametrable. runs-on STATIQUE jambe Linux containerisee (meme
    #   routage que notebook-papermill-ratchet.yml, tranche 1 #13378).
    #   Concurrency cancel-in-progress (le balayage de kernel sur N notebooks
    #   peut etre rejoue sans frais). Pas de label pose. Rollback = revert
    #   de la PR (l'entree disparait de l'allowlist).
    # #16776 (owner myia-po-2023:CoursIA, PR #16801) : organ-duplication
    #   advisory -- signale les symboles ajoutes qui collident avec l'organ
    #   API d'une autre serie (scripts/audit/organ_api_index.yaml, regle
    #   organ-first). Pure-Python stdlib, garde same-repo au niveau job
    #   (#13874) -- fork PRs skipped, pull_request filtre par paths en
    #   auto-couverture des fichiers de l'organe (#8822), workflow_dispatch
    #   pour re-run manuel. runs-on STATIQUE jambe Linux containerisee
    #   (routage #14283 tranche 3). Advisory non-bloquant (sticky comment).
    #   Entree ajoutee par le repair du rouge WORKFLOW_NOT_ALLOWED signale
    #   par Hermes (CONCERNS 19/09) : la PR routait le job self-hosted sans
    #   toucher cette allowlist fail-closed. Rollback = revert de la PR.
    # #14623 (owner myia-po-2024:CoursIA, PR #18595) : docs-transients
    #   guard -- detecteur de fichiers transients (rapports/coordination)
    #   qui doivent vivre sur le dashboard, pas dans le repo (regle
    #   harness-hygiene, tier Ephemere). Pure-Python stdlib, garde
    #   same-repo au niveau job (#13874, if head.repo == repository),
    #   pull_request filtre par paths en auto-couverture des fichiers
    #   de l'organe, workflow_dispatch pour re-run manuel. runs-on
    #   STATIQUE jambe Linux containerisee (routage #14283 tranche 3).
    #   Entree ajoutee au repair du rouge WORKFLOW_NOT_ALLOWED (relecture
    #   ai-01 c.5917276825) : la PR routait le job self-hosted sans
    #   toucher cette allowlist fail-closed. Rollback = revert de la PR.
    # #19290 (owner myia-po-2026:CoursIA-2, PR #19296) : lean-formal-logic
    #   proof-integrity workflow pour le lake consumer FFL
    #   formal_logic_lean (Tweety <-> Lean, EPIC #15066). Le job
    #   `target-coverage` est advisory (exit 0 toujours) et tourne sur
    #   la jambe Linux containerisee (meme profil que
    #   docs-transients-guard / organ-duplication-advisory -- tranche 3).
    #   Les jobs `ci` et `proof-integrity` reutilisent lean-build.yml /
    #   lean-axiom.yml (GitHub-hosted), donc ne sont pas concernes par
    #   cette allowlist. Garde same-repo universelle parenthesee au
    #   niveau job (`if: head.repo.full_name == repository`).
    #   Rollback = revert de la PR (l'entree disparait de l'allowlist).
    "lean-formal-logic.yml",
    # #20049 (owner myia-po-2024:CoursIA-2, PR #20076) : live-read-freshness --
    #   troisieme axe des ratchets de carnet : la coherence entre la sortie
    #   COMMITTEE d'une cellule et l'etat COURANT du fichier qu'elle lit. Les
    #   ratchets existants comparent une base a une tete
    #   (check_output_collapse / check_source_collapse) ou mesurent la
    #   structure d'un carnet ; aucun ne relie une sortie committee a sa
    #   source vivante. Detecteur scripts/notebook_tools/
    #   check_live_read_freshness.py, stdlib-only, self-test a controle
    #   positif ET negatif. Le verdict par-PR est rendu par
    #   fast-lane-shadow.yml (entree TRANCHE2 de fast_lane_registry.py) ; ce
    #   fichier ne garde que workflow_dispatch (relance manuelle + cible
    #   d'identite). Aucun secret, aucun GITHUB_TOKEN cote job, garde
    #   same-repo universelle parenthesee au niveau job (#13874). Runner =
    #   jambe Linux containerisee (LINUX_RUNNER_LABELS, meme profil que
    #   translation-hot-drift-advisory.yml / notebook-plan-loss-gate.yml).
    #   Entree ajoutee par le repair du rouge WORKFLOW_NOT_ALLOWED remonte par
    #   `Scripts Tests (CPU)` (run 37931243189) : la PR routait le job
    #   self-hosted sans toucher cette allowlist fail-closed -- meme classe que
    #   organ-duplication-advisory.yml et docs-transients-guard.yml.
    #   Rollback = revert de la PR (l'entree disparait de l'allowlist).
    "live-read-freshness.yml",
    "pr-gate-rerun.yml",
    "pr-gate-sweep-health-advisory.yml",
    "stale-guard-red-sweep.yml",
    "adjacency-stale-sweep.yml",
    "concurrency-conj-guard.yml",
    "pr-path-collision-advisory.yml",
    "repeated-prose-advisory.yml",
    "repo-size-advisory.yml",
    "testpaths-coverage-guard.yml",
    "notebook-outputs-required.yml",
    # 2026-10-27 (#22461, lane myia-ai-01:CoursIA-2) : les 26 workflows
    #   deports vers ubuntu-latest par #22820/#22821/#22822 REDEVIENNENT
    #   porteurs d'une jambe self-hosted CONDITIONNELLE : la forme hybride
    #   de debordement (garde meme-depot && vars.CI_OVERFLOW_LOCAL ==
    #   'true' -> LINUX_RUNNER_LABELS, sinon ubuntu-latest). Par defaut
    #   (variable absente ou != 'true'), chaque job resout sur ubuntu-latest
    #   -- l'etat du 27/10 est conserve ; l'entree d'allowlist ne rend le
    #   pool local atteignable QUE si la variable est basculee par un
    #   operateur (phase A : gh variable set CI_OVERFLOW_LOCAL --body
    #   true|false --repo jsboige/CoursIA, jeton jsboige). Rollback =
    #   variable a false ou supprimee, sans toucher les fichiers.
    #   scripts-tests.yml N'EST PAS reconcerne : sa migration avait ete
    #   ANNULEE sur mesure (#22820 -- suite couplee a la forme du runner).
    "always-on-guards.yml",
    "always-on-guards-body.yml",
    "arxiv-attributions-guard.yml",
    "bios-companion-coverage.yml",
    "catalog-drift.yml",
    "docs-transients-guard.yml",
    "harness-coauthor-guard.yml",
    "label-paths-guard.yml",
    "manifest-description-visuelle-gate.yml",
    "notebook-cell-source-parses.yml",
    "notebook-exec-sequence-ratchet.yml",
    "notebook-kernel-drift-guard.yml",
    "notebook-latex-control-chars.yml",
    "notebook-link-render-check.yml",
    "notebook-math-render.yml",
    "notebook-papermill-ratchet.yml",
    "organ-duplication-advisory.yml",
    "orphaned-delivery-scan.yml",
    "owui-playwright-check.yml",
    "paragraph-length-advisory.yml",
    "quantconnect-notebook-freshness.yml",
    "scan-md-hierarchy-drift.yml",
    "solution-leak-guard.yml",
    "translation-drift.yml",
    "twin-parity.yml",
    "unique-check-run-names-guard.yml",

    # #23053 (vague 3, ordre de passage du coordinateur du 2026-10-28, lane
    #   myia-ai-01:CoursIA-2) : la famille « gardes et advisories » adopte la
    #   forme hybride de debordement (#22944/#23016). Ces quatre workflows
    #   n'avaient AUCUNE entree : leur job etait heberge et ne lisait jamais
    #   `CI_OVERFLOW_LOCAL` (mesure #23053 : 12 des 12 jobs en file
    #   demandaient `ubuntu-latest` alors que 12 slots locaux etaient libres).
    #   L'entree ne rend la jambe locale ATTEIGNABLE que si un operateur
    #   bascule la variable : par defaut (absente ou != 'true') le job resout
    #   sur ubuntu-latest, l'etat du 28/10 est conserve. La garde anti-fork vit
    #   DANS l'expression `runs-on` -- aucune ligne `if:` n'est ajoutee ni
    #   retiree. Chaque job porte un `timeout-minutes` ancre sur une duree
    #   mesuree (un job sans borne a tenu 16 slots ephemeres sur 18 le 15/10).
    #   Rollback = variable a `false` ou supprimee, sans toucher les fichiers.
    #   pedagogy-density-advisory.yml figure deja ci-dessus (tranche 4 #14283) :
    #   seule sa seconde jambe (`baseline-orphans-guard`) est convertie ici.
    "assert-memory-budget.yml",
    "docs-reference-guard.yml",
    "dryrun-sizing-control.yml",
    "twin-attestation-name-guard.yml",
    # local-path-waiver-guard.yml n'est PAS ajoute ici : il figure deja plus
    # haut dans l'allowlist. La branche #23053 l'y avait remis en doublon ; la
    # fusion de main l'a revele, l'entree en double est retiree et seule la
    # conversion du workflow (forme hybride, garde anti-fork dans `runs-on`)
    # reste portee par cette PR.
    # #23053 (meme vague, meme lane, 2026-10-29) : `creation-provenance-advisory.yml`
    #   est un workflow NEUF -- il est arrive sur main par #23185 ("Feat(budget,
    #   #23174)", meme lane), donc APRES que le cliquet soit ecrit, et son job
    #   etait nu sur `ubuntu-latest` (violation `HOSTED_PR_JOB_UNEXCEPTED`).
    #   Conversion en forme hybride dans la meme PR : meme expression que les
    #   workflows ci-dessus, meme `if:` anti-fork conserve, `timeout-minutes: 10`.
    #   La variable vaut `false` au 29/10 : le routage est donc INCHANGE (100 %
    #   heberge) -- la conversion retire la violation sans changer ou le job
    #   s'execute. Rollback = variable a `false` ou supprimee, sans toucher les
    #   fichiers.
    "creation-provenance-advisory.yml",
    # 2026-10-31 (c2740, lane myia-ai-01:CoursIA) : rouge de `main` apres le
    #   squash-merge de #23063. Le cliquet a ete valide sur une base qui ne
    #   contenait pas encore `sudoku-tests.yml` (82734d24b) ni
    #   `twin-index-collision-gate.yml` (38141f743), arrives sur main entre
    #   l'ecriture et le merge ; `scripts-tests.yml:qc-mcp-lite-tests` est
    #   arrive apres. Les trois jobs etaient nus sur `ubuntu-latest`
    #   (HOSTED_PR_JOB_UNEXCEPTED). Conversion en forme hybride, meme
    #   expression que ci-dessus ; chaque job porte deja son `timeout-minutes`
    #   (10, 15, 15). `scripts-tests.yml` figure deja plus haut dans
    #   l'allowlist. La variable vaut `true` depuis le 2026-10-31T04:09Z : le
    #   routage change reellement (jambe locale quand le controleur deborde).
    #   Rollback = variable a `false`, sans toucher les fichiers.
    "sudoku-tests.yml",
    "twin-index-collision-gate.yml",

    # #23053 (meme PR, meme lane, 2026-10-31) : `cycle-time-guard.yml` est
    #   lui aussi un workflow NEUF pour le cliquet -- son job `cycle_time`
    #   etait nu sur `ubuntu-latest` (violation `HOSTED_PR_JOB_UNEXCEPTED`),
    #   alors meme qu'il porte `timeout-minutes: 10` et une garde anti-fork.
    #   Conversion en forme hybride dans la meme PR : meme expression que les
    #   workflows ci-dessus, meme `if:` anti-fork conserve, borne de temps
    #   conservee.
    #   La variable vaut `false` au 2026-10-31 : le routage est donc INCHANGE
    #   (100 % heberge) -- la conversion retire la violation sans changer ou
    #   le job s'execute. Rollback = variable a `false` ou supprimee, sans
    #   toucher les fichiers.
    #   L'argument d'origine du workflow (le garder heberge : lecteur pur,
    #   0,7 s, aucun besoin local) reste vrai -- il porte desormais sur la
    #   jambe locale elue par l'operateur, pas sur la forme du `runs-on`.
    "cycle-time-guard.yml",

    # ------------------------------------------------------------------
    # #23053 famille (c) -- Lean, Quarto et slides.
    # 2026-10-28 (lane myia-ai-01:CoursIA-2) : les jobs declenches par
    # `pull_request` de ces workflows passent a la forme hybride de debordement
    # (#22937/#22944/#23016) : garde meme-depot && vars.CI_OVERFLOW_LOCAL ==
    # 'true' -> LINUX_RUNNER_LABELS, sinon ubuntu-latest. Par defaut (variable
    # absente ou != 'true'), chaque job resout sur ubuntu-latest : l'etat du
    # 27/10 est conserve, et l'entree d'allowlist ne rend le pool local
    # atteignable QUE si un operateur bascule la variable.
    # Les six autres workflows de la famille (lean-conway, lean-i18n-drift,
    # lean-knot, quarto-pages-deploy, slides-build-advisory,
    # slides-composition-pr-relay) etaient DEJA declares plus haut : seul
    # l'absent est ajoute ici.
    # `lean-planning.yml` n'est PAS declare : le workflow a ete SUPPRIME sur
    # main par #23467 (#13751 -- migration de planning_lean vers la matrice
    # CI, le wrapper est retire) entre la base de cette PR et aujourd'hui. Une
    # entree d'allowlist pointant un workflow inexistant serait une reference
    # morte ; la forme hybride de la famille (c) s'applique donc a
    # `lean-ci-matrix.yml`, qui porte les jobs planning_lean depuis la
    # migration.
    # Exceptions nommees, laissees hebergees : quarto-pages-deploy `build`
    # (OOM mesure sur le pool, #15202) et `deploy` (push-only, deploy-pages +
    # OIDC/PAGES). Rollback = revert de la PR (l'entree disparait de
    # l'allowlist, et le garde fail-closed refuse alors le runs-on).
    # ------------------------------------------------------------------
    "lean-ci-matrix.yml",

    # 2026-10-28 (#23053 famille b -- « les tests », lane
    #   myia-ai-01:CoursIA-2) : ces 6 suites de tests n'avaient AUCUNE jambe
    #   self-hosted sur main ; elles recoivent une jambe CONDITIONNELLE, la
    #   forme hybride de debordement deja auditee (#22461 phase A : garde
    #   meme-depot && vars.CI_OVERFLOW_LOCAL == 'true' -> LINUX_RUNNER_LABELS,
    #   sinon ubuntu-latest). Par defaut (variable absente ou != 'true'),
    #   chaque job resout sur ubuntu-latest : l'etat du 27/10 est conserve, et
    #   cette entree ne rend le pool local atteignable QUE si un operateur
    #   bascule la variable (gh variable set CI_OVERFLOW_LOCAL --body
    #   true|false --repo jsboige/CoursIA, jeton jsboige). Rollback = variable
    #   a false ou supprimee, sans toucher les fichiers.
    #   Deja presents dans l'ensemble ci-dessus, donc NON reajoutes :
    #   ict-tests.yml, ml-tests.yml, scripts-tests.yml, validation-matrix.yml.
    #   Sur scripts-tests.yml, seul le job `adk-contracts` est reconcerne -- le
    #   job `scripts-tests` reste sur la jambe locale STATIQUE (suite couplee a
    #   la forme du runner, #22820). Sur validation-matrix.yml, le job
    #   `validate` reste STATIQUE local : le basculer sur ubuntu-latest par
    #   defaut serait un recul, il ne recoit donc pas la forme hybride.
    # ------------------------------------------------------------------
    "dotnet-AgentSafetyAnalyzer.yml",
    "dotnet-ArgumentAnalysis.yml",
    "dotnet-OrphanApps.yml",
    "dotnet-Shared.Tests.yml",
    "gametheory-tests.yml",
    "genai-helpers-tests.yml",
    # 2026-10-27 (#22937 vague 2, lane myia-ai-01:CoursIA-2) : meme forme
    #   hybride de debordement que la phase A (#22461), appliquee aux
    #   workflows a fort volume qui n'etaient PAS dans la phase A.
    #   Les trois autres fichiers de la vague 2
    #   (notebook-execution-required.yml, always-on-metadata-guards.yml,
    #   notebook-validation.yml) sont deja dans l'allowlist -- ils y etaient
    #   depuis la tranche 3c (#14283), avant leur deport Q35 du 27/10.
    #   `twin-parity.yml` y est aussi, mais il est porte par une PR
    #   dediee (#22944) : les deux PRs ne peuvent pas toucher le meme
    #   workflow, et le perimetre accorde est « 5 workflows par volume
    #   decroissant ».
    #   Perimetre : 5 workflows, 6 jobs. Exclus, avec leur motif :
    #   - codeql.yml : le setup par defaut de GitHub-heberge le job, la
    #     ligne `runs-on` du fichier n'est pas honoree ;
    #   - lean-ci-matrix.yml : la toolchain Lean vit dans une image distincte
    #     (label `coursia-lean`), pas dans le pool `coursia-linux` ;
    #     [2026-10-29, fusion de main dans #23053 famille (c) : ce motif vise
    #     les jobs de BUILD, pas le dispatcher. Sur main, ce fichier n'a qu'un
    #     job, `lean-matrix-changes`, qui checkout, calcule les fichiers
    #     changes et appelle `scripts/lean/lake_matrix_dispatch.py` -- il
    #     n'execute aucun `lake`. Le build reste delegue au workflow
    #     reutilisable `lean-build.yml`, qui porte ses propres labels. Le
    #     dispatcher est donc convertible vers `coursia-linux`, et il l'est
    #     ci-dessous.]
    #   - local-path-waiver-guard.yml et perimeter-review-guard.yml :
    #     declencheurs `issue_comment` et `pull_request_review`, classes
    #     FORK_REACHABLE par l'instrument (default-deny) ;
    #     [2026-10-29, fusion de main dans #23053 : la premisse ne vaut plus
    #     pour local-path-waiver-guard.yml -- son `on:` ne porte desormais que
    #     `pull_request` (opened/synchronize/reopened) et `workflow_dispatch`,
    #     aucun declencheur atteignable par un fork. Il entre donc dans
    #     l'allowlist ci-dessous et passe en forme hybride, garde anti-fork
    #     dans l'expression `runs-on`. perimeter-review-guard.yml reste exclu.]
    #   - les deux starvation-advisory : un chien de garde de la file ne
    #     doit pas occuper la file qu'il observe ;
    #   - ict-tests.yml : venv + pyphi/numpy/scipy, 8,1 min medianes -- le
    #     debordement absorbe d'abord les jobs courts ;
    #   - quarto-pages-deploy.yml : `build` et `deploy` dependent du
    #     service GitHub Pages (upload-pages-artifact, deploy-pages + OIDC) ;
    #     seul `validate-pr` est portable (Quarto par tarball curl).
    "quarto-render-list-freshness.yml",
    "enrich-quality-gate.yml",
}
GITHUB_HOSTED_LABELS = {
    "ubuntu-latest",
    "ubuntu-24.04",
    "ubuntu-22.04",
    "ubuntu-20.04",
    "ubuntu-slim",
    "windows-latest",
    "windows-2025",
    "windows-2022",
    "windows-2019",
    "macos-latest",
    "macos-26",
    "macos-15",
    "macos-14",
    "macos-13",
}
LOCAL_REUSABLE_PREFIX = "./.github/workflows/"
SAME_REPO_REUSABLE_PATTERN = re.compile(
    r"^jsboige/CoursIA/\.github/workflows/[^/@]+@main$"
)
SAME_REPO_GUARD = (
    "github.event.pull_request.head.repo.full_name == github.repository"
)
# Universal form (#13874): ne s'appuie pas sur la valeur textuelle de
# github.event_name (qui distingue pull_request de pull_request_target,
# le second etant le vecteur d'exfiltration classique sur runner public).
# Teste la presence du champ pull_request + l'identite du repo source,
# couvrant les deux variantes de declencheur en un seul predicat.
# Acceptee en plus de la forme directe SAME_REPO_GUARD.
SAME_REPO_GUARD_UNIVERSAL = (
    "github.event.pull_request.head.repo.full_name == null "
    "|| github.event.pull_request.head.repo.full_name == github.repository"
)
ACCEPTED_SAME_REPO_GUARDS = frozenset({SAME_REPO_GUARD, SAME_REPO_GUARD_UNIVERSAL})
# Evenements dont le code de workflow vient de la branche par defaut mais dont
# le payload nomme une pull request potentiellement issue d'un fork : un job
# peut faire `checkout refs/pull/N/head` et executer du code de fork sur le
# runner. Refuses sur self-hosted au meme titre que pull_request_target
# (#14148, reserve NanoClaw n.2). A l'inverse, push / schedule /
# workflow_dispatch ne portent que des refs du depot : la branche `== null`
# de la garde universelle y est sure par construction, pas par accident.
FORK_REACHABLE_TRIGGERS = frozenset({
    "issue_comment",
    "pull_request_review",
    "pull_request_review_comment",
})
# Safe triggers for a self-hosted job (#14201, tranche 2). push, schedule and
# workflow_dispatch only run repository-owned refs, so the `== null` branch of
# the universal guard is safe there by construction (NanoClaw concern 2,
# measured on the routed workflows: banner-guard.yml / notebook-cell-source-
# parses.yml / hooks-parity.yml rely on push / schedule). pull_request is safe
# only WITH the same-repo guard (enforced above). Everything else is rejected
# fail-closed: a denylist alone (the FORK_REACHABLE_TRIGGERS form of #14148) is
# fail-OPEN on any trigger we have not enumerated -- check_run / check_suite,
# whose payloads carry pull_requests[], and any future GitHub event that does
# the same. Default-deny is the form that does not perish with each new event.
SAFE_SELF_HOSTED_TRIGGERS = frozenset({
    "pull_request",
    "push",
    "schedule",
    "workflow_dispatch",
})
DEFAULT_WORKFLOWS_DIR = Path(__file__).resolve().parents[2] / ".github" / "workflows"

# ---------------------------------------------------------------------------
# Cliquet des jobs heberges sur pull_request (#23053)
# ---------------------------------------------------------------------------
# La forme hybride de debordement (#22944, #23016) ne sert a rien si un job
# reste fige sur `ubuntu-latest` nu : il ne lit jamais `CI_OVERFLOW_LOCAL` et
# rejoint la file hebergee meme quand le parc local est libre. Mesure
# fondatrice (#23053, 2026-10-28 04:45Z) : 56 runs en file, 12 slots locaux
# libres, et les 12 jobs echantillonnes demandaient TOUS `ubuntu-latest`. C'est
# un defaut de routage, pas de capacite -- et sans cliquet, le prochain
# workflow ajoute recree la file.
#
# Ce cliquet S'AJOUTE aux verifications existantes, il n'en remplace aucune :
# il a ses propres codes, sa propre passe, et ne touche ni l'allowlist, ni la
# forme hybride, ni les gardes de declencheur.
#
# Deux invariants :
#   1. tout job d'un workflow declenche par `pull_request` dont le `runs-on`
#      est `ubuntu-latest` NU (chaine seule, ou liste `[ubuntu-latest]`) doit
#      appartenir a un workflow declare dans HOSTED_PR_JOB_EXCEPTIONS ;
#   2. la liste courante ne fait que RETRECIR : ses cles doivent etre un
#      sous-ensemble de HOSTED_PR_JOB_EXCEPTIONS_BASELINE. Une exception
#      absente de la baseline est elle-meme une violation.
#
# Faire evoluer la liste : une PR de famille convertit des workflows et retire
# leurs entrees de HOSTED_PR_JOB_EXCEPTIONS ET de
# HOSTED_PR_JOB_EXCEPTIONS_BASELINE dans le meme commit. Ajouter une entree
# reste possible mais exige d'etendre la baseline : c'est un geste delibere,
# visible en diff et en review. Le garde ne lit pas les intentions ; il rend
# l'ecart bloquant plutot que silencieux.
#
# Limite assumee : l'exception porte sur le WORKFLOW. Un job nu ajoute dans un
# workflow deja excepte echappe au cliquet jusqu'a la conversion de ce
# workflow. Le cliquet empeche la creation de nouvelles files ; il ne dispense
# pas de lire le diff. La granularite par job rendrait la liste instable (les
# jobs changent de nom plus souvent que les workflows) sans fermer cette
# limite sur le fond.
HOSTED_PR_JOB_EXCEPTIONS: dict[str, str] = {
    # --- famille (c) : conversion en vol dans la PR #23059 (ouverte) --------
    "lean-ci-matrix.yml": (
        "famille (c) : le dispatcher `changes` reste nu, sa conversion est "
        "portee par la PR #23059 (ouverte au 2026-10-30)"
    ),
    # --- jobs heberges pour une raison propre, mesuree dans le fichier -----
    "codeql.yml": (
        "CodeQL en advanced setup (#22548) : `analyze` telecharge le bundle "
        "CodeQL, lance l'analyse et televerse du SARIF (`security-events: "
        "write`), ~14 min/run heberge ; son routage sur le conteneur ephemere "
        "n'est pas verifie -- #23053 laisse la question ouverte"
    ),
    "ml-tests.yml": (
        "job `prover-tests` heberge : offre GitHub d'abord (consigne user "
        "#17397 du 2026-10-25, note portee par le fichier)"
    ),
    "notebook-execution-required.yml": (
        "job `golden-set-execute` heberge : offre GitHub d'abord (consigne "
        "user #17397 du 2026-10-25, note portee par le fichier)"
    ),
    "perimeter-review-guard.yml": (
        "declencheur `pull_request_review` classe FORK_REACHABLE (#14201) : le "
        "runner local est interdit, le garde refuse la jambe self-hosted"
    ),
    "quarto-pages-deploy.yml": (
        "`build` : OOM du rendu complet mesuree sur le pool (1145/1276 "
        "notebooks, run 34217750689, #15202) ; `deploy` : push-only, "
        "OIDC/PAGES ; `validate-pr` : offre GitHub d'abord (#17397)"
    ),
    "secret-scan.yml": (
        "jambe `gitleaks-fork` : elle n'existe QUE pour les PRs de fork (son "
        "`if:` exclut le depot lui-meme) et appelle `docker run`, dont le "
        "socket manque au pool conteneur (uid 1001, no-new-privileges) ; la "
        "jambe self-hosted voisine couvre les runs du depot"
    ),
    "slides-build-advisory.yml": (
        "job `slides-build-advisory` heberge : offre GitHub d'abord (consigne "
        "user #17397 du 2026-10-25) ; le fichier documente le nocturne "
        "(#12817) et son runs-on statique"
    ),
}

# Figee a la creation du cliquet (#23053, 2026-10-28) a 21 entrees, puis
# reduite le 2026-10-30 aux 8 exceptions vivantes : les conversions #23016
# (merge 2026-10-29) et #23058 famille (b) (merge 2026-10-30) sont arrivees
# sur main et leurs entrees sont retirees avec elle, ainsi que celle de
# lean-planning.yml, supprime par #23467. Elle NE S'ELARGIT PAS --
# seule une decision de review peut le faire, et la PR qui nomme une nouvelle
# exception retire au moins autant d'entrees dans le meme commit.
HOSTED_PR_JOB_EXCEPTIONS_BASELINE: frozenset[str] = frozenset({
    "codeql.yml",
    "lean-ci-matrix.yml",
    "ml-tests.yml",
    "notebook-execution-required.yml",
    "perimeter-review-guard.yml",
    "quarto-pages-deploy.yml",
    "secret-scan.yml",
    "slides-build-advisory.yml",
})

# -- #22954: ratchet baseline for job-level timeout-minutes ------------------
# A job that can reach a self-hosted runner without `timeout-minutes` can hold
# its slot for six hours (the Actions default) if it freezes; that slot is then
# missing from the PR gates. The rule is measured on `origin/main` 2f1291f01
# (2026-10-29): **138 self-hosted jobs, 75 without a job-level bound** -- 12 in
# the audited hybrid/overflow form (#22461) and **63 static**. The 12 are bound
# by the PR that introduced this ratchet; the 63 static ones are the debt this
# baseline names, so the guard can be green at merge while refusing to let the
# set GROW. Retire a line as soon as its job is bound; `--update-baseline`
# rewrites the file from what is measured.
BASELINE_NAME = "self_hosted_timeout_baseline.txt"
DEFAULT_BASELINE = Path(__file__).with_name(BASELINE_NAME)


def load_baseline(path: Path) -> set[str]:
    """Read the tolerated `workflow.yml:job` keys.

    The key is `workflow:job`, never `workflow:line`: a line-anchored key
    expires as soon as anything is inserted above it, and a guard that reddens
    on an unchanged site is the fastest way to get itself disabled.
    """
    if not path.is_file():
        return set()
    return {
        line.strip()
        for line in path.read_text(encoding="utf-8").splitlines()
        if line.strip() and not line.startswith("#")
    }


@dataclass(frozen=True)
class Violation:
    workflow: str
    job: str
    code: str
    message: str


@dataclass(frozen=True)
class ScanResult:
    workflows_scanned: int
    jobs_scanned: int
    self_hosted_jobs: int
    violations: list[Violation]
    broken: list[str]
    # Workflows encore exceptes du cliquet #23053 (nom, trie). Expose pour que
    # le verdict -- texte et JSON -- nomme la liste au lieu de la laisser
    # implicite : une liste d'exceptions invisible est une liste qui ne
    # retrecit pas.
    hosted_pr_exceptions: list[str] = field(default_factory=list)
    # Baseline effectivement utilisee pour le scan (toujours un sur-ensemble de
    # ``hosted_pr_exceptions`` quand l'invariant tient). Portee par le resultat
    # pour que le verdict -- texte et JSON -- ne mente pas quand un test
    # injecte ses propres listes.
    hosted_pr_exceptions_baseline: list[str] = field(default_factory=list)
    # -- #22954: job-level timeout-minutes ratchet ---------------------------
    # Defaults keep every existing reader (and every synthetic-workflow test)
    # working unchanged: the ratchet is only engaged by --check-timeouts.
    timeouts_checked: bool = False
    timeout_missing: int = 0
    timeout_baselined: int = 0


def _load_yaml():
    try:
        import yaml
    except ImportError:
        return None
    return yaml


def _parse_workflow(text: str, yaml: Any) -> dict[str, Any] | None:
    """Parse Actions YAML while preserving the top-level ``on`` key."""
    lines: list[str] = []
    for line in text.splitlines():
        if line.startswith("on:") and (
            len(line) == 3 or line[3] in (" ", "[", "\t")
        ):
            lines.append('"on":' + line[3:])
        else:
            lines.append(line)
    try:
        data = yaml.safe_load("\n".join(lines))
    except yaml.YAMLError:
        return None
    return data if isinstance(data, dict) else None


def _triggers(data: dict[str, Any]) -> set[str]:
    value = data.get("on", data.get(True))
    if isinstance(value, dict):
        return {str(item) for item in value}
    if isinstance(value, list):
        return {str(item) for item in value}
    if isinstance(value, str):
        return {value}
    return set()


def _contains_expression(value: Any) -> bool:
    if isinstance(value, str):
        return "${{" in value
    if isinstance(value, list):
        return any(_contains_expression(item) for item in value)
    if isinstance(value, dict):
        return any(
            _contains_expression(key) or _contains_expression(item)
            for key, item in value.items()
        )
    return False


def _is_github_hosted_label(label: str) -> bool:
    return label.lower() in GITHUB_HOSTED_LABELS


def _runner_selection(
    runs_on: Any,
) -> tuple[bool, str | None, set[str], str | None]:
    """Return (is_self_hosted, group, labels, error) for a static selection.

    Any explicit runner group is self-hosted. A scalar/list label is considered
    GitHub-hosted only when every value names a documented hosted-image family;
    custom labels route to self-hosted runners even when the implicit
    ``self-hosted`` label is omitted from the workflow.
    """
    if isinstance(runs_on, str):
        labels = {runs_on.lower()}
        return not _is_github_hosted_label(runs_on), None, labels, None
    if isinstance(runs_on, list):
        if not runs_on or not all(isinstance(item, str) for item in runs_on):
            return False, None, set(), "runs-on list must contain labels"
        labels = {item.lower() for item in runs_on}
        is_self_hosted = any(not _is_github_hosted_label(item) for item in labels)
        return is_self_hosted, None, labels, None
    if isinstance(runs_on, dict):
        group = runs_on.get("group")
        raw_labels = runs_on.get("labels", [])
        if group is None and "labels" not in runs_on:
            return False, None, set(), "runs-on mapping needs group or labels"
        if group is not None and not isinstance(group, str):
            return False, None, set(), "runner group must be a string"
        if isinstance(raw_labels, str):
            labels = {raw_labels.lower()}
        elif isinstance(raw_labels, list) and raw_labels and all(
            isinstance(item, str) for item in raw_labels
        ):
            labels = {item.lower() for item in raw_labels}
        elif raw_labels == [] and group is not None:
            labels = set()
        else:
            return False, None, set(), "runner labels must be a string or list"
        is_self_hosted = group is not None or any(
            not _is_github_hosted_label(item) for item in labels
        )
        return is_self_hosted, group, labels, None
    return False, None, set(), "runs-on has an unsupported type"


# Audited hybrid runs-on (#13363 jambe B). Exactly ONE shape is statically
# provable, under TWO enumerated guards: the self-hosted leg is reached ONLY
# when the exact same-repo guard is true -- the #22461 guard additionally
# requires vars.CI_OVERFLOW_LOCAL == 'true'; everything else falls back to a
# GitHub-hosted label. Guard, label set and fallback are enumerated -- any
# variation (different guard, different labels, different fallback) stays an
# unauditable expression and keeps the DYNAMIC_RUNS_ON rejection.
#
# c.509 (dispatch c.2180, owner myia-ai-01:CoursIA-2) : the audited label
# set is now a TUPLE of accepted dedicated sets, not a single set. The
# waiter pool (WAITER_LABELS) keeps the #13363 B role (pr-gate.yml
# aggregator that polls up to 45 min -- the dedicated label is what lets
# the gate WAIT without holding a work slot, arbitrage ai-01 2026-09-02).
# The Linux pool (LINUX_RUNNER_LABELS, [self-hosted, coursia-ephemeral,
# coursia-linux]) is added to relieve the ubuntu-latest queue (#14283
# tranche 5 + Q35 etape 4 tranche 2): the same audited dynamic form now
# applies to pure-Python guards (gitleaks, kernel-drift, papermill
# ratchet, outputs-required) routed to the containerized Linux leg
# without forfeiting the same-repo guard or the github-hosted fallback.
# Every other expression stays an unauditable DYNAMIC_RUNS_ON.
#
# #22461 (dispatch ai-01 2026-10-27) : SECONDE garde enumeree. La garde
# meme-depot conjoine a la variable de debordement vars.CI_OVERFLOW_LOCAL
# == 'true' -- le parc local ne recoit le job que si un operateur a bascule
# la variable de depot (phase A du debordement : l'offre hebergee saturee
# portait 28 des 29 jobs en file de l'echantillon, mesure #22461). Le nom
# de la variable et sa valeur sont ENUMERES : toute autre variable, toute
# autre valeur, toute autre expression reste hors audit (DYNAMIC_RUNS_ON,
# refus inchange). Cette garde n'admet QUE le pool Linux ; la garde
# d'origine conserve ses deux pools -- rien n'est retreci.
HYBRID_RUNS_ON_GUARD = SAME_REPO_GUARD
HYBRID_RUNS_ON_LABELS = WAITER_LABELS  # kept for backward compat (single set)
HYBRID_RUNS_ON_LABEL_SETS = (WAITER_LABELS, LINUX_RUNNER_LABELS)
HYBRID_RUNS_ON_FALLBACK = "ubuntu-latest"
# Variable de depot de la seconde garde (phase A du debordement, #22461) :
# nom et valeur ENUMERES -- cf. bloc de commentaire ci-dessus.
CI_OVERFLOW_LOCAL_VAR = "CI_OVERFLOW_LOCAL"
HYBRID_RUNS_ON_OVERFLOW_GUARD = (
    f"{SAME_REPO_GUARD} && vars.{CI_OVERFLOW_LOCAL_VAR} == 'true'"
)
# Garde enumeree -> ensembles de labels admis pour la forme hybride. La
# garde d'origine (#13363/c.509) garde exactement ses deux pools ; la garde
# overflow (#22461) n'admet que LINUX_RUNNER_LABELS.
HYBRID_RUNS_ON_GUARD_LABEL_SETS: dict[str, tuple[set[str], ...]] = {
    HYBRID_RUNS_ON_GUARD: HYBRID_RUNS_ON_LABEL_SETS,
    HYBRID_RUNS_ON_OVERFLOW_GUARD: (LINUX_RUNNER_LABELS,),
}
_HYBRID_PATTERN = re.compile(
    r"^\s*\("
    r"(?P<guard>[^()]+)"
    r"\)\s*&&\s*fromJSON\(\s*(?P<q1>['\"])(?P<labels>.*?)(?P=q1)\s*\)"
    r"\s*\|\|\s*(?P<q2>['\"])(?P<fallback>.*?)(?P=q2)\s*$"
)


def _hybrid_runs_on(runs_on: Any) -> dict[str, set[str]] | None:
    """Return the audited hybrid legs for ``runs_on``, or None if it is not
    one of the enumerated forms (#13363, then the #22461 overflow guard).
    The caller keeps the DYNAMIC_RUNS_ON rejection for every other
    expression."""
    if not isinstance(runs_on, str):
        return None
    text = runs_on.strip()
    if not (text.startswith("${{") and text.endswith("}}")):
        return None
    match = _HYBRID_PATTERN.match(text[3:-2].strip())
    if match is None:
        return None
    guard = " ".join(match.group("guard").split())
    allowed_label_sets = HYBRID_RUNS_ON_GUARD_LABEL_SETS.get(guard)
    if allowed_label_sets is None:
        return None
    if match.group("fallback") != HYBRID_RUNS_ON_FALLBACK:
        return None
    try:
        labels = {str(item) for item in json.loads(match.group("labels"))}
    except json.JSONDecodeError:
        return None
    if labels not in allowed_label_sets:
        return None
    return {"labels": labels}


# --- Parc local mesure par le controleur de debordement (#22937 phase A) ----
#
# Le controleur mesure l'occupation du parc LOCAL (label `coursia-linux`) et
# celle de l'offre HEBERGEE (label `ubuntu-latest`). Sa lecture locale doit
# viser les runs qui PEUVENT porter un job local : sinon elle consomme son
# budget de lectures sur des runs qui n'en portent pas (mesure du
# coordinateur, 2026-10-28 16:55Z : 250 runs anciens en file, presque tous en
# attente d'`ubuntu-latest`, budget 120 lectures -> la lecture locale se
# tronque avant d'etablir quoi que ce soit, et la soupape se ferme exactement
# dans le regime ou elle doit s'ouvrir).
#
# Ce module possede la connaissance « quel workflow peut atterrir sur quel
# runner » : la liste est donc derivee ICI, pas reecrite dans le controleur.
LOCAL_PARK_LABEL = "coursia-linux"


def _job_can_reach_local_park(runs_on: Any) -> bool:
    """True si un job portant ce `runs-on` peut atterrir sur le parc local.

    - selection STATIQUE (scalaire, liste ou mapping) : il suffit qu'un de
      ses labels soit celui du parc local ;
    - forme hybride auditee : la jambe locale y est atteinte quand la garde
      est vraie -> capable ;
    - expression dynamique NON auditee : traitee comme CAPABLE. Une
      expression non auditee peut atterrir n'importe ou ; l'ignorer
      cacherait une affamescence locale -- c'est le piege que cet organe
      combat partout ailleurs.
    """
    hybrid = _hybrid_runs_on(runs_on)
    if hybrid is not None:
        return LOCAL_PARK_LABEL in hybrid["labels"]
    if _contains_expression(runs_on):
        return True
    _is_self_hosted, _group, labels, _error = _runner_selection(runs_on)
    return LOCAL_PARK_LABEL in labels


def local_capable_workflows(
    workflows_dir: Path = DEFAULT_WORKFLOWS_DIR,
) -> tuple[set[str], str]:
    """Derive les workflows capables de porter un job sur le parc local.

    Rend `(chemins, motif)`. Les chemins portent la forme de `run.path` dans
    l'API des runs (`.github/workflows/<fichier>`). Le motif est VIDE quand la
    derivation a reussi, et NON VIDE sinon.

    Echec -- repertoire absent, PyYAML absent, fichier illisible, YAML
    invalide, aucun workflow -- : ensemble VIDE et motif. Un ensemble vide ne
    se lit JAMAIS « aucun workflow local » (ce serait une affirmation de
    NON-affamescence locale) : il se lit « la liste n'est pas etablie »
    (fail-CLOSED, meme convention que `derive_cohort_workflows`).

    Un job dont le `runs-on` n'est pas analysable n'est jamais traite comme
    absent : il est traite comme CAPABLE. Seule la LECTURE du fichier peut
    faire echouer la derivation.

    Les APPELS de workflow reutilisable sont propages : le `run.path` d'un run
    est le workflow APPELANT, pas le workflow appele. Un appelant qui
    appelle un workflow local est donc capable lui aussi (sinon ses jobs
    locaux seraient invisibles) ; un appelant d'un workflow reutilisable
    MEME-REPO est traite comme capable (le contenu distant n'est pas
    analysable ici, et l'ignorer cacherait une affamescence).
    """
    yaml = _load_yaml()
    if yaml is None:
        return set(), "PyYAML est indisponible"

    workflows_dir = Path(workflows_dir)
    if not workflows_dir.is_dir():
        return set(), f"repertoire des workflows absent ({workflows_dir})"
    try:
        files = sorted(
            list(workflows_dir.glob("*.yml")) + list(workflows_dir.glob("*.yaml"))
        )
    except OSError as exc:
        return set(), f"enumeration des workflows impossible ({exc})"
    if not files:
        return set(), f"aucun workflow dans {workflows_dir}"

    parsed: dict[str, dict[str, Any]] = {}
    for path in files:
        try:
            text = path.read_text(encoding="utf-8")
        except OSError as exc:
            return set(), f"lecture de {path.name} impossible ({exc})"
        data = _parse_workflow(text, yaml)
        if data is None:
            return set(), f"YAML de {path.name} invalide"
        parsed[path.name] = data

    capable: set[str] = set()
    calls: dict[str, set[str]] = {}
    for name, data in parsed.items():
        jobs = data.get("jobs")
        if not isinstance(jobs, dict):
            continue
        for job in jobs.values():
            if not isinstance(job, dict):
                continue
            if "uses" in job:
                reusable = str(job["uses"])
                if reusable.startswith(LOCAL_REUSABLE_PREFIX):
                    calls.setdefault(name, set()).add(
                        reusable[len(LOCAL_REUSABLE_PREFIX):].split("@", 1)[0]
                    )
                elif SAME_REPO_REUSABLE_PATTERN.fullmatch(reusable):
                    # Contenu distant non analysable ici : l'appelant est
                    # traite comme capable (fail-safe).
                    capable.add(name)
                continue
            runs_on = job.get("runs-on")
            if runs_on is None:
                continue
            if _job_can_reach_local_park(runs_on):
                capable.add(name)
                break

    # Propagation : un appelant d'un workflow capable l'est aussi. Le
    # `run.path` designe l'APPELANT -- sans cette propagation, les jobs d'un
    # workflow reutilisable local seraient invisibles pour la mesure locale.
    changed = True
    while changed:
        changed = False
        for caller, callees in calls.items():
            if caller in capable:
                continue
            for callee in callees:
                if callee in capable:
                    capable.add(caller)
                    changed = True
                    break

    return {f".github/workflows/{name}" for name in capable}, ""


def _normalise_condition(value: Any) -> str:
    if not isinstance(value, str):
        return ""
    condition = value.strip()
    if condition.startswith("${{") and condition.endswith("}}"):
        condition = condition[3:-2].strip()
    return " ".join(condition.split())


def _starts_with_accepted_guard(condition: str) -> bool:
    """True iff ``condition`` leads with one of the accepted same-repo
    guards, optionally followed by `&& ...` selection predicates. The guard
    must be the LEAD predicate, and any suffix joined by `||` is rejected
    (the `||` would let the guard fall through). The standalone tests
    ``test_guard_weakened_by_or_is_rejected`` and
    ``test_universal_guard_weakened_by_or_is_rejected`` verify that
    `|| always()` is refused.

    Parentheses: the direct guard may be bare or wrapped. The UNIVERSAL guard
    carries an internal `||`, so it is accepted bare only when it is the whole
    condition; combined with `&& ...` it MUST be wrapped --
    `(<universal>) && <selection>`. This is not a parser limitation to work
    around: in GitHub expressions `&&` binds tighter than `||`, so the bare
    form reads `A == null || (A == repo && sel)` and runs the job on every
    non-pull_request event regardless of the selection. The bare scan below
    splits at the first top-level operator (the internal `||`) and rejects;
    ``_guard_violation_message`` names the required parentheses
    (#14148, NanoClaw concern 1).
    """
    if not condition:
        return False
    # Short-circuit: the whole condition is itself an accepted guard.
    if condition in ACCEPTED_SAME_REPO_GUARDS:
        return True
    lead = condition
    suffix = ""
    if lead.startswith("("):
        depth = 0
        for idx, ch in enumerate(lead):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0:
                    lead = lead[: idx + 1]
                    suffix = condition[idx + 1 :].lstrip()
                    break
    else:
        # Bare form: scan character by character for a top-level ` && `
        # or ` || ` (4 chars including surrounding spaces). An external
        # `&&` joining a selection predicate is OK; an external `||` is
        # rejected because it lets the guard fall through. The internal
        # `||` of the universal form is captured by the short-circuit
        # above (whole-condition match), so this branch only fires when
        # the condition is followed by an external operator.
        depth = 0
        i = 0
        while i < len(lead) - 3:
            ch = lead[i]
            if ch == "(":
                depth += 1
                i += 1
                continue
            if ch == ")":
                depth -= 1
                i += 1
                continue
            if depth == 0 and lead[i : i + 4] in (" && ", " || "):
                lead = lead[:i]
                suffix = condition[i:]
                break
            i += 1
    for accepted in ACCEPTED_SAME_REPO_GUARDS:
        if lead == accepted or lead == "(" + accepted + ")":
            if not suffix:
                return True
            if suffix.lstrip().startswith("&&"):
                return True
            return False
    return False


def _guard_violation_message(condition: str) -> str:
    """Name the exact defect: a bare universal guard followed by `&&` is the
    one rejection whose fix is not "add the guard" but "add parentheses"."""
    if condition.startswith(SAME_REPO_GUARD_UNIVERSAL):
        tail = condition[len(SAME_REPO_GUARD_UNIVERSAL):].lstrip()
        if tail.startswith("&&"):
            return (
                "universal same-repo guard combined with `&&` must be parenthesised: "
                "`(<universal guard>) && <selection>` -- `&&` binds tighter than `||`, "
                "so the bare form bypasses the selection outside pull_request context"
            )
    return "pull_request self-hosted job must lead with the same-repo job guard"


def _is_naked_hosted_runner(runs_on: Any) -> bool:
    """Vrai si ``runs-on`` ne nomme QUE le label heberge par defaut.

    ``ubuntu-latest`` seul (scalaire) ou une liste a un seul element
    ``[ubuntu-latest]``. Une expression (forme hybride), un label self-hosted
    ou une liste multi-labels ne sont PAS « nus » : ils sont deja routes, ou
    le sont par construction.
    """
    if isinstance(runs_on, str):
        return runs_on.strip().lower() == HYBRID_RUNS_ON_FALLBACK
    if isinstance(runs_on, list):
        return (
            len(runs_on) == 1
            and isinstance(runs_on[0], str)
            and runs_on[0].strip().lower() == HYBRID_RUNS_ON_FALLBACK
        )
    return False


def _hosted_pr_job_violations(
    workflow: str,
    triggers: set[str],
    jobs: dict[str, Any],
    exceptions: dict[str, str],
) -> list[Violation]:
    """Cliquet #23053, invariant 1 : un job nu sur un workflow PR doit etre
    couvert par une exception nommee. La granularite est le workflow (cf. le
    bloc de commentaire de ``HOSTED_PR_JOB_EXCEPTIONS``)."""
    if "pull_request" not in triggers:
        return []
    violations: list[Violation] = []
    for job_name, job in jobs.items():
        if not isinstance(job, dict) or "uses" in job:
            continue
        if not _is_naked_hosted_runner(job.get("runs-on")):
            continue
        if workflow in exceptions:
            continue
        violations.append(Violation(
            workflow,
            str(job_name),
            "HOSTED_PR_JOB_UNEXCEPTED",
            "job fige sur `ubuntu-latest` dans un workflow declenche par "
            "pull_request : adopter la forme hybride de debordement "
            "(#22944/#23016) avec un `timeout-minutes`, ou declarer une "
            "exception nommee dans HOSTED_PR_JOB_EXCEPTIONS avec son motif "
            "(#23053)",
        ))
    return violations


def _exception_list_violations(
    exceptions: dict[str, str],
    baseline: frozenset[str],
) -> list[Violation]:
    """Cliquet #23053, invariant 2 : la liste d'exceptions ne fait que
    retrecir, et chaque entree porte un motif."""
    violations: list[Violation] = []
    for workflow in sorted(exceptions):
        if workflow not in baseline:
            violations.append(Violation(
                workflow,
                "*",
                "HOSTED_PR_JOB_EXCEPTION_ADDED",
                "exception absente de HOSTED_PR_JOB_EXCEPTIONS_BASELINE : la "
                "liste ne fait que retrecir -- une exception ajoutee doit etre "
                "compensee par au moins autant d'entrees retirees dans le meme "
                "commit (#23053)",
            ))
        if not str(exceptions[workflow]).strip():
            violations.append(Violation(
                workflow,
                "*",
                "HOSTED_PR_JOB_EXCEPTION_NO_MOTIVE",
                "une exception nommee porte un motif qui explique POURQUOI le "
                "job reste heberge (#23053)",
            ))
    return violations


def scan_workflows(
    workflows_dir: Path = DEFAULT_WORKFLOWS_DIR,
    *,
    hosted_pr_exceptions: dict[str, str] | None = None,
    hosted_pr_exceptions_baseline: frozenset[str] | None = None,
    check_timeouts: bool = False,
    baseline: set[str] | None = None,
) -> ScanResult:
    """Scan ``workflows_dir`` and return the isolation verdict.

    ``check_timeouts`` engages the #22954 ratchet: every job that can reach a
    self-hosted runner must carry a job-level ``timeout-minutes``. It is opt-in
    so that the ~60 synthetic-workflow tests that build a job on the fly keep
    testing one invariant at a time; the blocking fast-lane entry passes the
    flag, so the rule is enforced where it matters.

    ``hosted_pr_exceptions`` / ``hosted_pr_exceptions_baseline`` carry the
    #23053 ratchet: a workflow whose ``pull_request`` job is left naked on
    ``ubuntu-latest`` must be named in the exception list, and that list may
    only shrink.

    The two ``baseline`` notions are distinct and never share a name: the
    #23053 one is a set of *workflow names*, the #22954 one a set of
    ``workflow.yml:job`` keys. Merging the two features without renaming
    would compare the exception list against job keys -- a mismatch that
    silently empties the ratchet.
    """
    yaml = _load_yaml()
    if yaml is None:
        return ScanResult(0, 0, 0, [], ["PyYAML is unavailable"])

    exceptions = (
        HOSTED_PR_JOB_EXCEPTIONS
        if hosted_pr_exceptions is None
        else hosted_pr_exceptions
    )
    exceptions_baseline = (
        HOSTED_PR_JOB_EXCEPTIONS_BASELINE
        if hosted_pr_exceptions_baseline is None
        else hosted_pr_exceptions_baseline
    )

    paths = sorted([*workflows_dir.glob("*.yml"), *workflows_dir.glob("*.yaml")])
    if not paths:
        return ScanResult(0, 0, 0, [], [f"no workflows in {workflows_dir}"])

    if baseline is None:
        baseline = load_baseline(DEFAULT_BASELINE) if check_timeouts else set()
    timeout_missing = 0
    timeout_baselined = 0

    violations: list[Violation] = []
    broken: list[str] = []
    jobs_scanned = 0
    self_hosted_jobs = 0

    for path in paths:
        try:
            text = path.read_text(encoding="utf-8")
        except OSError as exc:
            broken.append(f"{path.name}: cannot read: {exc}")
            continue
        data = _parse_workflow(text, yaml)
        if data is None:
            broken.append(f"{path.name}: invalid workflow YAML")
            continue

        if "on" not in data and True not in data:
            broken.append(f"{path.name}: missing on trigger")
            continue
        triggers = _triggers(data)
        if not triggers:
            broken.append(f"{path.name}: on trigger is empty or unsupported")
            continue

        if "jobs" not in data:
            broken.append(f"{path.name}: missing jobs")
            continue
        jobs = data["jobs"]
        if not isinstance(jobs, dict) or not jobs:
            broken.append(f"{path.name}: jobs is not a non-empty mapping")
            continue

        for job_name, job in jobs.items():
            if not isinstance(job, dict):
                broken.append(f"{path.name}:{job_name}: job is not a mapping")
                continue
            jobs_scanned += 1

            if "uses" in job:
                reusable = str(job["uses"])
                is_local = reusable.startswith(LOCAL_REUSABLE_PREFIX)
                is_auditable_same_repo = bool(
                    SAME_REPO_REUSABLE_PATTERN.fullmatch(reusable)
                )
                if not is_local and not is_auditable_same_repo:
                    violations.append(Violation(
                        path.name,
                        str(job_name),
                        "REMOTE_REUSABLE_WORKFLOW",
                        "reusable workflow must be local or pin jsboige/CoursIA "
                        "to main",
                    ))
                continue

            runs_on = job.get("runs-on")
            if runs_on is None:
                broken.append(f"{path.name}:{job_name}: missing runs-on")
                continue

            hybrid = _hybrid_runs_on(runs_on)
            if _contains_expression(runs_on) and hybrid is None:
                violations.append(Violation(
                    path.name,
                    str(job_name),
                    "DYNAMIC_RUNS_ON",
                    "runs-on contains an expression other than the audited "
                    "hybrid forms (same-repo guard, optionally && "
                    "vars.CI_OVERFLOW_LOCAL == 'true', -> self-hosted pool, "
                    "else ubuntu-latest; see #13363, #22461) and cannot be "
                    "audited statically",
                ))
                continue

            if hybrid is not None:
                # Audited hybrid leg (#13363): self-hosted by construction, and
                # the same-repo guard lives inside the expression itself -- the
                # self-hosted labels are unreachable for any fork payload. All
                # other invariants (triggers, allowlist, label set) apply as
                # for a static leg; only the job-level SAME_REPO_GUARD check is
                # carried by the runs-on instead of `if:`.
                is_self_hosted = True
                group = None
                labels = hybrid["labels"]
                selection_error = None
                hybrid_leg = True
            else:
                is_self_hosted, group, labels, selection_error = _runner_selection(runs_on)
                hybrid_leg = False
                if selection_error is not None:
                    broken.append(f"{path.name}:{job_name}: {selection_error}")
                    continue
                if not is_self_hosted:
                    continue
            self_hosted_jobs += 1

            if check_timeouts:
                # #22954: GitHub's default job timeout is SIX HOURS. A frozen
                # job then holds a slot the PR gates need -- measured on
                # 2026-10-15, where frozen `Twin parity audit` runs (#22944)
                # held 16 of 18 ephemeral slots overnight and 104 runs had to
                # be cancelled by hand. The baseline names the debt that
                # predates the rule; it must never grow.
                if job.get("timeout-minutes") is None:
                    timeout_missing += 1
                    key = f"{path.name}:{job_name}"
                    if key in baseline:
                        timeout_baselined += 1
                    else:
                        violations.append(Violation(
                            path.name,
                            str(job_name),
                            "MISSING_TIMEOUT",
                            "a job that can reach a self-hosted runner must "
                            "carry a job-level timeout-minutes: the Actions "
                            "default is 6 hours, and a frozen job holds its "
                            "slot that long (#22954)",
                        ))

            if "pull_request_target" in triggers:
                violations.append(Violation(
                    path.name,
                    str(job_name),
                    "PULL_REQUEST_TARGET",
                    "pull_request_target must never reach a self-hosted runner",
                ))
            if "workflow_run" in triggers:
                violations.append(Violation(
                    path.name,
                    str(job_name),
                    "WORKFLOW_RUN",
                    "workflow_run artifacts must never reach a self-hosted runner",
                ))
            if "workflow_call" in triggers:
                violations.append(Violation(
                    path.name,
                    str(job_name),
                    "REUSABLE_SELF_HOSTED",
                    "self-hosted jobs must not hide inside reusable workflows",
                ))
            for trigger in sorted(FORK_REACHABLE_TRIGGERS & triggers):
                violations.append(Violation(
                    path.name,
                    str(job_name),
                    "FORK_REACHABLE_TRIGGER",
                    f"{trigger} can check out a fork pull request and must never "
                    "reach a self-hosted runner",
                ))
            # Fail-closed default deny (#14201, tranche 2). The known-dangerous
            # triggers above carry specific codes; ANY other trigger outside the
            # safe set is refused by default. A denylist alone (the #14148
            # FORK_REACHABLE_TRIGGERS form) is fail-OPEN on anything unlisted.
            known_unsafe = FORK_REACHABLE_TRIGGERS | {
                "pull_request_target",
                "workflow_run",
                "workflow_call",
            }
            unknown_unsafe = sorted(
                triggers - SAFE_SELF_HOSTED_TRIGGERS - known_unsafe
            )
            if unknown_unsafe:
                violations.append(Violation(
                    path.name,
                    str(job_name),
                    "UNSAFE_TRIGGER",
                    "self-hosted job is gated on a trigger outside the safe set "
                    "(pull_request, push, schedule, workflow_dispatch): "
                    + ", ".join(unknown_unsafe),
                ))

            if path.name not in SELF_HOSTED_WORKFLOW_ALLOWLIST:
                violations.append(Violation(
                    path.name,
                    str(job_name),
                    "WORKFLOW_NOT_ALLOWED",
                    "self-hosted runners are restricted to explicitly allowed workflows",
                ))

            if group is not None:
                violations.append(Violation(
                    path.name,
                    str(job_name),
                    "RUNNER_GROUP_UNAVAILABLE",
                    "runner groups are unavailable for this personal-account repository",
                ))

            if any(set(labels) == allowed for allowed in DEDICATED_LABEL_SETS):
                missing: list[str] = []
                unexpected: list[str] = []
            else:
                missing = sorted(REQUIRED_LABELS - labels)
                unexpected = sorted(labels - REQUIRED_LABELS)
            if missing or unexpected:
                detail = []
                if missing:
                    detail.append(f"missing: {', '.join(missing)}")
                if unexpected:
                    detail.append(f"unexpected: {', '.join(unexpected)}")
                violations.append(Violation(
                    path.name,
                    str(job_name),
                    "RUNNER_LABELS",
                    "dedicated labels must match exactly (" + "; ".join(detail) + ")",
                ))

            if "pull_request" in triggers and not hybrid_leg:
                # Hybrid legs carry the guard in their runs-on expression.
                condition = _normalise_condition(job.get("if"))
                # Accept either the bare guard or the guard followed by a
                # selection predicate (e.g. `&& inputs.target == '...'`)
                # joined with `&&` -- the guard must be the lead predicate,
                # never weakened by `||` (cf. test_guard_weakened_by_or_is_rejected).
                if not _starts_with_accepted_guard(condition):
                    violations.append(Violation(
                        path.name,
                        str(job_name),
                        "SAME_REPO_GUARD",
                        _guard_violation_message(condition),
                    ))

        # Cliquet #23053 (passe independante, apres l'isolation : elle ne lit
        # ni l'allowlist ni la forme hybride, seulement le `runs-on` nu).
        violations.extend(
            _hosted_pr_job_violations(path.name, triggers, jobs, exceptions)
        )

    # Invariant « la liste ne fait que retrecir » : une passe globale, elle ne
    # depend d'aucun workflow du dossier scanne.
    violations.extend(_exception_list_violations(exceptions, exceptions_baseline))

    return ScanResult(
        len(paths),
        jobs_scanned,
        self_hosted_jobs,
        violations,
        broken,
        sorted(exceptions),
        sorted(exceptions_baseline),
        timeouts_checked=check_timeouts,
        timeout_missing=timeout_missing,
        timeout_baselined=timeout_baselined,
    )


def _payload(result: ScanResult) -> dict[str, Any]:
    return {
        "ok": not result.violations and not result.broken,
        "workflows_scanned": result.workflows_scanned,
        "jobs_scanned": result.jobs_scanned,
        "self_hosted_jobs": result.self_hosted_jobs,
        "violations": [asdict(item) for item in result.violations],
        "broken": result.broken,
        "hosted_pr_job_exceptions": result.hosted_pr_exceptions,
        "hosted_pr_job_exceptions_baseline": result.hosted_pr_exceptions_baseline,
        "timeouts_checked": result.timeouts_checked,
        "timeout_missing": result.timeout_missing,
        "timeout_baselined": result.timeout_baselined,
    }


def _print_text(result: ScanResult) -> None:
    print(
        "[self-hosted-policy] "
        f"workflows={result.workflows_scanned} jobs={result.jobs_scanned} "
        f"self_hosted={result.self_hosted_jobs}"
    )
    if result.timeouts_checked:
        print(
            "[self-hosted-policy] timeouts: "
            f"sans job-level timeout-minutes={result.timeout_missing} "
            f"(dont {result.timeout_baselined} en baseline #22954, "
            f"{result.timeout_missing - result.timeout_baselined} nouveaux)"
        )
    for item in result.violations:
        print(
            f"  VIOLATION {item.code}: {item.workflow}:{item.job}: "
            f"{item.message}"
        )
    for item in result.broken:
        print(f"  BROKEN: {item}")
    print(
        "[self-hosted-policy] hosted-pr-ratchet (#23053): "
        f"{len(result.hosted_pr_exceptions)} workflow(s) encore excepte(s) "
        f"sur {len(result.hosted_pr_exceptions_baseline)} dans la baseline"
    )
    # La liste n'est detaillee que lorsqu'elle est en cause : sur un run vert,
    # une ligne de synthese suffit et n'inonde pas le journal du garde.
    if any(item.code.startswith("HOSTED_PR_JOB_") for item in result.violations):
        for name in result.hosted_pr_exceptions:
            print(f"  EXCEPTION {name}")
    if not result.violations and not result.broken:
        if result.self_hosted_jobs == 0:
            print("[self-hosted-policy] OK -- explicit baseline: 0 self-hosted jobs.")
        else:
            print("[self-hosted-policy] OK -- all self-hosted jobs satisfy isolation policy.")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="print a text verdict")
    parser.add_argument("--json", action="store_true", help="print a JSON verdict")
    parser.add_argument(
        "--workflows-dir",
        type=Path,
        default=DEFAULT_WORKFLOWS_DIR,
        help="workflow directory (used by tests and offline audits)",
    )
    parser.add_argument(
        "--check-timeouts",
        action="store_true",
        help="engage the #22954 ratchet: every job that can reach a "
             "self-hosted runner must carry a job-level timeout-minutes",
    )
    parser.add_argument(
        "--baseline",
        type=Path,
        default=DEFAULT_BASELINE,
        help="known tolerated jobs for the timeout ratchet (workflow.yml:job)",
    )
    parser.add_argument(
        "--update-baseline",
        action="store_true",
        help="rewrite the timeout baseline from what is measured",
    )
    args = parser.parse_args(argv)

    if args.update_baseline:
        measured = scan_workflows(
            args.workflows_dir, check_timeouts=True, baseline=set()
        )
        keys = sorted({
            f"{item.workflow}:{item.job}"
            for item in measured.violations
            if item.code == "MISSING_TIMEOUT"
        })
        header = (
            "# Jobs auto-heberges sans `timeout-minutes` au niveau du job (#22954).\n"
            "# Cle = `workflow.yml:job`, jamais `workflow:ligne` : une cle ancree\n"
            "# sur une ligne perime des qu'on insere au-dessus, et un garde qui\n"
            "# rougit sur un site inchange finit desactive.\n"
            "# Dette mesuree le 2026-10-29 sur origin/main 2f1291f01 : 63 jobs\n"
            "# STATIQUES. Les 12 jobs HYBRIDES (#22461), eux, sont bornes par la PR\n"
            "# qui a introduit ce cliquet -- la forme hybride n'a AUCUNE tolerance.\n"
            "# Retirer une ligne des que son job est borne.\n"
        )
        args.baseline.write_text(
            header + "\n".join(keys) + "\n", encoding="utf-8", newline="\n"
        )
        print(f"baseline reecrite : {args.baseline} ({len(keys)} jobs)")
        return EXIT_OK

    result = scan_workflows(args.workflows_dir, check_timeouts=args.check_timeouts)
    if args.json:
        print(json.dumps(_payload(result), indent=2, ensure_ascii=False))
    else:
        _print_text(result)

    if result.broken:
        return EXIT_BROKEN
    if result.violations:
        return EXIT_VIOLATION
    return EXIT_OK


if __name__ == "__main__":
    sys.exit(main())
