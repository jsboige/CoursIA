#!/usr/bin/env python3
"""Couche CLI de check_twin_parity -- tranche T7 de #26364.

Extraction verbatim de la construction du parser et de la validation
croisee des drapeaux depuis `_main` : aucun verdict ne change. Ce module
n'importe pas l'organe -- les dependances (`_repo_root`, `_run_git`) sont
injectees en parametre (`organ`), donc aucun cycle d'import. Le parametre
`default_registry` remplace la constante `DEFAULT_REGISTRY` de l'organe et
`description` son `__doc__` : seules substitutions au verbatim.
"""

from __future__ import annotations

import argparse
from pathlib import Path


def build_parser(default_registry, description):
    """Parser de l'organe, extrait verbatim de `_main` (T7, #26364)."""
    p = argparse.ArgumentParser(description=description)
    p.add_argument("--registry", default=str(default_registry),
                   help=f"Chemin du registre YAML (defaut: {default_registry.name})")
    p.add_argument("--repo-root", default=None,
                   help="Racine du depot git (defaut: detectee en remontant les parents "
                        "jusqu'a un `.git`, sans fork -- cf #16111). Utile pour les tests "
                        "(mini-depot tmp_path) et le cron CI qui pointe sur le checkout "
                        "explicite.")
    p.add_argument("--family", default=None,
                   help="Restreindre a une famille (ex. SMT/Z3-API)")
    p.add_argument("--check", action="store_true",
                   help="Exit 1 si DRIFT/MISSING/NUMBERING-DRIFT detecte (CI-ready)")
    p.add_argument("--update", action="store_true",
                   help="Rebaseline : ecrit les SHAs courants comme nouveau last_audit "
                        "(a lancer APRES une audit firsthand d'une paire, ET EN DERNIER : "
                        "toute normalisation outillee ulterieure -- strip_probe_banner.py, "
                        "strip_machine_paths.py, scrub_papermill_paths.py -- deplace le "
                        "blob SHA sans toucher le contenu calcule et invaliderait cette "
                        "attestation, cf #8957). Depuis #9399 critere 2, --update "
                        "REFUSE par defaut d'ecrire une nouvelle entree d'audit si "
                        "les SHAs de comparaison sont identiques au `_latest_audit` "
                        "(no-op = faux audit, --update devient facultatif). "
                        "Utilisez --force pour outrepasser avec un avertissement.")
    p.add_argument("--json", action="store_true", help="Sortie machine JSON")
    p.add_argument("--summary-by-verdict", action="store_true",
                   help="Compte les paires par `bridge_verdict` (#10439) : SOTA-OK / "
                        "RECOVERABLE-* / INTRINSIC / (non-rompu = actionnable). "
                        "Le point du champ structurel : soustraire les verdicts "
                        "INTRINSIC/SOTA-OK du denominateur 'actionnable' SANS "
                        "intervention manuelle. Incompatible avec --update/--per-pair.")
    p.add_argument("--coverage", action="store_true",
                   help="Recense les notebooks C# versionnes NON couverts par le "
                        "registre (jumeau Python present mais paire non declaree). "
                        "Avec --check, sort 1 s'il reste des paires non enregistrees.")
    p.add_argument("--per-pair", action="store_true",
                   help="Mode per-pair : compare HEAD vs --base <ref>. Ne FAIL que "
                        "le drift INTRODUIT par la PR, jamais le drift pre-existant.")
    p.add_argument("--base", default=None,
                   help="Ref git de base pour le mode --per-pair (ex. origin/main, "
                        "HEAD~1, ou 'auto' : HEAD^1 quand HEAD est un merge ref "
                        "GitHub, origin/main sinon -- cf #22292).")
    p.add_argument("--ci-strict", action="store_true",
                   help="Mode CI cron (#9399 volet b) : check fleet-wide SANS base ref, "
                        "avec breakdown 4 categories (ok_legacy / ok_content / drift_blob / "
                        "drift_content / drift_legacy_after_content / missing_python / "
                        "missing_csharp / no_audit). Combine avec --check pour FAIL sur N'IMPORTE "
                        "QUEL drift (vs la semantique 'DRIFT_or_MISSING only' historique). "
                        "Distingue erreur d'outil vs constat de drift (cf L948/L949, c.1240).")
    p.add_argument("--pair", default=None,
                   help="Restreindre a une paire nommee (ex. 'Search-9-LP') : applique par "
                        "--update, --migrate-audits, --check et --verify-recorded-sha "
                        "(#20197), ainsi qu'en --per-pair --base <ref> (#21281) ; refuse par "
                        "--coverage et --summary-by-verdict (modes de recensement integral). "
                        "Nom inconnu = rc 2. Impossible a combiner avec --family.")
    p.add_argument("--yes-all-pairs", action="store_true",
                   help="Opt-in explicite pour rebaseline TOUTES les paires du registre "
                        "avec --update. Sans ce flag (ou --family/--pair), --update refuse.")
    p.add_argument("--by", default=None,
                   help="Auteur de l'audit inscrit dans last_audit.by (ex. "
                        "'myia-po-2024:CoursIA-2'). Avec --update, la date est "
                        "TOUJOURS mise a aujourd'hui : sans --by, l'entree garderait "
                        "l'auteur de l'audit precedent alors que les SHAs sont neufs.")
    p.add_argument("--force", action="store_true",
                   help="Avec --update : outrepasser la detection no-op (cf #9399 "
                        "critere 2). Par defaut, --update REFUSE d'ecrire une "
                        "nouvelle entree d'audit si les SHAs de comparaison sont "
                        "identiques au `_latest_audit` (--update devient "
                        "facultatif : la CI derive elle-meme les SHAs depuis "
                        "volet b, un rebaseline manuel identique n'apporte aucune "
                        "information nouvelle et serait un faux audit). --force "
                        "est l'opt-in explicite pour forcer la nouvelle entree "
                        "malgre le no-op, avec un avertissement explicite sur "
                        "stdout. Sans effet sur les modes non --update.")
    p.add_argument("--allocate-against", default="origin/main", metavar="REF",
                   help="Avec --update : plancher d'allocation du prefixe NNNN, lu "
                        "sur cette ref (defaut 'origin/main', vide = desactive). "
                        "L'index ne peut plus etre <= au max deja publie pour la "
                        "paire sur cette ref (#22299) : sans ce plancher, deux "
                        "branches issues du meme main calculent le meme max et "
                        "emettent le meme prefixe, que le garde d'integrite refuse "
                        "apres merge. Avant la lecture, un `git fetch` borne "
                        "rafraichit la ref <remote>/<branche> (#22547) : sans lui, "
                        "le plancher lirait la ref telle que le clone la connaissait "
                        "a son dernier fetch et la collision resterait possible. Si "
                        "le fetch echoue ou si la ref est illisible, repli sur la ref "
                        "locale -- cela ne bloque jamais l'ecriture (le plancher est "
                        "un garde, pas une mesure). Ce plancher ne voit pas les "
                        "PRs encore ouvertes : l'ordinal qu'elles revendiquent "
                        "est couvert par le second plancher (--no-open-claims-floor).")
    p.add_argument("--no-allocate-against", action="store_true",
                   help="Desactive le plancher d'allocation (comportement "
                        "historique : max local + 1). Utile dans un depot sans "
                        "remote, ou pour reproduire un registre ancien. Desactive "
                        "aussi le plancher des PRs ouvertes.")
    p.add_argument("--no-open-claims-floor", action="store_true",
                   help="Avec --update : n'alloue pas au-dessus des ordinals "
                        "REVENDIQUES par les PRs ouvertes (lecture via "
                        "twin_open_claims.py). Ce plancher est, lui, un garde : "
                        "une lecture impossible (gh absent, reseau coupe, liste "
                        "tronquee) n'annule jamais l'ecriture, elle est dite sur "
                        "stderr. Inutilise hors ligne -- l'allocation reste "
                        "celle du plancher d'integration.")
    p.add_argument("--verify-recorded-sha", action="store_true",
                   help="Gate CI #9399 volet b : verifie que les SHA enregistres "
                        "dans le YAML (last_audit legacy OU audits[-1] append-only) "
                        "correspondent aux SHA recalcules a HEAD (git ls-tree + "
                        "SHA-256 metadata-immune). Exit 1 si MISMATCH sur au moins "
                        "une paire (avec --check). Mode read-only : n'ecrit rien.")
    p.add_argument("--migrate-audits", action="store_true",
                   help="Reecrit le registre en forme file-per-audit (#14911) : "
                        "chaque audit migre vers `twin_pairs.d/<pair>/<date>-<lane>.yaml` "
                        "et la liste `audits:`/`last_audit:` est retiree du fichier "
                        "d'intention. Exige un selecteur (--pair / --family / "
                        "--yes-all-pairs) pour eviter une invocation nue qui "
                        "reecrirait les 157 paires (cf #8508).")
    return p


def parse_and_validate(p, argv, organ):
    """`parse_args` + validation croisee, extraits verbatim (T7, #26364)."""
    _repo_root = organ._repo_root
    _run_git = organ._run_git
    args = p.parse_args(argv)

    # Cross-validation : --per-pair <-> --base
    if args.coverage and (args.update or args.per_pair or args.base or args.verify_recorded_sha):
        p.error("--coverage est un mode de recensement seul : incompatible avec "
                "--update / --per-pair / --base / --verify-recorded-sha.")
    if args.summary_by_verdict and (args.update or args.per_pair or args.base
                                    or args.verify_recorded_sha or args.coverage):
        p.error("--summary-by-verdict est un mode de recensement seul : incompatible "
                "avec --update / --per-pair / --base / --verify-recorded-sha / --coverage.")
    if args.per_pair and not args.base:
        p.error("--per-pair necessite --base <ref>")
    if args.base and not args.per_pair:
        p.error("--base necessite --per-pair")
    if args.update and (args.per_pair or args.base or args.verify_recorded_sha):
        p.error("--update est incompatible avec --per-pair/--base/--verify-recorded-sha")
    if args.verify_recorded_sha and (args.per_pair or args.base or args.update):
        p.error("--verify-recorded-sha est read-only : incompatible avec "
                "--update/--per-pair/--base.")
    # --update exige un selecteur (anti-corruption silencieuse du registre, cf #8508)
    if args.update and not (args.family or args.pair or args.yes_all_pairs):
        p.error("--update exige un selecteur explicite : --family <f>, --pair <name>, "
                "OU --yes-all-pairs. Le defaut '--update' seul reecrirait le last_audit "
                "de TOUTES les paires du registre, ce qui masque des DRIFTs legitimes "
                "(cf issue #8508 + lecons L963/L974).")
    # --migrate-audits est un mode de reecriture structurelle exclusive (#14911) :
    # le selecteur est deja obligatoire (bloc d'execution), et il est incompatible
    # avec les autres modes d'ecriture/conservation.
    if args.migrate_audits and (args.update or args.per_pair or args.base
                                or args.verify_recorded_sha or args.coverage
                                or args.summary_by_verdict or args.ci_strict):
        p.error("--migrate-audits est un mode exclusif : incompatible avec "
                "--update / --per-pair / --base / --verify-recorded-sha / "
                "--coverage / --summary-by-verdict / --ci-strict.")
    # Selecteurs sans portee pour les modes de recensement seul (#21281,
    # reliquat #20578) : un --pair/--family sur --coverage ou
    # --summary-by-verdict etait silencieusement ignore -- un selecteur
    # inconnu rendait rc 0 sur le recensement integral. On refuse a
    # l'analyse (p.error) plutot que d'evaluer un selecteur qui n'a aucun
    # sens pour ces deux modes.
    if args.coverage and (args.pair or args.family):
        p.error("--coverage est un mode de recensement integral : --pair/--family "
                "n'y designent rien (recense justement les notebooks ABSENTS du "
                "registre). Retirer le selecteur.")
    if args.summary_by_verdict and (args.pair or args.family):
        p.error("--summary-by-verdict est un mode de recensement integral : "
                "--pair/--family n'y designent rien (compte les paires par "
                "bridge_verdict). Retirer le selecteur.")
    # Garde anti-derive merge/rebase en cours (#11732) : pendant un merge non
    # commite, `git ls-tree HEAD` lit l'ANCIENNE tete de branche (pas le resultat
    # du merge). --update atteste alors des blob SHAs qui ne refletent pas l'etat
    # final du notebook -- au commit du merge, les notebooks obtiennent de
    # nouveaux blobs, et l'attestation fraichement ecrite est deja DRIFT avant
    # meme que la CI ne la voie. Variante operationnelle de #8957 (« attester
    # en DERNIER ») : le commit du merge lui-meme deplace le blob apres
    # attestation. Refus : on commit d'abord, puis on re-atteste.
    if args.update:
        try:
            if args.repo_root:
                repo_root_for_state = Path(args.repo_root)
            else:
                repo_root_for_state = _repo_root()
        except SystemExit:
            repo_root_for_state = None
        if repo_root_for_state is not None:
            # Le check precede `_repo_root()` final pour economiser un subprocess
            # en cas d'erreur deja connue (mais apres args.repo_root parse, qui
            # peut etre override dans les tests --repo-root sur tmp_path).
            #
            # Merge en cours : `git rev-parse -q --verify MERGE_HEAD` (rc=0 si
            # et seulement si un merge est non commite) -- detection inchangee.
            r = _run_git(
                ["git", "rev-parse", "-q", "--verify", "MERGE_HEAD"],
                cwd=str(repo_root_for_state),
            )
            if r.returncode == 0:
                p.error("--update pendant un merge non committe : HEAD ne contient pas "
                        "le resultat du merge. Commitez d'abord, puis re-attestez "
                        "(cf #11732, variante operationnelle de #8957).")
            # Rebase en cours : l'indicateur fiable est l'existence du repertoire
            # `rebase-merge` (interactif/merge backend) ou `rebase-apply`
            # (backend am), PAS le ref REBASE_HEAD. Git peut y laisser un
            # REBASE_HEAD orphelin apres un rebase interrompu : un clone qui en
            # porte un sans rebase en cours voyait alors --update refuse a tort
            # (signale par le coordinateur 2026-10-27 : REBASE_HEAD du 20/09,
            # ni rebase-merge ni rebase-apply, 3 tests update_guard rouges).
            # `git rev-parse --git-path <name>` resout le chemin dans le git dir
            # du depot (worktree compris) ; la sortie est relative au cwd dans
            # le clone principal (`.git/rebase-merge`) et absolue dans un
            # worktree -- d'ou la resolution explicite ci-dessous.
            for state_dir in ("rebase-merge", "rebase-apply"):
                r = _run_git(
                    ["git", "rev-parse", "--git-path", state_dir],
                    cwd=str(repo_root_for_state),
                )
                raw = r.stdout.strip() if r.returncode == 0 else ""
                if not raw:
                    continue
                state_path = Path(raw)
                if not state_path.is_absolute():
                    state_path = repo_root_for_state / state_path
                if state_path.exists():
                    p.error("--update pendant un rebase non termine : HEAD ne contient pas "
                            "le resultat du rebase. Terminez ou annulez le rebase "
                            "(git rebase --continue / --abort), puis re-attestez "
                            "(cf #11732, variante operationnelle de #8957).")
    if args.pair and args.family:
        p.error("--pair et --family sont mutuellement exclusifs avec --update.")
    if args.ci_strict and args.per_pair:
        p.error("--ci-strict est un mode fleet-wide SANS base ref : incompatible avec --per-pair.")
    if args.ci_strict and args.update:
        p.error("--ci-strict est un mode read-only : incompatible avec --update.")
    # Cross-validation --ci-strict x --verify-recorded-sha (#9481, post-rebase c.984) :
    # les deux sont des modes fleet-wide read-only avec des sorties JSON disjointes
    # (breakdown 4 categories vs recorded-vs-HEAD mismatch). Les coupler en CLI
    # melange deux verdicts dans la meme invocation, ce qui rend le choix du
    # categoriel d'echec ambigu pour le mainteneur. Le cron les lance separement
    # (twin-parity-cron.yml pour --ci-strict, twin-parity-sha-mismatch du
    # twin-parity.yml #9481 pour --verify-recorded-sha). Mutuellement exclusifs.
    if args.ci_strict and args.verify_recorded_sha:
        p.error("--ci-strict et --verify-recorded-sha sont deux modes fleet-wide "
                "read-only avec des sorties JSON disjointes : incompatibles. "
                "Lancer l'un ou l'autre, pas les deux (le cron les dispatch separement).")
    return args
