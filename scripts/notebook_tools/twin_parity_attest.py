#!/usr/bin/env python3
"""Modes d'ecriture/attestation de check_twin_parity -- tranche T7 de #26364.

Corps des modes --update / --migrate-audits / --verify-recorded-sha,
extraits verbatim de `_main`. L'organe est injecte en parametre
(`organ`) : ce module ne l'importe pas, donc aucun cycle.
"""

from __future__ import annotations

import json
import sys


def run_update(args, organ, reg_path, repo_root):
    """Mode --update, extrait verbatim (T7, #26364)."""
    _audit_dir = organ._audit_dir
    _audit_floor = organ._audit_floor
    _inline_audits_of = organ._inline_audits_of
    _next_audit_index = organ._next_audit_index
    _open_claim_floors = organ._open_claim_floors
    _pair_file = organ._pair_file
    _refresh_allocate_ref = organ._refresh_allocate_ref
    _slug = organ._slug
    _strip_audits_from_yaml = organ._strip_audits_from_yaml
    _write_audit_file = organ._write_audit_file
    load_registry = organ.load_registry
    surgical_rebaseline = organ.surgical_rebaseline
    update_pair = organ.update_pair
    write_registry_text = organ.write_registry_text
    # Selecteur obligatoire depuis c.909 (#8508) : --family OU --pair OU
    # --yes-all-pairs. Sans lui, --update rebaselinerait les 116 paires et
    # masquerait des DRIFTs legitimes.
    all_pairs = load_registry(reg_path)
    if args.pair:
        target = [pp for pp in all_pairs if pp.get("name") == args.pair]
        if not target:
            names = sorted({pp.get("name", "?") for pp in all_pairs})
            print(
                f"Aucune paire nommee '{args.pair}'. "
                f"Noms connus : {', '.join(names[:10])}{'...' if len(names) > 10 else ''}",
                file=sys.stderr,
            )
            return 1
    elif args.family:
        target = [pp for pp in all_pairs if pp.get("family") == args.family]
        if not target:
            print(f"Aucune paire pour la famille '{args.family}'.", file=sys.stderr)
    else:
        # --yes-all-pairs (filet anti-corruption silencieuse, cf #8508)
        target = all_pairs
    updates: dict[str, dict] = {}
    skipped: list[str] = []
    # No-op detection (#9399 critere 2) : un rebaseline qui n'apporte
    # aucune information nouvelle (SHAs de comparaison identiques au
    # `_latest_audit`) est un "faux audit" -- dater une attestation
    # identique. On les distingue pour les compter separement et (sans
    # --force) refuser de les ecrire.
    no_op: list[str] = []
    forced_no_op: list[str] = []
    for pp in target:
        audit, cur_py, is_noop = update_pair(repo_root, pp, by=args.by)
        if cur_py is None:
            skipped.append(pp.get("name", "?"))
            continue
        if is_noop and not args.force:
            # Refuse par defaut : message comprehensible + n'ecrit rien.
            # Le worker peut relancer avec --force s'il a une raison
            # explicite de re-attester (rare, mais legitime).
            no_op.append(pp.get("name", "?"))
            continue
        if is_noop and args.force:
            forced_no_op.append(pp.get("name", "?"))
        updates[pp["name"]] = audit
    # Rebaseline CHIRURGICAL (#8570) : seules les lignes d'audit des paires
    # ciblees changent. En mode file-per-entry (#8542) + file-per-audit
    # (#14911), on ecrit CHAQUE audit dans son propre fichier
    # `<pair>/<idx>-<date>-<lane>.yaml` (un ajout, pas un remplacement
    # d'historique) et on retire la liste `audits:` du fichier d'intention.
    # Pour le mono-fichier legacy, on conserve `surgical_rebaseline`
    # (append chirurgical au bloc d'audit inline).
    if reg_path.is_dir():
        written = 0
        # Plancher d'allocation (#22299) : resolu une fois, lu par paire.
        allocate_ref = None if args.no_allocate_against else args.allocate_against
        # #22547 : la ref d'integration vaut ce que vaut son dernier
        # fetch. Un seul fetch borne avant la boucle (pas un par paire),
        # repli silencieux sur la ref locale si le remote ne repond pas.
        if updates:
            _refresh_allocate_ref(repo_root, allocate_ref)
        # Plancher des PRs OUVERTES (#22299) : une PR ouverte peut deja
        # tenir l'ordinal propose. Lue UNE fois avant la boucle, via
        # l'organe natif `twin_open_claims.py`. Un `--no-allocate-against`
        # (comportement historique) le desactive aussi.
        open_claims = ({} if (not updates
                               or args.no_allocate_against
                               or args.no_open_claims_floor)
                       else _open_claim_floors(repo_root))
        for name, audit in updates.items():
            pfile = _pair_file(reg_path, name)
            if not pfile.exists():
                print(f"Aucun fichier pour la paire '{name}' "
                      f"(attendu : {pfile.name}).", file=sys.stderr)
                continue
            # Nouvelle forme file-per-audit (#14911) : on ecrit chaque audit
            # dans un fichier separe `<pair>/<idx>-<date>-<lane>.yaml`, puis
            # on retire la liste `audits:`/`last_audit:` du fichier
            # d'intention `<pair>.yaml` (le lecteur reconstitue `audits:`
            # depuis les fichiers separes -- voir `load_registry`).
            #
            # Anti-regression (paire non encore migree) : si le fichier
            # d'intention porte ENCORE des audits inline, on les migre
            # d'abord vers des fichiers (indices 1..N) AVANT d'appender le
            # nouvel audit (sinon `_strip_audits_from_yaml` les perdrait :
            # seuls les fichiers restants seraient relus). Sur une paire deja
            # migree (intention sans audits), `_write_audit_file` appende au
            # prochain slot (index=None -> count+1).
            raw = pfile.read_text(encoding="utf-8")
            inline = _inline_audits_of(raw)
            if inline:
                used: set[str] = set()
                # Migre les audits inline existants (1..len(inline)).
                for idx, a in enumerate(inline, start=1):
                    _write_audit_file(reg_path, name, a,
                                      used_names=used, index=idx)
                _write_audit_file(reg_path, name, audit,
                                  used_names=used, index=len(inline) + 1)
            else:
                floor = _audit_floor(repo_root, reg_path, name, allocate_ref)
                # Plancher des PRs OUVERTES (#22299) : une PR ouverte peut
                # deja tenir l'ordinal que l'on s'apprete a proposer.
                open_floor = open_claims.get(_slug(name), 0)
                if open_floor > floor:
                    floor = open_floor
                    print(f"  '{name}' : prefixe alloue au-dessus des PRs "
                          f"ouvertes (ordinal revendique le plus haut = "
                          f"{open_floor})")
                if floor >= _next_audit_index(_audit_dir(reg_path, _slug(name))):
                    # Observabilite : l'index retenu n'est pas le max local,
                    # c'est le plancher publie. Sans cette ligne, le worker
                    # lirait la numerotation comme un trou inexplique.
                    print(f"  '{name}' : prefixe alloue au-dessus de "
                          f"{allocate_ref} (max publie = {floor})")
                _write_audit_file(reg_path, name, audit, floor=floor)
            new_raw = _strip_audits_from_yaml(raw)
            if new_raw != raw:
                write_registry_text(pfile, new_raw)
            written += 1
        updated = written
    else:
        # mono-fichier legacy (--registry <file.yaml>)
        raw = reg_path.read_text(encoding="utf-8")
        new_raw, updated = surgical_rebaseline(raw, updates, force=args.force)
        write_registry_text(reg_path, new_raw)
        if updated < len(updates):
            print(
                f"AVERTISSEMENT : {len(updates) - updated} paire(s) a "
                f"rebaseliner sans bloc d'audit reconnu dans {reg_path.name} "
                f"-- rebaseline IGNORE pour elles (header introuvable).",
                file=sys.stderr,
            )
    if skipped:
        print(
            f"Ignorees (notebook absent de git) : {', '.join(skipped)}",
            file=sys.stderr,
        )
    # Bilan no-op vs reelles (#9399 critere 2) -- informe le worker de
    # la portee reelle de sa commande. Sans --force, les paires no-op ne
    # sont PAS ecrites ; le worker voit la liste et peut relancer --force
    # s'il a une raison explicite de re-attester.
    if no_op:
        print(
            f"Refusees (no-op, --update facultatif post-volet-b : les SHAs "
            f"enregistres sont deja ceux du carnet a HEAD) : "
            f"{', '.join(no_op)}",
            file=sys.stderr,
        )
    if forced_no_op:
        print(
            f"ATTENTION --force : {len(forced_no_op)} paire(s) no-op "
            f"ecrite(s) avec une nouvelle entree d'audit identique au "
            f"_latest_audit precedent : {', '.join(forced_no_op)}. "
            f"Cela produit un faux audit au sens du design-gate #9399 "
            f"critere 2 (dater une attestation sans information nouvelle). "
            f"Verifiez que c'est bien votre intention.",
            file=sys.stderr,
        )
    msg = f"Registre rebaseline : {updated} paire(s) mise(s) a jour -> {reg_path}"
    print(msg)
    # Rappel d'ordre (#8957) : ce rebaseline est l'attestation des SHAs courants.
    # Il va EN DERNIER -- si un strip outille (strip_probe_banner.py --apply,
    # strip_machine_paths.py, scrub_papermill_paths.py) edite le notebook APRES
    # ce point, le blob SHA deplace et le gate --per-pair sortira DRIFT-INTRO
    # sur la prochaine PR (la parite est vraie, c'est son empreinte qui a bouge).
    print(
        "Rappel : cette attestation est celle du notebook TEL QU'IL EST MAINTENANT. "
        "Tout strip outille ulterieur deplace le blob SHA -- si vous devez "
        "normaliser (strip_probe_banner / strip_machine_paths / scrub_papermill), "
        "refaites --update en dernier, apres (cf #8957)."
    )
    # Exit code (#10430 acceptance) :
    #   0 = ecrit OK (peut inclure des no_op informes sur stderr)
    #   1 = au moins une paire DEMANDEE n'a pas pu etre ecrite parce que
    #       son bloc d'audit etait introuvable / indentation non reconnue.
    #       L'AVERTISSEMENT ci-dessus a deja liste les paires concernees ;
    #       l'exit non-zero est le signal que le worker doit inspecter
    #       l'indentation et relancer --update (ou investiguer le fichier).
    #   2 = aucun nom de paire trouve (path `Aucune paire nommee` plus haut).
    # Le commentaire historique qui disait « 0 meme si toutes les cibles
    # etaient no-op » est REVOQUE ici : un worker qui voit exit=0 et 0
    # ligne ecrite conclut legitimement « rien a faire ». Si le probleme
    # reel est que le scanner est aveugle (entrees manquees), c'est
    # INVISIBLE. L'exit 1 ferme la boucle.
    # Garder la garde sur les paires skippees (`notebook absent de git`)
    # en dehors de cette logique : ce n'est PAS un failed-rebaseline, juste
    # une mise en garde environnementale.
    # #10430 exit 1 : un rebaseline IGNORE (header d'audit introuvable /
    # indentation non reconnue) ne doit pas laisser le worker conclure
    # « rien a faire ». Ce mode d'echec est propre au mono-fichier legacy :
    # en mode file-per-audit (#14911) il n'existe plus de header inline a
    # manquer -- les audits sont des fichiers (glob, jamais aveugles).
    if not reg_path.is_dir() and updated < len(updates):
        return 1
    return 0


def run_migrate_audits(args, p, organ, reg_path):
    """Mode --migrate-audits, extrait verbatim (T7, #26364)."""
    load_registry = organ.load_registry
    migrate_registry_files_per_audit = organ.migrate_registry_files_per_audit
    # Selecteur obligatoire (replique la politique --update, cf #8508) :
    # une invocation nue reecrirait les 157 paires du registre. L'invocation
    # --pair / --family / --yes-all-pairs borne la migration (migrer une
    # tranche est utile pour tester la forme sur une seule famille avant
    # de committer l'ensemble).
    if not (args.family or args.pair or args.yes_all_pairs):
        p.error("--migrate-audits exige un selecteur explicite : --family <f>, "
                "--pair <name>, OU --yes-all-pairs. Une invocation nue "
                "reecrirait les 157 paires (cf #8508).")
    if reg_path is None or not reg_path.is_dir():
        p.error("--migrate-audits ne s'applique qu'au registre en forme "
                "file-per-entry (--registry <dir> avec twin_pairs.d/) ; "
                "le mono-fichier legacy n'a pas de sous-repertoires.")
    all_pairs = load_registry(reg_path)
    if args.pair:
        target = [pp for pp in all_pairs if pp.get("name") == args.pair]
        if not target:
            names = sorted({pp.get("name", "?") for pp in all_pairs})
            print(
                f"Aucune paire nommee '{args.pair}'. "
                f"Noms connus : {', '.join(names[:10])}{'...' if len(names) > 10 else ''}",
                file=sys.stderr,
            )
            return 1
        sel_names = {args.pair}
    elif args.family:
        target = [pp for pp in all_pairs if pp.get("family") == args.family]
        if not target:
            print(f"Aucune paire pour la famille '{args.family}'.", file=sys.stderr)
            return 1
        sel_names = {pp.get("name") for pp in target}
    else:
        target = all_pairs
        sel_names = None
    result = migrate_registry_files_per_audit(reg_path, names=sel_names)
    print(
        f"Registre migre vers file-per-audit (#14911) : "
        f"{result['migrated']} paire(s) traitee(s), "
        f"{result['audits_moved']} audit(s) deplace(s) vers "
        f"{reg_path}/<pair>/<date>-<lane>.yaml."
    )
    return 0


def run_verify_recorded_sha(args, organ, reg_path, repo_root, pairs):
    """Mode --verify-recorded-sha, extrait verbatim (T7, #26364)."""
    _paire_inconnue = organ._paire_inconnue
    verify_recorded_sha = organ.verify_recorded_sha
    # Accepte --family comme selecteur (replique la politique --update) :
    # en CI on cible generalement tout le registre, mais un audit local peut
    # vouloir borner a une famille.
    target_pairs = pairs
    if args.pair is not None:
        # #20197 : --pair etait accepte puis ignore ici aussi. Nom inconnu = rc 2.
        selection = [pp for pp in target_pairs if pp.get("name") == args.pair]
        if not selection:
            _paire_inconnue(args.pair, target_pairs)
            return 2
        target_pairs = selection
    if args.family:
        target_pairs = [pp for pp in target_pairs if pp.get("family") == args.family]
        if not target_pairs:
            print(
                f"Aucune paire pour la famille '{args.family}'.",
                file=sys.stderr,
            )
            # En --check ce serait un gate casse ; ici on retourne 2
            # (distinct de 1=MISMATCH, 0=clean) pour discriminer le cas.
            return 2

    results = [verify_recorded_sha(repo_root, pp) for pp in target_pairs]
    n_ok = sum(1 for r in results if r["status"] == "OK")
    n_mismatch = sum(1 for r in results if r["status"] == "MISMATCH")
    n_no_audit = sum(1 for r in results if r["status"] == "NO_AUDIT")

    if args.json:
        out = {
            "mode": "verify_recorded_sha",
            "registry": str(reg_path),
            "total": len(results),
            "ok": n_ok,
            "mismatch": n_mismatch,
            "no_audit": n_no_audit,
            "pairs": results,
        }
        print(json.dumps(out, ensure_ascii=False, indent=2))
    else:
        tag_map = {"OK": "OK", "MISMATCH": "MISMATCH", "NO_AUDIT": "NO_AUDIT"}
        for r in results:
            if r["status"] == "OK":
                continue  # ne pas bruiter les OK en sortie humaine
            tag = tag_map[r["status"]]
            print(f"[{tag}] {r['name']} ({r.get('family','?')})")
            for m in r.get("mismatches", []):
                print(f"       - {m}")
        print(
            f"\nTotal : {len(results)} paire(s) | "
            f"OK={n_ok} MISMATCH={n_mismatch} NO_AUDIT={n_no_audit}"
        )

    if args.check and n_mismatch > 0:
        # Gate CI : un seul mismatch = RED. Message d'erreur oriente
        # l'auteur vers --update (le seul moyen legitime de resoudre :
        # l'audit firsthand + rebaseline, cf #8508 selector policy).
        print(
            f"::error title=Twin parity SHA mismatch (#9399 volet b)::"
            f"{n_mismatch} paire(s) ont un SHA enregistre dans le YAML qui ne "
            f"correspond pas au SHA reel du carnet a HEAD. L'integrite du "
            f"registre est corrompue (sha invente / stale / modifie a la "
            f"main). Remediation : lancer "
            f"`python scripts/notebook_tools/check_twin_parity.py --update "
            f"--pair \"<nom>\" --by \"<machine:workspace>\"` APRES audit "
            f"firsthand de la parite. Le selecteur --pair est obligatoire "
            f"(cf #8508).",
            file=sys.stderr,
        )
        return 1
    return 0
