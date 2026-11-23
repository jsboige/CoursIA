#!/usr/bin/env python3
"""Modes de recensement de check_twin_parity -- tranche T7 de #26364.

Corps des modes --summary-by-verdict / --coverage / --per-pair /
--ci-strict, extraits verbatim de `_main`. L'organe est injecte en
parametre (`organ`) : ce module ne l'importe pas, donc aucun cycle.
"""

from __future__ import annotations

import json
import sys


def run_summary_by_verdict(args, organ, reg_path):
    """Mode --summary-by-verdict, extrait verbatim (T7, #26364)."""
    load_registry = organ.load_registry
    validate_pair_fields = organ.validate_pair_fields
    pairs = load_registry(reg_path)
    # Fail-loud sur un bridge_verdict invalide avant de resumer : un resume
    # qui ignore silencieusement une valeur hors enum est le defaut meme
    # que #10439 vient corriger.
    schema_errs = [e for pp in pairs for e in validate_pair_fields(pp)]
    if schema_errs:
        for e in schema_errs:
            print(f"SCHEMA ERROR: {e}", file=sys.stderr)
        return 2
    counts: dict = {}
    names_by: dict = {}
    for pp in pairs:
        bv = pp.get("bridge_verdict", "(non-rompu)")
        counts[bv] = counts.get(bv, 0) + 1
        names_by.setdefault(bv, []).append(pp.get("name", "?"))
    actionable = sum(c for k, c in counts.items()
                     if k not in ("INTRINSIC", "SOTA-OK"))
    if args.json:
        print(json.dumps({
            "mode": "summary_by_verdict",
            "registry": str(reg_path),
            "total": len(pairs),
            "counts": counts,
            "actionable": actionable,
        }, ensure_ascii=False, indent=2))
    else:
        order = ["(non-rompu)", "SOTA-OK", "RECOVERABLE-LOCAL",
                 "RECOVERABLE-MACHINE", "RECOVERABLE-USER-HAND", "INTRINSIC"]
        shown = [k for k in order if k in counts] + sorted(set(counts) - set(order))
        print(f"Summary by bridge_verdict ({len(pairs)} paires) :")
        for k in shown:
            tag = " ACTIONNABLE" if k not in ("INTRINSIC", "SOTA-OK") else ""
            print(f"  {k:<22} {counts[k]:>3}{tag}")
        print(f"  {'actionnables (a bridger)':<22} {actionable:>3}"
              f"  = total - INTRINSIC - SOTA-OK")
    return 0


def run_coverage(args, organ, reg_path, repo_root):
    """Mode --coverage, extrait verbatim (T7, #26364)."""
    load_registry = organ.load_registry
    scan_coverage = organ.scan_coverage
    cov = scan_coverage(repo_root, load_registry(reg_path))
    n_unreg, n_only = len(cov["unregistered"]), len(cov["csharp_only"])
    if args.json:
        print(json.dumps(cov, ensure_ascii=False, indent=2))
    else:
        for e in cov["unregistered"]:
            print(f"[UNREGISTERED] {e['csharp']}")
            for c in e["python_candidates"]:
                print(f"        <-> {c}")
        for e in cov["csharp_only"]:
            print(f"[CSHARP-ONLY]  {e['csharp']}")
        print(
            f"\nNotebooks C# versionnes : {cov['csharp_tracked']} | "
            f"enregistres={cov['registered']} "
            f"NON-ENREGISTRES={n_unreg} C#-only={n_only}"
        )
        if n_unreg:
            print(
                f"\n{n_unreg} paire(s) reelle(s) hors registre : invisibles au "
                f"gate de derive tant qu'elles n'y sont pas declarees.\n"
                f"Enregistrer par tranche APRES audit de parite firsthand "
                f"(cf #8057), jamais en masse."
            )
    return 1 if (args.check and n_unreg) else 0


def run_per_pair(args, organ, reg_path, repo_root):
    """Mode --per-pair, extrait verbatim (T7, #26364)."""
    _classify_per_pair = organ._classify_per_pair
    _load_registry_at_ref = organ._load_registry_at_ref
    _merge_base_ref = organ._merge_base_ref
    _pair_paths_diverge = organ._pair_paths_diverge
    _stale_branch_probe = organ._stale_branch_probe
    check_pair = organ.check_pair
    load_registry = organ.load_registry
    # Charge le registre a HEAD (working tree) et au base-ref (git show).
    # Le base-ref peut porter l'ancien mono-fichier (frontiere de migration
    # #8542) -> _load_registry_at_ref essaie le repertoire puis retombe sur
    # le fichier legacy.
    pairs_head = load_registry(reg_path)

    # Application stricte des selecteurs (#21281, reliquat #20578) :
    # un nom ou une famille inconnue -> rc 2 avec la liste des noms
    # connus, comme --check --update le fait deja depuis #20578.
    # On check AVANT le load du base-ref (qui fait un git ls-tree par
    # paire et est dispendieux) : un selecteur inconnu ne doit jamais
    # payer le cout d'un parcours integral.
    if args.family:
        known_families = sorted({pp.get("family", "?") for pp in pairs_head})
        if args.family not in known_families:
            print(
                f"--family {args.family!r} inconnue. Familles connues : "
                f"{known_families}",
                file=sys.stderr,
            )
            return 2
        pairs_head = [pp for pp in pairs_head if pp.get("family") == args.family]
    elif args.pair:
        known_names = sorted({pp.get("name", "?") for pp in pairs_head})
        if args.pair not in known_names:
            print(
                f"--pair {args.pair!r} inconnue. Noms connus ({len(known_names)}) : "
                f"{known_names}",
                file=sys.stderr,
            )
            return 2
        pairs_head = [pp for pp in pairs_head if pp.get("name") == args.pair]

    # #21972 : ne charger au base-ref que les paires selectionnees. `pairs_head`
    # est deja filtre par --pair/--family (juste dessus) ; sans selecteur il
    # porte tout le registre -> `names` = tous les noms -> chargement integral,
    # comportement strictement inchange.
    pairs_base = _load_registry_at_ref(
        repo_root, args.base, reg_path,
        names={pp.get("name", "?") for pp in pairs_head},
    )
    # Index par nom (au cas ou l'ordre ou les ajouts/suppressions different)
    base_by_name = {pp.get("name", "?"): pp for pp in pairs_base}

    # #22920 : verdict STALE_BRANCH, decide EN AMONT de _classify_per_pair
    # (le cas est invisible dans ses entrees : deux statuts seulement). Le
    # point de fork (merge-base) n'est resolu QUE si au moins une paire est
    # declaree avec des chemins differents aux deux refs -- un test pur,
    # sans appel git : un registre sans divergence ne paie rien.
    merge_base = (
        _merge_base_ref(repo_root, args.base)
        if any(
            (b := base_by_name.get(pp.get("name", "?"))) is not None
            and _pair_paths_diverge(b, pp)
            for pp in pairs_head
        )
        else None
    )

    results = []
    for pp in pairs_head:
        name = pp.get("name", "?")
        head_state = check_pair(repo_root, pp, git_ref="HEAD")
        base_pp = base_by_name.get(name)
        if base_pp is None:
            # Paire ajoutee par la PR -> si elle n'est PAS OK au HEAD, c'est du drift introduit
            base_status = "MISSING"
            base_drift: set[str] = set()
            base_no_baseline = False
            base_details = [f"Paire '{name}' absente du registre au base-ref '{args.base}' (ajoutee par la PR)"]
        else:
            base_check = check_pair(repo_root, base_pp, git_ref=args.base)
            base_status = base_check["status"]
            base_drift = set(base_check.get("drift_sides") or ())
            base_no_baseline = bool(base_check.get("no_baseline"))
            base_details = base_check["details"]

        head_status = head_state["status"]
        head_drift = set(head_state.get("drift_sides") or ())
        head_no_baseline = bool(head_state.get("no_baseline"))
        # #22920 : branche perimee ? Paire deplacee par la branche base apres
        # le fork -- le registre de la tete declare encore l'ancien chemin.
        # Sondes croisees + orientation, uniquement si les chemins divergent.
        stale_paths = (
            _stale_branch_probe(repo_root, base_pp, pp, args.base, merge_base)
            if base_pp is not None and _pair_paths_diverge(base_pp, pp)
            else None
        )
        if stale_paths is not None:
            # Verdict dedie : PAS un DRIFT_INTRODUCED (compteur propre), et le
            # remede est `gh pr update-branch`, jamais un rebaseline.
            verdict = "STALE_BRANCH"
        else:
            # Classification per-pair (cf _classify_per_pair -- le cas paire ajoutee
            # est special : pas d'etat pre-existant, l'etat HEAD = ce que la PR introduit).
            verdict = _classify_per_pair(base_status, head_status,
                                        base_drift, head_drift,
                                        base_no_baseline, head_no_baseline)

        entry = {
            "name": name,
            "family": pp.get("family", "?"),
            "parity_level": pp.get("parity_level", "?"),
            "base_ref": args.base,
            "base_status": base_status,
            "head_status": head_status,
            "verdict": verdict,
            # #23020 : les COTES en drift a chaque ref, et le nom du jumeau
            # que la PR a mis en drift -- le verdict ne le disait pas.
            "base_drift_sides": sorted(base_drift),
            "head_drift_sides": sorted(head_drift),
            "introduced_twins": sorted(head_drift - base_drift),
            # La pair PERD sa reference (audit absent / sans sha) a cette
            # ref : distinct du drift, et c'est ce qui permet au verdict
            # de ne pas classer "pre-existant" une PR qui supprime une
            # attestation.
            "base_no_baseline": base_no_baseline,
            "head_no_baseline": head_no_baseline,
            "base_details": base_details,
            "head_details": head_state["details"],
        }
        if stale_paths is not None:
            entry["paths_base"] = stale_paths["paths_base"]
            entry["paths_head"] = stale_paths["paths_head"]
        results.append(entry)

    n_ok = sum(1 for r in results if r["verdict"] == "OK")
    n_introduced = sum(1 for r in results if r["verdict"] == "DRIFT_INTRODUCED")
    n_resolved = sum(1 for r in results if r["verdict"] == "DRIFT_RESOLVED")
    n_pre_existing = sum(1 for r in results if r["verdict"] == "DRIFT_PRE_EXISTING")
    n_stale = sum(1 for r in results if r["verdict"] == "STALE_BRANCH")

    if args.json:
        out = {
            "mode": "per_pair",
            "registry": str(reg_path),
            "base_ref": args.base,
            "total": len(results),
            "ok": n_ok,
            "drift_introduced": n_introduced,
            "drift_resolved": n_resolved,
            "drift_pre_existing": n_pre_existing,
            "stale_branch": n_stale,
            "pairs": results,
        }
        print(json.dumps(out, ensure_ascii=False, indent=2))
    else:
        tag_map = {
            "OK": "OK",
            "DRIFT_INTRODUCED": "DRIFT-INTRO",
            "DRIFT_RESOLVED": "DRIFT-FIXED",
            "DRIFT_PRE_EXISTING": "DRIFT-PRE",
            "STALE_BRANCH": "STALE-BRANCH",
        }
        for r in results:
            tag = tag_map[r["verdict"]]
            print(f"[{tag}] {r['name']} ({r['family']}, {r['parity_level']}) "
                  f"base={r['base_status']} head={r['head_status']}")
            if r["verdict"] != "OK":
                for d in r["head_details"]:
                    print(f"       HEAD: {d}")
            if r["verdict"] == "DRIFT_INTRODUCED" and r.get("introduced_twins"):
                # #23020 : le message nomme LE jumeau en cause.
                print(f"       Jumeau(x) mis en drift par la PR : "
                      f"{', '.join(r['introduced_twins'])}")
        print(f"\nTotal : {len(results)} paire(s) | "
              f"OK={n_ok} INTRO={n_introduced} FIXED={n_resolved} "
              f"PRE={n_pre_existing} STALE={n_stale}")

    # Le gate rougit sur DRIFT_INTRODUCED **et** sur STALE_BRANCH : une paire
    # perimee exige une action lane (`gh pr update-branch`) -- le bloc de
    # remediation du workflow, ou vit la ligne update-branch, n'est rendu que
    # sur exit 1. Les paires STALE ne comptent PAS dans drift_introduced
    # (#22920) : le message de derive de contenu ne doit pas les viser.
    if args.check and (n_introduced > 0 or n_stale > 0):
        if args.per_pair:
            # Le DRIFT d'une normalisation outillee (strip_probe_banner.py --apply,
            # strip_machine_paths.py, scrub_papermill_paths.py) deplace le blob SHA
            # SANS toucher le contenu calcule : la parite est vraie, c'est son
            # empreinte qui a bouge. Dans ce cas le rebaseline --update va EN DERNIER,
            # apres ces strips, sinon l'attestation est invalidee par le strip qui suit
            # (piege naturel, #8957).
            #
            # Ce rappel est un DIAGNOSTIC destine a l'humain : il va sur stderr, pas stdout.
            # En mode --json, stdout est un contrat machine (un unique objet JSON consomme
            # par le workflow CI via json.load) ; imprimer ce rappel sur stdout apres le
            # JSON -> json.load levait "Extra data" et faisait tomber le gate en raw
            # traceback (PRs #9097/#9098, exit 1 sur drift introduit). stderr reste visible
            # dans les logs CI sans corrompre le rapport.
            #
            # Uniquement si un vrai DRIFT_INTRODUCED existe : sur une sortie
            # rouge STALE_BRANCH seule, ce rappel (rebaseline apres strips)
            # ne s'applique pas -- le remede est `gh pr update-branch`.
            if n_introduced > 0:
                # #23020 : le message d'erreur nomme le jumeau en cause.
                intro = [
                    f"{r['name']} ({', '.join(r['introduced_twins'])})"
                    for r in results
                    if r["verdict"] == "DRIFT_INTRODUCED"
                ]
                if intro:
                    print(
                        "\nJumeau(x) mis(s) en drift par la PR : "
                        + " ; ".join(intro)
                        + " -- rebaseline l'attestation de la paire "
                        "(check_twin_parity.py --update) ou deplace le "
                        "jumeau en lockstep.",
                        file=sys.stderr,
                    )
                print(
                    "\nRappel : si le DRIFT vient d'une normalisation outillee qui "
                    "deplace le blob SHA (strip_probe_banner.py --apply, "
                    "strip_machine_paths.py, scrub_papermill_paths.py), le rebaseline "
                    "--update va EN DERNIER, apres ces strips -- attester PUIS "
                    "stripper invalide l'attestation (#8957).",
                    file=sys.stderr,
                )
        return 1
    return 0


def run_ci_strict(args, organ, results, pairs, reg_path, n_ok, n_drift, n_missing):
    """Mode --ci-strict, extrait verbatim (T7, #26364)."""
    _latest_audit = organ._latest_audit
    # Breakdown par categorie : legacy vs content vs missing vs ok
    cat = {
        "n_ok_legacy": 0,             # blob SHA match, pas de content_sha enregistre
        "n_ok_content": 0,            # content_sha match (volet c)
        "n_drift_blob": 0,            # legacy blob SHA mismatch
        "n_drift_content": 0,         # content_sha mismatch
        "n_drift_legacy_after_content": 0,  # legacy blob drift mais content_sha OK
                                         # = strip outille detecte
        "n_missing_python": 0,
        "n_missing_csharp": 0,
        "n_no_audit": 0,              # paire sans audits ni last_audit
        "n_numbering_drift": 0,       # numeros de base distincts (#12933)
    }
    ci_results = []
    for pp, r in zip(pairs, results):
        audit = _latest_audit(pp)
        rec_py = audit.get("python_sha")
        rec_cs = audit.get("csharp_sha")
        rec_cpy = audit.get("content_python_sha")
        rec_ccs = audit.get("content_csharp_sha")
        cur_py = r["current_python_sha"]
        cur_cs = r["current_csharp_sha"]
        cur_cpy = r["current_content_python_sha"]
        cur_ccs = r["current_content_csharp_sha"]

        entry_ci = {
            "name": r["name"],
            "family": r["family"],
            "parity_level": r["parity_level"],
            "status": r["status"],
            "details": list(r["details"]),
            "has_content_sha_audit": bool(rec_cpy and rec_ccs),
        }

        # NUMBERING-DRIFT (#12933) : compte dans SA categorie, sans
        # re-classer la paire dans les buckets SHA (blob/content) -- une
        # paire renumerotee unilateralement est rouge pour une raison qui
        # n'a rien a voir avec l'attestation d'empreinte, et la double
        # comptabilisation (ex. no_audit en plus) fausserait chaque
        # categorie.
        if r["status"] == "NUMBERING-DRIFT":
            cat["n_numbering_drift"] += 1
            ci_results.append(entry_ci)
            continue

        if not audit:
            cat["n_no_audit"] += 1
            ci_results.append(entry_ci)
            continue

        py_missing = (cur_py is None)
        cs_missing = (cur_cs is None)
        if py_missing:
            cat["n_missing_python"] += 1
        if cs_missing:
            cat["n_missing_csharp"] += 1

        blob_py_drift = (not py_missing and rec_py and cur_py != rec_py)
        blob_cs_drift = (not cs_missing and rec_cs and cur_cs != rec_cs)
        content_py_drift = (rec_cpy and cur_cpy and cur_cpy != rec_cpy)
        content_cs_drift = (rec_ccs and cur_ccs and cur_ccs != rec_ccs)

        if entry_ci["has_content_sha_audit"]:
            if content_py_drift or content_cs_drift:
                cat["n_drift_content"] += 1
            elif blob_py_drift or blob_cs_drift:
                # Churn metadata-only carnet : INFORMATIF, jamais bloquant.
                # `_content_sha` hache les cellules ET leurs outputs, en
                # n'excluant que `nb["metadata"]` (cost / papermill /
                # kernelspec / language_info). Donc « blob bouge, content
                # identique » ne peut signifier QUE du churn de metadata
                # carnet -- exactement le faux positif que le volet c a ete
                # construit pour tuer (cf docstring de `_content_sha`).
                # Rougir ici le re-fabriquerait au niveau du cron : incident
                # du 2026-08-07, cron rouge sur main pour Sudoku-08/14 BDD --
                # les 2 paires nommees dans cette meme docstring -- avec un
                # `::error ...::<none>` qui ne designait aucune paire (leur
                # `status` reste OK, donc `_cron_extract_drift` n'en listait
                # aucune). Et le remede prescrit (`--update`) est un NO-OP
                # par design puisque `_shas_match` compare les content_sha :
                # un gate que son propre remede ne peut pas eteindre.
                cat["n_drift_legacy_after_content"] += 1
                entry_ci["metadata_only_blob_drift"] = True
                entry_ci["details"].append(
                    "blob SHA drift MAIS content_sha OK : churn metadata-only "
                    "(metadata.cost / papermill / kernelspec) -- aucune divergence "
                    "pedagogique. INFORMATIF : ne fait pas rougir le gate. "
                    "`--update` est un no-op par design ici (il compare les "
                    "content_sha) ; re-tamponner le blob SHA exigerait --force et "
                    "n'apporterait aucune information nouvelle (cf #9399 critere 2)."
                )
            else:
                cat["n_ok_content"] += 1
        else:
            if blob_py_drift or blob_cs_drift:
                cat["n_drift_blob"] += 1
            else:
                cat["n_ok_legacy"] += 1

        ci_results.append(entry_ci)

    # Anomalies BLOQUANTES (celles qui font rougir le gate).
    # `n_drift_legacy_after_content` en est volontairement EXCLU : blob
    # bouge + content identique == churn metadata-only, informatif (cf la
    # classification ci-dessus). `n_total_drift` reste le total de TOUTES
    # les anomalies, pour le reporting.
    n_blocking_drift = (cat["n_drift_blob"] + cat["n_drift_content"]
                        + cat["n_missing_python"] + cat["n_missing_csharp"]
                        + cat["n_no_audit"] + cat["n_numbering_drift"])
    n_total_drift = n_blocking_drift + cat["n_drift_legacy_after_content"]

    if args.json:
        out = {
            "mode": "ci_strict",
            "registry": str(reg_path),
            "total": len(ci_results),
            "ok_total": n_ok,
            "drift_total": n_drift,
            "missing_total": n_missing,
            "ci_strict": cat,
            "n_total_drift": n_total_drift,
            "n_blocking_drift": n_blocking_drift,
            "pairs": ci_results,
        }
        print(json.dumps(out, ensure_ascii=False, indent=2))
    else:
        print(f"[CI-STRICT] {len(ci_results)} paire(s) | "
              f"ok_legacy={cat['n_ok_legacy']} ok_content={cat['n_ok_content']} "
              f"drift_blob={cat['n_drift_blob']} drift_content={cat['n_drift_content']} "
              f"drift_legacy_after_content={cat['n_drift_legacy_after_content']} "
              f"missing_py={cat['n_missing_python']} missing_cs={cat['n_missing_csharp']} "
              f"no_audit={cat['n_no_audit']} numbering_drift={cat['n_numbering_drift']}")
        for r in ci_results:
            if r["status"] != "OK":
                print(f"  [{r['status']}] {r['name']} ({r['family']}, {r['parity_level']})")
                for d in r["details"]:
                    print(f"       - {d}")
        # Les paires en churn metadata-only gardent `status == OK` (aucune
        # divergence pedagogique) : sans cette boucle elles ne seraient
        # nommees NULLE PART, et un compteur non nul sans nom n'est pas
        # actionnable (c'est le `::error ...::<none>` du 2026-08-07).
        for r in ci_results:
            if r.get("metadata_only_blob_drift"):
                print(f"  [INFO metadata-only] {r['name']} "
                      f"({r['family']}, {r['parity_level']})")
                for d in r["details"]:
                    print(f"       - {d}")

    # CI gate : rouge sur les anomalies BLOQUANTES uniquement (le but du
    # cron fleet-wide). Le churn metadata-only est compte et nomme, mais
    # ne rougit pas -- sinon on re-fabrique le faux positif que le volet c
    # a elimine, et sur un gate dont le remede prescrit est un no-op.
    if args.check and n_blocking_drift > 0:
        return 1
    return 0
