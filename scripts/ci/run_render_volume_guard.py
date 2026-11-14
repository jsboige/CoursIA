#!/usr/bin/env python3
"""Garde de la voie rapide : perte de volume de RENDU d'un carnet (#11656).

Ce module est l'ADAPTATEUR du workflow `render-volume-delta-advisory.yml` vers
la voie rapide. Il ne REIMPLEMENTE aucune detection : la mesure reste celle de
`scripts/notebook_tools/check_render_volume_delta.py`, appele ici comme
bibliotheque (regle « organ-first » : nommer l'organe natif avant de
reimplementer).

Ce que le workflow source fait, et ce que ce module conserve
-------------------------------------------------------------
1. La base est le **merge-base** (`git merge-base origin/main HEAD`), jamais
   `origin/main` deux-points : sur une branche en retard, le deux-points
   inclut les evolutions de main hors PR et fait signaler des pertes que la
   PR n'a pas causees (c.357-L1, durable).
2. Si le merge-base est introuvable, on **s'abstient en le disant** -- jamais
   de repli silencieux qui rendrait « pas regarde » et « rien trouve »
   indistinguables.
3. Les carnets mesures sont ceux du diff `BASE..HEAD` filtres en `MR` avec
   detection de renommage (`-M50%`). Le plafond historique de 50 carnets
   n'ECARTE plus rien : il est nomme quand il est franchi (une fournee de
   serie entiere est aujourd'hui admise, et une troncature silencieuse
   faisait passer une moitie de carnets non mesures pour « rien a signaler »).

Ce que ce module AJOUTE (ecarts assumes, declares)
--------------------------------------------------
- **Verdict cible** : seul un finding `LOST_MIME` de famille `image` est un
  verdict. Les autres kinds (`DELTA_SIGNAL`, `NEW_MIME`, `TEXT_DELTA`,
  `TEXT_LOST`, `UNAVAILABLE_SIGNAL`) sont RAPPORTES mais ne font pas echouer
  la garde : ils sont plus larges que le cas vise (#26032 : une PNG de 40 Ko
  disparue de la cellule 10) et feraient du bruit dans le verdict PR.
- **Abstention = rc 2** (erreur structurelle), la ou le workflow source
  sortait en 0 avec un simple `::warning`. Un abstention qui se lit « OK »
  dans un check-run est un vert muet ; la doctrine du depot est « jamais un
  vert muet ». La voie rapide classe ce rc en `warn_rc` : le verdict est
  publie NEUTRE (« incident »), visible et non bloquant.
- **Erreur structurelle sur un carnet = rc 2**, la ou le workflow source
  laissait passer un JSON illisible qui rendait `findings_total=0`, donc un
  « rien de perdu » sur un carnet jamais mesure.
- **Le renommage est MESURE** : `--name-status` donne les DEUX chemins
  d'une entree `R` (l'ancien a la base, le nouveau a la tete). Avec
  `--name-only`, seul le nouveau arrivait, l'organe le lisait comme un
  carnet absent de la base, donc l'exemptait (`new_file`) -- et un carnet
  renomme n'etait jamais mesure. L'organe natif accepte desormais deux
  chemins (`head_path`).
- **Un `git diff` en echec rend rc 2**, jamais « aucun carnet modifie » :
  un verdict « rien a signaler » sur une mesure qui n'a pas eu lieu est un
  vert muet.
- **Plusieurs carnets dans UNE invocation** : le workflow source passait la
  liste des carnets a un outil dont l'argument positionnel est unique --
  argparse echouait des le second carnet, le JSON restait illisible, et le
  commentaire affichait « rien de perdu » sur une PR qui en avait change
  plusieurs. Ici, chaque carnet est mesure dans le meme processus.

Codes de sortie
---------------
0 : mesure faite, aucun finding cible.
1 : au moins un finding cible (`LOST_MIME` / famille `image`).
2 : abstention (merge-base introuvable) ou erreur structurelle.

Usage
-----
    python scripts/ci/run_render_volume_guard.py --base-ref origin/main
    python scripts/ci/run_render_volume_guard.py --base-ref origin/main --json
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
NOTEBOOK_TOOLS = REPO_ROOT / "scripts" / "notebook_tools"
if str(NOTEBOOK_TOOLS) not in sys.path:
    sys.path.insert(0, str(NOTEBOOK_TOOLS))

# L'organe natif de la mesure : on l'APPELE, on ne le reecrit pas.
import check_render_volume_delta as rvd  # noqa: E402

# Plafond de carnets mesures, repris du workflow source (`head -50`). Il
# n'ECARTE plus rien : c'est un seuil d'ALERTE. La version precedente
# tronquait (`notebooks[:MAX_NOTEBOOKS]`) SANS LE DIRE -- une fournee de
# serie entiere passait alors pour « rien a signaler » alors que la
# moitie des carnets n'avait pas ete mesuree. Au-dela, le verdict nomme le
# nombre de carnets mesures.
MAX_NOTEBOOKS = 50
# La cible du verdict : une MIME IMAGE disparue entre la base et la tete.
TARGET_KIND = "LOST_MIME"
TARGET_FAMILY = "image"


def git(*args: str) -> subprocess.CompletedProcess:
    return subprocess.run(
        ["git", *args],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )


def resolve_merge_base(base_ref: str, head_ref: str) -> str:
    """Rend le merge-base `base_ref`/`head_ref`, ou '' s'il n'existe pas.

    Vide = abstention. Aucun repli sur `base_ref` deux-points : la base
    deux-points inclut les evolutions de main hors PR et produit des pertes
    factices (c.357-L1).
    """
    proc = git("merge-base", base_ref, head_ref)
    if proc.returncode != 0:
        return ""
    return proc.stdout.strip()


def changed_notebooks(base_ref: str, head_ref: str) -> tuple[list[dict], str]:
    """Carnets modifies (ou renommes) entre la base et la tete.

    `--name-status` (et non `--name-only`) est INDISPENSABLE : une entree
    `R` porte DEUX chemins -- l'ancien (base) et le nouveau (tete). Avec
    `--name-only`, seul le nouveau arrivait, et l'organe le lisait comme un
    carnet absent de la base : il l'exemptait donc (`new_file`). Un carnet
    renomme n'etait alors JAMAIS mesure -- or les descentes en
    sous-series renomment ET re-executent dans la meme PR, ce qui est
    exactement la ou la perte de volume de rendu se cache.

    Deux etats de nommage sont distingues :

    - le renommage que git VOIT (`R`, similarite de contenu >= 50 %) : les
      deux chemins sont connus, le carnet est mesure sur les deux ;
    - le renommage que git ne voit PLUS (`D` + `A`) : le carnet a ete
      re-execute au point de ne plus ressembler a sa version de base.
      Mesure (13/11) : un carnet dont la sortie image a disparu tombe a
      ~1 % de similarite, et git le rend `D` + `A` -- le carnet sortait
      alors du filtre `MR`, donc n'etait pas mesure du tout. Ces paires
      sont reconnues par les **identifiants de cellules** (nbformat 4.5),
      qui survivent au renommage ET a la re-execution, alors que la
      similarite de contenu, non.

    Rend le couple (carnets, erreur). Une erreur de `git` n'est PAS une
    liste vide : elle rend rc 2, jamais « aucun carnet modifie ».
    """
    proc = git("diff", "--name-status", "--diff-filter=MARD", "-M50%",
               base_ref, head_ref)
    if proc.returncode != 0:
        return [], (f"`git diff --name-status {base_ref} {head_ref}` a echoue : "
                    f"{proc.stderr.strip()[:300]}")

    modifies: list[str] = []
    ajouts: list[str] = []
    suppressions: list[str] = []
    renommages: list[tuple[str, str]] = []
    for line in proc.stdout.splitlines():
        line = line.strip()
        if not line:
            continue
        parts = line.split("\t")
        kind = parts[0][:1]
        if kind == "R":
            if len(parts) >= 3:
                renommages.append((parts[1], parts[2]))
        elif kind == "A":
            if len(parts) >= 2:
                ajouts.append(parts[1])
        elif kind == "D":
            if len(parts) >= 2:
                suppressions.append(parts[1])
        elif len(parts) >= 2:
            modifies.append(parts[1])

    # Appariement des renommages que git ne voit plus : un carnet AJOUTE et
    # un carnet SUPPRIME qui partagent des identifiants de cellules sont le
    # MEME carnet, deplace.
    apparies: dict[str, str] = {}
    ajouts_libres = []
    suppressions_libres = []
    for chemin in ajouts:
        if chemin.endswith(".ipynb"):
            ajouts_libres.append(chemin)
    for chemin in suppressions:
        if chemin.endswith(".ipynb"):
            suppressions_libres.append(chemin)
    # Borne de cout : la comparaison est au plus N*N lectures de carnet.
    if len(ajouts_libres) * len(suppressions_libres) <= 100:
        ids_base = {chemin: rvd.cell_ids_at_ref(Path(chemin), base_ref)
                    for chemin in suppressions_libres}
        pris: set[str] = set()
        for ajout in ajouts_libres:
            ids_head = rvd.cell_ids_at_ref(Path(ajout), head_ref)
            if not ids_head:
                continue
            for suppression in suppressions_libres:
                if suppression in pris:
                    continue
                if ids_base.get(suppression, set()) & ids_head:
                    apparies[ajout] = suppression
                    pris.add(suppression)
                    break

    notebooks: list[dict] = []
    for base_path, head_path in renommages:
        if base_path.endswith(".ipynb") or head_path.endswith(".ipynb"):
            notebooks.append({"base": base_path, "head": head_path,
                              "kind": "renomme"})
    for chemin in modifies:
        if chemin.endswith(".ipynb"):
            notebooks.append({"base": chemin, "head": chemin,
                              "kind": "modifie"})
    for chemin in ajouts:
        if not chemin.endswith(".ipynb"):
            continue
        if chemin in apparies:
            notebooks.append({"base": apparies[chemin], "head": chemin,
                              "kind": "renomme"})
        else:
            notebooks.append({"base": chemin, "head": chemin,
                              "kind": "nouveau"})
    return notebooks, ""


def target_findings(findings: list[dict]) -> list[dict]:
    """Les findings qui font echouer la garde (`LOST_MIME` / famille image)."""
    return [f for f in findings
            if f.get("kind") == TARGET_KIND
            and f.get("mime_family") == TARGET_FAMILY]


def scan(notebooks: list[dict], base_ref: str, head_ref: str) -> dict:
    """Mesure chaque carnet et classe les findings.

    Rend un rapport : `target` (les findings qui font echouer), `other` (les
    autres, rapportes sans effet), `errors` (carnets illisibles), `scanned`.
    """
    report: dict = {
        "base_ref": base_ref,
        "head_ref": head_ref,
        "scanned": [],
        "target": [],
        "other": [],
        "errors": [],
        "new_files": [],
        "renamed": [],
        "notebooks_total": len(notebooks),
        "above_cap": len(notebooks) > MAX_NOTEBOOKS,
    }
    for entry in notebooks:
        base_path = entry["base"]
        head_path = entry["head"]
        # L'identite lue est celle de la TETE (le chemin que le lecteur voit
        # dans la PR) ; le chemin de BASE sert a la comparaison.
        notebook = head_path
        relative = Path(head_path)
        path = REPO_ROOT / relative
        if not path.exists():
            report["errors"].append(
                {"notebook": notebook,
                 "error": "absent de l'arbre de travail"})
            continue
        if base_path != head_path:
            report["renamed"].append({"base": base_path, "head": head_path})
        # L'organe natif attend des chemins RELATIFS a la racine du depot :
        # il les passe tels quels a `git show <ref>:<chemin>`. Le chemin de
        # base et le chemin de tete sont distincts pour un renommage.
        result = rvd.scan_notebook(Path(base_path), base_ref, head_ref,
                                    head_path=relative)
        if "error" in result:
            report["errors"].append({"notebook": notebook,
                                     "error": result["error"]})
            continue
        if result.get("new_file"):
            # Un carnet NEUF n'a rien a perdre : il est exempt, et il est
            # COMPTE comme tel -- il ne passe pas dans `scanned`, qui
            # compte les carnets reellement mesures.
            report["new_files"].append(notebook)
            continue
        report["scanned"].append(notebook)
        for finding in result.get("findings", []):
            item = {"notebook": notebook, **finding}
            if finding.get("kind") == TARGET_KIND \
                    and finding.get("mime_family") == TARGET_FAMILY:
                report["target"].append(item)
            else:
                report["other"].append(item)
    return report


def render(report: dict) -> None:
    """Rend le rapport en texte lisible (sortie standard du garde)."""
    print(f"[BASE]  {report['base_ref']} (merge-base)")
    print(f"[HEAD]  {report['head_ref']}")
    print(f"[SCAN]  {len(report['scanned'])} carnet(s) mesure(s), "
          f"{len(report['new_files'])} nouveau(x) exempt(s), "
          f"{len(report['errors'])} erreur(s)")
    if report.get("above_cap"):
        # Le plafond n'ecarte plus rien, mais il se nomme : une mesure
        # partielle qui ne le dit pas est un vert muet.
        print(f"[PLAFOND] {report.get('notebooks_total', 0)} carnet(s) "
              f"modifie(s), au-dela du plafond historique de {MAX_NOTEBOOKS} : "
              "aucun n'est ecarte, tous sont mesures.")
    for entry in report.get("renamed", []):
        print(f"  - renomme {entry['base']} -> {entry['head']}")
    for entry in report["errors"]:
        print(f"  - ERREUR {entry['notebook']} : {entry['error']}")
    for entry in report["target"]:
        print(f"  - CIBLE {entry['notebook']} : {entry['kind']} "
              f"famille '{entry.get('mime_family')}' disparue "
              f"(base {entry.get('before_bytes')}B, "
              f"head {entry.get('after_bytes')}B)")
    for entry in report["other"]:
        print(f"  - autre {entry['notebook']} : {entry['kind']} "
              f"({entry.get('mime_family', '-')})")
    if report["target"]:
        print(f"[VERDICT] {len(report['target'])} finding(s) CIBLE : "
              "une MIME image a disparu du rendu.")
    elif report["errors"]:
        print("[VERDICT] rien n'a pu etre certifie : erreur structurelle.")
    else:
        print("[VERDICT] aucune MIME image perdue sur les carnets mesures.")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=__doc__.split("\n", 1)[0])
    parser.add_argument("--base-ref", default="origin/main",
                        help="Ref de la branche de base (defaut: origin/main)")
    parser.add_argument("--head-ref", default="HEAD",
                        help="Ref de la tete (defaut: HEAD)")
    parser.add_argument("--notebook", action="append", default=None,
                        help="Carnet a mesurer (repete). Par defaut : "
                             "les carnets modifies entre la base et la tete.")
    parser.add_argument("--json", action="store_true",
                        help="Rend le rapport en JSON")
    args = parser.parse_args(argv)

    # L'organe natif appelle `git` sans `cwd` : il faut etre a la racine du
    # depot pour que `git show <ref>:<chemin relatif>` trouve le carnet.
    os.chdir(REPO_ROOT)

    merge_base = resolve_merge_base(args.base_ref, args.head_ref)
    if not merge_base:
        message = (f"[ABSTENTION] merge-base {args.base_ref} {args.head_ref} "
                   "introuvable : aucun carnet n'a ete mesure. Aucun "
                   "verdict n'est fabrique (ref rate ou branche sans ancre "
                   "commune).")
        if args.json:
            print(json.dumps({"abstained": True, "reason": message},
                             ensure_ascii=False, indent=2))
        else:
            print(message)
        return 2

    if args.notebook:
        # Un carnet impose a la main : un seul chemin, pas de renommage.
        notebooks = [{"base": path, "head": path} for path in args.notebook]
    else:
        notebooks, error = changed_notebooks(merge_base, args.head_ref)
        if error:
            # Un `git diff` en echec n'est pas « aucun carnet modifie » :
            # c'est une mesure qui n'a pas eu lieu. Rendre 0 ici publierait
            # un vert muet sur une PR jamais regardee.
            message = (f"[ABSTENTION] {error} -- aucun carnet n'a ete mesure. "
                       "Aucun verdict n'est fabrique.")
            if args.json:
                print(json.dumps({"abstained": True, "reason": message},
                                 ensure_ascii=False, indent=2))
            else:
                print(message)
            return 2
    if not notebooks:
        message = ("[OK] aucun carnet modifie entre la base et la tete : "
                   "rien a mesurer.")
        if args.json:
            print(json.dumps({"scanned": [], "target": [], "other": [],
                              "errors": []}, ensure_ascii=False, indent=2))
        else:
            print(message)
        return 0

    report = scan(notebooks, merge_base, args.head_ref)
    if args.json:
        print(json.dumps(report, ensure_ascii=False, indent=2))
    else:
        render(report)

    if report["errors"]:
        # Un carnet non mesure ne vaut pas « rien de perdu » : le verdict
        # est structurel, la voie rapide le publie NEUTRE.
        return 2
    if report["target"]:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
