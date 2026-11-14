#!/usr/bin/env python3
"""Decision par lake de l'opt-in i18n de la porte d'axiomes (#24107).

La porte d'axiomes (`scripts/lean/axiom_check_step.py`) derive, pour la
derivation `'*'`, la surface qu'elle inspecte : `discover_modules` (tout ce que
`lake build` compile) puis `filter_i18n_siblings` (les freres `_en` sont
retires). Le retrait des freres est **voyant** (la porte affiche la surface
exclue) mais **muet** sur la decision : le manifeste
`scripts/lean/ci_lakes.json` ne portait aucune cle `axiom-include-i18n-siblings`,
et le workflow interpolait donc toujours le defaut `|| 'false'`. Le resultat :
la porte d'axiomes ne verifiait que la moitie FR de chaque lac bilingue.

Ce module etablit, **lake par lake**, la decision `"true"` (l'opt-in) ou
`"false"` (l'ecart assume, avec la raison ecrite), et l'ecrit dans le
manifeste. Il ne lance **aucun Lean** : la mesure est faite sur les SOURCES,
avec les memes outils que la porte elle-meme :

  - la surface : `check_target_coverage.discover_modules` /
    `filter_i18n_siblings` (une seule copie du predicat `_en` dans le depot) ;
  - les declarations : `lean_server._enumerate_module_declarations` et
    `lean_server._classify_empty_enumeration` (le lexique de la porte, pas un
    second) ;
  - les ancres interdites : `check_added_axioms_cliquet.detect_anchors`
    (`native_decide`, `sorry`, `admit`) sur le source comment-stripped par le
    stripper de la porte (`lean_server._get_strip_lean_comments`).

Regle de decision (une seule, lisible, appliquee identiquement a tous les
lakes) :

  L'opt-in est `"true"` SI ET SEULEMENT SI
    (a) la porte tourne pour ce lake (`axiom-target-modules` present) ;
    (b) la surface inspectee est DERIVEE (`'*'`) -- une liste explicite
        inspecte deja les modules `_en` qu'elle nomme ;
    (c) la surface `_en` est non vide ;
    (d) chaque module `_en` est soit auditable (declarations > 0), soit
        declaration-free PAR CONCEPTION (`empty_reason ==
        declaration_free_module`) -- tout autre raison est un trou de source
        que la porte fait echouer fort (fail loud) ;
    (e) aucun module `_en` ne porte une ancre qui ferait rougir la porte :
        `native_decide` / `Lean.ofReduceBool` (axiome non white-liste ->
        rouge inconditionnel), `sorry` / `admit` (rouge seulement si la porte
        gate sur `sorryAx`, c'est-a-dire `axiom-fail-on-sorry` vrai).

  Sinon la decision est `"false"` et la raison est ecrite.

Ce que la mesure NE dit pas (et que seul CI peut dire) : que la surface `_en`
compile et que les axioms qu'elle expose sont ceux de son jumeau FR. La
premiere est garantie par la jambe de build du meme job (le lac qui build est
vert, donc ses modules `_en` elaborent) ; la seconde decoule de la fidelite de
la traduction (memes imports, meme corps). La preuve reste la CI : le
manifeste est dans le `GATE_SELF_COVER` du dispatcher, donc ce changement
relance la porte d'axiomes pour TOUS les lakes du manifeste.

Modes :
  (defaut)     table par lake : decision, raison, mesures
  --json       sortie machine
  --check      porte : exit 1 si le manifeste diverge des decisions
               recomputees, si une entree n'a pas de cle explicite, ou si le
               fichier de decisions a derive
  --update     ecrit la cle explicite dans le manifeste ET le fichier de
               decisions `axiom_i18n_siblings_decisions.json`

Aucune decision n'est un pave de prose : chaque ligne du fichier de decisions
porte la mesure qui l'a produite (surface, declarations, ancres).
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from datetime import datetime, timezone
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
MANIFEST = REPO_ROOT / "scripts" / "lean" / "ci_lakes.json"
DECISIONS = REPO_ROOT / "scripts" / "lean" / "axiom_i18n_siblings_decisions.json"
LEAN_AGENT_TESTS = (
    REPO_ROOT / "MyIA.AI.Notebooks" / "SymbolicAI" / "Lean" / "agent_tests"
)

# `Lean.ofReduceBool` est l'axiome que `native_decide` introduit ; une source
# peut l'ecrire directement, et le lexique d'ancres du cliquet ne le couvre pas.
# On l'ajoute ICI, explicitement, plutot que dans le lexique du cliquet : ce
# lexique decrit les ancres d'un DIFF de code ajoute, ici on classe une
# surface entiere.
_OF_REDUCE_BOOL_RE = re.compile(r"\bLean\.ofReduceBool\b")

# Ancres qui font rougir la porte quelle que soit sa politique sorry.
# `sorryAx` n'est jamais dans `forbidden` (lean_server) : seule la politique
# `fail_on_sorry` le gate. D'ou la separation des deux listes.
ALWAYS_FORBIDDEN_ANCHORS = ("native_decide", "Lean.ofReduceBool")
SORRY_ANCHORS = ("sorry", "admit")


def _load_gate_tools():
    """Charge les outils de la porte (enumeration, classification, ancres).

    Le chemin d'import est celui de `axiom_coverage.py` : par le FICHIER,
    jamais par un `__init__.py` de package. On ne reimplemente ici aucune
    notion : ni « declaration », ni « module `_en` », ni « ancre interdite ».
    """
    for path in (str(LEAN_AGENT_TESTS), str(REPO_ROOT / "scripts" / "lean")):
        if path not in sys.path:
            sys.path.insert(0, path)
    import lean_server  # noqa: E402
    from check_target_coverage import (  # noqa: E402
        discover_modules,
        filter_i18n_siblings,
    )
    from check_added_axioms_cliquet import detect_anchors  # noqa: E402
    return lean_server, discover_modules, filter_i18n_siblings, detect_anchors


def _i18n_subset(modules, filter_i18n_siblings):
    """Les modules `_en` d'un ensemble, par la soustraction de l'appel unique.

    Exactement le calcul de la porte (`axiom_check_step.py`) : la surface
    exclue est la difference entre l'ensemble et sa version filtree. Jamais un
    second predicat `_en` ici.
    """
    return sorted(set(modules) - set(filter_i18n_siblings(set(modules))))


def _module_anchors(ls, project, module, detect_anchors):
    """Ancres interdites portees par un module, sur le source sans commentaires."""
    src = ls._module_source_path(project, module)
    if src is None:
        return []
    text = ls._get_strip_lean_comments()(
        src.read_text(encoding="utf-8", errors="replace")
    )
    found = set()
    for line in text.splitlines():
        for token in detect_anchors(line):
            found.add(token)
        if _OF_REDUCE_BOOL_RE.search(line):
            found.add("Lean.ofReduceBool")
    return sorted(found)


def lake_surface(entry, tools):
    """Surface inspectee et surface i18n d'un lac du manifeste."""
    ls, discover_modules, filter_i18n_siblings, detect_anchors = tools
    targets = (entry.get("axiom-target-modules") or "").strip()
    project = REPO_ROOT / entry["project-path"]
    surface = {
        "mode": None,
        "modules": [],
        "i18n": [],
        "project": project,
        "project_exists": project.is_dir(),
    }
    if not targets:
        surface["mode"] = "SKIPPED"
        return surface
    if targets != "*":
        surface["mode"] = "EXPLICIT"
        surface["modules"] = [m.strip() for m in targets.split(",") if m.strip()]
        surface["i18n"] = _i18n_subset(surface["modules"], filter_i18n_siblings)
        return surface
    surface["mode"] = "WILDCARD"
    discovered = set(discover_modules(project, None))
    surface["modules"] = sorted(filter_i18n_siblings(discovered))
    surface["i18n"] = sorted(discovered - set(surface["modules"]))
    return surface


def decide_lake(entry, tools):
    """Decision d'opt-in i18n d'un lac + la raison ecrite + les mesures."""
    ls, _discover, _filter, detect_anchors = tools
    surface = lake_surface(entry, tools)
    gates_on_sorry = str(entry.get("axiom-fail-on-sorry", "true")).lower() == "true"
    # Une ancre « toujours interdite » ne l'est que sous la allow-list PAR
    # DEFAUT de la porte. Un lac qui porte `axiom-allow-axioms` (fichier `@`
    # ou liste inline) decide LUI-MEME de ses ancres : la source ne dit pas
    # si l'ancre enumeratee au build est couverte par la liste -- seul CI le
    # dit (le gate reel compare les noms resolus). Ces ancres restent
    # RAPPORTEES (i18n-anchors + noted), jamais decision-blockantes, sinon
    # l'organe fabrique un ecart assume la ou le wrapper tournait vert :
    # conway (79 ancres allow-listees, dont les jumeaux `_en` -- #25256).
    custom_allow = str(entry.get("axiom-allow-axioms", "")).strip() != ""

    row = {
        "lake": entry["lake"],
        "display-name": entry.get("display-name", entry["lake"]),
        "project-path": entry.get("project-path", ""),
        "mode": surface["mode"],
        "modules-inspected": len(surface["modules"]),
        "i18n-modules": len(surface["i18n"]),
        "i18n-declarations": 0,
        "i18n-anchors": {},
        "unsafe": [],
        "decision": "false",
        "reason": "",
    }

    if surface["mode"] == "SKIPPED":
        row["reason"] = (
            "pas de cle `axiom-target-modules` : la jambe Proof integrity est "
            "sautee pour ce lake (le workflow la conditionne a "
            "`matrix.axiom-target-modules != ''`) ; l'opt-in n'a aucune "
            "surface a couvrir")
        return row

    if surface["mode"] == "EXPLICIT":
        row["i18n-declarations"] = _count_declarations(ls, surface, detect_anchors)
        if surface["i18n"]:
            row["reason"] = (
                "liste de modules explicite : les modules `_en` qu'elle nomme "
                "sont deja inspectes par la porte (le filtre i18n ne vaut que "
                "pour la derivation '*') ; l'opt-in ne change rien")
        else:
            row["reason"] = (
                "liste de modules explicite sans module `_en` : la surface "
                "i18n est vide, l'opt-in ne change rien")
        return row

    if not surface["i18n"]:
        row["reason"] = (
            "aucun frere `_en` dans la surface derivee : lac monolingue, "
            "l'opt-in ne change rien")
        return row

    for module in surface["i18n"]:
        declarations = ls._enumerate_module_declarations(
            surface["project"], module)
        if declarations:
            row["i18n-declarations"] += len(declarations)
            empty_reason = None
        else:
            empty_reason = ls._classify_empty_enumeration(
                surface["project"], module)
        anchors = _module_anchors(ls, surface["project"], module, detect_anchors)
        if anchors:
            row["i18n-anchors"][module] = anchors
        blocking = [a for a in anchors
                    if a in ALWAYS_FORBIDDEN_ANCHORS and not custom_allow]
        if gates_on_sorry:
            blocking += [a for a in anchors if a in SORRY_ANCHORS]
        if empty_reason is not None and empty_reason != "declaration_free_module":
            row["unsafe"].append({
                "module": module,
                "reason": f"trou de source ({empty_reason}) : la porte echoue "
                          f"fort sur ce module",
            })
        for anchor in blocking:
            row["unsafe"].append({
                "module": module,
                "reason": f"ancre `{anchor}` sur la surface `_en` : la porte "
                          f"la ferait rougir"
                          + ("" if anchor in ALWAYS_FORBIDDEN_ANCHORS
                             else " (elle gate sur sorryAx)"),
            })

    if row["unsafe"]:
        first = row["unsafe"][0]
        row["reason"] = (
            f"l'ecart assume : {len(row['unsafe'])} module(s) `_en` "
            f"incompatible(s) avec l'opt-in (premier : {first['module']} -- "
            f"{first['reason']})")
        return row

    noted = sorted({a for anchors in row["i18n-anchors"].values()
                    for a in anchors
                    if a in SORRY_ANCHORS
                    or (custom_allow and a in ALWAYS_FORBIDDEN_ANCHORS)})
    if noted:
        governed = [a for a in noted if a in ALWAYS_FORBIDDEN_ANCHORS]
        if governed:
            row["reason"] = (
                f"opt-in sur : la surface `_en` ({row['i18n-modules']} modules, "
                f"{row['i18n-declarations']} declarations) ; les ancres "
                f"reportees ({', '.join(noted)}) sont gouvernees par la "
                f"allow-list du lac (`axiom-allow-axioms`) -- la source ne dit "
                f"pas si l'ancre resolue au build y est couverte, seule la CI "
                f"le dit (le gate reel compare les noms resolus)")
        else:
            row["reason"] = (
                f"opt-in sur : la surface `_en` ({row['i18n-modules']} modules, "
                f"{row['i18n-declarations']} declarations) ne porte aucun ancrage "
                f"qui ferait rougir la porte ; les `sorry` y sont rapportes, non "
                f"gates (la porte ne gate pas sur sorryAx pour ce lake)")
    else:
        row["reason"] = (
            f"opt-in sur : la surface `_en` ({row['i18n-modules']} modules, "
            f"{row['i18n-declarations']} declarations) est integralement "
            f"auditable et sans ancre interdite ; la porte couvre desormais "
            f"la surface bilingue entiere")
    row["decision"] = "true"
    return row


def _count_declarations(ls, surface, detect_anchors):
    """Declarations portees par la surface `_en` (mesure du compte du PR)."""
    total = 0
    for module in surface["i18n"]:
        total += len(ls._enumerate_module_declarations(
            surface["project"], module))
    return total


def report():
    """Decisions recomputees pour tous les lakes du manifeste."""
    tools = _load_gate_tools()
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    rows = [decide_lake(entry, tools) for entry in manifest["lakes"]]
    return manifest, rows


def decisions_payload(rows, lane):
    return {
        "_comment": (
            "Decision par lake de l'opt-in i18n de la porte d'axiomes "
            "(#24107). Genere par `scripts/lean/axiom_i18n_siblings.py "
            "--update` ; le registre du manifeste fait foi sur la valeur, ce "
            "fichier porte la RAISON et la MESURE. Une cle du manifeste qui "
            "diverge de ce fichier fait rougir `--check`."),
        "generated-at": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "generated-by": lane,
        "organ": "scripts/lean/axiom_i18n_siblings.py",
        "issue": 24107,
        "lakes": [
            {
                "lake": r["lake"],
                "decision": r["decision"],
                "reason": r["reason"],
                "mode": r["mode"],
                "i18n-modules": r["i18n-modules"],
                "i18n-declarations": r["i18n-declarations"],
            }
            for r in rows
        ],
    }


def _manifest_drift(rows):
    """Ecarts entre la cle du manifeste et la decision recomputee."""
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    by_lake = {e["lake"]: e for e in manifest["lakes"]}
    drifts = []
    for row in rows:
        entry = by_lake.get(row["lake"])
        if entry is None:
            drifts.append(f"{row['lake']}: absent du manifeste")
            continue
        key = entry.get("axiom-include-i18n-siblings")
        if key is None:
            drifts.append(
                f"{row['lake']}: pas de cle explicite "
                f"`axiom-include-i18n-siblings` (le workflow retombe alors "
                f"toujours sur son defaut 'false')")
        elif str(key).lower() != row["decision"]:
            drifts.append(
                f"{row['lake']}: manifeste={key} / decision recomputee="
                f"{row['decision']}")
    return drifts


def _decisions_drift(rows):
    """Ecarts entre le fichier de decisions et les decisions recomputees."""
    if not DECISIONS.exists():
        return ["fichier de decisions absent"]
    payload = json.loads(DECISIONS.read_text(encoding="utf-8"))
    recorded = {r["lake"]: r for r in payload.get("lakes", [])}
    drifts = []
    for row in rows:
        rec = recorded.get(row["lake"])
        if rec is None:
            drifts.append(f"{row['lake']}: absent du fichier de decisions")
            continue
        if rec.get("decision") != row["decision"]:
            drifts.append(
                f"{row['lake']}: fichier={rec.get('decision')} / "
                f"recomputee={row['decision']}")
        elif rec.get("reason") != row["reason"]:
            drifts.append(f"{row['lake']}: raisonderivee dans le fichier")
    for lake in recorded:
        if lake not in {r["lake"] for r in rows}:
            drifts.append(f"{lake}: lake inconnu du manifeste")
    return drifts


def apply_updates(rows, lane):
    """Ecrit la cle explicite dans le manifeste + le fichier de decisions."""
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    by_lake = {r["lake"]: r for r in rows}
    for entry in manifest["lakes"]:
        row = by_lake[entry["lake"]]
        entry["axiom-include-i18n-siblings"] = row["decision"]
    # `newline="\n"` explicite : sur Windows, `write_text` traduit le "\n" en
    # CRLF et le manifeste entier apparait reecrit (le fichier est versionne
    # en LF). Un diff de 500 lignes pour 35 cles Added = un manifeste
    # illisible ; le diff doit montrer LES decisions.
    MANIFEST.write_text(
        json.dumps(manifest, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8", newline="\n")
    DECISIONS.write_text(
        json.dumps(decisions_payload(rows, lane), ensure_ascii=False, indent=2)
        + "\n",
        encoding="utf-8", newline="\n")


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--json", action="store_true",
                        help="Sortie JSON machine-readable")
    parser.add_argument("--check", action="store_true",
                        help="Porte : exit 1 si le manifeste ou le fichier de "
                             "decisions divergent des decisions recomputees")
    parser.add_argument("--update", action="store_true",
                        help="Ecrit la cle explicite dans le manifeste et le "
                             "fichier de decisions")
    parser.add_argument("--lane", default="myia-po-2027:CoursIA-2",
                        help="Lane signataire du fichier de decisions")
    args = parser.parse_args(argv)

    _manifest, rows = report()

    if args.update:
        apply_updates(rows, args.lane)
        print(f"manifeste et fichier de decisions mis a jour "
              f"({sum(1 for r in rows if r['decision'] == 'true')} opt-in / "
              f"{len(rows)} lakes)")
        return 0

    if args.check:
        drifts = _manifest_drift(rows) + _decisions_drift(rows)
        if drifts:
            print("FAIL: divergence entre le manifeste, le fichier de "
                  "decisions et la mesure recomputee :")
            for d in drifts:
                print(f"  - {d}")
            return 1
        print("OK: chaque lake du manifeste porte une decision explicite "
              "`axiom-include-i18n-siblings`, conforme a la mesure "
              "recomputee et au fichier de decisions.")
        return 0

    if args.json:
        json.dump({"lakes": rows}, sys.stdout, ensure_ascii=False, indent=1)
        print()
        return 0

    opted_in = [r for r in rows if r["decision"] == "true"]
    print(f"opt-in i18n de la porte d'axiomes -- {len(opted_in)}/{len(rows)} "
          f"lakes du manifeste en opt-in")
    print()
    name_w = max(len(r["display-name"]) for r in rows)
    for row in rows:
        mark = "TRUE " if row["decision"] == "true" else "false"
        print(f"  {mark} {row['display-name']:<{name_w}}  "
              f"{row['mode']:<8} i18n={row['i18n-modules']:<3} "
              f"decl={row['i18n-declarations']}")
        print(f"        {row['reason']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
