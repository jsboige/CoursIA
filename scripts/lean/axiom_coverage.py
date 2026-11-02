#!/usr/bin/env python3
"""Couverture proof-integrity (B.3) des lakes de la matrice lean CI.

Rend la couverture du gate d'axiomes LISIBLE par un reviewer en une commande,
pour trancher B.3 (« non applicable » vs « applicable ») sans enquete :
quels lakes portent `axiom-target-modules` dans le manifeste
`scripts/lean/ci_lakes.json` (le gate tourne pour eux), lesquels sont nus,
et — pour les listes explicites — si chaque module nomme existe reellement
sous le chemin du lake (ferme le cas #8782 : un vert dont les
target-modules n'atteignent aucun module reellement modifie).

Sortie : table alignée + comptes. `--json` pour dossier/CI. Exit 0 en
lecture ; `--require-covered` durcit en gate (exit 1 si un lake est nu) —
a n'activer que lorsque le cablage progressif (#18038) est termine.

Verdicts B.3 par lake :
- WIRED      : cle presente, modules verifies sur disque (ou passe-partout)
- WIRED-DEAD : cle presente mais au moins un module nomme introuvable
               (le vert du gate ne dit alors rien des modules reels)
- BARE       : pas de cle — le step Proof integrity ne tourne pas,
               B.3 se lit « non applicable » (#8677 cas a)
- NOT-APPLICABLE : pas de cle ET le lake ne declare RIEN enumerable (tous
               ses modules rendent `declaration_free_module` a
               l'enumerateur du gate : `import` + `#check` + prose, ou des
               `example` anonymes). Le cabler est impossible : le gate
               echoue sur sa non-vacuite de lac (« the gate inspected
               nothing »), et la jambe resterait rouge a perpetuite.
               Mesure du 2026-11-02 : `conway_cgt_lean` et
               `mathlib_examples` sont les deux seuls lakes dans ce cas sur
               33 — la decision « sans gate » est celle de #22519 §4.1,
               ce verdict la rend lisible par la commande (#24092, #18038).
"""
import argparse
import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
MANIFEST = REPO_ROOT / "scripts" / "lean" / "ci_lakes.json"
# L'organe du gate est le code du checkout QUI EXECUTE ce census, pas un
# chemin relatif a l'arbre ausculte : un census peut viser un autre arbre
# (tests, worktree) sans que l'enumerateur change de version sous ses pieds.
LEAN_AGENT_TESTS = (
    Path(__file__).resolve().parents[2]
    / "MyIA.AI.Notebooks" / "SymbolicAI" / "Lean" / "agent_tests"
)


def _modules_on_disk(project_path: Path) -> set:
    """Noms de modules `.lean` du lake en notation pointee (SocialChoice.Arrow),
    relative au chemin du lake — la convention du manifeste."""
    if not project_path.is_dir():
        return set()
    root = project_path
    return {
        str(p.relative_to(root).with_suffix("")).replace("\\", "/").replace("/", ".")
        for p in root.rglob("*.lean")
        if ".lake" not in p.parts
    }


def _load_gate_enumerator():
    """L'enumerateur de declarations du gate, charge paresseusement.

    On ne reimplemente PAS la notion de « declaration » ici : `axiom_coverage`
    doit repondre la meme chose que le step Proof integrity, et un second
    lexique de mots-cles derive du premier. La premiere version de ce fichier
    l'a fait (regex locale incluant `example`/`instance`) et rendait
    `mathlib_examples` « cablable » la ou le gate enumere zero declaration —
    exactement la derive que l'alarme `EMPTY_PARSE_GAP` de `lean_server`
    existe pour signaler (#8722). Le chemin d'import est celui de
    `axiom_check_step.py` : par le fichier, jamais par `prover/__init__.py`.
    """
    agent_tests = str(LEAN_AGENT_TESTS)
    if agent_tests not in sys.path:
        sys.path.insert(0, agent_tests)
    import lean_server  # noqa: E402  (chemin pose juste au-dessus)

    return lean_server


def _declaration_state(project_path: Path):
    """(declarations enumerables, raison du zero) pour un lake entier.

    `-1` = disque muet (aucun `.lean`), qui n'est PAS la meme chose que
    « declare rien » : un checkout partiel ne doit pas blanchir un lake.
    La raison est celle du gate (`_classify_empty_enumeration`), pas une
    lecture de prose : seul `declaration_free_module` sur TOUS les modules
    autorise le verdict NOT-APPLICABLE — un `all_private_declarations` ou un
    `source_not_found` reste un etat a instruire, pas une exoneration.
    """
    if not project_path.is_dir():
        return -1, "source_not_found"
    modules = sorted(_modules_on_disk(project_path) - {"lakefile"})
    if not modules:
        return -1, "source_not_found"
    ls = _load_gate_enumerator()
    total = 0
    reasons = set()
    for module in modules:
        declarations = ls._enumerate_module_declarations(project_path, module)
        if declarations:
            total += len(declarations)
        else:
            reasons.add(ls._classify_empty_enumeration(project_path, module))
    return total, ",".join(sorted(reasons))


def coverage_report(verify_modules: bool = True) -> dict:
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    lakes = []
    for entry in manifest["lakes"]:
        targets = (entry.get("axiom-target-modules") or "").strip()
        row = {
            "lake": entry["lake"],
            "display-name": entry.get("display-name", entry["lake"]),
            "project-path": entry.get("project-path", ""),
            "axiom-target-modules": targets or None,
            "axiom-fail-on-sorry": entry.get("axiom-fail-on-sorry"),
            "verdict": "BARE",
            "dead_modules": [],
        }
        if targets:
            row["verdict"] = "WIRED"
            if targets == "*":
                row["wildcard"] = True
            elif verify_modules:
                on_disk = _modules_on_disk(REPO_ROOT / entry["project-path"])
                dead = [m for m in targets.split(",") if m not in on_disk]
                if dead:
                    row["verdict"] = "WIRED-DEAD"
                    row["dead_modules"] = sorted(dead)
        else:
            # Pas de cle : soit le cablage manque (BARE, un grain reste a
            # prendre), soit le lake ne declare rien et AUCUN cablage ne peut
            # le rendre vert (NOT-APPLICABLE). Le second etat se mesure avec
            # l'enumerateur du gate, il ne se declare pas par une liste qui
            # rouille.
            n_decl, reason = _declaration_state(REPO_ROOT / entry["project-path"])
            row["declaration_count"] = n_decl
            row["declaration_reason"] = reason
            if n_decl == 0 and reason == "declaration_free_module":
                row["verdict"] = "NOT-APPLICABLE"
        lakes.append(row)
    counts = {}
    for row in lakes:
        counts[row["verdict"]] = counts.get(row["verdict"], 0) + 1
    return {"total": len(lakes), "counts": counts, "lakes": lakes}


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--json", action="store_true", help="Sortie JSON machine-readable")
    parser.add_argument("--no-verify", action="store_true",
                        help="Sauter la verification d'existence des modules explicites")
    parser.add_argument("--require-covered", action="store_true",
                        help="Gate : exit 1 si un lake est BARE (cablage #18038 non termine)")
    args = parser.parse_args(argv)

    report = coverage_report(verify_modules=not args.no_verify)

    if args.json:
        json.dump(report, sys.stdout, ensure_ascii=False, indent=1)
        print()
        return 1 if (args.require_covered and report["counts"].get("BARE")) else 0

    counts = report["counts"]
    print(f"proof-integrity coverage — {report['total']} lakes du manifeste : "
          f"{counts.get('WIRED', 0)} wired, {counts.get('WIRED-DEAD', 0)} wired-dead, "
          f"{counts.get('BARE', 0)} bare, "
          f"{counts.get('NOT-APPLICABLE', 0)} sans declaration")
    print()
    name_w = max(len(r["display-name"]) for r in report["lakes"])
    for row in report["lakes"]:
        mods = row["axiom-target-modules"]
        if mods:
            mod_str = "*" if row.get("wildcard") else mods
        elif row["verdict"] == "NOT-APPLICABLE":
            mod_str = "0 declaration (rien a gate par construction)"
        else:
            mod_str = "-"
        if len(mod_str) > 48:
            mod_str = mod_str[:45] + f"... ({len(mods.split(','))} modules)"
        print(f"  {row['verdict']:<14} {row['display-name']:<{name_w}}  {mod_str}")
        for dead in row["dead_modules"]:
            print(f"             ! module introuvable: {dead}")
    if counts.get("WIRED-DEAD"):
        print("\nWIRED-DEAD : un module nomme n'existe pas sous le chemin du lake —")
        print("le vert du gate n'atteint pas ce module (cf #8782). Corriger la cle.")
    if counts.get("NOT-APPLICABLE"):
        print("\nNOT-APPLICABLE : le lake ne declare rien d'enumerable (imports +")
        print("`#check` + prose, ou des `example` anonymes). Le cabler ne peut pas")
        print("verdir : le gate echoue sur la non-vacuite (« the gate inspected")
        print("nothing »). Ne pas le compter comme un cable manquant.")
    if args.require_covered and counts.get("BARE"):
        print(f"\nFAIL: {counts['BARE']} lake(s) BARE (cablage #18038 non termine)")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
