#!/usr/bin/env python3
"""measure_autoloaded_harness.py -- mesure la surface de harnais REELLEMENT auto-chargee.

Issue #11554 ("compacter les 195 Ko auto-charges, en mesurant ce qui est
reellement envoye"). Le ticket et son apport de mesure du 2026-08-19 comptent
tous deux `.claude/rules/*.md` en entier. Or CLAUDE.md pose la distinction :

    "Les regles sans frontmatter `paths:` sont auto-chargees [...] Celles qui
     portent un frontmatter `paths:` ne se chargent que si la session touche
     les fichiers vises."

Une regle path-gated ne coute donc RIEN a une session qui ne touche pas ses
chemins. Les additionner au total auto-charge surestime la surface, et surtout
deplace la priorite : `notebook-conventions.md` est le plus gros fichier de
`.claude/rules/` (12 738 o), l'apport du 2026-08-19 le met en tete des cibles
au titre d'un bloc "charge par toutes les lanes" -- or il est path-gated depuis
au moins le 2026-07-08 (plus ancien point mesurable dans ce clone), donc jamais
auto-charge sur toute la fenetre decrite. Compacter la mesure du ticket ne
rendrait pas un octet aux sessions qui ne touchent pas de notebook.

Ce script mesure la bonne quantite, et la mesure au lieu de la relire : un
compte derive a la main se refait faux a chaque PR -- c'est exactement ce qui
est arrive a celui du ticket.

Usage :
    py scripts/audit/measure_autoloaded_harness.py
    py scripts/audit/measure_autoloaded_harness.py --json
    py scripts/audit/measure_autoloaded_harness.py --ref origin/main
    py scripts/audit/measure_autoloaded_harness.py --self-check
    py scripts/audit/measure_autoloaded_harness.py --max-bytes 170000

Exit codes :
    0 -- mesure rendue (et sous le seuil si --max-bytes est passe)
    1 -- --max-bytes depasse
    2 -- mesure impossible : self-check en echec, aucun fichier de regle trouve
         (une mesure vide n'est pas une mesure a zero), ou --ref inatteignable
         (typiquement hors de la greffe d'un clone superficiel)

Aucun workflow CI n'appelle ce script : --max-bytes existe pour cabler le
garde-fou de non-regression demande par #11554, il ne rougit nulle part tant
que personne ne l'a cable.
"""

import argparse
import json
import subprocess
import sys
import tempfile
from pathlib import Path

RULES_GLOB = ".claude/rules/*.md"
PROJECT_ROOT_FILE = "CLAUDE.md"


def is_path_gated(text):
    """Vrai si le fichier porte un frontmatter YAML declarant `paths:`.

    La detection porte sur le BLOC de tete delimite par `---`, pas sur les N
    premieres lignes : un `paths:` cite dans la prose ne gate rien, et un
    frontmatter de plus de cinq lignes gate quand meme. Ce sont les deux faux
    negatifs qu'un `head -5 | grep '^paths:'` produit en silence.
    """
    lines = text.splitlines()
    if not lines or lines[0].strip() != "---":
        return False
    for line in lines[1:]:
        if line.strip() == "---":
            return False          # fin du frontmatter, `paths:` absent
        if line.startswith("paths:"):
            return True
    return False                   # frontmatter jamais referme


def _read_worktree(root):
    for p in sorted(root.glob(RULES_GLOB)):
        yield p.name, p.read_text(encoding="utf-8", errors="replace")
    cm = root / PROJECT_ROOT_FILE
    if cm.exists():
        yield PROJECT_ROOT_FILE, cm.read_text(encoding="utf-8", errors="replace")


class RefUnavailable(Exception):
    """Le ref demande n'est pas atteignable (inconnu, ou hors greffe d'un clone
    superficiel). Un clone `--depth N` rend une erreur de ref sur tout ce qui
    precede sa greffe : c'est une LIMITE DE MESURE, a dire comme telle, pas un
    plantage a laisser filer en trace d'exception."""


def _read_ref(root, ref):
    def git(*args):
        return subprocess.run(["git", "-C", str(root), *args],
                              capture_output=True, text=True, check=True).stdout

    try:
        listing = git("ls-tree", "-r", "--name-only", ref, "--", ".claude/rules")
    except subprocess.CalledProcessError as exc:
        raise RefUnavailable(exc.stderr.strip().splitlines()[0]
                             if exc.stderr.strip() else "ref illisible")
    for path in sorted(x for x in listing.splitlines() if x.endswith(".md")):
        yield Path(path).name, git("show", ref + ":" + path)
    try:
        yield PROJECT_ROOT_FILE, git("show", ref + ":" + PROJECT_ROOT_FILE)
    except subprocess.CalledProcessError:
        pass


def measure(root, ref=None):
    auto, gated = [], []
    root_file = None
    reader = _read_ref(root, ref) if ref else _read_worktree(root)
    for name, text in reader:
        size = len(text.encode("utf-8"))
        if name == PROJECT_ROOT_FILE:
            root_file = {"name": name, "bytes": size}
        elif is_path_gated(text):
            gated.append({"name": name, "bytes": size})
        else:
            auto.append({"name": name, "bytes": size})

    auto.sort(key=lambda e: -e["bytes"])
    gated.sort(key=lambda e: -e["bytes"])
    auto_bytes = sum(e["bytes"] for e in auto)
    gated_bytes = sum(e["bytes"] for e in gated)
    root_bytes = root_file["bytes"] if root_file else 0
    return {
        "ref": ref or "(worktree)",
        "autoloaded_rules": auto,
        "path_gated_rules": gated,
        "root_file": root_file,
        "n_autoloaded": len(auto),
        "n_path_gated": len(gated),
        "autoloaded_rules_bytes": auto_bytes,
        "path_gated_rules_bytes": gated_bytes,
        "root_file_bytes": root_bytes,
        "autoloaded_total_bytes": auto_bytes + root_bytes,
        "all_rules_bytes": auto_bytes + gated_bytes,
    }


# --------------------------------------------------------------------------- #
#  Controle : valide par ses FAUX NEGATIFS, jamais par ses hits
# --------------------------------------------------------------------------- #
CONTROL_CASES = [
    ("gate nominal", "---\npaths: a/**/*.ipynb\n---\n\n# X\n", True),
    ("aucun frontmatter", "# X\n\nDu texte.\n", False),
    ("frontmatter sans paths", "---\ndescription: x\n---\n\n# X\n", False),
    # Les deux cas qu'un `head -5 | grep '^paths:'` classe a l'envers :
    ("paths: en PROSE, pas en frontmatter",
     "# X\n\npaths: ceci n'est pas un gate\n", False),
    ("paths: au-dela de la 5e ligne du frontmatter",
     "---\na: 1\nb: 2\nc: 3\nd: 4\ne: 5\npaths: z/**\n---\n\n# X\n", True),
]


def self_check():
    bad = [(label, expected, is_path_gated(text))
           for label, text, expected in CONTROL_CASES
           if is_path_gated(text) != expected]
    for label, expected, got in bad:
        print("  ECHEC  %s : attendu gated=%s, obtenu %s" % (label, expected, got))
    if bad:
        print("self-check : %d/%d cas en echec -- instrument invalide"
              % (len(bad), len(CONTROL_CASES)))
        return 2
    # Le classifieur peut etre juste et la MESURE vide : un repertoire sans
    # regle doit lever, pas rendre "0 octet, tout va bien".
    with tempfile.TemporaryDirectory() as tmp:
        empty = measure(Path(tmp))
    if empty["n_autoloaded"] or empty["n_path_gated"]:
        print("  ECHEC  un repertoire vide rend des regles")
        return 2
    print("self-check : %d/%d cas OK (dont 2 faux negatifs d'un grep naif) ;"
          " mesure vide detectable" % (len(CONTROL_CASES), len(CONTROL_CASES)))
    return 0


def render(m, top):
    print("Harnais auto-charge -- ref %s" % m["ref"])
    print()
    print("  %3d regles auto-chargees   %8d o"
          % (m["n_autoloaded"], m["autoloaded_rules_bytes"]))
    print("  %3d regles path-gated      %8d o   (cout nul hors des chemins vises)"
          % (m["n_path_gated"], m["path_gated_rules_bytes"]))
    if m["root_file"]:
        print("      %-20s   %8d o" % (PROJECT_ROOT_FILE, m["root_file_bytes"]))
    print("      TOTAL AUTO-CHARGE      %8d o" % m["autoloaded_total_bytes"])
    print("      (total brut des rules  %8d o -- la valeur qu'on obtient en"
          " oubliant le gating)" % m["all_rules_bytes"])
    print()
    print("  Top %d auto-charges :" % top)
    for e in m["autoloaded_rules"][:top]:
        print("    %7d o  %s" % (e["bytes"], e["name"]))
    if m["path_gated_rules"]:
        print("  Path-gated (hors total) :")
        for e in m["path_gated_rules"]:
            print("    %7d o  %s" % (e["bytes"], e["name"]))


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--root", default=".", help="racine du depot (defaut : .)")
    ap.add_argument("--ref", help="mesurer un ref git au lieu de l'arbre de travail")
    ap.add_argument("--json", action="store_true", help="sortie JSON")
    ap.add_argument("--json-out", help="ecrire le JSON dans ce fichier")
    ap.add_argument("--top", type=int, default=10, help="taille du palmares (defaut : 10)")
    ap.add_argument("--self-check", action="store_true",
                    help="valider l'instrument et sortir (0 = sain, 2 = invalide)")
    ap.add_argument("--max-bytes", type=int,
                    help="exit 1 si le total auto-charge depasse ce seuil")
    args = ap.parse_args()

    if args.self_check:
        return self_check()

    try:
        m = measure(Path(args.root), args.ref)
    except RefUnavailable as exc:
        print("ref %r inatteignable (%s) -- mesure impossible." % (args.ref, exc),
              file=sys.stderr)
        print("Sur un clone superficiel, tout ce qui precede la greffe est hors"
              " de portee : `git fetch --unshallow` d'abord.", file=sys.stderr)
        return 2
    if not m["n_autoloaded"] and not m["n_path_gated"]:
        sys.stderr.write("aucun fichier de regle sous %s -- mesure impossible,"
                         " pas une mesure a zero\n" % RULES_GLOB)
        return 2

    if args.json_out:
        Path(args.json_out).write_text(
            json.dumps(m, indent=2, ensure_ascii=False), encoding="utf-8")
    if args.json:
        print(json.dumps(m, indent=2, ensure_ascii=False))
    else:
        render(m, args.top)

    if args.max_bytes is not None and m["autoloaded_total_bytes"] > args.max_bytes:
        sys.stderr.write("\nDEPASSEMENT : %d o > seuil %d o\n"
                         % (m["autoloaded_total_bytes"], args.max_bytes))
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
