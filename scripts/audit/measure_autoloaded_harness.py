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
    py scripts/audit/measure_autoloaded_harness.py --with-machine
    py scripts/audit/measure_autoloaded_harness.py --max-perimeter-bytes 157500

Exit codes :
    0 -- mesure rendue (et sous le seuil si --max-bytes est passe)
    1 -- --max-bytes depasse
    2 -- mesure impossible : self-check en echec, aucun fichier de regle trouve,
         --ref inatteignable, ratio invalide, ou seuil demande alors qu'une
         surface machine manque (une somme partielle ne certifie aucun budget)

Deux nombres, jamais un seul (cf `acceptance_view`) :
  - `autoloaded_total_bytes` -- tout ce qu'une session charge reellement,
    rules globales de `~/.claude/rules/` comprises ;
  - `acceptance.bytes` -- le PERIMETRE de la cible de #15204 (regles du
    depot + CLAUDE.md du depot + MEMORY.md par machine + CLAUDE.md global).
    C'est contre `acceptance.gap_bytes` que la cible se juge.

Contrat du JSON (ce qu'un consommateur peut compter sur) :
  - chaque surface porte `bytes` ET `sha256` (empreinte du contenu) : c'est
    elle qui permet de distinguer une SUPPRESSION d'un renommage ;
  - `missing` liste les surfaces du DEPOT absentes, `machine_surfaces_missing`
    celles de la machine -- une absence se DIT, elle ne se compte pas zero ;
  - `measurement_complete` vaut vrai seulement si aucune surface demandee ne
    manque (depot ET machine) ;
  - `acceptance.certified` vaut faux quand le perimetre n'est pas certifiable
    (surfaces machine absentes ou non demandees) : alors `acceptance.bytes`
    et `acceptance.satisfied` valent `null`, jamais zero ;
  - `ratio_bytes_per_token` est emis par la MESURE : un consommateur ne doit
    pas redoubler la constante (une constante dupliquee derive des que l'une
    des deux change).

Aucun workflow CI n'appelle ce script : --max-bytes existe pour cabler le
garde-fou de non-regression demande par #11554, il ne rougit nulle part tant
que personne ne l'a cable.
"""

import argparse
import hashlib
import json
import math
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

RULES_GLOB = ".claude/rules/*.md"
PROJECT_ROOT_FILE = "CLAUDE.md"

# Octets par token, CALIBRE et non estime : le client affiche le compte de tokens
# de MEMORY.md, le rapport a sa taille en octets donne le ratio du corpus reel
# (francais dense + liens [[...]]). Mesure du 2026-09-08 : 24705 o pour 11,1k
# tokens. A re-calibrer si le corpus change de nature (plus de code, plus
# d'anglais, moins de liens) -- passer --ratio.
DEFAULT_RATIO = 2.25

# Cible d'acceptance de #15204 (mandat user 2026-09-08) : « redescendre en
# dessous de 70 ktokens ». Au ratio calibre de 2,25 o/token, cela fait
# 157 500 octets. La cible porte sur un PERIMETRE de surfaces, pas sur le
# total de tout ce qui est charge : voir `acceptance_view`.
ACCEPTANCE_TARGET_TOKENS = 70000
ACCEPTANCE_TARGET_BYTES = 157500


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
        # encoding explicite (#12811) : sans lui, un hote cp1252 decode les
        # regles -- toutes accentuees -- avec la mauvaise table. Ici l'enjeu
        # n'est pas seulement le crash : `len(text.encode("utf-8"))` d'un texte
        # mal decode rend un AUTRE nombre, donc une mesure --ref fausse et
        # silencieuse.
        return subprocess.run(["git", "-C", str(root), *args],
                              capture_output=True, text=True,
                              encoding="utf-8", errors="replace",
                              check=True).stdout

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


def memory_slug(root):
    """Slug du repertoire de memoire associe a un chemin de projet.

    La convention est MESUREE sur les repertoires reels de la machine (le
    2026-11-28), et non deduite : chaque caractere qui n'est ni
    alphanumerique ni `-` devient `-`, le reste du chemin est conserve tel
    quel (casse comprise).

        C:\\dev\\roo-extensions\\.claude\\worktrees\\wt-13089\\myia-po-2026\\20260831-212600
            -> C--dev-roo-extensions--claude-worktrees-wt-13089-myia-po-2026-20260831-212600
        d:\\Dev\\CoursIA-3
            -> d--Dev-CoursIA-3

    La lettre du lecteur garde la casse **ecrite** : `resolve()` la passe en
    majuscule (`d:` -> `D:`) et produirait un slug introuvable, alors que
    `abspath` la conserve (`d--Dev-CoursIA-3` est le repertoire reel).

    L'ancienne derivation (lettre de lecteur + `--` + NOM DU REPEROIRE
    FINAL) ne couvrait que les projets poses a la racine d'un lecteur : sur
    `d:\\Dev\\CoursIA-3` elle rendait `d--CoursIA-3`, un repertoire qui
    n'existe pas -- la surface `MEMORY.md` etait donc declaree MANQUANTE sur
    tout projet a chemin imbrique, et le budget de #15204 ne pouvait jamais
    etre certifie (le total etait mesure sans la surface machine, sans le
    dire).
    """
    return re.sub(r"[^A-Za-z0-9-]", "-", os.path.abspath(str(root)))


def machine_surfaces(root, memory_file=None):
    """Surfaces auto-chargees qui vivent HORS du depot, sur la machine.

    Trois d'entre elles pesent autant que la moitie des regles du depot et
    n'apparaissent dans aucun ref git : le CLAUDE.md global, les regles globales
    de ~/.claude/rules/, et le MEMORY.md par machine. Les omettre rend un total
    plus petit que ce qu'une session recoit vraiment -- c'est-a-dire un chiffre
    rassurant et faux.

    Rend (entrees, manquants). Une surface introuvable est RENDUE COMME TELLE,
    jamais comptee zero : la doctrine de ce fichier est qu'une mesure vide n'est
    pas une mesure a zero, et elle vaut pour chaque surface prise a part.
    """
    root = Path(root).resolve()
    home = Path(os.path.expanduser("~"))
    entries, missing = [], []

    def take(surface, path):
        if path.is_file():
            text = path.read_text(encoding="utf-8", errors="replace")
            entries.append({
                "surface": surface,
                "name": path.name,
                "path": str(path),
                "bytes": len(text.encode("utf-8")),
                "sha256": _sha(text),
                "gated": is_path_gated(text),
            })
        else:
            missing.append({"surface": surface, "path": str(path)})

    take("CLAUDE.md global", home / ".claude" / "CLAUDE.md")
    rules_dir = home / ".claude" / "rules"
    if rules_dir.is_dir():
        for f in sorted(rules_dir.glob("*.md")):
            take("rule globale", f)
    else:
        missing.append({"surface": "rules globales", "path": str(rules_dir)})

    if memory_file is None:
        # Le repertoire de memoire est nomme d'apres le chemin du PROJET, pas
        # d'apres le worktree courant : mesurer depuis /d/wt<N> chercherait un
        # slug qui n'existe pas. --memory-file leve l'ambiguite.
        memory_file = home / ".claude" / "projects" / memory_slug(root) \
            / "memory" / "MEMORY.md"
    take("MEMORY.md (par machine)", Path(memory_file))

    return entries, missing


def _sha(text):
    """Empreinte du CONTENU d'une surface.

    Elle permet de distinguer une suppression d'un renommage : une regle
    renommee garde son contenu, donc son empreinte. Sans elle, un comparateur
    qui apparie les surfaces par NOM ne peut pas dire « cette surface a
    disparu » de « cette surface a change de nom » -- il voit la meme chose
    dans les deux cas, et le rate dans le second.
    """
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def acceptance_view(auto, root_bytes, machine_included, complete,
                    ratio, target_bytes=ACCEPTANCE_TARGET_BYTES):
    """Perimetre d'acceptance de #15204, et ecart a la cible.

    La cible (70k tokens = 157 500 o au ratio calibre) a ete fixee le
    2026-09-08 sur un perimetre de QUATRE surfaces : les regles auto-chargees
    du depot, le `CLAUDE.md` du depot, le `MEMORY.md` par machine et le
    `CLAUDE.md` global de la machine. Les regles globales de
    `~/.claude/rules/` n'existaient pas ce jour-la : elles sont
    auto-chargees AUJOURD'HUI, mais hors du perimetre de la cible.

    Additionner les deux familles donne un total qui n'est comparable a
    rien : il depasse la cible de 21 190 o (mesure du 2026-11-28) sans
    qu'aucune surface comptee n'appartienne au perimetre. L'organe rend
    donc DEUX nombres distincts, jamais un seul :

      - `bytes` -- le perimetre citable, comparable a la cible ;
      - `excluded_surfaces` -- ce qu'une session charge reellement et qui ne
        compte pas dans la cible.

    Un perimetre non certifiable (surfaces machine absentes, ou option
    machine non demandee) rend `bytes: null` et `satisfied: null` : une
    absence se DIT, elle ne se compte pas zero.
    """
    repo_rules = [e for e in auto if e.get("surface") is None]
    global_claude = [e for e in auto if e.get("surface") == "CLAUDE.md global"]
    memory = [e for e in auto
              if str(e.get("surface", "")).startswith("MEMORY.md")]
    global_rules = [e for e in auto if e.get("surface") == "rule globale"]

    surfaces = [
        {"surface": "regles auto-chargees du depot",
         "bytes": sum(e["bytes"] for e in repo_rules), "n": len(repo_rules)},
        {"surface": "CLAUDE.md du depot",
         "bytes": root_bytes, "n": 1 if root_bytes else 0},
        {"surface": "MEMORY.md (par machine)",
         "bytes": sum(e["bytes"] for e in memory), "n": len(memory)},
        {"surface": "CLAUDE.md global",
         "bytes": sum(e["bytes"] for e in global_claude), "n": len(global_claude)},
    ]
    excluded = [
        {"surface": "regles globales (~/.claude/rules)",
         "bytes": sum(e["bytes"] for e in global_rules),
         "n": len(global_rules),
         "reason": "hors du perimetre de la cible (mesure du 2026-09-08), "
                   "mais auto-chargees a chaque session depuis leur de"},
    ]

    certified = bool(machine_included and complete)
    perimeter = sum(s["bytes"] for s in surfaces) if certified else None
    gap = (perimeter - target_bytes) if perimeter is not None else None
    return {
        "target_bytes": target_bytes,
        "target_tokens": int(target_bytes / ratio),
        "certified": certified,
        "surfaces": surfaces,
        "excluded_surfaces": excluded,
        "bytes": perimeter,
        "tokens_derived": round(perimeter / ratio) if perimeter is not None else None,
        "gap_bytes": gap,
        "gap_tokens_derived": round(gap / ratio) if gap is not None else None,
        "satisfied": (gap <= 0) if gap is not None else None,
    }


def measure(root, ref=None, machine=False, memory_file=None,
            ratio=DEFAULT_RATIO, target_bytes=ACCEPTANCE_TARGET_BYTES):
    auto, gated = [], []
    root_file = None
    reader = _read_ref(root, ref) if ref else _read_worktree(root)
    for name, text in reader:
        size = len(text.encode("utf-8"))
        digest = _sha(text)
        if name == PROJECT_ROOT_FILE:
            root_file = {"name": name, "bytes": size, "sha256": digest}
        elif is_path_gated(text):
            gated.append({"name": name, "bytes": size, "sha256": digest})
        else:
            auto.append({"name": name, "bytes": size, "sha256": digest})

    # Surfaces du DEPOT absentes : elles ne se comptent pas zero (cf
    # machine_surfaces). Un depot dont le CLAUDE.md racine manque, ou dont le
    # repertoire de regles est vide, n'a pas de surface auto-chargee
    # COMPLETE -- la mesure ne certifie alors rien, et le dit au lieu de
    # produire un total trop petit et silencieux.
    missing = []
    if root_file is None:
        missing.append({"surface": "CLAUDE.md racine",
                        "path": str(Path(root) / PROJECT_ROOT_FILE)})
    if not auto and not gated:
        missing.append({"surface": "regles du depot",
                        "path": str(Path(root) / ".claude" / "rules")})

    machine_entries, machine_missing = ([], [])
    if machine:
        machine_entries, machine_missing = machine_surfaces(Path(root), memory_file)
        for e in machine_entries:
            (gated if e["gated"] else auto).append(
                {"name": e["name"], "bytes": e["bytes"], "sha256": e.get("sha256"),
                 "surface": e["surface"]})

    auto.sort(key=lambda e: -e["bytes"])
    gated.sort(key=lambda e: -e["bytes"])
    auto_bytes = sum(e["bytes"] for e in auto)
    gated_bytes = sum(e["bytes"] for e in gated)
    root_bytes = root_file["bytes"] if root_file else 0
    total = auto_bytes + root_bytes
    complete = not missing and not machine_missing
    acceptance = acceptance_view(auto, root_bytes, machine, complete, ratio,
                                 target_bytes)
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
        "autoloaded_total_bytes": total,
        "all_rules_bytes": auto_bytes + gated_bytes,
        "machine_surfaces_included": bool(machine),
        "machine_surfaces": machine_entries,
        "missing": missing,
        "machine_surfaces_missing": machine_missing,
        # Une mesure n'est complete que si TOUTES les surfaces demandees ont
        # ete lues -- celles du depot comme celles de la machine. La voie
        # repo-seule ne demande pas les secondes : elle reste complete.
        "measurement_complete": not missing and not machine_missing,
        # Le perimetre d'acceptance de #15204, distinct du total ci-dessus :
        # voir `acceptance_view`. C'est contre `acceptance.gap_bytes` que la
        # cible de 157 500 o se juge -- pas contre `autoloaded_total_bytes`,
        # qui compte des surfaces que la cible ne compte pas.
        "acceptance": acceptance,
        # Le ratio est emis par la MESURE, pas reecrit chez le consommateur :
        # une constante dupliquee derive des que l'une des deux change.
        "ratio_bytes_per_token": ratio,
        "autoloaded_total_tokens_derived": round(total / ratio),
        "tokens_are_derived_not_tokenized": True,
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


def render(m, top, ratio=DEFAULT_RATIO, budget_tokens=None):
    print("Harnais auto-charge -- ref %s" % m["ref"])
    if m.get("machine_surfaces_included"):
        print("  (surfaces machine incluses : CLAUDE.md global, ~/.claude/rules/,"
              " MEMORY.md -- elles ne vivent dans aucun ref git)")
    for miss in m.get("machine_surfaces_missing") or []:
        print("  MANQUANTE  %-24s %s"
              % (miss["surface"], miss["path"]))
        print("             non comptee -- et PAS comptee zero")
    print()
    print("  %3d regles auto-chargees   %8d o"
          % (m["n_autoloaded"], m["autoloaded_rules_bytes"]))
    print("  %3d regles path-gated      %8d o   (cout nul hors des chemins vises)"
          % (m["n_path_gated"], m["path_gated_rules_bytes"]))
    if m["root_file"]:
        print("      %-20s   %8d o" % (PROJECT_ROOT_FILE, m["root_file_bytes"]))
    total = m["autoloaded_total_bytes"]
    print("      TOTAL AUTO-CHARGE      %8d o   ~%.1fk tokens"
          % (total, total / ratio / 1000))
    print("      tokens DERIVES du ratio %.2f o/tok -- pas produits par un"
          " tokenizer (cf --ratio)" % ratio)
    if budget_tokens is not None:
        if not m.get("measurement_complete", True):
            print("      cible %d tok : NON CERTIFIEE (surface demandee manquante)"
                  % budget_tokens)
        else:
            budget_bytes = int(budget_tokens * ratio)
            delta = total - budget_bytes
            verdict = ("SOUS LA CIBLE de %d o (%.1fk tok de marge)"
                       % (-delta, -delta / ratio / 1000)) if delta <= 0 else (
                      "AU-DESSUS de %d o (%.1fk tok a retirer)"
                      % (delta, delta / ratio / 1000))
            print("      cible %d tok = %d o : %s"
                  % (budget_tokens, budget_bytes, verdict))
    acc = m.get("acceptance") or {}
    if acc:
        print()
        print("  Perimetre d'acceptance #15204 -- cible %d o (~%.1fk tok) :"
              % (acc["target_bytes"], acc["target_bytes"] / ratio / 1000))
        for s in acc["surfaces"]:
            print("      %-32s %8d o" % (s["surface"], s["bytes"]))
        if acc["certified"]:
            print("      %-32s %8d o   ~%.1fk tok"
                  % ("PERIMETRE", acc["bytes"], acc["bytes"] / ratio / 1000))
            gap = acc["gap_bytes"]
            if gap <= 0:
                print("      cible : SOUS LA CIBLE de %d o (%.1fk tok de marge)"
                      % (-gap, -gap / ratio / 1000))
            else:
                print("      cible : AU-DESSUS de %d o (%.1fk tok a retirer)"
                      % (gap, gap / ratio / 1000))
        else:
            print("      %-32s %8s"
                  % ("PERIMETRE", "NON CERTIFIE"))
            print("      (surfaces machine absentes ou non demandees : le"
                  " perimetre ne certifie rien)")
        for s in acc["excluded_surfaces"]:
            print("      hors perimetre, auto-charge : %7d o  %s"
                  % (s["bytes"], s["surface"]))
        print("      reellement charge par une session : %7d o"
              % m["autoloaded_total_bytes"])
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
    ap.add_argument("--with-machine", action="store_true",
                    help="inclure les surfaces machine (CLAUDE.md global,"
                         " ~/.claude/rules/, MEMORY.md). Elles ne vivent dans"
                         " aucun ref git : avec --ref, le total melange alors un"
                         " arbre versionne et l'etat courant de CETTE machine")
    ap.add_argument("--memory-file",
                    help="chemin du MEMORY.md par machine (defaut : deduit du nom"
                         " du projet ; a passer explicitement depuis un worktree,"
                         " dont le nom ne correspond a aucun slug de memoire)")
    ap.add_argument("--ratio", type=float, default=DEFAULT_RATIO,
                    help="octets par token pour la derivation (defaut : %.2f,"
                         " calibre le 2026-09-08)" % DEFAULT_RATIO)
    ap.add_argument("--budget-tokens", type=int,
                    help="exit 1 si le total derive depasse ce budget en tokens"
                         " -- jumeau de --max-bytes, dans l'unite du mandat")
    ap.add_argument("--acceptance-target-tokens", type=int,
                    default=ACCEPTANCE_TARGET_TOKENS,
                    help="cible du perimetre d'acceptance #15204, en tokens"
                         " (defaut : %d -- le mandat user du 2026-09-08)"
                         % ACCEPTANCE_TARGET_TOKENS)
    ap.add_argument("--max-perimeter-bytes", type=int,
                    help="exit 1 si le PERIMETRE d'acceptance depasse ce seuil"
                         " (exit 2 si le perimetre n'est pas certifiable)")
    args = ap.parse_args()

    if args.self_check:
        return self_check()

    if not math.isfinite(args.ratio) or args.ratio <= 0:
        ap.error("--ratio doit etre strictement positif et fini")

    root = Path(args.root).resolve()
    target_bytes = int(args.acceptance_target_tokens * args.ratio)
    try:
        m = measure(root, args.ref, machine=args.with_machine,
                    memory_file=args.memory_file, ratio=args.ratio,
                    target_bytes=target_bytes)
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
        render(m, args.top, args.ratio, args.budget_tokens)

    if ((args.max_bytes is not None or args.budget_tokens is not None)
            and not m["measurement_complete"]):
        sys.stderr.write("\nMESURE INCOMPLETE : seuil/budget non certifie "
                         "car une surface demandee manque\n")
        return 2

    if args.max_bytes is not None and m["autoloaded_total_bytes"] > args.max_bytes:
        sys.stderr.write("\nDEPASSEMENT : %d o > seuil %d o\n"
                         % (m["autoloaded_total_bytes"], args.max_bytes))
        return 1
    if args.budget_tokens is not None:
        budget_bytes = int(args.budget_tokens * args.ratio)
        if m["autoloaded_total_bytes"] > budget_bytes:
            sys.stderr.write("\nDEPASSEMENT : %d o > budget %d tok = %d o\n"
                             % (m["autoloaded_total_bytes"], args.budget_tokens,
                                budget_bytes))
            return 1
    if args.max_perimeter_bytes is not None:
        acc = m["acceptance"]
        if not acc["certified"]:
            sys.stderr.write("\nPERIMETRE NON CERTIFIABLE : aucune surface"
                             " machine lue -- seuil non juge\n")
            return 2
        if acc["bytes"] > args.max_perimeter_bytes:
            sys.stderr.write("\nPERIMETRE AU-DESSUS : %d o > %d o (cible %d o)\n"
                             % (acc["bytes"], args.max_perimeter_bytes,
                                acc["target_bytes"]))
            return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
