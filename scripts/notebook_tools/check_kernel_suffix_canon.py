#!/usr/bin/env python3
"""Garde de casse canonique des suffixes de noyau (#15489, defaut 3).

Origine -- W0 de #5081/#11840, point 3 de #15489 :

    "Aucun garde dedie n'impose la casse canonique `Python` / `CSharp` / `Lean`
     apres adoption d'une serie."

La tranche precedente (#15503) a livre le parseur partage `naming_canon.py` en
declarant explicitement hors de sa portee "la casse canonique des suffixes de
langue" : un module qui lit un nom sans lire sa casse ne peut pas fermer ce
defaut, et il l'ecrit lui-meme pour ne pas passer pour le canon entier. C'est ce
trou que ce fichier ferme.

CE QUE CE GARDE MESURE
----------------------
Sur les seuls notebooks AJOUTES par la revision, deux choses :

1. **Casse du suffixe** -- un nouvel `-python` au lieu de `-Python`, `-csharp` au
   lieu de `-CSharp`, porte une casse hors canon. Un `-Csharp` dans une serie
   qui n'a PAS adopte la casse canonique ne rougit pas : la mesure de l'arbre
   donne 114 `-Csharp` contre 16 `-CSharp`, et imposer la regle a une serie qui
   n'a pas tranche fabrique du rouge sans defaut -- lecon du garde de zero-pad
   (#12586). L'adoption est une **liste explicite** (`kernel_suffix_canon.json`),
   jamais une deduction.

2. **Coherence suffixe <-> noyau reel** -- le suffixe dit quel moteur execute le
   notebook, et il peut mentir. Mesure : `GenAI/SemanticKernel/
   Workbook-Template-Python.ipynb` porte `-Python` et un kernelspec `.net-csharp`.
   Deux lecteurs du meme nom (le fichier, le metadata) se contredisent, et rien
   ne le signalait. Ce defaut la est independant de toute adoption.

CE QU'IL NE MESURE PAS, ET POURQUOI LA LISTE EST COURTE
-------------------------------------------------------
`KERNEL_LANG_SUFFIXES` ne contient que `-csharp` et `-python`, parce que ce sont
les deux seuls suffixes dont la mesure montre qu'ils NOMMENT le noyau :

    -Csharp / -CSharp  130 fichiers  -> 130 x kernelspec `.net-csharp`
    -Python             44 fichiers  -> 41 x `python3`, 2 x `coursia-ml-training`,
                                        1 x `.net-csharp` (le defaut ci-dessus)
    -Lean                4 fichiers  -> 2 x `python3`, 1 x `lean4-wsl`,
                                        1 x `lean4-wsl-perc`

`-Lean` est donc **exclu** : dans ce depot il marque le CONTENU, pas le moteur.
Le pendant reellement Lean d'un notebook porte `-Native`
(`Lean-16d-Conway-Game-of-Life-Lean-Native.ipynb` -> `lean4-wsl`), et 2 des 4
`-Lean` tournent sous `python3`. Declarer `lean` comme famille de noyau
injecterait un faux positif dans une famille de ~50 notebooks -- et un garde qui
crie a tort est un garde qu'on desactive. `-FSharp` est exclu pour une raison
distincte : aucun kernelspec F# n'existe dans l'arbre (17 noyaux distincts,
aucun `fsharp`) et `.net-csharp` est partage par les langages .NET, donc une
famille F# deduite du suffixe produirait un faux positif au premier notebook F#.
Ces deux exclusions sont des decisions mesurees, pas des oublis.

Ce qu'il ne mesure toujours PAS : le contenu, l'index de position (c'est
`check_duplicate_notebook_index.py`), la reservation d'un slot contre les PR
ouvertes (point 4 de #15489), ni la configuration padding par serie (point 5).
Un vert dit "les suffixes des notebooks ajoutes sont coherents", jamais "le
corpus est homogene" -- les 114 `-Csharp` herites restent, deliberement.

PORTEE DELTA
------------
Les fichiers examines sont lus en `--no-renames --diff-filter=A`, comme le garde
de collision d'index : un `git mv X.ipynb X-Csharp.ipynb` introduit un suffixe
non canonique et sort par defaut en `R100`, que `--diff-filter=A` ecarterait. Le
rename est une manoeuvre legitime ; c'est le nom introduit qui est juge. Les
defauts herites ne rougissent donc pas -- c'est ce qui rend l'adoption d'une
serie compatible avec ses fichiers deja non conformes.

Usage
-----
    python scripts/notebook_tools/check_kernel_suffix_canon.py --base origin/main
    python scripts/notebook_tools/check_kernel_suffix_canon.py --base origin/main --json
    python scripts/notebook_tools/check_kernel_suffix_canon.py --scan-all
    python scripts/notebook_tools/check_kernel_suffix_canon.py --self-test

Sortie : 0 = aucun defaut introduit ; 1 = defaut ; 2 = erreur d'invocation.
Le denombrement des fichiers examines et la ventilation par etat sont TOUJOURS
imprimes : "rien trouve" et "rien regarde" ne doivent jamais se confondre.
"""
from __future__ import annotations

import argparse
import fnmatch
import json
import os
import subprocess
import sys
from pathlib import Path

_here = str(Path(__file__).resolve().parent)
if _here not in sys.path:
    sys.path.insert(0, _here)
# La liste des suffixes de noyau vient du canon partage (#5081/#15489) : deux
# lectures du meme nom divergent au premier cas limite, c'est ce que la tranche
# #15503 a corrige. Ce garde lit `KERNEL_LANG_SUFFIXES` au lieu de redefinir
# `("-csharp", "-python")` une troisieme fois.
from naming_canon import KERNEL_LANG_SUFFIXES  # noqa: E402

CONFIG_PATH = Path(__file__).resolve().parent / "kernel_suffix_canon.json"

# Casse canonique par famille, telle que #15489 la nomme (`CSharp` / `Python`).
KERNEL_CANONICAL = {"csharp": "CSharp", "python": "Python"}

# Environnements Python du depot dont le nom ne commence pas par `python`.
# Mesures dans l'arbre, pas supposes : `coursia-ml-training` (27 notebooks),
# `conda-torch` (2), `pyphi` (6), `global-3.13` (1). Le prefixe `python` couvre
# les autres (`python3`, `python3-wsl`, `python3-coursia2`, ...). Un kernelspec
# absent de ces regles n'est pas devine : il tombe en `unknown_kernel`, etat
# VISIBLE, jamais un vert silencieux.
PYTHON_ENV_NAMES = {"coursia-ml-training", "conda-torch", "pyphi", "global-3.13"}


def kernel_family(kernelspec: str | None) -> str | None:
    """Famille de noyau d'un `metadata.kernelspec.name`, ou None si non reconnue.

    Lecture par FAMILLE et non par nom exact : le depot emploie `python3`,
    `python3-wsl`, `python3-coursia2` et `coursia-ml-training` pour le meme
    noyau, et une table fermee de noms exacts rouvrirait le defaut au prochain
    environnement ajoute -- meme piege que la liste de suffixes incomplete.
    """
    if not kernelspec:
        return None
    low = kernelspec.strip().lower().lstrip(".")
    if "csharp" in low:
        return "csharp"
    if low.startswith("lean"):
        return "lean"
    if low.startswith("python") or low in PYTHON_ENV_NAMES:
        return "python"
    return None


def raw_kernel_suffix(stem: str) -> str | None:
    """Suffixe de noyau tel qu'ECRIT (casse d'origine), ou None.

    `naming_canon.lang_of` normalise en minuscules -- c'est ce qu'il faut pour
    apparier deux rendus, et exactement ce qui interdit de juger la casse. On
    relit donc le suffixe brut en s'appuyant sur la MEME liste partagee : la
    grammaire reste au canon, seul le jugement de casse est local.
    """
    low = stem.lower()
    for suf in KERNEL_LANG_SUFFIXES:
        if low.endswith(suf):
            return stem[len(stem) - len(suf):]
    return None


def load_config(path: Path) -> dict:
    """Configuration explicite : series ayant adopte le canon + exceptions."""
    if not path.is_file():
        return {"adopted": [], "exceptions": []}
    with path.open(encoding="utf-8") as fh:
        data = json.load(fh)
    data.setdefault("adopted", [])
    data.setdefault("exceptions", [])
    return data


def glob_match(path: str, pattern: str) -> bool:
    """Motif d'adoption. `.../**` couvre le dossier et toute sa descendance.

    `fnmatch.fnmatchcase` et non `fnmatch.fnmatch` : ce dernier replie la casse
    sous Windows (`normcase`) et pas sous Linux, donc le meme depot rendrait deux
    verdicts selon la machine du runner.
    """
    if not pattern:
        return False
    if pattern.endswith("/**"):
        base = pattern[:-3]
        return path == base or path.startswith(base + "/")
    return fnmatch.fnmatchcase(path, pattern)


def is_adopted(path: str, adopted: list[dict]) -> dict | None:
    for entry in adopted:
        if glob_match(path, entry.get("path_glob", "")):
            return entry
    return None


def find_exception(path: str, exceptions: list[dict]) -> dict | None:
    """Exception declarée, par chemin exact (`path`) ou par motif (`path_glob`).

    Le motif existe pour qu'une convention MINUSCULE assumee par une serie
    entiere (cf la contre-exemple Fort-Boyard de `kernel_suffix_canon.json`) se
    declare en une ligne au lieu d'enumerer ses fichiers un par un.
    """
    for entry in exceptions:
        if entry.get("path") == path:
            return entry
        if entry.get("path_glob") and glob_match(path, entry["path_glob"]):
            return entry
    return None


def read_kernelspec(abs_path: Path) -> tuple[str | None, bool]:
    """(kernelspec.name, metadata_present). Ne leve jamais : un notebook
    illisible ou sans metadata est un etat a part, pas un crash de garde."""
    try:
        with abs_path.open(encoding="utf-8") as fh:
            data = json.load(fh)
    except (OSError, ValueError):
        return None, False
    meta = data.get("metadata")
    if not isinstance(meta, dict):
        return None, False
    ks = meta.get("kernelspec")
    name = ks.get("name") if isinstance(ks, dict) else None
    return (name if isinstance(name, str) else None), True


def classify(path: str, name: str, kernelspec: str | None, meta_present: bool,
             config: dict) -> dict:
    """Etat d'un notebook ajoute. `verdict` = "violation" | "ok" | "info"."""
    stem = name[:-len(".ipynb")] if name.lower().endswith(".ipynb") else name
    raw = raw_kernel_suffix(stem)

    if raw is None:
        # Sans suffixe de noyau il n'y a rien a juger -- ce n'est pas une faute.
        # Les `-Lean` tombent ici, conformement a la mesure (le suffixe y marque
        # le contenu, pas le moteur).
        return {"file": path, "state": "no_kernel_suffix", "verdict": "info"}

    # L'exception est lue APRES la presence d'un suffixe : declarer une exception
    # sur un fichier sans suffixe de noyau n'a pas de sens et ne doit pas creer
    # un etat `exception` trompeur.
    exc = find_exception(path, config.get("exceptions", []))
    if exc is not None:
        return {"file": path, "state": "exception", "verdict": "info",
                "reason": exc.get("reason", "")}

    if not meta_present or kernelspec is None:
        # "rien trouve" != "rien regarde" : sans kernelspec la coherence est
        # INVERIFIABLE, etat distinct et non silencieux.
        return {"file": path, "state": "kernelspec_missing", "verdict": "info"}

    fam = kernel_family(kernelspec)
    if fam is None:
        return {"file": path, "state": "unknown_kernel", "verdict": "info",
                "kernelspec": kernelspec}

    got_case = raw.lstrip("-_")

    # 1. Le suffixe contredit le noyau : defaut factuel, hors adoption. Le
    #    message ne prescrit pas de suffixe (la famille reelle peut n'en avoir
    #    aucun de canonique, cf `-Lean`/`-Native`) : il nomme les deux versions.
    if got_case.lower() != fam:
        return {"file": path, "state": "kernel_mismatch", "verdict": "violation",
                "suffix": raw, "kernelspec": kernelspec}

    # 2. Casse hors canon : defaut seulement dans une serie qui a adopte.
    want = KERNEL_CANONICAL[fam]
    if got_case != want:
        adoption = is_adopted(path, config.get("adopted", []))
        if adoption is not None:
            return {"file": path, "state": "case_deviation",
                    "verdict": "violation", "suffix": raw, "expected": want,
                    "adopted": adoption.get("note", "")}
        return {"file": path, "state": "case_deviation_unadopted",
                "verdict": "info", "suffix": raw, "expected": want}

    return {"file": path, "state": "canonical", "verdict": "ok", "suffix": raw}


# ------------------------------------------------------------------ sources
def _git(args: list[str]) -> str:
    env = dict(os.environ, MSYS_NO_PATHCONV="1")
    r = subprocess.run(["git"] + args, capture_output=True, text=True,
                       encoding="utf-8", errors="replace", env=env)
    if r.returncode != 0:
        raise RuntimeError("git %s -> %s"
                           % (" ".join(args), (r.stderr or "").strip()[:200]))
    return r.stdout


def repo_root() -> Path:
    """Racine du depot JUGE, resolue depuis git (cwd), pas depuis le script.

    Le garde lit le contenu des notebooks qu'il vient d'identifier par `git
    diff` : les deux doivent porter sur le meme arbre. Une racine figee sur
    `__file__` lirait le depot qui heberge le script -- faux des qu'on lance le
    garde depuis un worktree, et impossible a tester sur un depot temporaire.
    """
    try:
        return Path(_git(["rev-parse", "--show-toplevel"]).strip())
    except RuntimeError:
        return Path(__file__).resolve().parents[2]


def added_notebooks(base: str, head: str) -> list[str]:
    """Notebooks AJOUTES, renames repliés en suppressions + additions.

    Meme raison que le garde de collision d'index : `git mv X.ipynb
    X-Csharp.ipynb` introduit le suffixe non canonique et sort en `R` par
    defaut -- une vue qui l'ecarte ne verrait jamais le cas qu'elle doit juger.
    """
    out = _git(["diff", "--no-renames", "--diff-filter=A", "--name-only",
                "%s...%s" % (base, head)])
    return [l.strip() for l in out.splitlines()
            if l.strip().lower().endswith(".ipynb")]


def notebooks_in_tree(root: Path, sub: str = "MyIA.AI.Notebooks") -> list[str]:
    """Notebooks de l'arbre, en chemins relatifs a la racine du depot."""
    base = root / sub
    if not base.is_dir():
        base = root
    return sorted(p.relative_to(root).as_posix()
                  for p in base.rglob("*.ipynb") if p.is_file())


def examine(paths: list[str], config: dict) -> list[dict]:
    root = repo_root()
    out = []
    for rel in paths:
        ks, meta = read_kernelspec(root / rel)
        out.append(classify(rel, os.path.basename(rel), ks, meta, config))
    return out


def _detail(r: dict) -> str:
    if r["state"] == "kernel_mismatch":
        return "  (suffixe %s, noyau %s)" % (r.get("suffix"), r.get("kernelspec"))
    if r["state"] in ("case_deviation", "case_deviation_unadopted"):
        return "  (suffixe %s, casse attendue %s)" % (r.get("suffix"),
                                                     r.get("expected"))
    if r["state"] == "unknown_kernel":
        return "  (noyau %s absent de la table de familles)" % r.get("kernelspec")
    if r["state"] == "exception":
        return "  (%s)" % r.get("reason", "")
    return ""


# ------------------------------------------------------------------ self-test
_SUFFIX_CASES = [
    ("-CSharp", "-CSharp"), ("-Csharp", "-Csharp"), ("-csharp", "-csharp"),
    ("-Python", "-Python"), ("-python", "-python"),
    # Hors canon de noyau : `-Lean` marque le contenu (mesure), `_en` est un
    # sibling i18n (#4980). Les deux doivent ressortir None -- c'est la
    # contre-epreuve des deux exclusions mesurees.
    ("-Lean", None), ("-FSharp", None), ("_en", None), ("-Native", None),
    ("", None),
]
_FAMILY_CASES = [
    (".net-csharp", "csharp"), ("python3", "python"),
    ("python3-wsl", "python"), ("python3-coursia2", "python"),
    ("coursia-ml-training", "python"), ("conda-torch", "python"),
    ("pyphi", "python"), ("global-3.13", "python"),
    ("lean4-wsl", "lean"), ("lean4", "lean"), ("lean4-wsl-perc", "lean"),
    ("", None), (None, None), ("smartcontracts", None),
]


def self_test() -> int:
    ko = 0
    print("--- suffixe brut de noyau (casse preservee) ---")
    for suffix, want in _SUFFIX_CASES:
        stem = "04-Item" + suffix
        got = raw_kernel_suffix(stem)
        ok = got == want
        ko += 0 if ok else 1
        print("  %-4s %-22s -> %-9s (attendu %s)"
              % ("OK" if ok else "KO", stem, got, want))
    print("--- famille de noyau ---")
    for ks, want in _FAMILY_CASES:
        got = kernel_family(ks)
        ok = got == want
        ko += 0 if ok else 1
        print("  %-4s %-24s -> %-9s (attendu %s)"
              % ("OK" if ok else "KO", ks, got, want))
    total = len(_SUFFIX_CASES) + len(_FAMILY_CASES)
    print("")
    print("%s : %d cas, %d echec(s)" % ("ECHEC" if ko else "SUCCES", total, ko))
    return 1 if ko else 0


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(
        description="Refuser un notebook ajoute dont le suffixe de noyau porte "
                    "une casse non canonique (serie adoptee) ou contredit le "
                    "noyau reel (#15489 defaut 3).")
    ap.add_argument("--base", default="origin/main")
    ap.add_argument("--head", default="HEAD")
    ap.add_argument("--config", default=str(CONFIG_PATH),
                    help="configuration d'adoption (defaut : celle livree)")
    ap.add_argument("--scan-all", action="store_true",
                    help="census de tout l'arbre au lieu du delta (mesure de "
                         "baseline ; sort en 1 si l'arbre porte des ecarts, y "
                         "compris herites)")
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--self-test", action="store_true")
    a = ap.parse_args(argv)

    if a.self_test:
        return self_test()

    config = load_config(Path(a.config))

    if a.scan_all:
        paths = notebooks_in_tree(repo_root())
        source = "arbre complet"
    else:
        try:
            paths = added_notebooks(a.base, a.head)
        except RuntimeError as e:
            print("ERREUR git : %s" % e, file=sys.stderr)
            return 2
        source = "%s...%s" % (a.base, a.head)

    results = examine(paths, config)
    violations = [r for r in results if r["verdict"] == "violation"]
    by_state: dict[str, int] = {}
    for r in results:
        by_state[r["state"]] = by_state.get(r["state"], 0) + 1

    if a.json:
        print(json.dumps({
            "source": source,
            "examined": len(results),
            "violations": violations,
            "states": by_state,
            "adopted": config.get("adopted", []),
        }, indent=2, ensure_ascii=False))
        return 1 if violations else 0

    print("notebooks examines : %d   (source %s)" % (len(results), source))
    if not results:
        print("VERDICT: OK -- aucun notebook ajoute, rien a verifier.")
        return 0
    print("etats : " + ", ".join("%s=%d" % kv for kv in sorted(by_state.items())))
    for r in results:
        # `no_kernel_suffix` est l'etat par defaut du corpus (86 %) : le lister
        # noierait les etats qui, eux, demandent un regard. Il reste denombre
        # ci-dessus, donc "rien a juger" ne se confond pas avec "rien regarde".
        if r["verdict"] != "ok" and r["state"] != "no_kernel_suffix":
            print("   [%s] %s%s" % (r["state"], r["file"], _detail(r)))
    if by_state.get("no_kernel_suffix"):
        print("   (no_kernel_suffix : %d fichier(s) sans suffixe de noyau -- "
              "aucun moteur annonce, rien a juger, non listes)"
              % by_state["no_kernel_suffix"])
    if not violations:
        print("VERDICT: OK -- aucun defaut de suffixe sur les notebooks ajoutes.")
        return 0
    print("")
    print("VERDICT: SUFFIXE DE NOYAU NON CONFORME (%d)" % len(violations))
    print("")
    print("Un suffixe de noyau dit quel moteur execute le notebook ; le nom du "
          "fichier et son metadata ne doivent pas se contredire.")
    print("- `case_deviation` : le nom porte la bonne langue, la mauvaise casse "
          "-> un rename suffit.")
    print("- `kernel_mismatch` : le suffixe et le kernelspec divergent -> "
          "verifier quel noyau a REELLEMENT produit les sorties (regle C.2)")
    print("  avant de renommer : corriger le nom sans re-executer fabrique une "
          "preuve d'execution qui ne correspond plus au fichier.")
    return 1


if __name__ == "__main__":
    sys.exit(main())
