#!/usr/bin/env python3
"""Mesure des trous de numérotation des séries de notebooks (issue #26707, tranche 0).

Le mainteneur a constaté le 15/11 que la numérotation des séries est « pleine de
trous » : des sous-séries descendent sans qu'un carnet récapitulatif (capstone)
reprenne le numéro vacant, et les numéros du haut de la série ne redescendent pas
dans des accrétions. Cet organe rend la mesure reproductible. Pour une racine de
série, il liste :

  - les TROUS : les numéros NUS absents entre 1 et le maximum des numéros nus ;
  - les LETTRES ORPHELINES : un `NNx` (accrétion) dont le `NN` nu n'existe pas.

Deux conventions du corps de #26707 gouvernent la mesure :

  1. Au niveau de la SÉRIE entière. Quand la numérotation continue d'un
     sous-dossier à l'autre (SmartContracts, Planners : `SC-03..06` vivent dans
     `01-Solidity-Foundation`), tous les carnets d'un même préfixe comptent, où
     qu'ils soient sous la racine. L'organe parcourt donc la racine en
     profondeur et regroupe par préfixe.
  2. Les préliminaires `0a`-`0d` sont un choix de structure, pas des trous : le
     `0` n'entre ni dans les trous (range 1..max) ni dans les lettres orphelines.

La mesure est une fonction de la REVISION mesurée (`--base`, défaut
`origin/main`) : la liste des carnets est lue par `git ls-tree`, jamais dans
l'arbre local (convention de `inventory_notebook_names.py`, #23623). Les
artefacts `_output` ne sont pas suivis par git et ne polluent pas la mesure.

La grammaire de nommage est importée du canon partagé
(`naming_canon.parse_name`) — aucune duplication de regex (règle organ-first,
#5081) : `parse_name` livre le préfixe de série, le numéro tel qu'écrit, la
lettre d'accrétion et le suffixe de langue.

Usage:
    # census : le tableau de référence de #26707 (9 racines)
    python scripts/notebook_tools/numbering_holes.py
    # une racine (mode principal, général)
    python scripts/notebook_tools/numbering_holes.py MyIA.AI.Notebooks/GameTheory
    # plusieurs racines, sortie machine
    python scripts/notebook_tools/numbering_holes.py A B C --base origin/main --json
    # préfixe explicite (une seule racine, ex. série à numérotation croisée)
    python scripts/notebook_tools/numbering_holes.py MyIA.AI.Notebooks/SmartContracts --prefix SC
    # contrôles positifs / négatifs sur fixtures synthétiques
    python scripts/notebook_tools/numbering_holes.py --self-test

Sortie : 0 = mesure produite ; 2 = erreur d'invocation ; self-test : 1 si échec.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from collections import Counter

_REPO_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
if _REPO_ROOT not in sys.path:
    sys.path.insert(0, _REPO_ROOT)

try:
    from scripts.notebook_tools.naming_canon import parse_name
except ImportError as e:  # pragma: no cover - garde d'invocation
    sys.stderr.write(
        "error: numbering_holes.py depends on naming_canon.parse_name. "
        "Run from repo root. Original: %s\n" % e)
    sys.exit(2)

# Racines du tableau de référence de #26707 (9 racines pour 8 lignes : PyMC et
# Infer partagent une ligne). C'est le census par défaut quand aucune racine
# n'est passée en argument — c'est lui que « l'organe rend ce tableau ».
REFERENCE_ROOTS = (
    "MyIA.AI.Notebooks/IIT/ICT-Series",
    "MyIA.AI.Notebooks/Search/Part3-Cas-pratiques",
    "MyIA.AI.Notebooks/SymbolicAI/Lean",
    "MyIA.AI.Notebooks/GameTheory",
    "MyIA.AI.Notebooks/RL",
    "MyIA.AI.Notebooks/Probas/DecisionTheory/DecInfer",
    "MyIA.AI.Notebooks/Probas/PyMC",
    "MyIA.AI.Notebooks/Probas/Infer",
    "MyIA.AI.Notebooks/SymbolicAI/Tweety",
)

# Paliers documentés : un numéro nu volontairement ABSENT parce que la série est
# née structurée en accrétions — un « niveau d'enseignement » scindé en plusieurs
# carnets (07a + 07b), pas un emplacement vidé par une descente. Le nu ne figure
# ni dans les trous ni dans les lettres orphelines. Source : note de numérotation
# de #26707 (Tweety, palier 07 = 07a Python + 07b probabiliste + 07ac C#, README
# de série) ; même statut que les conventions SmartContracts/Planners du body.
PALIER_EXCEPTIONS: dict[str, frozenset[int]] = {
    "MyIA.AI.Notebooks/SymbolicAI/Tweety": frozenset({7}),
}

_OUTPUT_SUFFIX = re.compile(r"_output\.ipynb$", re.I)


def _base(path: str) -> str:
    """Basename d'un chemin relatif de repo (séparateur `/` garanti par git)."""
    return path.rsplit("/", 1)[-1]


def _is_output_artifact(path: str) -> bool:
    """Artefact d'exécution Papermill : dossier `_output/` ou suffixe `_output`."""
    if "/_output/" in path or path.startswith("_output/"):
        return True
    return _OUTPUT_SUFFIX.search(_base(path)) is not None


def git_ls_tree_ipynb(ref: str) -> list[str]:
    """Chemins `.ipynb` suivis d'une révision git, artfacts `_output` exclus.

    `-z` : la sortie est séparée par NUL et non échappée — un chemin avec espace
    ou caractère non-ASCII survit intact (même convention que l'inventaire).
    """
    env = dict(os.environ, MSYS_NO_PATHCONV="1")
    r = subprocess.run(
        ["git", "ls-tree", "-r", "-z", "--name-only", ref],
        capture_output=True, text=True, encoding="utf-8", errors="replace", env=env)
    if r.returncode != 0:
        raise RuntimeError(
            "git ls-tree %s -> %s" % (ref, (r.stderr or "").strip()[:200]))
    out = []
    for p in r.stdout.split("\0"):
        p = p.strip()
        if not p or not p.lower().endswith(".ipynb"):
            continue
        if _is_output_artifact(p):
            continue
        out.append(p)
    return out


def measure_paths(paths: list[str], prefix: str | None = None,
                 palier_exceptions: frozenset[int] | None = None) -> dict:
    """Mesure trous + lettres orphelines sur une liste de chemins `.ipynb`.

    `prefix` : préfixe de série à mesurer. Si `None`, c'est le préfixe DOMINANT
    de l'arbre (le plus fréquent, tiré au plus haut nom en cas d'égalité) qui
    est mesuré — c'est ce qui rend la mesure au niveau de la série entière quand
    la numérotation continue d'un sous-dossier à l'autre, sans confondre une
    sous-série de préfixe distinct.

    Retourne un dict : `prefix`, `notebook_count` (tous les carnets), `matched`
    (ceux du préfixe mesuré), `max` (numéro nu max, ou None), `holes`,
    `orphan_letters`.
    """
    names = [parse_name(_base(p)) for p in paths]
    prefix_counts = Counter(n.series for n in names if n.series is not None)
    if prefix is None:
        if not prefix_counts:
            return {"prefix": None, "notebook_count": len(paths), "matched": 0,
                    "max": None, "holes": [], "orphan_letters": []}
        prefix = max(prefix_counts.items(), key=lambda kv: (kv[1], kv[0]))[0]

    bare: set[int] = set()
    letters: set[str] = set()
    matched = 0
    for name in names:
        if name.series != prefix or name.number is None:
            continue
        matched += 1
        n = int(name.number)
        if name.accr is None:
            bare.add(n)
        else:
            letters.add("%d%s" % (n, name.accr.lower()))

    paliers = palier_exceptions if palier_exceptions is not None else frozenset()
    max_num = max(bare) if bare else None
    holes = (sorted(k for k in range(1, max_num + 1)
                    if k not in bare and k not in paliers)
             if max_num is not None else [])
    # Lettres orphelines : `NNx` dont le nu `NN` est absent, à l'exception des
    # préliminaires `0x` (choix de structure) et des paliers documentés (nu
    # volontairement absent, scindé en accrétions — hors mesure).
    orphans = sorted(
        (L for L in letters
         if int(L[:-1]) not in bare and int(L[:-1]) >= 1
         and int(L[:-1]) not in paliers),
        key=lambda L: (int(L[:-1]), L[-1]))
    return {"prefix": prefix, "notebook_count": len(paths), "matched": matched,
            "max": max_num, "holes": holes, "orphan_letters": orphans}


def measure_root(all_ipynb: list[str], root: str,
                 prefix: str | None = None) -> dict:
    """Mesure une racine de série : tous les `.ipynb` sous `root` (en profondeur)."""
    root = root.rstrip("/")
    paths = [p for p in all_ipynb if p == root or p.startswith(root + "/")]
    paliers = PALIER_EXCEPTIONS.get(root, frozenset())
    m = measure_paths(paths, prefix=prefix, palier_exceptions=paliers)
    m["root"] = root
    return m


def compress_runs(nums: list[int]) -> str:
    """`[18, 19, 20, 24, 25, 26]` -> `'18-20, 24-26'` (sortie humaine)."""
    if not nums:
        return ""
    nums = sorted(nums)
    out: list[str] = []
    i = 0
    while i < len(nums):
        j = i
        while j + 1 < len(nums) and nums[j + 1] == nums[j] + 1:
            j += 1
        out.append(str(nums[i]) if i == j else "%d-%d" % (nums[i], nums[j]))
        i = j + 1
    return ", ".join(out)


def _fmt_human(inv: dict) -> str:
    lines = [
        "base=%s  séries=%d  trous=%d  lettres orphelines=%d"
        % (inv["base"], inv["totals"]["series"], inv["totals"]["holes"],
           inv["totals"]["orphan_letters"]),
        "",
        "%-40s %5s  %-28s  %s"
        % ("Série (racine)", "Max", "Trous", "Lettres orphelines"),
    ]
    for s in inv["series"]:
        lines.append("%-40s %5s  %-28s  %s   [préfixe %s, %d/%d]" % (
            s["root"],
            s["max"] if s["max"] is not None else "—",
            compress_runs(s["holes"]) or "—",
            ", ".join(s["orphan_letters"]) or "—",
            s["prefix"], s["matched"], s["notebook_count"]))
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------- self-test
# Fixtures synthétiques : la logique de mesure (parse + trous + orphelines) est
# testée sur des listes de chemins, sans état git. Les contrôles réels
# (GameTheory positif, une racine sans trou) sont joués à la main dans le body
# de PR sur `origin/main` — un self-test qui dépendrait de l'état du dépôt
# casserait dès que les fournées bouchent les trous.
_CASES = [
    # (label, paths, préfixe, max, trous, lettres orphelines)
    ("trous + lettre orpheline",
     ["S/S-01-A-Python.ipynb", "S/S-02-B-Python.ipynb", "S/S-04-C-Python.ipynb",
      "S/S-03c-D-Python.ipynb"],
     "S", 4, [3], ["3c"]),
    ("sans trou (contrôle négatif)",
     ["S/S-01-A-Python.ipynb", "S/S-02-B-Python.ipynb", "S/S-03-C-Python.ipynb"],
     "S", 3, [], []),
    ("préliminaires 0x exclus de la mesure",
     ["S/S-0a-P1.ipynb", "S/S-0b-P2.ipynb", "S/S-01-A-Python.ipynb",
      "S/S-02-B-Python.ipynb"],
     "S", 2, [], []),
    ("jumeau CSharp ne double pas le numéro nu",
     ["S/S-01-A-Python.ipynb", "S/S-01-A-CSharp.ipynb", "S/S-02-B-Python.ipynb"],
     "S", 2, [], []),
    ("numérotation croisée d'un sous-dossier à l'autre",
     ["S/d1/SC-01-A-Python.ipynb", "S/d2/SC-02-B-Python.ipynb",
      "S/d3/SC-04-C-Python.ipynb"],
     "SC", 4, [3], []),
    ("lettre dont le nu existe = pas orpheline",
     ["S/S-01-A-Python.ipynb", "S/S-01b-A2-Python.ipynb", "S/S-02-B-Python.ipynb"],
     "S", 2, [], []),
    ("sans préfixe alphabétique = hors mesure",
     ["S/01-Freeform.ipynb", "S/02-Other.ipynb"],
     None, None, [], []),
]


def self_test() -> int:
    ko = 0
    print("--- numbering_holes self-test (%d cas) ---" % len(_CASES))
    for label, paths, w_prefix, w_max, w_holes, w_orph in _CASES:
        m = measure_paths(paths)
        ok = (m["prefix"] == w_prefix and m["max"] == w_max
              and m["holes"] == w_holes and m["orphan_letters"] == w_orph)
        if not ok:
            ko += 1
        print("  %s %-40s -> préfixe=%s max=%s trous=%s orphelines=%s"
              % ("OK " if ok else "KO ", label, m["prefix"], m["max"],
                 m["holes"], m["orphan_letters"]))
    # Palier documenté : un nu volontairement absent (scindé en accrétions
    # 07a/07b, le nu n'a jamais existé) est hors mesure — ni trou 7, ni 07a/07b.
    m = measure_paths(
        ["T/T-07a-C-Python.ipynb", "T/T-07b-D-Python.ipynb",
         "T/T-01-A-Python.ipynb", "T/T-08-E-Python.ipynb"],
        palier_exceptions=frozenset({7}))
    ok = (7 not in m["holes"]) and m["orphan_letters"] == []
    if not ok:
        ko += 1
    print("  %s palier 07 (07a/07b, nu absent) exclu  -> trous=%s "
          "orphelines=%s" % ("OK " if ok else "KO ", m["holes"],
                             m["orphan_letters"]))
    # compress_runs : les plages consécutives sont repliées.
    for nums, want in [([18, 19, 20, 24, 25, 26], "18-20, 24-26"),
                       ([2], "2"), ([], ""), ([41, 44, 45], "41, 44-45")]:
        got = compress_runs(nums)
        ok = got == want
        if not ok:
            ko += 1
        print("  %s compress_runs(%s) -> %s (attendu %s)"
              % ("OK " if ok else "KO ", nums, got, want))
    print("")
    print("%s : %d cas, %d échec(s)" % ("ECHEC" if ko else "SUCCES",
                                        len(_CASES) + 5, ko))
    return 1 if ko else 0


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Mesure des trous de numérotation des séries "
                    "(organe #26707, tranche 0). Lecture seule, base git.")
    ap.add_argument("roots", nargs="*",
                    help="racines de série à mesurer (défaut : le tableau de "
                         "référence de #26707)")
    ap.add_argument("--base", default="origin/main",
                    help="révision mesurée (défaut origin/main)")
    ap.add_argument("--prefix", default=None,
                    help="préfixe de série explicite (exactement une racine)")
    ap.add_argument("--json", action="store_true",
                    help="sortie JSON machine (défaut : humain)")
    ap.add_argument("--self-test", action="store_true",
                    help="contrôles positifs/négatifs sur fixtures synthétiques")
    a = ap.parse_args()

    if a.self_test:
        return self_test()
    if a.prefix is not None and len(a.roots) != 1:
        ap.error("--prefix n'est valable qu'avec exactement une racine")

    roots = a.roots if a.roots else list(REFERENCE_ROOTS)
    all_ipynb = git_ls_tree_ipynb(a.base)
    series = [measure_root(all_ipynb, r, a.prefix) for r in roots]
    inv = {
        "base": a.base,
        "series": series,
        "totals": {
            "series": len(series),
            "holes": sum(len(s["holes"]) for s in series),
            "orphan_letters": sum(len(s["orphan_letters"]) for s in series),
            "series_with_holes": sum(1 for s in series if s["holes"]),
        },
    }
    if a.json:
        # RFC 8259 : le JSON est de l'UTF-8, même sous Windows (page de code
        # locale cp1252 sur stdout ; cf inventaire_notebook_names).
        if hasattr(sys.stdout, "reconfigure"):
            sys.stdout.reconfigure(encoding="utf-8")
        sys.stdout.write(json.dumps(inv, indent=2, sort_keys=True,
                                    ensure_ascii=False) + "\n")
    else:
        sys.stdout.write(_fmt_human(inv))
    return 0


if __name__ == "__main__":
    sys.exit(main())
