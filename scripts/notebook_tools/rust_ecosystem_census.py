#!/usr/bin/env python3
"""Recensement des bibliothèques en usage, par série.

Organe de l'Epic Rust (#26510), pli 1 (#26513) : « partir du dépôt, pas de
l'écosystème ». Avant de mapper chaque bibliothèque à un crate Rust, on mesure
d'abord quelles bibliothèques les carnets utilisent **vraiment** :

- **Python** : les modules de niveau supérieur importés (`import X`,
  `from X import …`), séparés en stdlib (via `sys.stdlib_module_names`, la liste
  du langage) et tiers (ce qui a un équivalent crate à envisager) ;
- **C#** : les paquets NuGet chargés en cellule par `#r "nuget: Paquet"`.

Comptage **par série** (répertoire de premier niveau sous `MyIA.AI.Notebooks/`)
et **par carnet distinct** : un module compté une fois par carnet, même importé
dans plusieurs cellules. Le corpus est celui des carnets suivis par git, hors
sorties `_output` et jumeaux de traduction `_en` (la même base que l'inventaire
de l'Epic).

Usage :
    python scripts/notebook_tools/rust_ecosystem_census.py            # tout le corpus
    python scripts/notebook_tools/rust_ecosystem_census.py --series Search
    python scripts/notebook_tools/rust_ecosystem_census.py --json
"""

from __future__ import annotations

import argparse
import dataclasses
import datetime as _dt
import json
import re
import subprocess
import sys
import sysconfig
from collections import Counter, defaultdict
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
NOTEBOOKS_ROOT = REPO_ROOT / "MyIA.AI.Notebooks"

# `import X` / `import X as Y` / `import a, b, c` — la liste est coupée par virgule.
_IMPORT_RE = re.compile(r"^\s*import\s+(?P<mods>.+)$")
# `from X import …` / `from X.Y import Z` — la partie avant `import` est le chemin.
_FROM_RE = re.compile(r"^\s*from\s+(?P<path>[A-Za-z_][A-Za-z0-9_.]*)\s+import\b")
# `#r "nuget: Paquet"` — la version est optionnelle : on veut le NOM du paquet,
# pas sa version (ce serait le rôle de notebook_lib_versions.py).
_NUGET_RE = re.compile(r'#r\s+["\']\s*nuget:\s*(?P<pkg>[A-Za-z0-9_.\-]+)', re.IGNORECASE)


def iter_notebooks() -> list[Path]:
    """Carnets suivis par git sous MyIA.AI.Notebooks/, hors _output et _en.

    Le corpus vient de `git ls-files` et non d'un glob : un glob ramasserait les
    artefacts non suivis et le chiffre ne décrirait plus ce qui est commité.
    """
    try:
        out = subprocess.run(
            ["git", "-C", str(REPO_ROOT), "ls-files", "-z", "*.ipynb"],
            capture_output=True,
            check=True,
        ).stdout
    except (subprocess.CalledProcessError, FileNotFoundError):
        return sorted(NOTEBOOKS_ROOT.rglob("*.ipynb"))
    prefix = "MyIA.AI.Notebooks/"
    kept: list[Path] = []
    for n in out.decode("utf-8", "replace").split("\0"):
        if not n.startswith(prefix):
            continue
        base = n.rsplit("/", 1)[-1]
        if base.endswith("_output.ipynb") or base.endswith("_en.ipynb"):
            continue
        kept.append(REPO_ROOT / n)
    return sorted(kept)


def series_of(rel: str) -> str:
    """Série = répertoire de premier niveau sous MyIA.AI.Notebooks/.

    Le chemin est relatif à la racine du dépôt : le préfixe `MyIA.AI.Notebooks/`
    est retiré, sinon TOUTES les séries s'appelleraient `MyIA.AI.Notebooks`.
    """
    parts = rel.split("/")
    parts = parts[1:] if parts and parts[0] == "MyIA.AI.Notebooks" else parts
    return parts[0] if parts else "racine"


def python_imports(source: str) -> set[str]:
    """Modules de niveau supérieur importés par le source Python d'un carnet."""
    mods: set[str] = set()
    for line in source.splitlines():
        s = line.strip()
        if not s or s.startswith("#"):
            continue
        m = _IMPORT_RE.match(s)
        if m:
            for part in m.group("mods").split(","):
                # `import x; <autre>` : on coupe au point-virgule avant de lire
                # le module, sinon `traceback;` reste entier.
                tok = part.strip().split()
                tok = [t for t in tok if t not in (";",)]
                if tok:
                    head = tok[0].rstrip(";").split(".")[0]
                    if head:
                        mods.add(head)
            continue
        m = _FROM_RE.match(s)
        if m:
            mods.add(m.group("path").split(".")[0])
    return mods


def nuget_packages(source: str) -> set[str]:
    return {m.group("pkg") for m in _NUGET_RE.finditer(source)}


def cell_sources(doc: dict):
    for cell in doc.get("cells") or []:
        if cell.get("cell_type") == "code":
            yield "".join(cell.get("source") or [])


# Modules fournis par le noyau lui-meme, et racines de paquets Java exposes par
# jpype (`import org`, `import java`): ils sont dans l'environnement du kernel
# ou du pont JVM, pas dans une dependance Python du carnet. Aucun n'a
# d'equivalent crate a discuter en tant que « bibliotheque Python ».
_KERNEL_PROVIDED = {
    "__main__",
    "IPython",
    "display",
    "google",
    "pydevd",
    "pdb",
    "bdb",
    "cmd",
    "code",
    "codeop",
    "runpy",
    # racines de paquets Java (jpype / Tweety par IKVM)
    "org",
    "java",
}

# Noms de module LOCAUX du depot : les tiges des `.py` ET `.lean` suivis par
# git sous MyIA.AI.Notebooks/. Un import dont la tige est ici est un helper du
# depot (ou un module Lean local genere, ex. `Astar`, `Discrepancy`), pas une
# bibliotheque tierce. Detection STRUCTURELLE, calculee en une passe — jamais
# une liste en dur a maintenir.
def local_module_names() -> set[str]:
    try:
        out = subprocess.run(
            ["git", "-C", str(REPO_ROOT), "ls-files", "-z", "*.py", "*.lean"],
            capture_output=True,
            check=True,
        ).stdout
    except (subprocess.CalledProcessError, FileNotFoundError):
        return set()
    prefix = "MyIA.AI.Notebooks/"
    names: set[str] = set()
    for n in out.decode("utf-8", "replace").split("\0"):
        if not n.startswith(prefix):
            continue
        stem = n.rsplit("/", 1)[-1].rsplit(".", 1)[0]
        if stem:
            names.add(stem)
    return names


# Bibliotheques « etrangeres » connues qui apparaissent dans des cellules Lean
# (carnets Python/Lean mixtes) mais ne sont ni Python ni un crate : on les met
# dans un bac `lean` a part, jamais dans le tiers Python.
_LEAN_FOREIGN = {"Mathlib"}


@dataclasses.dataclass
class SeriesStats:
    third_party: Counter = dataclasses.field(default_factory=Counter)  # module -> carnets
    local: Counter = dataclasses.field(default_factory=Counter)        # helper du depot
    lean: Counter = dataclasses.field(default_factory=Counter)         # import Lean (Mathlib)
    nuget: Counter = dataclasses.field(default_factory=Counter)         # paquet -> carnets
    n_py: int = 0         # carnets portant au moins un import 3e partie
    n_cs: int = 0         # carnets portant au moins un nuget
    n_notebooks: int = 0


def census(notebooks: list[Path], series_filter: str | None = None) -> dict[str, SeriesStats]:
    """Par série : tiers (hors stdlib), helpers locaux, imports Lean, nuget.

    Le comptage est par carnet distinct : un module compté une fois par carnet,
    même importé dans plusieurs cellules.
    """
    stdlib = sys.stdlib_module_names  # liste officielle du langage, pas une copie
    local = local_module_names()      # passe unique, structurelle
    stats: dict[str, SeriesStats] = defaultdict(SeriesStats)
    for nb in notebooks:
        rel = nb.relative_to(REPO_ROOT).as_posix()
        series = series_of(rel)
        if series_filter and series != series_filter:
            continue
        try:
            doc = json.loads(nb.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        st = stats[series]
        st.n_notebooks += 1
        py, cs = set(), set()
        for src in cell_sources(doc):
            py |= python_imports(src)
            cs |= nuget_packages(src)
        third = set()
        for m in py:
            if m in stdlib or m in _KERNEL_PROVIDED:
                continue
            if m in local:
                st.local[m] += 1
            elif m in _LEAN_FOREIGN:
                st.lean[m] += 1
            else:
                third.add(m)
        if third:
            st.n_py += 1
            for m in third:
                st.third_party[m] += 1
        if cs:
            st.n_cs += 1
            for p in cs:
                st.nuget[p] += 1
    return dict(stats)


def _md_table(counter: Counter, limit: int | None = None) -> list[str]:
    rows = counter.most_common(limit)
    out = ["| nom | carnets |", "|---|---:|"]
    out += [f"| `{name}` | {n} |" for name, n in rows]
    return out


def render(stats: dict[str, SeriesStats]) -> str:
    now = _dt.datetime.now(_dt.timezone.utc).strftime("%Y-%m-%d %H:%MZ")
    L: list[str] = []
    L.append(f"_(généré le {now} par `rust_ecosystem_census.py`, corpus git-tracked hors `_output`/`_en`)_")
    L.append("")
    # Synthèse
    L.append("## Synthèse par série")
    L.append("")
    L.append("| Série | Carnets | Py (3e partie) | C# (nuget) | Top Python | Top C# |")
    L.append("|---|---:|---:|---:|---|---|")
    for series in sorted(stats, key=lambda s: -stats[s].n_notebooks):
        st = stats[series]
        top_py = ", ".join(f"`{m}`({n})" for m, n in st.third_party.most_common(3)) or "—"
        top_cs = ", ".join(f"`{p}`({n})" for p, n in st.nuget.most_common(3)) or "—"
        L.append(f"| {series} | {st.n_notebooks} | {st.n_py} | {st.n_cs} | {top_py} | {top_cs} |")
    L.append("")
    # Détail
    L.append("## Détail par série")
    for series in sorted(stats, key=lambda s: -stats[s].n_notebooks):
        st = stats[series]
        L.append("")
        L.append(f"### {series}")
        L.append("")
        L.append(f"**Python — tiers (hors stdlib, hors helpers locaux), {st.n_py} carnets :**")
        L.append("")
        if st.third_party:
            L += _md_table(st.third_party)
        else:
            L.append("_aucun import tiers mesuré_")
        L.append("")
        L.append(f"**C# — nuget, {st.n_cs} carnets :**")
        L.append("")
        if st.nuget:
            L += _md_table(st.nuget)
        else:
            L.append("_aucun nuget mesuré_")
        if st.local or st.lean:
            L.append("")
            L.append(f"_hors tiers — helpers du dépôt : {sum(st.local.values())} · imports Lean : {sum(st.lean.values())}_")
            if st.local:
                L.append("")
                L += _md_table(st.local)
            if st.lean:
                L.append("")
                L += _md_table(st.lean)
    return "\n".join(L)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--series", help="nommer une seule série à recenser")
    ap.add_argument("--json", action="store_true", help="sortie JSON (machine)")
    args = ap.parse_args()

    notebooks = iter_notebooks()
    stats = census(notebooks, args.series)

    if args.json:
        payload = {
            s: {
                "notebooks": st.n_notebooks,
                "notebooks_py": st.n_py,
                "notebooks_cs": st.n_cs,
                "third_party": dict(st.third_party.most_common()),
                "nuget": dict(st.nuget.most_common()),
                "local": dict(st.local.most_common()),
                "lean": dict(st.lean.most_common()),
            }
            for s, st in sorted(stats.items())
        }
        print(json.dumps(payload, ensure_ascii=False, indent=2))
    else:
        print(render(stats))
    return 0


if __name__ == "__main__":
    sys.exit(main())
