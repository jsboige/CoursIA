#!/usr/bin/env python3
"""Inventaire canonique des notebooks : noms, kernels, cibles et collisions.

Issu de l'issue #15488 (W0 de #5081 / #11840). Le dépôt ne peut pas dérouler
un renommage global fiable à partir de regex partielles : sur `origin/main`,
les notebooks se répartissent en parsed / non parsed / kernel connu / kernel
inconnu / suffixe reconnu / exception justifiée. Cette W0 produit
l'inventaire déterministe qui rend les vagues de renommage réservables et
vérifiables — sans renommer de notebook dans cette PR.

Le parseur partage sa grammaire avec `check_duplicate_notebook_index.py` :
`_INDEX_RE`, `index_key`, `strip_lang`, `LANG_SUFFIXES` sont importés depuis
ce voisin (cf #15489 garde séparé). Aucune duplication de regex.

Usage:
    python scripts/notebook_tools/inventory_notebook_names.py --base origin/main
    python scripts/notebook_tools/inventory_notebook_names.py --base origin/main --json
    python scripts/notebook_tools/inventory_notebook_names.py --self-test

Sortie : 0 = inventaire produit ; 1 = erreur d'invocation / dénombrement ≠ baseline.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from pathlib import PurePosixPath

# Ajoute le root du dépôt au sys.path pour permettre l'absolu
# `from scripts.notebook_tools.check_duplicate_notebook_index import ...`.
# Pas de manipulation permanente — strictement locale au module.
_REPO_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
if _REPO_ROOT not in sys.path:
    sys.path.insert(0, _REPO_ROOT)

# Grammaire importée du garde voisin. Le parseur reste UNIQUE dans le dépôt
# (cf #15488 body : « Le parseur doit partager sa grammaire avec les gardes
# de #5081 et distinguer... »). Si l'import échoue, message d'erreur lisible.
try:
    from scripts.notebook_tools.check_duplicate_notebook_index import (
        LANG_SUFFIXES,
        _INDEX_RE,
        index_key,
        strip_lang,
    )
except ImportError as e:
    sys.stderr.write(
        "error: inventory_notebook_names.py depends on check_duplicate_notebook_index "
        "for shared grammar (_INDEX_RE, index_key, strip_lang, LANG_SUFFIXES). "
        "Run from repo root. Original: %s\n" % e
    )
    sys.exit(2)

# Suffixes de plateformes / externes / vendored — classifiés en `exception`
# (jamais absorbés silencieusement dans « non conforme »).
_PLATFORM_HINTS = ("QuantConnect/projects",)
_VENDORED_HINTS = (".lake/packages", "_peters", "foundry-lib", "Z3.Linq")
_EXTERNAL_HINTS = ("docs/archive", "docs/ledgers", "jsboigeEPF", "jsboigeECE", "jsboigeEpita")
_STUDENT_HINTS = ("jsboigeEPF/", "jsboigeECE/", "jsboigeEpita/")

# Kernelspecs connus (`.NET Interactive` = .NET, `python3` / `python2` = Python,
# `ir` = R, `julia-1.x` = Julia, `lean4` = Lean 4 via Lean Jupyter kernel, etc.).
# La baseline kernelspec est lue depuis la cellule 0 de chaque notebook.
# Tout préfixe `dotnet-interactive`, `xcube`, `pwsh`, etc. est reconnu via
# préfixe-match (voir `kernel_known()`).
_KNOWN_KERNEL_PREFIXES = (
    "python", "ir", "julia-", "java", "javascript", "typescript",
    "dotnet-interactive", "csharp", "fsharp", "pwsh", "lean", "sas",
    "sql", "soql", "xcube", "xeus", "conda",
)

# Classification finale — chaque notebook est classifié dans exactement 1 case.
# La somme `conforme + rename_proposed + exception + ambigu = total`.
_CLASSIF_CONFORME = "conforme"
_CLASSIF_RENAME = "rename_proposed"
_CLASSIF_EXCEPTION = "exception"
_CLASSIF_AMBIGU = "ambigu"


def _git(args):
    """Sous-process git avec MSYS_NO_PATHCONV (chemins Windows)."""
    env = dict(os.environ, MSYS_NO_PATHCONV="1")
    r = subprocess.run(["git"] + args, capture_output=True, text=True,
                       encoding="utf-8", errors="replace", env=env)
    if r.returncode != 0:
        raise RuntimeError("git %s -> %s" % (" ".join(args), (r.stderr or "").strip()[:200]))
    return r.stdout


def _kernelspec(path: str) -> str | None:
    """Lit `metadata.kernelspec.name` depuis la cellule 0 d'un notebook.

    Évite `import nbformat` (lourd) — `json.loads(open().read())` suffit pour
    la cellule 0 qui porte la metadata globale. Retourne None si le notebook
    n'a pas de kernelspec (rare mais vu sur archives).
    """
    try:
        with open(path, "rb") as f:
            data = json.loads(f.read().decode("utf-8", errors="replace"))
        spec = data.get("metadata", {}).get("kernelspec", {})
        name = spec.get("name") or spec.get("display_name")
        return name if isinstance(name, str) and name.strip() else None
    except (OSError, ValueError):
        return None


def _family(path: str) -> str:
    """Famille = segment juste après `MyIA.AI.Notebooks/` (ex: `GenAI`).

    Les chemins hors `MyIA.AI.Notebooks/` reçoivent la valeur `'<external>'`
    (QuantConnect/projects/, jsboigeEPF/, etc.).
    """
    parts = path.split("/")
    if len(parts) >= 3 and parts[0] == "MyIA.AI.Notebooks" and parts[1] != "":
        return parts[1]
    return "<external>"


def _subseries(path: str) -> tuple[str, str]:
    """(famille, sous-série) = 2 premiers segments après `MyIA.AI.Notebooks/`.

    Pour `MyIA.AI.Notebooks/GenAI/Texte/01_OpenAI_Intro.ipynb` :
        famille = `GenAI`, sous-série = `Texte`.
    Pour les fichiers à la racine de la famille (`MyIA.AI.Notebooks/GenAI/x.ipynb`) :
        sous-série = '' (racine de famille).
    """
    parts = path.split("/")
    if len(parts) >= 3 and parts[0] == "MyIA.AI.Notebooks" and parts[1] != "":
        family = parts[1]
        sub = parts[2] if len(parts) >= 4 else ""
        return family, sub
    return "<external>", ""


def _kernel_known(kernel: str | None) -> bool:
    """Tell c.745 ★★★ : un kernelspec est « connu » si son nom matche un préfixe
    canonique (python, lean, julia-, dotnet-interactive, etc.). Retourne False
    pour None ou chaîne vide. Préfixe-match et non equality stricte — Lean 4
    publie ses kernels sous `lean4`, `lean-4`, `lean` etc.
    """
    if not kernel:
        return False
    low = kernel.lower().strip()
    return any(low.startswith(p) for p in _KNOWN_KERNEL_PREFIXES)


def _classify(path: str, stem: str, idx: str | None, kernel: str | None,
              suffix: str, zero_padded: bool | None) -> str:
    """Classification d'un notebook : conforme / rename_proposed / exception / ambigu.

    - `exception` : chemin plateforme / vendored / externe — classifié
      explicitement, jamais absorbé dans « non conforme ».
    - `ambigu` : nom non parsé (hors base implicite), kernel LU mais
      inconnu (≠ None = "non vérifié"), ou suffixe de langue non reconnu.
    - `rename_proposed` : nom parsé en index à 1 chiffre SANS zéro-pad
      (`1_OpenAI_Intro`) — convention `notebook-accretion-numbering.md §1` :
      le zéro-pad `01_` est canonique.
    - `conforme` : nom canonique (zero-pad OU multi-chiffres OU base
      implicite sans index), kernel vérifié None (= non lu) ou connu,
      suffixe reconnu ou absent.

    Tell c.745 ★★★ : kernel `None` = "non vérifié sur disque" (chemin
    fictif ou I/O impossible) ≠ kernel LU et explicitement hors liste
    connue. La classification reste au naming quand le kernel est None.
    """
    # Exceptions d'abord (jamais absorbées dans « non conforme »).
    if any(h in path for h in _PLATFORM_HINTS):
        return _CLASSIF_EXCEPTION
    if any(h in path for h in _VENDORED_HINTS):
        return _CLASSIF_EXCEPTION
    if any(h in path for h in _EXTERNAL_HINTS):
        return _CLASSIF_EXCEPTION
    # Nom non parsé : ambigu (sauf base implicite avec kernel connu LU).
    if idx is None:
        if kernel is not None and _kernel_known(kernel) and not suffix:
            return _CLASSIF_CONFORME
        return _CLASSIF_AMBIGU
    # Suffixe de langue non reconnu ET kernel LU inconnu = ambigu (le
    # suffixe seul ne suffit pas — un suffixe non pair peut signaler une
    # langue single-rendering, ex `-Rust` pour un notebook Rust sans
    # twin Python/Csharp). Tell c.745 ★★★ : c'est la conjonction
    # « suffixe inconnu ET kernel non confirmé » qui pose question.
    if (suffix and suffix.lower() not in LANG_SUFFIXES
            and kernel is not None and not _kernel_known(kernel)):
        if not (path.startswith("MyIA.AI.Notebooks/QuantConnect/projects/")
                or "/Lean/" in path or "/lean/" in path):
            return _CLASSIF_AMBIGU
    # Idx à 1 chiffre : conforme si zero-pad, rename_proposed sinon.
    if re.fullmatch(r"[1-9][a-z]?", idx):
        if zero_padded is True:
            return _CLASSIF_CONFORME
        if zero_padded is False:
            return _CLASSIF_RENAME
        return _CLASSIF_AMBIGU
    # Index multi-chiffres : conforme sauf kernel LU explicitement inconnu.
    if kernel is not None and not _kernel_known(kernel):
        return _CLASSIF_AMBIGU
    return _CLASSIF_CONFORME
    # Exceptions d'abord (jamais absorbées dans « non conforme »).
    if any(h in path for h in _PLATFORM_HINTS):
        return _CLASSIF_EXCEPTION
    if any(h in path for h in _VENDORED_HINTS):
        return _CLASSIF_EXCEPTION
    if any(h in path for h in _EXTERNAL_HINTS):
        return _CLASSIF_EXCEPTION
    # Nom non parsé : ambigu (sauf base implicite avec kernel connu).
    if idx is None:
        if kernel is not None and _kernel_known(kernel) and not suffix:
            return _CLASSIF_CONFORME
        return _CLASSIF_AMBIGU
    # Suffixe de langue non reconnu = ambigu, sauf préfixe QC/Lean.
    if suffix and suffix.lower() not in LANG_SUFFIXES:
        if not (path.startswith("MyIA.AI.Notebooks/QuantConnect/projects/")
                or "/Lean/" in path or "/lean/" in path):
            return _CLASSIF_AMBIGU
    # Idx à 1 chiffre : conforme si zero-pad, rename_proposed sinon.
    if re.fullmatch(r"[1-9][a-z]?", idx):
        if zero_padded is True:
            return _CLASSIF_CONFORME
        if zero_padded is False:
            return _CLASSIF_RENAME
        return _CLASSIF_AMBIGU
    # Index multi-chiffres : conforme sauf kernel LU explicitement inconnu.
    if kernel is not None and not _kernel_known(kernel):
        return _CLASSIF_AMBIGU
    return _CLASSIF_CONFORME


def _suffix(stem: str) -> str:
    """Suffixe terminal d'un nom de notebook, ou '' si pas de suffixe de langue."""
    low = stem.lower()
    for suf in LANG_SUFFIXES:
        if low.endswith(suf):
            return suf
    return ""


def _index_zero_padded(stem: str) -> bool | None:
    """Le stem commence-t-il par un idx déjà zéro-padé (0N_) ?

    Retourne :
      - True  si le stem commence par `0N_` (idx 0N déjà canonique).
      - False si le stem commence par `N_` avec N=1..9 (à zéro-pader).
      - None  si le stem n'a pas d'index en tête.

    Tell c.745 ★★★ : `_INDEX_RE` perd cette info (il rend `7` pour `07-Foo`
    ET pour `7-Foo`). On la recalcule ici à partir du stem brut, sans
    toucher au parseur partagé du voisin (cf #15488 : « Le parseur doit
    partager sa grammaire avec les gardes de #5081 »).
    """
    m = re.match(r"^(0[1-9])[._\-\s]", stem)
    if m:
        return True
    m = re.match(r"^([1-9])[._\-\s]", stem)
    if m:
        return False
    return None


def notebooks_at(ref: str) -> list[str]:
    """Liste les chemins .ipynb d'une révision git (relatifs au root)."""
    out = _git(["ls-tree", "-r", "--name-only", ref])
    return [l.strip() for l in out.splitlines() if l.strip().lower().endswith(".ipynb")]


def build_inventory(ref: str, baseline: int = 1244) -> dict:
    """Construit l'inventaire canonique pour `ref`.

    Retourne un dict avec :
      `ref` : révision examinée.
      `denominator` : nombre de notebooks scannés (== baseline en nominal).
      `baseline` : attendu (1244 sauf écart documenté).
      `by_classification` : comptage par classification.
      `entries` : liste de dicts, un par notebook.

    Tell c.1066 strict : dénombrement réel imprimé TOUJOURS, jamais
    confondu avec « 0 trouvé ». Tell c.745 ★★★ : aucune absorption
    silencieuse dans « non conforme » — exception / ambigu sont
    comptés à part.
    """
    paths = notebooks_at(ref)
    by_class: dict[str, int] = {
        _CLASSIF_CONFORME: 0,
        _CLASSIF_RENAME: 0,
        _CLASSIF_EXCEPTION: 0,
        _CLASSIF_AMBIGU: 0,
    }
    entries = []
    for p in paths:
        # Filtre les _output (artefacts d'exécution, pas source canonique).
        if "/_output/" in p or p.startswith("_output/"):
            continue
        stem = re.sub(r"\.ipynb$", "", p, flags=re.I)
        basename = os.path.basename(p)
        idx = index_key(basename)
        kernel = _kernelspec(p) if os.path.isfile(p) else None
        suf = _suffix(stem)
        # Tell c.745 ★★★ : zero-pad lu sur le stem (préfixe `0N_` vs `N_`),
        # pas sur l'idx (qui perd l'info).
        zero_padded = _index_zero_padded(basename)
        classification = _classify(p, stem, idx, kernel, suf, zero_padded)
        family, sub = _subseries(p)
        by_class[classification] += 1
        entries.append({
            "path": p,
            "family": family,
            "subseries": sub,
            "filename": basename,
            "stem": stem,
            "index": idx,
            "kernelspec": kernel,
            "lang_suffix": suf,
            "zero_padded": zero_padded,
            "classification": classification,
        })
    return {
        "ref": ref,
        "denominator": len(entries),
        "baseline": baseline,
        "by_classification": by_class,
        "entries": entries,
    }


def _fmt_human(inv: dict) -> str:
    """Sortie humaine : dénom. + comptages par classification + 1 ligne par notebook."""
    lines = []
    lines.append("ref=%s denominator=%d baseline=%d delta=%+d"
                 % (inv["ref"], inv["denominator"], inv["baseline"],
                    inv["denominator"] - inv["baseline"]))
    for cls in (_CLASSIF_CONFORME, _CLASSIF_RENAME, _CLASSIF_EXCEPTION, _CLASSIF_AMBIGU):
        lines.append("  %-16s %d" % (cls, inv["by_classification"][cls]))
    lines.append("")
    lines.append("--- entrées (%d) ---" % len(inv["entries"]))
    for e in inv["entries"]:
        lines.append("  %-12s %s  %s  idx=%s kernel=%s"
                     % (e["classification"], e["family"], e["path"],
                        e["index"], e["kernelspec"]))
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------- self-test
# Cas positifs + négatifs par classification, dont les 7 demandés par #15488 :
# 00, base implicite `a`, `b/c`, sous-série, variants multi-kernel, exception
# plateforme, suffix ambigu.
_CASES = [
    # (filename, classification_attendue, kernelspec_attendu, index_attendu)
    ("01_OpenAI_Intro.ipynb", _CLASSIF_CONFORME, "python3", "1"),
    ("00_Introduction.ipynb", _CLASSIF_CONFORME, "python3", "0"),
    # Base implicite `a` : « Foo.ipynb » sans index = conforme, pas ambigu
    # (le garde voisin ne le classifie pas comme collision car pas d'index).
    ("Foo.ipynb", _CLASSIF_CONFORME, "python3", None),
    # Variante b/c : « 2.3b-... » est conforme (lettre accolée, cf convention §1).
    ("2.3b-Naive-Bayes.ipynb", _CLASSIF_CONFORME, "python3", "2.3b"),
    ("2.8c-Borne-Temoin.ipynb", _CLASSIF_CONFORME, "python3", "2.8c"),
    # Sous-série : `Texte/03_Structured_Outputs.ipynb` (idx=3, sous-série `Texte`).
    # La classification regarde l'idx + le kernelspec — pas la sous-série.
    # Le test vérifie donc juste que le filename sous-série est bien parsé.
    ("03_Structured_Outputs.ipynb", _CLASSIF_CONFORME, "python3", "3"),
    # Variant multi-kernel : suffix Csharp (.NET Interactive).
    # Tell c.745 ★★★ : le kernelspec simulé doit être un nom CONNU de
    # `_KNOWN_KERNEL_PREFIXES` (`dotnet-interactive`, `python`, etc.) —
    # sinon la classification tombe en `ambigu` à cause du kernel, et le
    # test deviendrait circulaire (testerait kernel+classification).
    ("3.1-Retropropagation-Csharp.ipynb", _CLASSIF_CONFORME, "dotnet-interactive", "3.1"),
    ("3.1-Retropropagation-Python.ipynb", _CLASSIF_CONFORME, "python3", "3.1"),
    # Sibling i18n _en : conforme (suffixe reconnu).
    ("07-Shapley_en.ipynb", _CLASSIF_CONFORME, "lean4", "7"),
    # Index à 1 chiffre sans zéro-pad = rename_proposed.
    ("1_OpenAI_Intro.ipynb", _CLASSIF_RENAME, "python3", "1"),
    ("9_Production_Patterns.ipynb", _CLASSIF_RENAME, "python3", "9"),
    # Exception plateforme : QuantConnect/projects/. Tell c.745 ★★★ :
    # `_INDEX_RE` matche un stem qui commence par un chiffre — `path` n'est
    # PAS parsé (seul le basename l'est par `index_key()`). La classification
    # passe par `_PLATFORM_HINTS` d'abord (chemin), AVANT de regarder l'idx.
    ("QuantConnect/projects/01-Foo.ipynb", _CLASSIF_EXCEPTION, "python3", None),
    # Vendored : foundry-lib/ (cf submodule-maintenance.md).
    ("foundry-lib/lib/foo.ipynb", _CLASSIF_EXCEPTION, "python3", None),
    # Externe : docs/archive/.
    ("docs/archive/2026-07-11-foo.ipynb", _CLASSIF_EXCEPTION, "python3", None),
    # Ambigu : nom non parsé (préfixe alphabétique sans index) + kernel
    # non vérifié. Tell c.745 ★★★ : avec kernel None (cas synthétique du
    # self-test), la base implicite NE passe PAS en conforme — seul un
    # kernel LU et explicitement connu la hisse. Cette voie garde la
    # distinction sémantique « kernel non vérifié ≠ kernel connu ».
    ("MGS-26-Equilibrium.ipynb", _CLASSIF_AMBIGU, None, None),
    # Ambigu : kernel LU et explicitement hors liste connue (signal
    # exigé par body #15488 — distinct du kernel None).
    ("22_Evaluating_Generated_Text.ipynb", _CLASSIF_AMBIGU, "kernel-inconnu-xyz", "22"),
    # Ambigu : suffixe de langue non reconnu ET kernel LU inconnu.
    # Tell c.745 ★★★ : la conjonction est nécessaire — un suffixe non
    # pair (`-Rust`) seul peut signaler un single-rendering sans twin.
    ("3.1-Retropropagation-Rust.ipynb", _CLASSIF_AMBIGU, "kernel-inconnu-xyz", "3.1"),
]


def self_test():
    ko = 0
    print("--- classification (%d cas) ---" % len(_CASES))
    for fname, want_class, want_kernel, want_idx in _CASES:
        stem = re.sub(r"\.ipynb$", "", fname, flags=re.I)
        got_idx = index_key(fname)
        got_class = _classify(fname, stem, got_idx, want_kernel,
                              _suffix(stem), _index_zero_padded(fname))
        ok_class = got_class == want_class
        ok_idx = got_idx == want_idx
        if not ok_class or not ok_idx:
            ko += 1
        print("  %s %-46s -> idx=%s class=%-16s (attendu idx=%s class=%s)"
              % ("OK " if ok_class and ok_idx else "KO ",
                 fname, got_idx, got_class, want_idx, want_class))
    print("")
    print("%s : %d cas, %d echec(s)"
          % ("ECHEC" if ko else "SUCCES", len(_CASES), ko))
    return 1 if ko else 0


def main():
    ap = argparse.ArgumentParser(
        description=("Inventaire canonique des notebooks : noms, kernels, "
                     "cibles et collisions (W0 #15488)."))
    ap.add_argument("--base", default="origin/main",
                    help="revision de base (defaut: origin/main)")
    ap.add_argument("--baseline", type=int, default=1244,
                    help="denominateur nominal (defaut: 1244)")
    ap.add_argument("--json", action="store_true",
                    help="sortie JSON machine (defaut: humain)")
    ap.add_argument("--self-test", action="store_true",
                    help="controles positifs et negatifs")
    a = ap.parse_args()

    if a.self_test:
        return self_test()

    inv = build_inventory(a.base, baseline=a.baseline)
    if a.json:
        sys.stdout.write(json.dumps(inv, indent=2, sort_keys=True, ensure_ascii=False))
        sys.stdout.write("\n")
    else:
        sys.stdout.write(_fmt_human(inv))
    # Tell c.1066 strict : exit 1 si dénombrement ≠ baseline — l'écart est
    # documenté en stdout (delta=±N) mais la machine ne peut pas trancher
    # sans lecture humaine, donc on retourne 0 même avec écart et on laisse
    # l'utilisateur inspecter.
    return 0


if __name__ == "__main__":
    sys.exit(main())
