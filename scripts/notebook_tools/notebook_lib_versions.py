#!/usr/bin/env python3
"""Recensement des versions de bibliotheques chargees par les carnets (#23073).

Le depot epingle des versions tierces a deux endroits qui ne se parlent pas : les
directives `#r "nuget: X, v"` des cellules C#/.NET Interactive, et les `pip install
x==v` des cellules Python. Rien ne compare ces litteraux a une reference commune,
donc une re-execution peut charger une autre version qu'une autre re-execution du
meme corpus, et une rupture d'API apparait carnet par carnet, des mois plus tard.

Cet organe est l'instrument de MESURE de l'issue #23073 (exigences 1 et 3) :

  - il lit `lib_version_manifest.json`, qui porte les versions canoniques et les
    ecarts arbitres (avec motif ecrit) ;
  - il recense, dans les cellules de CODE des carnets suivis, chaque litteral de
    version et l'attribue a son carnet et a sa cellule ;
  - il classe chaque site : OK (canonique), CONVERGE (ecart non arbitre), ALLOWED
    (ecart arbitre au manifeste), NO_CANONICAL (manifeste sans canonique fixee --
    arbitrage non tranche), UNKNOWN (paquet absent du manifeste),
    CANONICAL_UNRESOLVED (la source pointee par `canonical_from` n'a pas pu etre
    lue ou n'a pas matche) ;
  - il imprime la table de dispersion : par paquet, les versions rencontrees avec
    leur nombre de carnets.

Ce n'est PAS le garde de PR : il sort en 0 par defaut, y compris quand des ecarts
existent. `--strict` rend 1 s'il reste au moins un CONVERGE, ce qui donne au futur
cablage (exigence 2) son point d'appui sans l'activer aujourd'hui.

Portee : les carnets SUIVIS par git (`git ls-files '*.ipynb'`), `_archive/` compris
-- le carnet archive `SymbolicAI/_archive/Tweety.ipynb` est justement le cas
declencheur de l'issue, l'exclure rendrait l'organe aveugle a son propre motif.
Les artefacts generes (`_output.ipynb`, `.ipynb_checkpoints`) ne sont pas suivis et
n'entrent donc jamais dans le recensement.

Deux limites assumees, et il faut les lire avant de conclure sur un chiffre :

  - **Le recensement compte des litteraux, pas des chargements effectifs.** Une
    directive dans une cellule non executee compte comme un site. C'est voulu : le
    site existe dans la source committee et tombera a la prochaine execution.
  - **Il ne distingue pas une derive d'un epinglage justifie.** C'est le role de
    l'allowlist du manifeste, et d'elle seule : un ecart sans motif ecrit reste
    CONVERGE, meme s'il est legitime.

Usage:
    python scripts/notebook_tools/notebook_lib_versions.py
    python scripts/notebook_tools/notebook_lib_versions.py --json
    python scripts/notebook_tools/notebook_lib_versions.py --only-dispersed
    python scripts/notebook_tools/notebook_lib_versions.py --strict
    python scripts/notebook_tools/notebook_lib_versions.py --paths "MyIA.AI.Notebooks/SymbolicAI/**/*.ipynb"

Sortie: 0 = recensement fait (meme avec des ecarts) ; 1 = `--strict` et au moins un
CONVERGE ; 2 = incident d'entree (manifeste illisible ou invalide).
"""

from __future__ import annotations

import argparse
import collections
import dataclasses
import fnmatch
import glob
import json
import pathlib
import re
import subprocess
import sys

REPO_ROOT = pathlib.Path(__file__).resolve().parents[2]
DEFAULT_MANIFEST = pathlib.Path(__file__).resolve().parent / "lib_version_manifest.json"

# `#r "nuget: Package, 1.2.3"` -- la virgule et la version sont optionnelles dans
# certaines formes, mais un `#r` sans version n'est pas un litteral a comparer : on
# l'ignore plutot que d'inventer une version.
_NUGET_RE = re.compile(
    r'#r\s+["\']nuget:\s*(?P<pkg>[A-Za-z0-9_.\-]+)\s*,\s*(?P<ver>[0-9][^"\'\s,]*)',
    re.IGNORECASE,
)
# `pip install`, `!pip install`, `%pip install`, `python -m pip install`
_PIP_CMD_RE = re.compile(r"(?:^|[\s!%])pip3?\s+install\s+(?P<args>[^\n\"'\\]+)")
_PIP_PIN_RE = re.compile(r"(?P<pkg>[A-Za-z0-9_.\-]+)==(?P<ver>[0-9][A-Za-z0-9_.\-]*)")
# Tweety se provisionne par URL de build ou par coordonnee Maven ; seule l'URL porte
# une version compacte et stable dans le corpus.
_TWEETY_URL_RE = re.compile(r"tweetyproject\.org/builds/(?P<ver>[0-9][^/\s\"'\\]*)")

ECOSYSTEM_PIP = "pip"
ECOSYSTEM_NUGET = "nuget"
ECOSYSTEM_TWEETY = "tweety"


@dataclasses.dataclass(frozen=True)
class Pin:
    """Un litteral de version rencontre dans une cellule de code."""

    package: str
    version: str
    ecosystem: str
    notebook: str
    cell: int
    snippet: str

    def as_dict(self) -> dict:
        return dataclasses.asdict(self)


def iter_notebooks(patterns: list[str] | None = None, repo_root: pathlib.Path = REPO_ROOT) -> list[pathlib.Path]:
    """Carnets a recenser : ceux suivis par git, ou les motifs fournis.

    Le corpus par defaut vient de `git ls-files` et non d'un `glob` : un glob
    ramasserait les artefacts non suivis (`*_output.ipynb`, environnements locaux)
    et le chiffre ne decrirait plus ce qui est committe.
    """
    if patterns:
        found: set[pathlib.Path] = set()
        for pattern in patterns:
            # `Path.glob` refuse un motif absolu ; le module `glob` accepte les deux
            # formes, ce qui laisse l'appelant passer un chemin relatif au depot
            # (usage courant) ou un chemin absolu (tests, scripts de serie).
            raw = pattern if pathlib.Path(pattern).is_absolute() else str(repo_root / pattern)
            found.update(pathlib.Path(p) for p in glob.glob(raw, recursive=True) if p.endswith(".ipynb"))
        return sorted(p for p in found if ".ipynb_checkpoints" not in p.parts)
    try:
        out = subprocess.run(
            ["git", "-C", str(repo_root), "ls-files", "-z", "*.ipynb"],
            capture_output=True,
            check=True,
        ).stdout
    except (subprocess.CalledProcessError, FileNotFoundError):
        return sorted(repo_root.glob("**/*.ipynb"))
    names = [n for n in out.decode("utf-8", "replace").split("\0") if n]
    return sorted(repo_root / n for n in names)


def _code_cells(doc: dict):
    """(index, source) des cellules de code, index comptes sur TOUTES les cellules."""
    for i, cell in enumerate(doc.get("cells") or []):
        if cell.get("cell_type") != "code":
            continue
        yield i, "".join(cell.get("source") or [])


def scan_notebook(path: pathlib.Path, repo_root: pathlib.Path = REPO_ROOT) -> list[Pin]:
    """Litteraux de version d'un carnet. Un carnet illisible ne fait pas echouer le scan."""
    try:
        doc = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return []
    try:
        rel = path.resolve().relative_to(repo_root.resolve()).as_posix()
    except ValueError:
        rel = path.as_posix()
    pins: list[Pin] = []
    for idx, src in _code_cells(doc):
        for m in _NUGET_RE.finditer(src):
            pins.append(Pin(m.group("pkg"), m.group("ver"), ECOSYSTEM_NUGET, rel, idx, _snippet(src, m.start())))
        for cmd in _PIP_CMD_RE.finditer(src):
            for m in _PIP_PIN_RE.finditer(cmd.group("args")):
                pins.append(Pin(m.group("pkg"), m.group("ver"), ECOSYSTEM_PIP, rel, idx, _snippet(src, cmd.start())))
        for m in _TWEETY_URL_RE.finditer(src):
            pins.append(Pin("Tweety", m.group("ver"), ECOSYSTEM_TWEETY, rel, idx, _snippet(src, m.start())))
    return pins


def _snippet(src: str, pos: int, width: int = 90) -> str:
    """La ligne porteuse du litteral, bornee : de quoi juger sans relire le carnet."""
    start = src.rfind("\n", 0, pos) + 1
    end = src.find("\n", pos)
    line = src[start : end if end != -1 else len(src)].strip()
    return line[:width]


def load_manifest(path: pathlib.Path) -> dict:
    doc = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(doc, dict) or not isinstance(doc.get("libraries"), dict):
        raise ValueError(f"manifeste invalide : {path} (cle 'libraries' absente)")
    return doc


def resolve_canonical(entry: dict, repo_root: pathlib.Path = REPO_ROOT) -> tuple[str | None, str | None]:
    """(version canonique, motif d'echec). `canonical_from` pointe l'organe de serie.

    Une entree sans canonique (`canonical: null`) n'est PAS un echec : c'est un
    arbitrage non tranche, que `classify` rend `NO_CANONICAL`. L'echec est reserve a
    une source pointee qui ne se lit pas ou ne matche pas.
    """
    cf = entry.get("canonical_from")
    if isinstance(cf, dict):
        target = repo_root / cf.get("file", "")
        try:
            text = target.read_text(encoding="utf-8")
        except OSError:
            return None, f"source introuvable : {cf.get('file')}"
        m = re.search(cf.get("regex", ""), text)
        if not m:
            return None, f"regex sans correspondance dans {cf.get('file')}"
        return (m.group(1) if m.groups() else m.group(0)), None
    canonical = entry.get("canonical")
    if canonical is None:
        return None, None
    return str(canonical), None


def _allowlisted(manifest: dict, pin: Pin) -> dict | None:
    for entry in manifest.get("allowlist") or []:
        if entry.get("package") != pin.package or str(entry.get("version")) != pin.version:
            continue
        scope = entry.get("notebooks")
        if not scope or any(fnmatch.fnmatch(pin.notebook, pat) for pat in scope):
            return entry
    return None


def classify(pins: list[Pin], manifest: dict, repo_root: pathlib.Path = REPO_ROOT) -> dict:
    """Classe chaque site contre le manifeste et agrege la dispersion."""
    libraries = manifest.get("libraries") or {}
    canon: dict[str, tuple[str | None, str | None]] = {name: resolve_canonical(e, repo_root) for name, e in libraries.items()}
    sites: list[dict] = []
    dispersion: dict[str, dict[str, set[str]]] = collections.defaultdict(lambda: collections.defaultdict(set))
    for pin in pins:
        dispersion[pin.package][pin.version].add(pin.notebook)
        if pin.package not in libraries:
            klass, note = "UNKNOWN", "paquet absent du manifeste"
        else:
            canonical, failure = canon[pin.package]
            if failure:
                klass, note = "CANONICAL_UNRESOLVED", failure
            elif canonical is None:
                klass, note = "NO_CANONICAL", libraries[pin.package].get("basis", "aucune canonique fixee")
            elif pin.version == canonical:
                klass, note = "OK", ""
            else:
                allowed = _allowlisted(manifest, pin)
                if allowed:
                    klass, note = "ALLOWED", allowed.get("reason", "")
                else:
                    klass, note = "CONVERGE", f"canonique {canonical}"
        row = pin.as_dict()
        row["class"] = klass
        row["note"] = note
        sites.append(row)
    classes = collections.Counter(s["class"] for s in sites)
    dispersed = {pkg: {v: len(nbs) for v, nbs in sorted(vers.items())} for pkg, vers in dispersion.items() if len(vers) > 1}
    return {
        "pins": sites,
        "classes": dict(classes),
        "dispersion": dispersed,
        "canonical": {name: {"version": v, "problem": p} for name, (v, p) in canon.items()},
    }


def render_text(result: dict, notebooks: int, shown: int, only_dispersed: bool = False) -> str:
    lines: list[str] = []
    add = lines.append
    add(f"Carnets recenses : {notebooks} (suivis par git)")
    add(f"Litteraux de version : {len(result['pins'])}")
    add("Classes : " + ", ".join(f"{k}={v}" for k, v in sorted(result["classes"].items())))
    add("")
    add("== Dispersion : paquets charges sous plusieurs versions ==")
    if not result["dispersion"]:
        add("  (aucune)")
    for pkg, vers in sorted(result["dispersion"].items()):
        if pkg not in result["canonical"]:
            add(f"  {pkg:<44} " + " · ".join(f"{v} ({n} carnet{'s' if n > 1 else ''})" for v, n in vers.items()))
            add(f"  {'':<44} canonique : aucune -- paquet absent du manifeste")
            continue
        canon = result["canonical"][pkg]
        label = canon["version"] or "A ARBITRER"
        detail = " · ".join(f"{v} ({n} carnet{'s' if n > 1 else ''})" for v, n in vers.items())
        add(f"  {pkg:<44} {detail}")
        add(f"  {'':<44} canonique : {label}" + (f" -- {canon['problem']}" if canon.get("problem") else ""))
    if only_dispersed:
        return "\n".join(lines)
    add("")
    add("== Sites a traiter (CONVERGE / UNKNOWN / CANONICAL_UNRESOLVED) ==")
    todo = [s for s in result["pins"] if s["class"] in {"CONVERGE", "UNKNOWN", "CANONICAL_UNRESOLVED"}]
    if not todo:
        add("  (aucun)")
    for s in todo[:shown]:
        add(f"  [{s['class']}] {s['package']} {s['version']} -- {s['notebook']} c.{s['cell']}")
        add(f"      {s['snippet']}")
        if s["note"]:
            add(f"      ({s['note']})")
    if len(todo) > shown:
        add(f"  ... {len(todo) - shown} autre(s) site(s), voir --json ou --shown 0")
    allowed = [s for s in result["pins"] if s["class"] == "ALLOWED"]
    if allowed:
        add("")
        add("== Ecarts arbitres (allowlist) ==")
        for s in allowed:
            add(f"  {s['package']} {s['version']} -- {s['notebook']} c.{s['cell']}")
    arbitrate = {n: c for n, c in result["canonical"].items() if c["version"] is None and not c["problem"]}
    if arbitrate:
        add("")
        add("== Canoniques a arbitrer (aucune version fixee au manifeste) ==")
        for name in sorted(arbitrate):
            add(f"  {name}")
    unresolved = {n: c for n, c in result["canonical"].items() if c["problem"]}
    if unresolved:
        add("")
        add("== Canoniques non resolues (source pointee illisible) ==")
        for name, c in unresolved.items():
            add(f"  {name} : {c['problem']}")
    return "\n".join(lines)


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--manifest", type=pathlib.Path, default=DEFAULT_MANIFEST)
    p.add_argument("--paths", action="append", metavar="GLOB", help="motif(s) de carnets ; defaut = carnets suivis par git")
    p.add_argument("--json", action="store_true", help="sortie machine")
    p.add_argument("--only-dispersed", action="store_true", help="ne rendre que les paquets a plusieurs versions")
    p.add_argument("--shown", type=int, default=25, help="nombre de sites a traiter affiches (defaut 25 ; 0 = tous)")
    p.add_argument("--strict", action="store_true", help="rc=1 s'il reste au moins un CONVERGE")
    return p


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        manifest = load_manifest(args.manifest)
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        print(f"ERREUR manifeste : {exc}", file=sys.stderr)
        return 2
    notebooks = iter_notebooks(args.paths)
    pins: list[Pin] = []
    for nb in notebooks:
        pins.extend(scan_notebook(nb))
    result = classify(pins, manifest)
    result["notebooks"] = len(notebooks)
    if args.json:
        print(json.dumps(result, indent=2, ensure_ascii=False, sort_keys=True))
    else:
        print(render_text(result, len(notebooks), args.shown if args.shown > 0 else len(result["pins"]), args.only_dispersed))
    if args.strict and result["classes"].get("CONVERGE"):
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())