#!/usr/bin/env python3
"""Garde single-source du PCM par poches (#20188, critere 2).

Le module canonique ``MultiStrategyPouchesPCM`` vit dans
``MyIA.AI.Notebooks/QuantConnect/projects/SharedPCM/pouches_pcm.py`` et les
projets composites l'importent comme bibliotheque de projet QC (#21134,
#21140). Les copies embarquees de la famille ``MultiStrategyPCM`` qui
restent hors de ce dossier sont des exceptions declarees : le manifeste
``projects/SharedPCM/embedded_copies.json`` porte l'empreinte sha256 du
bloc de classe de chaque copie et son motif. La garde rougit sur :

  UNDECLARED           un fichier porte la famille de classes sans etre au
                       manifeste (nouvelle copie non declaree) ;
  DRIFT                une copie declaree a ete modifiee sans re-declaration
                       -- c'est le coeur du critere 2 : une copie
                       volontairement modifiee DOIT faire rougir la garde ;
  STALE                une entree du manifeste ne correspond plus a aucune
                       copie (fichier supprime ou copie retiree : la
                       declaration se retire dans la meme PR) ;
  CANONICAL_DUPLICATE  la classe canonique ``MultiStrategyPouchesPCM``
                       apparait hors de ``SharedPCM/pouches_pcm.py`` (ni
                       import, ni declaration : le canonique ne se duplique
                       pas) ;
  CANONICAL_LEGACY_MIX le fichier canonique porte aussi une classe legacy
                       de la famille ;
  CANONICAL_MISSING    le module canonique a disparu ou n'a plus sa classe.

Controle positif (``--selftest``) : un arbre synthetique ou une copie
declaree est volontairement modifiee DOIT faire rougir la garde, de meme
qu'une copie nouvelle non declaree. En CI, ``--selftest`` est le
pre-controle (``pre_argv``) de la garde : la garde ne rend son verdict que
si son propre controle positif vient de passer -- un detecteur qui ne
prouve pas qu'il tire est indiscernable d'un detecteur debranche (lecon
#11685/#12817).

Empreinte : sha256 du bloc de classe extrait (ligne ``class`` jusqu'au
prochain element de niveau module pour .py, cloture de cloture de fence
pour .md, cellule entiere pour .ipynb), fins de ligne normalisees LF pour
rester stable entre checkouts CRLF et LF.

Sorties : exit 0 = OK, exit 1 = au moins un finding, exit 2 = erreur.
``--json`` rend un verdict machine ; ``--emit`` imprime les entrees
calculees pour bootstrapper ou rafraichir le manifeste (la recopie dans le
manifeste reste un geste conscient : c'est elle qui documente la
re-declaration apres une modification volontaire).
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
import tempfile
from pathlib import Path, PurePosixPath

REPO_ROOT = Path(__file__).resolve().parents[2]

SCAN_ROOT = "MyIA.AI.Notebooks/QuantConnect"
CANONICAL_REL = "MyIA.AI.Notebooks/QuantConnect/projects/SharedPCM/pouches_pcm.py"
MANIFEST_REL = "MyIA.AI.Notebooks/QuantConnect/projects/SharedPCM/embedded_copies.json"

CANONICAL_CLASS = "MultiStrategyPouchesPCM"
LEGACY_CLASS = "MultiStrategyPCM"

MARKER_RE = re.compile(r"^class MultiStrategy(Pouches)?PCM\b", re.M)
CLASS_NAME_RE = re.compile(r"^class (MultiStrategy(?:Pouches)?PCM)\b", re.M)

SCAN_SUFFIXES = {".py", ".md", ".ipynb"}
SKIP_DIRNAMES = {".git", ".ipynb_checkpoints", "__pycache__", "node_modules"}


def _norm(text: str) -> str:
    """Normalise les fins de ligne (CRLF -> LF) pour une empreinte stable."""
    return text.replace("\r\n", "\n").replace("\r", "\n")


def extract_blocks(text: str, is_ipynb: bool) -> list[tuple[str, str]]:
    """Extrait les blocs de classe de la famille, dans l'ordre d'apparition.

    .ipynb : le bloc est la source jointe de la cellule porteuse (un
    notebook pedagogique presente la classe dans une cellule complete).
    .py    : de la ligne ``class`` au prochain element de niveau module
             (``class ``/``def `` en colonne 0) ou a la fin du fichier.
    .md    : de la ligne ``class`` a la cloture de fence suivante ou a la
             fin du fichier (la copie vit dans un bloc de code clote).
    """
    if is_ipynb:
        blocks: list[tuple[str, str]] = []
        nb = json.loads(text)
        for cell in nb.get("cells", []):
            src = _norm("".join(cell.get("source", [])))
            m = MARKER_RE.search(src)
            if m:
                name = CLASS_NAME_RE.search(src)
                blocks.append((name.group(1) if name else LEGACY_CLASS, src))
        return blocks

    lines = _norm(text).split("\n")
    blocks = []
    i = 0
    while i < len(lines):
        m = CLASS_NAME_RE.match(lines[i])
        if not m:
            i += 1
            continue
        name = m.group(1)
        j = i + 1
        while j < len(lines):
            nxt = lines[j]
            if nxt.startswith("class ") or nxt.startswith("def ") or nxt.startswith("```"):
                break
            j += 1
        block = "\n".join(lines[i:j]).rstrip("\n")
        blocks.append((name, block))
        i = j
    return blocks


def fingerprint(blocks: list[tuple[str, str]]) -> str:
    """Empreinte des blocs concatenes dans l'ordre d'apparition (LF)."""
    joined = "\n\n".join(b for _name, b in blocks)
    return hashlib.sha256(joined.encode("utf-8")).hexdigest()


def iter_scan_files(root: Path):
    base = root / SCAN_ROOT
    if not base.is_dir():
        return
    for p in sorted(base.rglob("*")):
        if not p.is_file():
            continue
        if any(part in SKIP_DIRNAMES for part in p.parts):
            continue
        if p.suffix.lower() in SCAN_SUFFIXES:
            yield p


def check_tree(root: Path) -> dict:
    """Rend le verdict de la garde sur l'arbre passe en racine."""
    findings: list[dict] = []
    canonical_path = root / CANONICAL_REL
    manifest_path = root / MANIFEST_REL

    if not canonical_path.is_file():
        findings.append({
            "type": "CANONICAL_MISSING",
            "path": CANONICAL_REL,
            "detail": "le module canonique est absent",
        })
        manifest: dict = {}
    else:
        blocks = extract_blocks(canonical_path.read_text(encoding="utf-8"),
                                canonical_path.suffix == ".ipynb")
        names = [n for n, _b in blocks]
        if CANONICAL_CLASS not in names:
            findings.append({
                "type": "CANONICAL_MISSING",
                "path": CANONICAL_REL,
                "detail": f"la classe {CANONICAL_CLASS} n'y figure plus "
                          f"(blocs: {names or 'aucun'})",
            })
        if LEGACY_CLASS in names:
            findings.append({
                "type": "CANONICAL_LEGACY_MIX",
                "path": CANONICAL_REL,
                "detail": f"le fichier canonique porte aussi {LEGACY_CLASS}",
            })

    if manifest_path.is_file():
        try:
            manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        except json.JSONDecodeError as exc:
            findings.append({
                "type": "MANIFEST_UNREADABLE",
                "path": MANIFEST_REL,
                "detail": f"JSON invalide: {exc}",
            })
            manifest = {}
    else:
        manifest = {}

    entries = {e["path"]: e for e in manifest.get("copies", [])}

    scanned_legacy: dict[str, str] = {}
    files_scanned = 0
    for path in iter_scan_files(root):
        files_scanned += 1
        rel = Path(path).relative_to(root).as_posix()
        if rel == CANONICAL_REL or rel == MANIFEST_REL:
            continue
        try:
            text = path.read_text(encoding="utf-8")
        except (UnicodeDecodeError, OSError):
            continue
        if "MultiStrategy" not in text:
            continue
        blocks = extract_blocks(text, path.suffix == ".ipynb")
        if not blocks:
            continue
        names = [n for n, _b in blocks]
        if CANONICAL_CLASS in names:
            findings.append({
                "type": "CANONICAL_DUPLICATE",
                "path": rel,
                "detail": f"{CANONICAL_CLASS} hors du fichier canonique "
                          f"(blocs: {names})",
            })
            continue
        scanned_legacy[rel] = fingerprint(blocks)
        if rel not in entries:
            findings.append({
                "type": "UNDECLARED",
                "path": rel,
                "detail": f"copie embarquee {LEGACY_CLASS} non declaree au "
                          f"manifeste ({MANIFEST_REL})",
            })
        elif entries[rel].get("sha256") != scanned_legacy[rel]:
            findings.append({
                "type": "DRIFT",
                "path": rel,
                "detail": "copie declaree modifiee : re-declarer au "
                          "manifeste (sha256 recalcule par --emit) dans la "
                          "meme PR, avec le motif de la modification",
            })

    for rel in sorted(set(entries) - set(scanned_legacy)):
        findings.append({
            "type": "STALE",
            "path": rel,
            "detail": "entree du manifeste sans copie correspondante : "
                      "retirer la declaration dans la meme PR",
        })

    return {
        "status": "FAIL" if findings else "OK",
        "files_scanned": files_scanned,
        "copies_declared": len(entries),
        "copies_seen": len(scanned_legacy),
        "findings": findings,
    }


def emit_entries(root: Path) -> list[dict]:
    """Calcule les entrees de manifeste pour les copies legacy trouvees."""
    out = []
    for path in iter_scan_files(root):
        rel = Path(path).relative_to(root).as_posix()
        if rel == CANONICAL_REL:
            continue
        try:
            text = path.read_text(encoding="utf-8")
        except (UnicodeDecodeError, OSError):
            continue
        if "MultiStrategy" not in text:
            continue
        blocks = extract_blocks(text, path.suffix == ".ipynb")
        legacy = [(n, b) for n, b in blocks if n == LEGACY_CLASS]
        if not legacy:
            continue
        out.append({
            "path": rel,
            "class": LEGACY_CLASS,
            "sha256": fingerprint(legacy),
        })
    return out


# ---------------------------------------------------------------------------
# Controle positif (--selftest) : exigence du critere 2 -- une copie
# volontairement modifiee doit faire rougir la garde.
# ---------------------------------------------------------------------------

_CANONICAL_SRC = '''from AlgorithmImports import *


class MultiStrategyPouchesPCM(PortfolioConstructionModel):
    """Module canonique (synthetique, self-test)."""

    def __init__(self, alpha_allocations):
        super().__init__()
        self.allocations = alpha_allocations
'''

_DECLARED_COPY = '''from AlgorithmImports import *


class MultiStrategyPCM(PortfolioConstructionModel):
    """Copie declaree (synthetique, self-test)."""

    def __init__(self, slices):
        super().__init__()
        self.slices = slices
'''


def _build_tree(tmp: Path, declared_sha: str) -> None:
    shared = tmp / SCAN_ROOT / "projects" / "SharedPCM"
    shared.mkdir(parents=True)
    (shared / "pouches_pcm.py").write_text(_CANONICAL_SRC, encoding="utf-8")
    proj = tmp / SCAN_ROOT / "projects" / "ProjSynthetic"
    proj.mkdir(parents=True)
    (proj / "portfolio_construction.py").write_text(
        _DECLARED_COPY, encoding="utf-8")
    (shared / "embedded_copies.json").write_text(json.dumps({
        "schema": 1,
        "canonical": CANONICAL_REL,
        "copies": [{
            "path": f"{SCAN_ROOT}/projects/ProjSynthetic/portfolio_construction.py",
            "class": LEGACY_CLASS,
            "sha256": declared_sha,
            "motif": "copie synthetique du self-test",
        }],
    }, indent=2, ensure_ascii=False), encoding="utf-8")


def selftest() -> int:
    base = Path(tempfile.mkdtemp(prefix="pcm-guard-selftest-"))
    _build_tree(base, fingerprint(extract_blocks(_DECLARED_COPY, False)))
    declared_rel = f"{SCAN_ROOT}/projects/ProjSynthetic/portfolio_construction.py"

    scenarios: list[tuple[str, str, list[str], int]] = []

    # S0 : arbre propre -> vert.
    scenarios.append(("S0-clean", str(base), [], 0))

    # S1 : CONTROLE POSITIF -- copie declaree volontairement modifiee.
    s1 = Path(tempfile.mkdtemp(prefix="pcm-guard-s1-"))
    _build_tree(s1, fingerprint(extract_blocks(_DECLARED_COPY, False)))
    victim = s1 / SCAN_ROOT / "projects" / "ProjSynthetic" / "portfolio_construction.py"
    victim.write_text(
        _DECLARED_COPY.replace("self.slices = slices",
                               "self.slices = slices * 2"),
        encoding="utf-8")
    scenarios.append(("S1-drift-positive-control", str(s1), ["DRIFT"], 1))

    # S2 : copie nouvelle non declaree.
    s2 = Path(tempfile.mkdtemp(prefix="pcm-guard-s2-"))
    _build_tree(s2, fingerprint(extract_blocks(_DECLARED_COPY, False)))
    undeclared = s2 / SCAN_ROOT / "projects" / "OtherProj"
    undeclared.mkdir(parents=True)
    (undeclared / "main.py").write_text(_DECLARED_COPY, encoding="utf-8")
    scenarios.append(("S2-undeclared", str(s2), ["UNDECLARED"], 1))

    # S3 : classe canonique duplimee hors SharedPCM.
    s3 = Path(tempfile.mkdtemp(prefix="pcm-guard-s3-"))
    _build_tree(s3, fingerprint(extract_blocks(_DECLARED_COPY, False)))
    dup = s3 / SCAN_ROOT / "projects" / "OtherProj"
    dup.mkdir(parents=True)
    (dup / "main.py").write_text(_CANONICAL_SRC, encoding="utf-8")
    scenarios.append(("S3-canonical-duplicate", str(s3),
                      ["CANONICAL_DUPLICATE"], 1))

    # S4 : copie declaree supprimee -> declaration perimee.
    s4 = Path(tempfile.mkdtemp(prefix="pcm-guard-s4-"))
    _build_tree(s4, fingerprint(extract_blocks(_DECLARED_COPY, False)))
    (s4 / declared_rel).unlink()
    scenarios.append(("S4-stale-manifest", str(s4), ["STALE"], 1))

    # S5 : module canonique disparu.
    s5 = Path(tempfile.mkdtemp(prefix="pcm-guard-s5-"))
    _build_tree(s5, fingerprint(extract_blocks(_DECLARED_COPY, False)))
    (s5 / CANONICAL_REL).unlink()
    scenarios.append(("S5-canonical-missing", str(s5),
                      ["CANONICAL_MISSING"], 1))

    failures = 0
    for name, root, expected_types, expected_rc in scenarios:
        verdict = check_tree(Path(root))
        got_types = sorted({f["type"] for f in verdict["findings"]})
        rc = 1 if verdict["status"] == "FAIL" else 0
        ok = (rc == expected_rc
              and (not expected_types
                   or all(t in got_types for t in expected_types)))
        print(f"  {name}: rc={rc} findings={got_types or '[]'}"
              f" -> {'PASS' if ok else 'FAIL'}")
        if not ok:
            failures += 1
    if failures:
        print(f"self-test: {failures} scenario(s) en echec", file=sys.stderr)
        return 2
    print("self-test: 6/6 scenarios PASS (controle positif S1 compris)")
    return 0


def resolve_root(explicit: str | None) -> Path:
    if explicit:
        return Path(explicit).resolve()
    cwd = Path.cwd()
    for candidate in (cwd, REPO_ROOT):
        if (candidate / SCAN_ROOT).is_dir() or (candidate / "scripts").is_dir():
            return candidate
    return cwd


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--root", help="racine du depot (defaut: auto)")
    parser.add_argument("--json", action="store_true",
                        help="verdict machine sur stdout")
    parser.add_argument("--emit", action="store_true",
                        help="imprimer les entrees calculees (bootstrap/"
                             "rafraichissement conscient du manifeste)")
    parser.add_argument("--selftest", action="store_true",
                        help="controle positif sur arbre synthetique "
                             "(pre-controle CI)")
    args = parser.parse_args(argv)

    if args.selftest:
        return selftest()

    root = resolve_root(args.root)
    if args.emit:
        print(json.dumps(emit_entries(root), indent=2, ensure_ascii=False))
        return 0

    verdict = check_tree(root)
    if args.json:
        print(json.dumps(verdict, indent=2, ensure_ascii=False))
    else:
        if verdict["status"] == "OK":
            print(f"OK : {verdict['copies_seen']} copie(s) embarquee(s), "
                  f"toutes declarees ; canonique present "
                  f"({verdict['files_scanned']} fichiers scannes)")
        else:
            print(f"FAIL : {len(verdict['findings'])} finding(s)")
            for f in verdict["findings"]:
                print(f"  [{f['type']}] {f['path']}: {f['detail']}")
    return 1 if verdict["status"] == "FAIL" else 0


if __name__ == "__main__":
    sys.exit(main())
