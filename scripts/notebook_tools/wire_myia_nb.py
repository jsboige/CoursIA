"""Cable la crate pedagogique `myia_nb` dans les carnets Rust (Pli 3, #27098).

Deux gestes, sur une seule classe de correction :

1. la ligne `:dep` de la crate, en tete du premier bloc de code du carnet ;
2. le remplacement de la definition locale de `py_bool` par un `use` de la
   crate, quand cette definition est **semantiquement identique** a la
   version partagee.

Le fixer est volontairement etroit. Il ne touche que les definitions dont le
corps se reduit a `if <x> { "True" } else { "False" }` (avec ou sans
`.to_string()`, coherent avec le type de retour). Toute autre definition de
`py_*` est **signalee**, jamais reecrite : les variantes mesurees de
`py_list` / `py_tup` different par le type d'argument ou par la semantique,
et une reecriture aveugle fabriquerait un ecart d'affichage silencieux.

Usage :
    python scripts/notebook_tools/wire_myia_nb.py --check <carnet|dossier>...
    python scripts/notebook_tools/wire_myia_nb.py --apply <carnet|dossier>...
    python scripts/notebook_tools/wire_myia_nb.py --check --all
    python scripts/notebook_tools/wire_myia_nb.py --check --all --json

Codes de sortie : 0 = rien a faire (ou tout applique), 1 = `--check` a trouve
un carnet non cable, 2 = lecture/eecriture impossible.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from pathlib import Path

CRATE_REL = "RustSupport/myia_nb"
NOTEBOOKS_ROOT = "MyIA.AI.Notebooks"

# Un corps de py_bool acceptable, une fois l'espace normalise. Le nom de
# l'argument est libre, mais la condition doit porter sur ce meme nom.
BODY_PATTERN = re.compile(
    r'^if (?P<var>[A-Za-z_][A-Za-z0-9_]*) '
    r'\{ "(?P<t>True)"(?P<ts1>\.to_string\(\))? \} '
    r'else \{ "(?P<f>False)"(?P<ts2>\.to_string\(\))? \}$'
)
SIGNATURE_PATTERN = re.compile(
    r"fn\s+py_bool\s*\(\s*(?P<arg>[A-Za-z_][A-Za-z0-9_]*)\s*:\s*bool\s*\)"
    r"\s*->\s*(?P<ret>&\s*'\s*static\s+str|String)\s*\{"
)
ANY_PY_DEF = re.compile(r"^fn\s+(py_[A-Za-z0-9_]+)\s*\(", re.M)


def _brace_block(source: str, open_index: int) -> int:
    """Rend l'index du `}` qui ferme l'accolade ouverte a `open_index`."""
    depth = 0
    for k in range(open_index, len(source)):
        if source[k] == "{":
            depth += 1
        elif source[k] == "}":
            depth -= 1
            if depth == 0:
                return k
    return -1


def _dep_line(nb_path: Path, repo_root: Path) -> str:
    """Ligne `:dep` avec le chemin relatif de la crate depuis le carnet.

    Le kernel resout un `path` de dependance contre son repertoire de
    travail, qui est celui du carnet : le chemin relatif se calcule donc
    depuis le dossier du carnet (mesure sur le noyau Rust, #27098).
    """
    target = (repo_root / NOTEBOOKS_ROOT / CRATE_REL).resolve()
    rel = os.path.relpath(target, nb_path.parent.resolve())
    return ':dep myia_nb = { path = "%s" }' % _posix(Path(rel))


def _posix(p: Path) -> str:
    return str(p).replace("\\", "/")


def analyse(nb: dict, dep: str) -> dict:
    """Rend le plan de correction d'un carnet, sans rien ecrire."""
    plan = {
        "dep_present": False,
        "replacements": [],  # (cell_index, start, end, new_text, kind)
        "unhandled": [],
        "first_code_cell": None,
    }
    for i, cell in enumerate(nb.get("cells", [])):
        if cell.get("cell_type") != "code":
            continue
        if plan["first_code_cell"] is None:
            plan["first_code_cell"] = i
        source = "".join(cell.get("source", []))
        if ":dep myia_nb" in source:
            plan["dep_present"] = True
        seen = set()
        for m in SIGNATURE_PATTERN.finditer(source):
            arg = m.group("arg")
            ret = re.sub(r"\s+", "", m.group("ret"))
            open_index = m.end() - 1
            close_index = _brace_block(source, open_index)
            if close_index < 0:
                continue
            body = source[open_index + 1:close_index]
            norm = re.sub(r"\s+", " ", body).strip()
            bm = BODY_PATTERN.match(norm)
            ok = False
            if bm and bm.group("var") == arg:
                to_string = bool(bm.group("ts1")) and bool(bm.group("ts2"))
                plain = not bm.group("ts1") and not bm.group("ts2")
                ok = (ret.startswith("&") and plain) or (ret == "String" and to_string)
            if ok:
                kind = "static_str" if ret.startswith("&") else "string"
                plan["replacements"].append((i, m.start(), close_index + 1, kind))
                seen.add("py_bool")
            # definition non reconnue : signalee, jamais reecrite
        for name_m in ANY_PY_DEF.finditer(source):
            if name_m.group(1) not in seen:
                plan["unhandled"].append({"cell": i, "name": name_m.group(1)})
    plan["dep"] = dep
    return plan


def apply_plan(nb: dict, plan: dict) -> dict:
    """Applique le plan au carnet en memoire ; rend des statistiques."""
    stats = {"py_bool_removed": 0, "dep_added": False}
    # Remplacements de la fin vers le debut, par cellule, pour garder les
    # index valides.
    per_cell: dict[int, list] = {}
    for (cell_index, start, end, kind) in plan["replacements"]:
        per_cell.setdefault(cell_index, []).append((start, end, kind))
    for cell_index, items in per_cell.items():
        cell = nb["cells"][cell_index]
        source = "".join(cell.get("source", []))
        for (start, end, kind) in sorted(items, reverse=True):
            new = (
                "use myia_nb::py_bool;"
                if kind == "static_str"
                else "use myia_nb::py_bool_string as py_bool;"
            )
            source = source[:start] + new + source[end:]
            stats["py_bool_removed"] += 1
        cell["source"] = _split_lines(source)
    first = plan["first_code_cell"]
    if first is not None and not plan["dep_present"]:
        cell = nb["cells"][first]
        source = "".join(cell.get("source", []))
        source = plan["dep"] + "\n" + source
        cell["source"] = _split_lines(source)
        stats["dep_added"] = True
    return stats


def _split_lines(source: str) -> list[str]:
    """Decoupe en lignes gardant les fins de ligne, comme nbformat."""
    out = re.findall(r"[^\n]*\n|[^\n]+$", source)
    return out


def _read(path: Path) -> tuple[dict, str]:
    raw = path.read_text(encoding="utf-8", newline="")
    return json.loads(raw), ("\r\n" if "\r\n" in raw else "\n")


def _write(path: Path, nb: dict, newline: str) -> None:
    text = json.dumps(nb, indent=1, ensure_ascii=False)
    if not text.endswith("\n"):
        text += "\n"
    if newline == "\r\n":
        text = text.replace("\n", "\r\n")
    path.write_text(text, encoding="utf-8", newline="")


def _iter_targets(args, repo_root: Path) -> list[Path]:
    if args.all:
        return sorted((repo_root / NOTEBOOKS_ROOT).rglob("*-Rust.ipynb"))
    out: list[Path] = []
    for raw in args.targets:
        p = Path(raw)
        if p.is_dir():
            out.extend(sorted(p.rglob("*-Rust.ipynb")))
        else:
            out.append(p)
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Cable la crate myia_nb dans les carnets Rust (#27098)"
    )
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true", help="n'ecrit rien, dit ce qui manque")
    mode.add_argument("--apply", action="store_true", help="applique le cablage")
    parser.add_argument("targets", nargs="*", help="carnets ou dossiers")
    parser.add_argument("--all", action="store_true", help="tous les carnets Rust du depot")
    parser.add_argument("--repo-root", default=".", help="racine du depot")
    parser.add_argument("--json", action="store_true", help="sortie structuree")
    args = parser.parse_args(argv)

    repo_root = Path(args.repo_root).resolve()
    targets = _iter_targets(args, repo_root)
    if not targets:
        print("aucun carnet Rust trouve", file=sys.stderr)
        return 2

    report = {"mode": "apply" if args.apply else "check", "notebooks": []}
    failed = False
    for path in targets:
        try:
            nb, newline = _read(path)
        except Exception as exc:  # noqa: BLE001 - on rapporte, on ne masque pas
            report["notebooks"].append({"path": str(path), "error": str(exc)})
            failed = True
            continue
        dep = _dep_line(path, repo_root)
        plan = analyse(nb, dep)
        entry = {
            "path": _posix(path.relative_to(repo_root)) if path.is_relative_to(repo_root) else str(path),
            "py_bool_found": len(plan["replacements"]),
            "dep_present": plan["dep_present"],
            "unhandled": plan["unhandled"],
            "changed": False,
        }
        if args.apply:
            if plan["replacements"] or not plan["dep_present"]:
                stats = apply_plan(nb, plan)
                _write(path, nb, newline)
                entry.update(stats)
                entry["changed"] = True
            report["notebooks"].append(entry)
        else:
            if plan["replacements"] or not plan["dep_present"]:
                entry["wired"] = False
                failed = True
            else:
                entry["wired"] = True
            report["notebooks"].append(entry)

    if args.json:
        print(json.dumps(report, ensure_ascii=False, indent=2))
    else:
        verb = "applique" if args.apply else "a cabler"
        for entry in report["notebooks"]:
            if entry.get("error"):
                print(f"ERREUR {entry['path']}: {entry['error']}")
                continue
            if args.apply and entry["changed"]:
                print(
                    "cable   %s : %d py_bool, dep %s"
                    % (entry["path"], entry["py_bool_found"], "+" if entry["dep_present"] is False else "deja la")
                )
            elif not args.apply and not entry.get("wired", True):
                print(
                    "%s %s : %d py_bool, dep %s"
                    % (verb, entry["path"], entry["py_bool_found"], "present" if entry["dep_present"] else "absent")
                )
            for item in entry["unhandled"]:
                print("  non migre (a voir a la main) : %s (cellule %d)" % (item["name"], item["cell"]))

    return 1 if (failed and not args.apply) else (2 if failed else 0)


if __name__ == "__main__":
    sys.exit(main())
