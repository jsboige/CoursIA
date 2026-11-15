"""Lecture partagée et stricte des sélecteurs de bibliothèques Lake."""
from __future__ import annotations

import re
import tomllib
from pathlib import Path

Selector = tuple[str, str]


class LakefileError(ValueError):
    """Le lakefile ne peut pas être interprété sans ambiguïté."""


_NAME = r"[A-Za-z0-9_']+(?:\.[A-Za-z0-9_']+)*"
_ITEM = re.compile(rf"(?:\.(one|submodules|andSubmodules)\s+)?`({_NAME}(?:\.[*+])?)")
_HEAD = re.compile(r"\blean_lib\s+(?:«([^»]+)»|([A-Za-z_][\w']*))")
_END = re.compile(r"(?m)^\s*(?:@\[[^\]]+\]\s*)?(?:lean_exe|require|package|script|extern_lib)\b")
_KINDS = {"one": "one", "submodules": "sub", "andSubmodules": "all"}


def _selector(value: str) -> Selector:
    if not re.fullmatch(rf"{_NAME}(?:\.[*+])?", value):
        raise LakefileError(f"sélecteur non reconnu : {value!r}")
    if value.endswith(".*"):
        return "all", value[:-2]
    if value.endswith(".+"):
        return "sub", value[:-2]
    return "one", value


def _dsl_items(raw: str, path: Path) -> list[Selector]:
    if _ITEM.sub("", raw).strip(" \t\r\n,"):
        raise LakefileError(f"{path} : tableau Lake non reconnu : {raw!r}")
    result = []
    for prefix, name in _ITEM.findall(raw):
        if prefix:
            if name.endswith((".*", ".+")):
                raise LakefileError(f"{path} : glob ambigu : {name}")
            result.append((_KINDS[prefix], name))
        else:
            result.append(_selector(name))
    return result


def _without_comments(text: str, path: Path) -> str:
    """Masque les commentaires Lean imbriqués sans toucher aux chaînes."""
    result: list[str] = []
    depth = 0
    quoted = False
    i = 0
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                result.append("  ")
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                result.append("  ")
                i += 2
            else:
                result.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif quoted:
            result.append(text[i])
            if text[i] == "\\" and i + 1 < len(text):
                result.append(text[i + 1])
                i += 2
            else:
                if text[i] == '"':
                    quoted = False
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            result.append("  ")
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            result.append(" " * (end - i))
            i = end
        else:
            quoted = text[i] == '"'
            result.append(text[i])
            i += 1
    if depth:
        raise LakefileError(f"{path} : commentaire Lean non fermé")
    return "".join(result)


def _dsl(text: str, path: Path) -> list[Selector]:
    text = _without_comments(text, path)
    heads = list(_HEAD.finditer(text))
    if len(heads) != len(re.findall(r"\blean_lib\b", text)):
        raise LakefileError(f"{path} : déclaration lean_lib non reconnue")
    result: list[Selector] = []
    for i, head in enumerate(heads):
        name = head.group(1) or head.group(2)
        end = heads[i + 1].start() if i + 1 < len(heads) else len(text)
        block = text[head.end():end]
        stop = _END.search(block)
        if stop:
            block = block[:stop.start()]
        values = {}
        for key in ("roots", "globs"):
            clause = re.search(rf"\b{key}\s*:=", block)
            if not clause and re.search(rf"\b{key}\b", block):
                raise LakefileError(f"{path} : `{key}` non reconnu pour {name}")
            if clause:
                match = re.match(r"\s*#\[([^\]]*)\]", block[clause.end():])
                if not match or re.match(r"\s*(?:\+\+|\|>)", block[clause.end() + match.end():]):
                    raise LakefileError(f"{path} : `{key}` non reconnu pour {name}")
                values[key] = _dsl_items(match.group(1), path)
        if "roots" in values:
            result.extend(values["roots"])
        if "globs" in values:
            result.extend(values["globs"])
        if not values:
            result.append(("one", name))
    return result


def read_lakefile(path: Path) -> list[Selector]:
    """Lit un lakefile TOML ou le sous-ensemble littéral explicite du DSL Lean."""
    try:
        text = path.read_text(encoding="utf-8")
        if path.name == "lakefile.lean":
            return _dsl(text, path)
        if path.name != "lakefile.toml":
            raise LakefileError(f"{path} : format inconnu")
        config = tomllib.loads(text)
        libs = config.get("lean_lib", [])
        if not isinstance(libs, list):
            raise LakefileError(f"{path} : lean_lib doit être une liste")
        result: list[Selector] = []
        for lib in libs:
            if not isinstance(lib, dict) or not isinstance(lib.get("name"), str):
                raise LakefileError(f"{path} : [[lean_lib]] sans nom")
            roots = lib.get("roots", [] if "globs" in lib else [lib["name"]])
            globs = lib.get("globs", [])
            for key, values in (("roots", roots), ("globs", globs)):
                if not isinstance(values, list) or not all(isinstance(v, str) for v in values):
                    raise LakefileError(f"{path} : {key} doit être une liste de chaînes")
                for value in values:
                    selector = _selector(value)
                    if key == "roots" and selector[0] != "one":
                        raise LakefileError(f"{path} : racine invalide {value!r}")
                    result.append(selector)
        return result
    except (OSError, UnicodeError, tomllib.TOMLDecodeError) as exc:
        raise LakefileError(f"{path} : {exc}") from exc


def lake_selectors(lake: Path) -> list[Selector]:
    toml, lean = lake / "lakefile.toml", lake / "lakefile.lean"
    if toml.exists() and lean.exists():
        raise LakefileError(f"{lake} : lakefile.toml et lakefile.lean coexistent")
    return read_lakefile(toml if toml.exists() else lean)


def selected(module: str, selectors: list[Selector]) -> bool:
    return any((kind in ("one", "all") and module == name) or
               (kind in ("all", "sub") and module.startswith(name + "."))
               for kind, name in selectors)
