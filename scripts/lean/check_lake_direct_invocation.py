"""Garde CI (#15666, tranche T4) : refuser toute NOUVELLE invocation directe
de ``lake build`` / ``lake env lean`` dans du code d'orchestration Python,
hors allowlist documentee.

L'organe canonique d'execution Lean est ``scripts/lean/lean_exec.py`` (epic
#15666) : admission machine-wide fail-closed (T1, #15841), budget
min-des-sources (T2, #16098), backend epingle par lake (T3, #16160). Toute
voie directe re-introduit le defaut fondateur de l'incident 2026-09-12 --
pres de 30 processus ``lean.exe`` a 95 % du CPU, machine etouffee, DriveFS
et Claudish arretes -- parce qu'elle echappe au budget commun.

Detection AST, pas grep : une invocation directe est un appel
``subprocess.run`` / ``Popen`` / ``check_output`` / ``check_call`` /
``os.system`` (ou variante par shell interpose ``sh``/``bash``/``wsl``) dont
un argument positionnel CONSTANT commence par les jetons ``lake build`` ou
``lake env lean``. Les docstrings et commentaires ne comptent pas : l'AST ne
les visite jamais comme arguments d'appel -- c'est tout l'interet de la
methode face aux dizaines de mentions de ``lake build`` en prose.

L'allowlist ``scripts/lean/lake_direct_allowlist.json`` documente la dette de
migration (chemin POSIX -> raison). Le garde ne rougit QUE les violations
hors allowlist : les entrees liste'es peuvent etre migrees tranquillement,
retrait de l'entree au moment du rebus -- une entree devenue sterile est
signalee en WARNING (ratchet descendant), jamais en silence.

Verdict : exit 0 si toute violation est allowlistee, exit 1 si au moins une
ne l'est pas, exit 2 sur erreur d'usage.
"""

from __future__ import annotations

import argparse
import ast
import json
import re
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
ALLOWLIST_PATH = Path(__file__).resolve().parent / "lake_direct_allowlist.json"

# L'organe lui-meme construit et lance ``lake build`` (insertion ``-Kjobs=N``) :
# c'est sa raison d'etre, pas une dette.
SELF_EXEMPT = {"scripts/lean/lean_exec.py"}

LAUNCH_ATTRS = {"run", "Popen", "check_output", "check_call", "system"}
SHELL_PREFIXES = {"sh", "bash", "wsl", "wsl.exe", "cmd", "cmd.exe"}


def _leading_tokens(text: str, n: int) -> list[str]:
    return text.split()[:n]


def _is_direct_lake(text: str) -> tuple[bool, str]:
    """Vrai si la chaine commence par ``lake build`` / ``lake env lean``."""
    tokens = _leading_tokens(text, 3)
    if not tokens or tokens[0] != "lake":
        return False, ""
    if len(tokens) >= 2 and tokens[1] == "build":
        return True, "lake build"
    if len(tokens) >= 3 and tokens[1:3] == ["env", "lean"]:
        return True, "lake env lean"
    return False, ""


def _constants_of(node: ast.expr, depth: int = 0) -> list[str]:
    """Constantes str d'une expression d'argument (str nue, liste, f-string)."""
    if depth > 2:
        return []
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        return [node.value]
    if isinstance(node, (ast.List, ast.Tuple)):
        out: list[str] = []
        for elt in node.elts:
            out.extend(_constants_of(elt, depth + 1))
        return out
    if isinstance(node, ast.JoinedStr):
        # f"lake build {target}" : le prefixe literal suffit a trancher.
        return [v.value for v in node.values
                if isinstance(v, ast.Constant) and isinstance(v.value, str)]
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Mod):
        return _constants_of(node.left, depth + 1)
    return []


def _launch_like(func: ast.expr) -> bool:
    if isinstance(func, ast.Attribute):
        return func.attr in LAUNCH_ATTRS
    if isinstance(func, ast.Name):
        return func.id in {"system", "Popen", "run", "check_output", "check_call"}
    return False


def _command_prefix(func_name: str, tokens: list[str]) -> bool:
    """Vrai si les jetons forment un lancement de lake, direct ou via shell."""
    if not tokens:
        return False
    if tokens[0] in SHELL_PREFIXES:
        return any(_is_direct_lake(t)[0] for t in tokens)
    return _is_direct_lake(" ".join(tokens))[0]


def _is_test_path(rel: str) -> bool:
    """Tests = fixtures et mocks de lake, pas du code d'orchestration.

    Les ``test_*.py`` construisent des commandes lake factices pour exercer
    les organes : les compter fabriquerait une allowlist dominee par du
    bruit mock alors que l'epic vise les voies qui ETTOUFFENT la machine.
    ``--include-tests`` rouvre le scan pour les audits ponctuels.
    """
    base = rel.rsplit("/", 1)[-1]
    return base.startswith("test_") or "/tests/" in f"/{rel}"


# Fragment de commande dans les parties LITTERALES d'une f-string ou d'une
# concatenation. Pour ne pas attraper la PROSE (message « lake build failed
# (exit …) »), le jeton ne compte qu'en POSITION DE COMMANDE : debut de
# chaine, apres « && », « ; » ou « | » -- les vrai fragments observes
# (f"cd {p} && lake {args}", "… ; lake build …") y passent, les messages
# d'erreur en francais non.
_LAKE_FRAGMENT = re.compile(
    r"(?:\A|&&\s|;\s|\|\s)lake(?:\.exe)?\s+(?:build|env)(?![\w])"
)
_BARE_LAKE_TOKEN = {"lake", "lake.exe"}


def _concat_constants(node: ast.expr, depth: int = 0) -> str:
    """Parties litterales d'une concatenation (additions de chaines)."""
    if depth > 6:
        return ""
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        return node.value
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
        return _concat_constants(node.left, depth + 1) + _concat_constants(
            node.right, depth + 1)
    if isinstance(node, ast.JoinedStr):
        return "".join(v.value for v in node.values
                       if isinstance(v, ast.Constant)
                       and isinstance(v.value, str))
    return ""


def _non_command_list_ids(tree: ast.AST) -> set[int]:
    """Ids des List/Tuple qui NOMMENT des outils sans jamais les lancer.

    Trois contextes non-commande : comparé par ``in`` / ``not in``
    (``cmd in ["elan", "lean", "lake", "repl"]``), itéré par un ``for``
    (``for tool in ["lake", "lean"]:`` suivi d'un ``which``), générateur de
    compréhension. La liste y énumère des executables a PROBER, elle n'est
    pas un argv.
    """
    ids: set[int] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Compare):
            for comp in node.comparators:
                if isinstance(comp, (ast.List, ast.Tuple)):
                    ids.add(id(comp))
        elif isinstance(node, (ast.For, ast.AsyncFor)):
            if isinstance(node.iter, (ast.List, ast.Tuple)):
                ids.add(id(node.iter))
        elif isinstance(node, ast.comprehension):
            if isinstance(node.iter, (ast.List, ast.Tuple)):
                ids.add(id(node.iter))
    return ids


def scan_file(path: Path) -> list[tuple[int, str, str]]:
    """Retourne [(ligne, forme, extrait)] des invocations directes du fichier."""
    try:
        tree = ast.parse(path.read_text(encoding="utf-8", errors="replace"))
    except SyntaxError:
        return []
    findings: list[tuple[int, str, str]] = []
    non_command_ids = _non_command_list_ids(tree)
    for node in ast.walk(tree):
        if isinstance(node, ast.Call) and _launch_like(node.func):
            constants: list[str] = []
            for arg in node.args[:4]:
                constants.extend(_constants_of(arg))
            joined = " ".join(c.strip() for c in constants if c.strip())
            hit, form = _is_direct_lake(joined)
            if not hit:
                hit = _command_prefix("", constants)
                form = "lake build/env lean"
            if hit:
                findings.append((node.lineno, form, joined[:90]))
            continue
        # Forme 2 : jeton de commande exact dans un literal de liste (ex.
        # ``["lake", *extra_args]``, ``["wsl", ..., "lake", ...]``) ou en
        # join de chemin (``elan_bin / "lake.exe"``). Les strings nus hors
        # de ces contextes (``shutil.which("lake")``, cles de dict, prose)
        # ne comptent PAS : un jeton seul n'est une commande que structuree.
        if isinstance(node, (ast.List, ast.Tuple)):
            if id(node) in non_command_ids:
                continue
            for elt in node.elts:
                if (isinstance(elt, ast.Constant)
                        and isinstance(elt.value, str)
                        and elt.value in _BARE_LAKE_TOKEN):
                    findings.append((node.lineno, "jeton lake",
                                     f"[{elt.value}, ...]"))
                    break
            continue
        if (isinstance(node, ast.BinOp) and isinstance(node.op, ast.Div)
                and isinstance(node.right, ast.Constant)
                and node.right.value in _BARE_LAKE_TOKEN):
            findings.append((node.lineno, "jeton lake",
                             f"... / {node.right.value!r}"))
            continue
        # Forme 3 : f-string / concatenation dont les parties litterales
        # forment un fragment de commande lake (ex. f"cd {p} && lake {args}").
        if isinstance(node, (ast.JoinedStr, ast.BinOp)):
            joined = _concat_constants(node)
            # Signal shell requis dans la meme litterale : les messages de
            # prose (« lake build failed (exit …) ») ne portent ni && ni ;
            # ni redirection, les vrais fragments de commande si.
            shellish = any(sig in joined for sig in
                           ("&&", ";", "|", "2>", "cd ", "$", "~"))
            if joined and shellish and _LAKE_FRAGMENT.search(joined):
                findings.append((node.lineno, "fragment f-string",
                                 joined.strip()[:90]))
    # Dedupe par ligne : un ``subprocess.run(["lake", "build"])`` declenche
    # la forme 1 (appel) ET la forme 2 (liste) au meme endroit -- ast.walk
    # etant BFS, l'appel est visite avant sa liste enfant, donc la forme la
    # plus specifique gagne.
    seen_lines: set[int] = set()
    unique: list[tuple[int, str, str]] = []
    for lineno, form, excerpt in findings:
        if lineno not in seen_lines:
            seen_lines.add(lineno)
            unique.append((lineno, form, excerpt))
    return unique


def tracked_python_files() -> list[Path]:
    out = subprocess.run(
        ["git", "ls-files", "*.py"],
        cwd=REPO_ROOT, capture_output=True, text=True, check=True,
        encoding="utf-8", errors="replace",
    ).stdout.splitlines()
    return [REPO_ROOT / p for p in out if p]


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("paths", nargs="*", help="fichiers ou dossiers a scanner")
    parser.add_argument("--all", action="store_true",
                        help="scanner tous les fichiers Python tracks du depot")
    parser.add_argument("--list", action="store_true",
                        help="lister les violations sans verdict (bootstrap)")
    parser.add_argument("--check", action="store_true",
                        help="comparer a l'allowlist et echouer hors allowlist")
    parser.add_argument("--include-tests", action="store_true",
                        help="scanner aussi les test_*.py (mocks lake inclus)")
    args = parser.parse_args(argv)

    if args.all or not args.paths:
        files = tracked_python_files()
    else:
        files = []
        for p in args.paths:
            pp = Path(p)
            if pp.is_dir():
                files.extend(pp.rglob("*.py"))
            elif pp.suffix == ".py":
                files.append(pp)

    try:
        allowlist: dict[str, str] = json.loads(ALLOWLIST_PATH.read_text("utf-8"))
    except (OSError, json.JSONDecodeError) as e:
        print(f"allowlist illisible ({ALLOWLIST_PATH.name}): {e}", file=sys.stderr)
        return 2

    violations: dict[str, list[tuple[int, str, str]]] = {}
    for f in files:
        rel = f.relative_to(REPO_ROOT).as_posix() if f.is_relative_to(REPO_ROOT) else f.as_posix()
        if rel in SELF_EXEMPT:
            continue
        if not args.include_tests and _is_test_path(rel):
            continue
        found = scan_file(f)
        if found:
            violations[rel] = found

    for rel in sorted(violations):
        for lineno, form, excerpt in violations[rel]:
            marker = "ALLOWED" if rel in allowlist else "DIRECT "
            print(f"{marker}  {rel}:{lineno}  [{form}]  {excerpt}")

    if args.list:
        return 0

    new = [rel for rel in violations if rel not in allowlist]
    stale = [rel for rel in allowlist
             if rel not in violations and rel not in SELF_EXEMPT]
    for rel in stale:
        print(f"STALE   {rel}  (allowlistee sans violation : migrer puis "
              f"retirer l'entree)")

    if new:
        print(f"\nVERDICT: FAIL -- {len(new)} fichier(s) hors allowlist avec "
              f"invocation directe de lake : {', '.join(sorted(new))}")
        print("Migrer vers scripts/lean/lean_exec.py (organe canonique, "
              "#15666) ou documenter l'entree dans "
              "scripts/lean/lake_direct_allowlist.json.")
        return 1

    print(f"\nVERDICT: OK -- {len(violations)} fichier(s) en dette, tous "
          f"allowlistes ; {len(stale)} entree(s) stale(s).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
