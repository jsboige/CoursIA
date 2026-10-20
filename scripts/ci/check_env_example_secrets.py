#!/usr/bin/env python3
"""Garde les fichiers *.env.example / *.env.sample / *.env.template sans valeur reelle.

gitleaks reconnait les formats de cles connus (sk-..., ghp_..., AIza...). Il ne voit
pas une phrase secrete faite d'un mot ordinaire ecrite en valeur dans un .env.example.
Ces fichiers sont publics par construction : une valeur reelle y est publiee des le
commit. Issue de reference : #20919.

Sorties : 0 = tous les fichiers tracent ne portent que des marqueurs ou des valeurs
legitimes · 1 = au moins une ligne rougit · 2 = mesure impossible (hors depot, git
absent). L'argument ``--files <f1> <f2> ...`` restreint la verification aux fichiers
donnes (mode pre-commit sur les fichiers modifies). Sans argument, scanne tous les
fichiers traces par git (mode CI).

Formes de marqueurs acceptees (case-insensitive) :
- valeur vide ;
- placeholder chevrons/crochets (``<your_key>``, ``[FILL_ME]``) ;
- ``your`` + separateur (``_``/``-``/``.``) + n'importe quoi + (``here`` / ``key`` /
  ``token`` / ``pass`` / ``password`` / ``secret`` / ``phrase``) ;
- ``change[._-]?me`` ;
- ``xxx`` ou plus (4+ ``x`` consecutifs) ;
- prefixes didactiques (``sk-...``, ``ghp_...``, ``sk-or-v1-...``, ``sk-proj-XXXX``,
  ``hf_...``, ``hf_xxx...``, ``xox[abp]-...``) ;
- ``auto[_-]?generated`` ;
- mots-cles : ``placeholder``, ``example``, ``dummy``, ``sample``, ``fake``,
  ``prototype``, ``fill``, ``replace_with`` ;
- ``0x<...>`` (placeholder EVM prive) ;
- URL ``^https?://`` (jamais un secret) ;
- chemin Windows/WSL ``\\...`` ou Unix ``/...`` ;
- numerique (entier ou flottant) ;
- boolean (``true``/``false``/``null``/``none``/``yes``/``no``/``on``/``off``) ;
- modele (``gpt-*``, ``claude-*``, ``llama-*``, ``qwen*``, etc.) ou ID HF
  (``org/model``) ;
- nom d'utilisateur par defaut (``admin``, ``root``, ``user``, ``default``,
  ``etudiant``, ``username``).

Cle de type secret : le nom matche ``(?i)(PASS|SECRET|TOKEN|KEY|PWD)`` (partiel,
insensible a la casse). Les lignes de commentaire (premier caractere non blanc = ``#``)
sont ignorees.
"""
from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

EXIT_OK = 0
EXIT_DEFECT = 1
EXIT_UNREACHABLE = 2

ENV_GLOBS = ("*.env.example", "*.env.sample", "*.env.template")
# Cle dont le nom matche ce motif (partiel) -- PAS de match sur le nom complet.
SECRET_NAME_RE = re.compile(r"(?i)(PASS|SECRET|TOKEN|KEY|PWD)")
LINE_RE = re.compile(r"^\s*(?:export\s+)?([A-Za-z_][A-Za-z0-9_]*)\s*=\s*(.*?)\s*$")
# Exemption inline documentee dans le message d'erreur : ``# OK: <reason>``
# (cf. issue #21013). On la detecte sur la ligne BRUTE, avant ``_strip_value``,
# qui sinon l'arracherait avec le commentaire. La raison est ignoree -- elle
# reste pour l'humain qui relit le diff.
_OK_INLINE_RE = re.compile(r"(?<!\\)#\s*OK\b", re.IGNORECASE)


# Motifs de marqueur (regex compilees, case-insensitive sauf mention contraire).
_MARKER_PATTERNS: tuple[re.Pattern[str], ...] = (
    re.compile(r"^true$|^false$|^null$|^none$|^yes$|^no$|^on$|^off$", re.IGNORECASE),
    re.compile(r"^-?\d+(\.\d+)?$"),
    re.compile(r"^[<\[][^\]>]*[>\]]$"),
    re.compile(r"^<[A-Za-z_][A-Za-z0-9_]*>$"),
    # your[_.\-]anything[_.\-](here|key|token|password|pass|secret|phrase)
    re.compile(
        r"your[._\-].*(here|key|token|password|pass|secret|phrase)\b", re.IGNORECASE
    ),
    re.compile(r"change[._\-]me", re.IGNORECASE),
    re.compile(r"^x{4,}$", re.IGNORECASE),
    re.compile(r"^\.{3,}$", re.IGNORECASE),
    re.compile(r"sk[-_]?local", re.IGNORECASE),
    re.compile(r"auto[_\-?\-]?generated", re.IGNORECASE),
    re.compile(
        r"\b(placeholder|example|dummy|sample|fake|prototype|fill|replace_with)\b",
        re.IGNORECASE,
    ),
    re.compile(r"hf_your", re.IGNORECASE),
    # Prefixes didactiques (gitleaks ne reconnait pas sk-..., sk-or-v1-..., etc.)
    re.compile(
        r"^(sk|sk-ant|sk-or|sk-proj|ghp|xox[abp])[-_.\w]*\.{3,}$",
        re.IGNORECASE,
    ),
    re.compile(
        r"^(sk|sk-ant|sk-or|sk-proj|ghp|xox[abp])[-_.\w]*(<.+>|\*+|your|xxx|placeholder|example|dummy)?$",
        re.IGNORECASE,
    ),
    re.compile(
        r"^(sk|sk-ant|sk-or|sk-proj|ghp|xox[abp])[-_.\w]*\d+$", re.IGNORECASE
    ),
    # hf_xxx / hf_... : prefixe huggingface + placeholder
    re.compile(r"^hf[_]?(xxx+|\.{3,}|your|<.+>)$", re.IGNORECASE),
    re.compile(r"^hf_xxx+", re.IGNORECASE),
    re.compile(r"^0x[<F]", re.IGNORECASE),
    re.compile(r"^https?://", re.IGNORECASE),
    re.compile(r"^[\\/]"),
    re.compile(r"^[A-Za-z0-9_.\-]+/[A-Za-z0-9_.\-]+(?::[A-Za-z0-9_.\-]+)?$"),
    re.compile(r"^\s+$"),
    # Valeurs communes de configuration (modeles, mode paper/live, etc.)
    re.compile(
        r"^(admin|root|user|username|default|paper|live|mainnet|testnet|local|localhost|etudiant|placeholder)$",
        re.IGNORECASE,
    ),
    re.compile(
        r"^(gpt|claude|llama|qwen|gemini|mistral|deepseek|meta|hf-|black-forest|facebook|google|openai|microsoft)/?[A-Za-z0-9.\-_:]*$",
        re.IGNORECASE,
    ),
    re.compile(
        r"^(gpt|claude|llama|qwen|gemini|whisper|kokoro|tada|qwen3)[-_.]?[A-Za-z0-9.\-]*$",
        re.IGNORECASE,
    ),
    re.compile(r"^(true|false)$", re.IGNORECASE),
)


def _strip_value(value: str) -> str:
    """Enleve les guillemets et le commentaire en fin de ligne.

    Convention .env : tout ce qui suit ``whitespace + #`` sur la meme ligne est
    un commentaire inline (cf. python-dotenv, dotenv crate). On retire aussi
    les guillemets appariés (``"..."`` ou ``'...'``).
    """
    # Coupe au premier '#' precede d'un blanc (ou en tete de valeur apres strip).
    s = value.lstrip()
    if s.startswith("#"):
        v = ""
    else:
        # Decoupe sur tout separateur ``<whitespace>#``.
        import re as _re
        v = _re.split(r"\s+#", value, maxsplit=1)[0]
    v = v.rstrip()
    if len(v) >= 2 and (
        (v.startswith('"') and v.endswith('"'))
        or (v.startswith("'") and v.endswith("'"))
    ):
        v = v[1:-1]
    return v.strip()


def is_marker(value: str) -> bool:
    """Vrai si la valeur est un marqueur (vide, placeholder, didactique)."""
    if not value:
        return True
    for pat in _MARKER_PATTERNS:
        if pat.search(value):
            return True
    return False


def _iter_files_from_git(root: Path) -> list[Path]:
    """Liste tous les fichiers traces par git matchant les globs ENV_GLOBS."""
    try:
        out = subprocess.run(
            ["git", "ls-files"],
            cwd=root, capture_output=True, text=True,
            encoding="utf-8", errors="replace", check=True,
        )
    except (subprocess.CalledProcessError, FileNotFoundError, OSError) as exc:
        raise RuntimeError(f"git ls-files failed: {exc}") from exc
    files: list[Path] = []
    for line in out.stdout.splitlines():
        for glob in ENV_GLOBS:
            # fnmatch case-sensitivity: keep it case-sensitive for *.env.example.
            import fnmatch
            if fnmatch.fnmatch(line, glob):
                files.append(root / line)
                break
    return files


def _collect_files(roots: list[Path], explicit: list[str]) -> list[Path]:
    files: list[Path] = []
    if explicit:
        for name in explicit:
            p = Path(name)
            if not p.is_file():
                continue
            if any(p.match(g) for g in ENV_GLOBS):
                files.append(p)
    else:
        seen: set[Path] = set()
        for root in roots:
            for glob in ENV_GLOBS:
                for p in root.rglob(glob):
                    if ".git" in p.parts:
                        continue
                    rp = p.resolve()
                    if rp not in seen:
                        seen.add(rp)
                        files.append(p)
    return sorted(set(files), key=lambda p: str(p).lower())


def check_file(path: Path) -> list[tuple[int, str, str, str]]:
    """Rend la liste des defauts (ligne, nom, valeur_brute, valeur_strip)."""
    defects: list[tuple[int, str, str, str]] = []
    try:
        text = path.read_text(encoding="utf-8", errors="replace")
    except OSError as exc:
        # Mesure impossible : on ne confonds pas avec un defaut (cf check_secret_paths_ignored).
        raise RuntimeError(f"read failed: {path}: {exc}") from exc
    for i, line in enumerate(text.splitlines(), 1):
        if line.lstrip().startswith("#"):
            continue
        m = LINE_RE.match(line)
        if not m:
            continue
        name, raw_value = m.group(1), m.group(2)
        # Exemption inline ``# OK: <reason>`` : la ligne est exemptee avant
        # l'evaluation du marqueur. Le commentaire doit etre separe de la
        # valeur par un blanc (cf. la convention .env). On l'evalue sur la
        # LIGNE BRUTE pour ne pas etre mange par ``_strip_value``.
        if _OK_INLINE_RE.search(line):
            continue
        value = _strip_value(raw_value)
        if not SECRET_NAME_RE.search(name):
            continue
        if not is_marker(value):
            defects.append((i, name, raw_value, value))
    return defects


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--files", nargs="*", default=[], help="Restreint aux fichiers indiques (mode pre-commit)")
    parser.add_argument("--root", type=Path, default=Path("."), help="Racine du repo (mode CI, defaut: .)")
    parser.add_argument("--json", action="store_true", help="Sortie JSON pour CI")
    args = parser.parse_args(argv)

    try:
        if args.files:
            files = _collect_files([Path(".")], args.files)
        else:
            files = _iter_files_from_git(args.root.resolve())
    except RuntimeError as exc:
        if args.json:
            print(f'{{"status":"UNREACHABLE","reason":"{exc}"}}')
        else:
            print(f"UNREACHABLE: {exc}", file=sys.stderr)
        return EXIT_UNREACHABLE

    all_defects: list[dict[str, object]] = []
    for path in files:
        try:
            defects = check_file(path)
        except RuntimeError as exc:
            if args.json:
                print(f'{{"status":"UNREACHABLE","reason":"{exc}"}}')
            else:
                print(f"UNREACHABLE: {exc}", file=sys.stderr)
            return EXIT_UNREACHABLE
        for line_no, name, raw_value, value in defects:
            all_defects.append({
                "file": str(path),
                "line": line_no,
                "name": name,
                "raw": raw_value,
                "value": value,
            })

    if args.json:
        import json
        print(json.dumps({
            "status": "OK" if not all_defects else "DEFECT",
            "files_scanned": len(files),
            "defects": all_defects,
        }, indent=2, ensure_ascii=False))
    else:
        if not all_defects:
            print(f"OK: {len(files)} files scanned, no real secret values in env examples.")
            return EXIT_OK
        print(f"DEFECT: {len(all_defects)} real secret value(s) in env examples:", file=sys.stderr)
        for d in all_defects:
            print(f"  {d['file']}:{d['line']}  {d['name']}={d['raw']!r}", file=sys.stderr)
        print("", file=sys.stderr)
        print("Either replace the value with a marker (your_X_here, <your_X>, xxx, ...),",
              file=sys.stderr)
        print("or exempt with a trailing comment  # OK: <reason>.",
              file=sys.stderr)
    return EXIT_OK if not all_defects else EXIT_DEFECT


if __name__ == "__main__":
    raise SystemExit(main())
