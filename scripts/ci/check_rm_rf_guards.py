#!/usr/bin/env python3
"""Garde des invocations `rm -rf` sur variable (#20208).

Mesure fondatrice (origin/main @ dcc9d7482, `scripts/` + `.claude/`, 3534 fichiers) :
48 invocations `rm` recursives+forcees, 36 portant une expansion de variable, et
**zero forme catastrophique** (`rm -rf "$VAR/"` -> `rm -rf /`, `rm -rf "$VAR"/*`
-> `rm -rf /*`). L'exposition est donc LATENTE, pas actuelle : 8 sites fuient hors
de leur racine si la variable est vide, dont 4 dans des fichiers sans garde, et ces
4 sites ne s'activent que par une edition future qui viderait la racine.

C'est pourquoi l'organe ne reecrit rien : il refuse une NOUVELLE occurrence.

Trois classes, decidees par ce que devient l'argument quand la variable est vide :

  ESCAPE_ROOT   `rm -rf "$VAR/suffixe"` -> `rm -rf "/suffixe"`  DANGEREUX
                la suppression sort de la racine declaree, a la racine du disque.
  UNQUOTED_VAR  `rm -rf $VAR/suffixe`   -> word splitting + globbing  DANGEREUX
  BARE_VAR      `rm -rf "$VAR"`         -> `rm -rf ""`  BENIN
                `rm` refuse un operande vide : aucune suppression.

La seule garde qui couvre le cas **vide** est `${VAR:?}` (`:` traite unset et vide
de la meme facon). `set -u` ne couvre que l'**unset** : il ne protege PAS du cas
vide, et il n'est donc pas accepte comme garde ici.

Usage :
    python scripts/ci/check_rm_rf_guards.py                  # arbre de travail
    python scripts/ci/check_rm_rf_guards.py --root scripts --root .claude
    python scripts/ci/check_rm_rf_guards.py --json
    python scripts/ci/check_rm_rf_guards.py --update-baseline

Sortie : 0 = aucune occurrence hors baseline, 1 = occurrence nouvelle.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

EXIT_CLEAN = 0
EXIT_FINDINGS = 1

# Un token de commande : soit une chaine quote, soit un mot nu.
_TOKEN = re.compile(r'"[^"]*"|\'[^\']*\'|\S+')
# Invocation `rm` en debut de commande shell (pas `docker rm`, pas `git rm`).
# Le `^[ \t]*` est indispensable : une commande indentee (`  rm -rf "$TMP/x"`) est
# une commande en debut de ligne. SANS lui, l'organe ne voyait que les sites en
# colonne 0 -- mesure : 2 sites trouves sur 8 attendus.
# Les arguments s'arretent au separateur de commande : `rm -rf "$D/x"; mkdir -p "$D/x"`
# ne doit pas faire compter le `"$D/x"` du `mkdir` comme un argument du `rm`.
_RM = re.compile(r"(?:^[ \t]*|[;&|(]\s*|\{\s*|\bthen\s+|\bdo\s+)(rm\s+[^;&|]*)")
_VAR_START = re.compile(r"^\$\{?([A-Za-z_][A-Za-z0-9_]*)\}?")
_VAR_GUARDED = re.compile(r"\$\{[A-Za-z_][A-Za-z0-9_]*:\?")
_EXT = (".sh", ".bash", ".py", ".ps1", ".yml", ".yaml", ".md", "Dockerfile")

DEFAULT_ROOTS = ("scripts", ".claude")
BASELINE_NAME = "rm_rf_guards_baseline.txt"


def _strip_quotes(word: str) -> str:
    if len(word) >= 2 and word[0] == word[-1] and word[0] in "\"'":
        return word[1:-1]
    return word


def classify_args(args: str) -> list[dict]:
    """Classe chaque argument d'une invocation `rm -rf`. Rend les sites dangereux."""
    out = []
    for word in _TOKEN.findall(args):
        if "$" not in word:
            continue
        raw = _strip_quotes(word)
        quoted = raw != word
        m = _VAR_START.match(raw)
        if not m:
            continue
        var = m.group(1)
        rest = raw[m.end():]
        if not quoted:
            # Le mot n'est pas entre guillemets : splitting + globbing.
            out.append({"klass": "UNQUOTED_VAR", "var": var, "word": word,
                        "why": f"${var} non quote : word splitting + globbing"})
        elif rest.startswith("/"):
            if _VAR_GUARDED.search(word):
                continue
            beyond = "/" + rest.lstrip("/")
            out.append({"klass": "ESCAPE_ROOT", "var": var, "word": word,
                        "why": f"{word} -> {beyond!r} si {var} est vide"})
        # else : BARE_VAR -- benin, `rm` refuse l'operande vide.
    return out


def _rm_flags(tokens: list[str]) -> tuple[bool, bool, int]:
    """Consomme les tokens de flags. Rend (recursif, force, index du 1er argument)."""
    recursive = force = False
    i = 0
    while i < len(tokens) and tokens[i].startswith("-"):
        t = tokens[i]
        if t == "--":
            i += 1
            break
        low = t.lower()
        if t == "--recursive" or ("r" in low and not t.startswith("--")):
            recursive = True
        if t == "--force" or ("f" in low and not t.startswith("--")):
            force = True
        i += 1
    return recursive, force, i


def scan_text(text: str, path: str) -> list[dict]:
    """Rend les sites dangereux d'un fichier, avec leur numero de ligne."""
    found = []
    for lineno, line in enumerate(text.splitlines(), 1):
        m = _RM.search(line)
        if not m:
            continue
        tokens = _TOKEN.findall(m.group(1))[1:]  # apres le mot `rm`
        recursive, force, idx = _rm_flags(tokens)
        if not (recursive and force):
            continue
        for site in classify_args(" ".join(tokens[idx:])):
            site.update({"file": path, "line": lineno})
            found.append(site)
    return found


def _tracked(roots: tuple[str, ...]) -> list[str]:
    out = subprocess.run(["git", "ls-files", *roots], capture_output=True,
                         text=True, encoding="utf-8", errors="replace")
    if out.returncode != 0:
        sys.exit(f"git ls-files a echoue : {out.stderr.strip()}")
    return [f for f in out.stdout.splitlines()
            if f.endswith(_EXT) and Path(f).is_file()]


def _key(site: dict) -> str:
    """Cle de baseline : fichier + argument, PAS fichier + ligne.

    Une cle `fichier:ligne` perimerait des qu'une ligne est inseree au-dessus du
    site tolere -- le garde rougirait alors sur un site inchange, ce qui est le
    meilleur moyen de le faire desactiver. `fichier:argument` survit aux
    decalages de lignes ; il reste permissif sur un site STRICTEMENT identique
    ajoute deux fois dans le meme fichier, ce qui est sans danger.
    """
    return f"{site['file']}:{site['word']}"


def load_baseline(path: Path) -> set[str]:
    if not path.is_file():
        return set()
    return {ln.strip() for ln in path.read_text(encoding="utf-8").splitlines()
            if ln.strip() and not ln.startswith("#")}


def findings(roots: tuple[str, ...] = DEFAULT_ROOTS) -> list[dict]:
    sites = []
    for f in _tracked(roots):
        try:
            text = Path(f).read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        sites.extend(scan_text(text, f))
    return sites


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--root", action="append", dest="roots",
                   help="racine a balayer (defaut : scripts, .claude)")
    p.add_argument("--baseline", default=str(Path(__file__).with_name(BASELINE_NAME)),
                   help="fichier des sites tolerants connus")
    p.add_argument("--update-baseline", action="store_true",
                   help="reecrit la baseline avec les sites mesures")
    p.add_argument("--json", action="store_true", help="verdict machine")
    args = p.parse_args(argv)

    roots = tuple(args.roots) if args.roots else DEFAULT_ROOTS
    baseline_path = Path(args.baseline)
    sites = findings(roots)

    if args.update_baseline:
        header = ("# Sites `rm -rf` sur variable tolerants connus (#20208).\n"
                  "# Ces sites fuient hors de leur racine SI la variable est vide ;\n"
                  "# ils sont toleres ici parce qu'un garde doit etre vert au merge.\n"
                  "# Retirer une ligne des qu'un site est corrige.\n")
        body = "\n".join(sorted({_key(s) for s in sites}))
        baseline_path.write_text(header + body + "\n", encoding="utf-8", newline="\n")
        print(f"baseline reecrite : {baseline_path} "
              f"({len(set(map(_key, sites)))} sites)")
        return EXIT_CLEAN

    baseline = load_baseline(baseline_path)
    new = [s for s in sites if _key(s) not in baseline]
    kept = len(sites) - len(new)

    if args.json:
        print(json.dumps({
            "verdict": "NEW_RM_RF_SITE" if new else "CLEAN",
            "total_flagged": len(sites),
            "baselined": kept,
            "new": [{**s, "key": _key(s)} for s in new],
        }, ensure_ascii=False, indent=1))
    else:
        print(f"sites `rm -rf` sur variable dangereux : {len(sites)} "
              f"({kept} en baseline, {len(new)} nouveaux)")
        for s in new:
            print(f"  {_key(s)}  [{s['klass']}] {s['why']}")
        if new:
            print("\nCorriger par `${VAR:?}` (couvre unset ET vide) -- `set -u` ne "
                  "couvre pas le cas vide.\nSi le site est un faux positif mesure, "
                  "relancer avec --update-baseline en le disant.")

    return EXIT_FINDINGS if new else EXIT_CLEAN


if __name__ == "__main__":
    sys.exit(main())
