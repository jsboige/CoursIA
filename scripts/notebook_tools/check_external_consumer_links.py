#!/usr/bin/env python3
"""Controle des liens absolus qu'un depot consommateur EXTERNE pose vers CoursIA.

Pourquoi cet organe existe
--------------------------
La regle `notebook-accretion-numbering` (surface « Referents hors depot »)
constatait : « aucun organe possible ». Les depots de projets etudiants
(premier consommateur connu : `jsboigeEPF/2026-MSMIN5IN52-GenAI`,
`docs/CATALOGUE.md`, #15289) referencent les notebooks de ce depot par des
URLs absolues `https://github.com/jsboige/CoursIA/blob/main/<chemin>`. Quand
un renommage deplace un notebook, ces liens cassent SILENCIEUSEMENT : aucun
balayage du depot ne traverse la frontiere de depot, et le vert d'un rollup
ne dit rien de ces referents. Audit externe du 2026-11-13 : 3 cibles cassees
sur 122 occurrences de liens dans ce consommateur. Cet organe ferme la brèche.

Ce qu'il fait
-------------
- extrait d'un dossier LOCAL de fichiers markdown les URLs vers
  `<owner>/<repo>` aux formes `github.com/.../blob/<branche>/<chemin>`,
  `github.com/.../tree/...`, `raw.githubusercontent.com/...`, et les formes
  enveloppees `colab.research.google.com/github/...` et `nbviewer.org/github/...`
  (casse-insensible sur proprietaire/depot ; le reseau n'est JAMAIS touche) ;
- verifie chaque chemin contre l'arbre git d'une ref (`git ls-tree -r -z`) ;
- pour une cible cassee, cherche une relocalisation dans cet ordre :
  (a) chaines `ancien -> nouveau` du registre `docs/reference/rename-ledger.tsv`
      (suivies jusqu'a une cible presente, cycles gardes),
  (b) basename unique parmi les fichiers de l'arbre,
  (c) pour un lien `tree`, basename unique parmi les repertoires ;
- `--apply` reecrit dans les fichiers du consommateur les liens `moved` vers
  leur cible suggeree (dry-run par defaut ; `missing` et `pinned` jamais touchees).

Registre de renommage : lecteur LOCAL, pas un import de `rename_notebooks`.
Ce module n'expose pas de lecteur importable — sa lecture du registre est
inline dans `rebase_helper` (scripts/notebook_tools/rename_notebooks.py,
lecture de l'en-tete sautee puis `parts = line.split("\\t")`), et l'importer
muterait `sys.path` au passage. Le lecteur ci-dessous (`load_ledger`) reproduit
la meme semantique : en-tete `ancien\\tnouveau\\tdate\\tlane` saute, deux
premieres colonnes, dernier gagnant.

Usage
-----
    python scripts/notebook_tools/check_external_consumer_links.py \
        --consumer <dossier> [--consumer ...]
        [--glob '**/*.md' ...] [--repo-root <racine>] [--ref HEAD]
        [--owner-repo jsboige/CoursIA] [--branch main]
        [--ledger docs/reference/rename-ledger.tsv]
        [--json | --markdown] [--all] [--apply]

Codes de sortie : 0 = aucun lien `moved` ni `missing` ; 1 = au moins un
`moved` ou `missing` (apres `--apply`, re-evaluation sur l'arbre re-ecrit) ;
2 = erreur d'usage ou d'environnement (consommateur absent, git/ref inconnu).
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import urllib.parse
from dataclasses import dataclass, field
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]

DEFAULT_OWNER_REPO = "jsboige/CoursIA"
DEFAULT_BRANCH = "main"
LEDGER_RELPATH = "docs/reference/rename-ledger.tsv"
DEFAULT_GLOB = "**/*.md"

# Coupure d'une URL au premier caractere d'arret (blanc, ) > " ' ]) ; le
# point-virgule final et la ponctuation de prose sont retires ensuite.
_URL_BODY_RE = re.compile(r"https://[^\s)\"'>\]]+", re.I)
_TRAILING_PUNCT = ".,;"
_FRAGMENT_OR_QUERY_RE = re.compile(r"[?#]")
_SHA_RE = re.compile(r"^[0-9a-fA-F]{7,40}$")

_GH_PREFIX = "https://github.com/"
_RAW_PREFIX = "https://raw.githubusercontent.com/"
_COLAB_PREFIX = "https://colab.research.google.com/github/"
_NBV_PREFIX = "https://nbviewer.org/github/"

#: Kinds enveloppes : le chemin suit `blob/<branche>/...` comme sur github.com.
_WRAPPED_BLOB_PREFIXES = ((_COLAB_PREFIX, "colab"), (_NBV_PREFIX, "nbviewer"))


class OrganError(Exception):
    """Erreur d'environnement (git, ref, dossier) : sortie 2, message d'une ligne."""


@dataclass
class Link:
    """Une URL vers ce depot, extraite telle qu'ecrite d'un fichier consommateur."""
    start: int            # offset du debut de l'URL dans le texte du fichier
    line: int             # numero de ligne, 1-based
    url: str              # URL ecrite (ponctuation de prose retiree, fragment garde)
    kind: str             # blob | tree | raw | colab | nbviewer
    branch: str           # segment de branche tel qu'ecrit
    path: str             # chemin DECODE (%20, accents)
    path_raw: str         # chemin tel qu'ecrit dans l'URL (avant decode)
    path_end: int         # offset de fin du chemin dans le texte (debut + prefixe)


@dataclass
class Verdict:
    """Statut d'un lien contre l'arbre d'une ref."""
    link: Link
    status: str                 # ok | moved | missing | pinned
    suggestion: str | None = None
    via: str | None = None      # ledger | basename
    candidates: list[str] = field(default_factory=list)


def _parse_url(url: str, owner_lc: str) -> tuple[str, str, str] | None:
    """(kind, branche, chemin_ecrit) si l'URL vise <owner>/<repo>, sinon None.

    `owner_lc` = `owner/repo` minuscule + `/` : la comparaison du bloc
    proprietaire/depot est insensible a la casse, la decoupe se fait sur la
    LONGUEUR du prefixe (la casse d'origine du chemin est preservee).
    """
    low = url.lower()
    for prefix, kind in _WRAPPED_BLOB_PREFIXES:
        if low.startswith(prefix):
            if not low[len(prefix):].startswith(owner_lc):
                return None
            rest = url[len(prefix) + len(owner_lc):]
            if not rest.lower().startswith("blob/"):
                return None
            return _split_tail(kind, rest[len("blob/"):])
    if low.startswith(_GH_PREFIX):
        if not low[len(_GH_PREFIX):].startswith(owner_lc):
            return None
        rest = url[len(_GH_PREFIX) + len(owner_lc):]
        low_rest = rest.lower()
        if low_rest.startswith("blob/"):
            return _split_tail("blob", rest[len("blob/"):])
        if low_rest.startswith("tree/"):
            return _split_tail("tree", rest[len("tree/"):])
        return None
    if low.startswith(_RAW_PREFIX):
        if not low[len(_RAW_PREFIX):].startswith(owner_lc):
            return None
        return _split_tail("raw", url[len(_RAW_PREFIX) + len(owner_lc):])
    return None


def _split_tail(kind: str, tail: str) -> tuple[str, str, str] | None:
    """`<branche>/<chemin...>` -> (kind, branche, chemin) ; None si chemin vide."""
    seg = tail.split("/", 1)
    if len(seg) != 2 or not seg[0] or not seg[1]:
        return None
    return kind, seg[0], seg[1]


def extract_links(
    text: str,
    owner_repo: str = DEFAULT_OWNER_REPO,
    branch: str = DEFAULT_BRANCH,
) -> list[Link]:
    """Toutes les URLs vers `<owner_repo>` d'un texte, avec leur span et ligne.

    Ordre des nettoyages (spec) : coupe aux caracteres d'arret, retrait de la
    ponctuation de prose finale (`.` `,` `;`), PUIS retrait du `#fragment` et
    de la `?query`. `branch` n'entre pas dans l'extraction : un lien epingle a
    une autre branche est EXTRAIT puis classe `pinned`, jamais ignore.
    """
    owner_lc = owner_repo.strip("/").lower() + "/"
    links: list[Link] = []
    for m in _URL_BODY_RE.finditer(text):
        url = m.group(0)
        base = _FRAGMENT_OR_QUERY_RE.split(url.rstrip(_TRAILING_PUNCT), 1)[0]
        parsed = _parse_url(base, owner_lc)
        if parsed is None:
            continue
        kind, branch_seg, path_raw = parsed
        links.append(Link(
            start=m.start(),
            line=text.count("\n", 0, m.start()) + 1,
            url=url.rstrip(_TRAILING_PUNCT),
            kind=kind,
            branch=branch_seg,
            path=urllib.parse.unquote(path_raw),
            path_raw=path_raw,
            path_end=m.start() + len(base),
        ))
    return links


def dirs_of(tree_files: set[str]) -> set[str]:
    """Tous les prefixes de repertoire des fichiers de l'arbre."""
    dirs: set[str] = set()
    for f in tree_files:
        parts = f.split("/")
        for i in range(1, len(parts)):
            dirs.add("/".join(parts[:i]))
    return dirs


def load_ledger(path: Path) -> dict[str, str]:
    """Registre `ancien -> nouveau` (en-tete saute, dernier gagnant).

    Lecteur local reproduisant la semantique inline de `rename_notebooks.
    rebase_helper` (voir docstring du module) ; registre absent = dict vide.
    """
    if not path.is_file():
        return {}
    renames: dict[str, str] = {}
    for line in path.read_text(encoding="utf-8").splitlines()[1:]:
        parts = line.split("\t")
        if len(parts) < 2:
            continue
        old, new = parts[0].strip(), parts[1].strip()
        if old and new and old != new:
            renames[old] = new
    return renames


def load_tree(repo_root: Path, ref: str) -> tuple[set[str], set[str]]:
    """(fichiers, repertoires) de l'arbre git d'une ref, un seul appel ls-tree.

    `-z` : sortie NUL-separee, immunisee contre `core.quotepath` (les chemins
    accentues ou espaces ne sont ni cites ni echappes). Echec git/ref inconnue
    -> OrganError (sortie 2), jamais un faux arbre vide.
    """
    proc = subprocess.run(
        ["git", "-C", str(repo_root), "ls-tree", "-r", "--name-only", "-z", ref],
        capture_output=True,
    )
    if proc.returncode != 0:
        err = (proc.stderr or b"").decode("utf-8", "replace").strip().splitlines()
        detail = err[-1] if err else f"rc={proc.returncode}"
        raise OrganError(f"git ls-tree {ref} a echoue dans {repo_root} : {detail}")
    files = {
        p.decode("utf-8", "surrogateescape")
        for p in proc.stdout.split(b"\x00")
        if p
    }
    return files, dirs_of(files)


def _target_present(path: str, kind: str,
                    tree_files: set[str], tree_dirs: set[str]) -> bool:
    """Un lien blob/raw/colab/nbviewer vise un FICHIER ; un lien tree vise un
    fichier OU un prefixe de repertoire."""
    if path in tree_files:
        return True
    return kind == "tree" and path in tree_dirs


def _basename(path: str) -> str:
    return path.rsplit("/", 1)[-1]


def classify(link: Link,
             tree_files: set[str],
             tree_dirs: set[str],
             ledger: dict[str, str],
             branch: str = DEFAULT_BRANCH) -> Verdict:
    """Statut d'un lien : pinned / ok / moved / missing (+ suggestion, via).

    Ordre de relocalisation d'une cible cassee : (a) chaines du registre
    (cycles gardes par un ensemble de vus), (b) basename unique parmi les
    fichiers, (c) pour un lien tree, basename unique parmi les repertoires.
    """
    if link.branch != branch:
        return Verdict(link, "pinned")
    if _target_present(link.path, link.kind, tree_files, tree_dirs):
        return Verdict(link, "ok")

    cur, seen = link.path, {link.path}
    while cur in ledger:
        cur = ledger[cur]
        if cur in seen:            # cycle du registre : garde, pas de boucle
            break
        seen.add(cur)
        if _target_present(cur, link.kind, tree_files, tree_dirs):
            return Verdict(link, "moved", suggestion=cur, via="ledger")

    base = _basename(link.path)
    matches = sorted(f for f in tree_files if _basename(f) == base)
    if len(matches) == 1:
        return Verdict(link, "moved", suggestion=matches[0], via="basename")
    if link.kind == "tree":
        dmatches = sorted(d for d in tree_dirs if _basename(d) == base)
        if len(dmatches) == 1:
            return Verdict(link, "moved", suggestion=dmatches[0], via="basename")
        if not matches:
            matches = dmatches
    if len(matches) > 1:
        return Verdict(link, "missing", candidates=matches[:5])
    return Verdict(link, "missing")


def apply_fixes(text: str, verdicts: list[Verdict]) -> tuple[str, int]:
    """Reecrit dans le texte les chemins des liens `moved` — eux seuls.

    Le remplacement vise le SPAN du chemin dans SON URL : les occurrences
    identiques hors URL ne sont pas touchees. Re-encodage : si l'ancien chemin
    ecrit portait des `%`-echappements, le nouveau est percent-encode
    (`quote(path, safe="/")`), sinon ecrit brut. Rend (nouveau_texte, n).
    """
    edits: list[tuple[int, int, str]] = []
    for v in verdicts:
        if v.status != "moved" or not v.suggestion:
            continue
        new = (urllib.parse.quote(v.suggestion, safe="/")
               if "%" in v.link.path_raw else v.suggestion)
        start = v.link.path_end - len(v.link.path_raw)
        edits.append((start, v.link.path_end, new))
    if not edits:
        return text, 0
    for start, end, replacement in sorted(edits, reverse=True):
        text = text[:start] + replacement + text[end:]
    return text, len(edits)


def _read_text_newlines_intact(path: Path) -> str:
    """Lecture utf-8 sans traduction de fins de ligne (`newline=""`)."""
    with open(path, "r", encoding="utf-8", newline="") as fh:
        return fh.read()


def _write_text_newlines_intact(path: Path, text: str) -> None:
    """Ecriture utf-8 sans traduction de fins de ligne : CRLF reste CRLF."""
    with open(path, "w", encoding="utf-8", newline="") as fh:
        fh.write(text)


def collect_consumer_files(root: Path, globs: list[str]) -> list[Path]:
    """Fichiers du consommateur couverts par les globs (dedupliques, triés)."""
    seen: set[Path] = set()
    for pattern in globs:
        for p in root.glob(pattern):
            if p.is_file():
                seen.add(p)
    return sorted(seen)


def _scan_consumer(consumer: Path, globs: list[str], owner_repo: str, branch: str,
                   tree_files: set[str], tree_dirs: set[str],
                   ledger: dict[str, str],
                   ) -> tuple[dict[str, tuple[str, list[Verdict]]], dict[str, int], int]:
    """Rend (texte+verdicts par fichier, totaux, fichiers scannes)."""
    per_file: dict[str, tuple[str, list[Verdict]]] = {}
    totals = {"occurrences": 0, "ok": 0, "moved": 0, "missing": 0, "pinned": 0}
    scanned = 0
    for path in collect_consumer_files(consumer, globs):
        rel = path.relative_to(consumer).as_posix()
        try:
            text = _read_text_newlines_intact(path)
        except (OSError, UnicodeDecodeError) as exc:
            print(f"AVERTISSEMENT : fichier illisible, ignore -- {rel} ({exc})",
                  file=sys.stderr)
            continue
        scanned += 1
        verdicts = [classify(l, tree_files, tree_dirs, ledger, branch)
                    for l in extract_links(text, owner_repo, branch)]
        per_file[rel] = (text, verdicts)
        for v in verdicts:
            totals[v.status] += 1
        totals["occurrences"] += len(verdicts)
    return per_file, totals, scanned


def _occurrence_dict(consumer: Path, rel: str, v: Verdict) -> dict:
    return {
        "consumer": str(consumer),
        "file": rel,
        "line": v.link.line,
        "url": v.link.url,
        "kind": v.link.kind,
        "path": v.link.path,
        "status": v.status,
        "suggestion": v.suggestion,
        "via": v.via,
        "candidates": v.candidates,
    }


_STATUS_ORDER = ("occurrences", "ok", "moved", "missing", "pinned")


def _print_markdown(consumers_report: list[dict]) -> None:
    print("| Fichier | Ligne | Statut | Cible | Suggestion | Via |")
    print("|---|---|---|---|---|---|")
    rows = 0
    for c in consumers_report:
        for occ in c["occurrences"]:
            if occ["status"] == "ok":
                continue
            sug = occ["suggestion"] or ""
            via = occ["via"] or ""
            print(f"| {occ['file']} | {occ['line']} | {occ['status']} "
                  f"| {occ['path']} | {sug} | {via} |")
            rows += 1
    t = consumers_report[-1]["_overall"] if consumers_report else {}
    print(f"\nOccurrences non-ok listees : {rows} "
          f"(moved {t.get('moved', 0)}, missing {t.get('missing', 0)}, "
          f"pinned {t.get('pinned', 0)}) sur {t.get('occurrences', 0)}.")


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(
        description="Controle des liens d'un depot consommateur externe vers CoursIA.")
    ap.add_argument("--consumer", action="append", required=True, metavar="DIR",
                    help="dossier local du consommateur (repeatable)")
    ap.add_argument("--glob", action="append", metavar="PATTERN",
                    help=f"glob de fichiers a scanner (repeatable, defaut {DEFAULT_GLOB})")
    ap.add_argument("--repo-root", metavar="DIR",
                    help="racine du depot CoursIA (defaut : celui du script)")
    ap.add_argument("--ref", default="HEAD",
                    help="ref git de l'arbre de reference (defaut HEAD)")
    ap.add_argument("--owner-repo", default=DEFAULT_OWNER_REPO, metavar="OWNER/REPO")
    ap.add_argument("--branch", default=DEFAULT_BRANCH,
                    help="seule branche verifiee ; les autres -> pinned")
    ap.add_argument("--ledger", default=LEDGER_RELPATH,
                    help="registre de renommage, relatif a --repo-root")
    fmt = ap.add_mutually_exclusive_group()
    fmt.add_argument("--json", action="store_true", help="sortie machine")
    fmt.add_argument("--markdown", action="store_true", help="tableau markdown")
    ap.add_argument("--all", action="store_true",
                    help="inclure aussi les occurrences ok dans la liste")
    ap.add_argument("--apply", action="store_true",
                    help="recrire les liens moved dans le consommateur (defaut dry-run)")
    args = ap.parse_args(argv)

    repo_root = Path(args.repo_root).resolve() if args.repo_root else REPO_ROOT
    owner_repo = args.owner_repo.strip("/")
    globs = args.glob or [DEFAULT_GLOB]

    consumers: list[Path] = []
    for c in args.consumer:
        p = Path(c)
        if not p.is_dir():
            print(f"ERREUR : consommateur absent ou non-dossier : {c}", file=sys.stderr)
            return 2
        consumers.append(p)

    try:
        tree_files, tree_dirs = load_tree(repo_root, args.ref)
    except OrganError as exc:
        print(f"ERREUR : {exc}", file=sys.stderr)
        return 2

    ledger = load_ledger(repo_root / args.ledger)
    if not ledger:
        print(f"AVERTISSEMENT : registre vide ou absent ({args.ledger}) -- "
              f"relocalisation par registre inactive.", file=sys.stderr)

    consumers_report: list[dict] = []
    overall = {"occurrences": 0, "ok": 0, "moved": 0, "missing": 0, "pinned": 0}
    scans: list[tuple[Path, dict[str, tuple[str, list[Verdict]]]]] = []
    for consumer in consumers:
        per_file, totals, scanned = _scan_consumer(
            consumer, globs, owner_repo, args.branch, tree_files, tree_dirs, ledger)
        scans.append((consumer, per_file))
        occurrences: list[dict] = []
        for rel, (_text, verdicts) in per_file.items():
            for v in verdicts:
                if v.status != "ok" or args.all:
                    occurrences.append(_occurrence_dict(consumer, rel, v))
        for k in overall:
            overall[k] += totals[k]
        consumers_report.append({
            "consumer": str(consumer),
            "files_scanned": scanned,
            "totals": totals,
            "occurrences": occurrences,
            "_overall": overall,
        })

    if args.json:
        payload = {
            "owner_repo": owner_repo,
            "branch": args.branch,
            "ref": args.ref,
            "consumers": [
                {k: c[k] for k in ("consumer", "files_scanned", "totals", "occurrences")}
                for c in consumers_report
            ],
            "totals": overall,
        }
        print(json.dumps(payload, indent=2, ensure_ascii=False))
    elif args.markdown:
        _print_markdown(consumers_report)
    else:
        for c in consumers_report:
            print(f"Consommateur : {c['consumer']}")
            t = c["totals"]
            print(f"  Fichiers scannes : {c['files_scanned']} ; occurrences : "
                  f"{t['occurrences']} (ok {t['ok']}, moved {t['moved']}, "
                  f"missing {t['missing']}, pinned {t['pinned']})")
            for occ in c["occurrences"]:
                print(f"  {occ['file']}:{occ['line']} [{occ['kind']}] {occ['status']}")
                print(f"    URL        : {occ['url']}")
                print(f"    chemin     : {occ['path']}")
                if occ["suggestion"]:
                    print(f"    suggestion : {occ['suggestion']} (via {occ['via']})")
                if occ["candidates"]:
                    print(f"    candidats  : {', '.join(occ['candidates'])}")
        print(f"TOTAL : {overall['occurrences']} occurrences "
              f"(ok {overall['ok']}, moved {overall['moved']}, "
              f"missing {overall['missing']}, pinned {overall['pinned']})")

    if args.apply:
        for consumer, per_file in scans:
            for rel, (text, verdicts) in per_file.items():
                new_text, n = apply_fixes(text, verdicts)
                if n:
                    _write_text_newlines_intact(consumer / rel, new_text)
                    print(f"[apply] {rel} : {n} remplacement(s) ecrit(s)")
        # Re-evaluation sur l'arbre RE-ECRIT : le code de sortie decrit l'etat
        # des fichiers du consommateur APRES le geste, pas avant.
        moved_left = missing_left = 0
        for consumer in consumers:
            _, totals2, _scanned = _scan_consumer(
                consumer, globs, owner_repo, args.branch,
                tree_files, tree_dirs, ledger)
            moved_left += totals2["moved"]
            missing_left += totals2["missing"]
        return 1 if (moved_left or missing_left) else 0

    return 1 if (overall["moved"] or overall["missing"]) else 0


if __name__ == "__main__":
    sys.exit(main())
