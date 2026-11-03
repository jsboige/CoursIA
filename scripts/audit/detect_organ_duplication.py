#!/usr/bin/env python3
"""Detecteur de duplication d'organe (#16776, fille de #13564 ; Lean : #20210).

Sert la regle .claude/rules/organ-first-implementation.md (merge #16778) :
avant de reimplementer une semantique qu'une autre serie possede deja,
une PR doit nommer l'organe (5 questions) ou declarer une copie
pedagogique dans son body.

Scan un diff (mode --patch ou --base) et repere les symboles AJOUTES qui
collisionnent avec un index des organes, dans un fichier hors de la serie
proprietaire de l'organe. Deux familles, deux sources :

- Python : index curate a la main (section ``series`` de
  scripts/audit/organ_api_index.yaml), symboles def/class ajoutes ;
- Lean (#20210) : index DERIVE A L'EXECUTION des lakes de l'arbre de base
  (jamais committe : un index fige se perime au premier ``def`` ajoute).
  Toute declaration ajoutee (structure, def, theorem, lemma, instance,
  abbrev, inductive, class) est comparee aux definitions des autres lakes,
  plus la citation de source : une ligne de commentaire citant ``R<n>`` et
  ``Annexe <X>`` (ex. ``R16 Annexe A``) deja citee par un autre lake.

Une phrase de copie declaree dans le body de la PR blanchit les collisions
(la porte de sortie vit dans le body). Les jumeaux ``X.lean`` / ``X_en.lean``
d'un meme lake partagent leur serie proprietaire : ils ne se signalent pas.

Sous-modules (#13902, item 4) : une collision avec un organe de la section
``submodules`` (les cinq depots sous-modules) exige la section « ce que cette
extraction rend a l'amont » (ou « ne rend rien ») -- la copie declaree seule
ne blanchit pas : extraire l'ame d'un sous-module sans nommer le contrat de
retour est l'affaiblissement que l'EPIC interdit.

Sortie : une ligne par collision au format
  COLLISION <serie demandeuse|?> (<fichier>) -> <serie organe> (<symbole>)
--check : exit 1 si au moins une collision non declaree.
--emit-lean-index : imprime l'index Lean derive (inspection, sur stdout).
"""

import argparse
import io
import json
import os
import re
import subprocess
import sys
import tarfile
from collections import defaultdict
from pathlib import Path

try:
    import yaml
except ImportError:  # pragma: no cover
    print("ERROR: PyYAML requis (pip install pyyaml)", file=sys.stderr)
    sys.exit(2)

REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_INDEX = Path(__file__).resolve().parent / "organ_api_index.yaml"

DEF_RE = re.compile(r"(?:^|[\s\"'(])(?:def|class)\s+([A-Za-z_][A-Za-z0-9_]*)")
DIFF_FILE_RE = re.compile(r"^diff --git a/(.+?) b/(.+?)(?:\s|$)")
HUNK_RE = re.compile(r"^@@ -\d+(?:,\d+)? \+(\d+)(?:,\d+)? @@")

# Formes acceptees pour la declaration : « copie pedagogique declarée »
# (forme canonique de la regle) et « copie fidèle » (forme retroactive du
# cas Greffe2, PR #13802). Les accents sont normalises avant matching.
DECLARATION_RE = re.compile(
    r"\bcopie\s+(?:pedagogique\s+)?(?:declaree|fidele)\b", re.IGNORECASE
)

# Contrat de retour amont (#13902, item 4) : une collision avec un organe
# SUBMODULE (les cinq depots sous-modules de .gitmodules, geste de perennite)
# n'est pas blanchie par la seule copie declaree -- le body doit dire ce que
# l'extraction rend a l'amont, ou declarer explicitement ne rien rendre.
PAYBACK_RE = re.compile(
    r"rend\w*\s+a\s+l['’]\s*amont"
    r"|cette\s+extraction\s+rend"
    r"|ne\s+rend\s+rien",
    re.IGNORECASE,
)

# --- Lean (#20210) ----------------------------------------------------------

# Declaration en tete de ligne de CODE (commentaires deja retires par mask_lean).
# Le nom s'arrete a l'espace, a la parenthese, au deux-points, a l'accolade.
LEAN_DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|unsafe|partial|nonrec)\s+)*"
    r"(structure|class|inductive|def|abbrev|theorem|lemma|instance)\s+([^\s:(){}\[\]⟨⟩,;@]+)"
)
# Seules les definitions forment l'index (organe = objets definis) ; theorem,
# lemma et instance sont scannes dans le diff mais ne sont pas indexes (noms de
# preuves, 3700 sur 5400 : bruit sans signal d'organe).
LEAN_INDEX_KINDS = frozenset({"structure", "class", "inductive", "def", "abbrev"})
LEAN_MIN_NAME_LEN = 4  # Aut, out, gid, c2 : trop courts pour etre distinctifs
LEAN_ARTICLE_RE = re.compile(r"\bR(\d{1,3})\b")
LEAN_ANNEX_RE = re.compile(r"\b(?:Annexe|Appendix)\s+([A-Z])\b")  # Appendix = jumeau _en
LEAN_SKIP_DIRS = frozenset({".lake", "reference_docs", "foundry-lib", "upstream", "node_modules"})
LEAN_TREE_DIR = "MyIA.AI.Notebooks"
LEAN_PATHSPECS = (":(glob)MyIA.AI.Notebooks/**/*.lean", ":(glob)MyIA.AI.Notebooks/**/lakefile.*")

# Fixtures du detecteur lui-meme : ses propres tests ajoutent des lignes
# « class <symbole> » DANS des chaines de patch de test -- ce ne sont pas des
# extractions, et l'organe qui se flaggerait lui-meme rendrait son advisory
# inutilisable sur ses propres PRs. Exemption bornee a ce fichier seul.
SELF_FIXTURE_FILES = frozenset({
    "scripts/tests/test_detect_organ_duplication.py",
})


def strip_accents(text: str) -> str:
    import unicodedata
    nfd = unicodedata.normalize("NFD", text)
    return "".join(c for c in nfd if not unicodedata.combining(c))


def is_declared(body: str) -> bool:
    if not body:
        return False
    return bool(DECLARATION_RE.search(strip_accents(body)))


def is_payback(body: str) -> bool:
    if not body:
        return False
    return bool(PAYBACK_RE.search(strip_accents(body)))


def load_index(path: Path):
    """(owners, symbol_owners, submodule_names) : la section ``submodules``
    (#13902) charge les memes champs que ``series`` -- ses organes exigent le
    contrat de retour amont au lieu de la copie declaree."""
    data = yaml.safe_load(path.read_text(encoding="utf-8"))
    series = data.get("series") or {}
    if not isinstance(series, dict) or not series:
        raise SystemExit(f"ERROR: index {path} sans section 'series' exploitable")
    symbol_owners = {}
    owners = {}
    for name, entry in series.items():
        owner_path = str(entry.get("owner_path", "")).rstrip("/")
        owners[name] = owner_path
        for sym in entry.get("symbols") or []:
            symbol_owners.setdefault(str(sym), name)
    submodule_names = set()
    submodules = data.get("submodules") or {}
    for name, entry in submodules.items():
        owner_path = str(entry.get("owner_path", "")).rstrip("/")
        owners[name] = owner_path
        submodule_names.add(name)
        for sym in entry.get("symbols") or []:
            # setdefault : un symbole deja proprietaire cote series reste a
            # son premier proprietaire -- la curation exclut les doublons.
            symbol_owners.setdefault(str(sym), name)
    return owners, symbol_owners, submodule_names


def resolve_series(path: str, owners: dict):
    """Serie propriétaire du fichier = owner_path le plus long prefix du chemin.

    Fallback hors index : composant racine sous MyIA.AI.Notebooks (label
    informatif ~, pas une serie indexee).
    """
    best, best_len = None, -1
    for name, owner_path in owners.items():
        if owner_path and (path + "/").startswith(owner_path + "/") and len(owner_path) > best_len:
            best, best_len = name, len(owner_path)
    if best is None:
        parts = path.split("/")
        if len(parts) >= 2 and parts[0] == "MyIA.AI.Notebooks":
            return "~" + parts[1]
    return best


def parse_patch(patch_text: str, owners: dict, symbol_owners: dict):
    """Retourne [(file, series, symbol)] pour chaque def/class ajoute en collision."""
    collisions = []
    current_file = None
    for line in patch_text.splitlines():
        m = DIFF_FILE_RE.match(line)
        if m:
            current_file = m.group(2)
            continue
        if current_file is None or current_file in SELF_FIXTURE_FILES:
            continue
        if not line.startswith("+") or line.startswith("+++"):
            continue
        content = line[1:].lstrip()
        if content.startswith("#"):
            continue
        for sym_m in DEF_RE.finditer(line[1:]):
            sym = sym_m.group(1)
            owner = symbol_owners.get(sym)
            if owner is None:
                continue
            file_series = resolve_series(current_file, owners)
            if file_series == owner:
                continue
            collisions.append((current_file, file_series, owner, sym))
    return collisions


def mask_lean(text: str):
    """Separe, ligne par ligne, le code Lean et son commentaire.

    Commentaires : ``-- ...`` jusqu'a la fin de ligne ; ``/- ... -/`` imbriques
    (docstrings ``/--`` et modules ``/-!`` compris). Le contenu des chaines
    ``"..."`` est neutralise dans le code. Retourne deux listes, une entree
    par ligne du texte ; les positions ne sont pas conservees, seul le texte
    par ligne sert (regex de declaration sur le code, citations sur le
    commentaire).
    """
    code_lines, com_lines = [], []
    code, com = [], []
    depth = 0
    in_str = False
    line_comment = False
    i, n = 0, len(text)
    while i < n:
        ch = text[i]
        if ch == "\n":
            code_lines.append("".join(code))
            com_lines.append("".join(com))
            code, com = [], []
            line_comment = False
            i += 1
            continue
        if line_comment:
            com.append(ch)
            i += 1
            continue
        if depth > 0:
            if text.startswith("-/", i):
                depth -= 1
                com.append("  ")
                i += 2
            elif text.startswith("/-", i):
                depth += 1
                com.append("  ")
                i += 2
            else:
                com.append(ch)
                i += 1
            continue
        if in_str:
            if ch == "\\" and i + 1 < n and text[i + 1] != "\n":
                code.append("  ")
                i += 2
                continue
            if ch == '"':
                in_str = False
            code.append(" ")
            com.append(" ")
            i += 1
            continue
        if text.startswith("/-", i):
            depth += 1
            com.append("  ")
            i += 2
            continue
        if text.startswith("--", i):
            line_comment = True
            com.append(ch)
            i += 1
            continue
        if ch == '"':
            in_str = True
            code.append(" ")
            com.append(" ")
            i += 1
            continue
        code.append(ch)
        com.append(" ")
        i += 1
    code_lines.append("".join(code))
    com_lines.append("".join(com))
    return code_lines, com_lines


def lean_cite_keys(comment: str):
    """Citations de source d'une ligne de commentaire : ``R<n> Annexe <X>``.

    Exige l'article ET l'annexe sur la meme ligne (« Annexe A de R16 »,
    « Tegmark R16 Annexe A §1 », « Appendix A of R16 »). Un numero seul
    (« R16 `85712871` ») ne cite pas une section et ne produit aucune cle.
    """
    if not comment:
        return set()
    articles = LEAN_ARTICLE_RE.findall(comment)
    annexes = LEAN_ANNEX_RE.findall(comment)
    return {f"R{a} Annexe {x}" for a in articles for x in annexes}


def parse_added(patch_text: str):
    """Blocs de lignes ajoutees, par fichier : {fichier: [[(numero, texte), ...], ...]}.

    Un bloc = lignes ajoutees contigues dans un hunk (une suppression ou un
    contexte le coupe). Le numero est celui de la ligne dans le fichier
    resultant, lu dans l'en-tete ``@@ -a,b +c,d @@``.
    """
    blocks = {}
    current_file = None
    block = None
    new_line = 0
    for line in patch_text.splitlines():
        m = DIFF_FILE_RE.match(line)
        if m:
            current_file = m.group(2)
            block = None
            continue
        h = HUNK_RE.match(line)
        if h:
            new_line = int(h.group(1))
            block = None
            continue
        if current_file is None:
            continue
        if line.startswith("+") and not line.startswith("+++"):
            if block is None:
                block = []
                blocks.setdefault(current_file, []).append(block)
            block.append((new_line, line[1:]))
            new_line += 1
        elif line.startswith(" "):
            new_line += 1
            block = None
        else:
            block = None
    return blocks


def parse_lean(blocks: dict, owners: dict, symbol_owners: dict, source_owners: dict,
               read_full=None):
    """Collisions Lean : [(file, series, owner, symbole-ou-« source Rn Annexe X »)].

    ``read_full(path)`` rend le texte integral du fichier au head (mode git) ;
    il permet de masquer les commentaires sur le fichier entier, y compris un
    ajout dans une docstring ouverte plus haut. Sans lui (mode --patch), le
    masquage ne voit que le hunk : une ligne ouverte dans un commentaire
    anterieur au hunk est alors lue comme du code.
    """
    collisions = []
    seen = set()  # une collision par (unite, lake, symbole) : deux citations, ou FR + jumeau _en
    for file, file_blocks in blocks.items():
        if not file.endswith(".lean") or _lean_is_config(file):
            continue
        file_series = resolve_series(file, owners)
        unit = _lean_twin_unit(file)
        full = read_full(file) if read_full else None
        items = []
        if full is not None:
            code_lines, com_lines = mask_lean(full)
            for blk in file_blocks:
                for num, _ in blk:
                    if 0 < num <= len(code_lines):
                        items.append((code_lines[num - 1], com_lines[num - 1]))
        else:
            for blk in file_blocks:
                code_lines, com_lines = mask_lean("\n".join(text for _, text in blk))
                items.extend(zip(code_lines, com_lines))
        for code, com in items:
            found = []
            decl = LEAN_DECL_RE.match(code)
            if decl:
                sym = decl.group(2)
                owner = symbol_owners.get(sym)
                if owner is not None and owner != file_series:
                    found.append((owner, sym))
            for key in sorted(lean_cite_keys(com)):
                for owner in source_owners.get(key, []):
                    if owner != file_series:
                        found.append((owner, f"source {key}"))
            for owner, label in found:
                if (unit, owner, label) not in seen:
                    seen.add((unit, owner, label))
                    collisions.append((file, file_series, owner, label))
    return collisions


def _lean_is_config(path: str) -> bool:
    # lakefile.lean / lakefile.toml : configuration Lake. Leur prose decrit les
    # modules, elle n'en porte pas la semantique (ni declaration, ni citation indexee).
    return Path(path).name.startswith("lakefile")


def _lean_twin_unit(path: str) -> str:
    # X_en.lean et X.lean ne forment qu'une unite de rapport : meme collision sur les deux
    # = une ligne (le jumeau ne double pas le frere).
    return re.sub(r"_en\.lean$", ".lean", path)


def _lean_skip_dir(name: str) -> bool:
    # Lakes externes : dossiers *_peters (dependance Lake, rule lean-i18n §Lean).
    return name in LEAN_SKIP_DIRS or name.endswith("_peters")


# --- Source de l'index Lean (derive a l'execution) ---------------------------

def lean_files_from_tree(root: Path):
    """[(chemin depot posix, texte)] des .lean et lakefile.* sous MyIA.AI.Notebooks de ``root``."""
    base = root / LEAN_TREE_DIR
    files = []
    if not base.is_dir():
        return files
    for dirpath, dirnames, filenames in os.walk(base):
        dirnames[:] = [d for d in dirnames if not _lean_skip_dir(d)]
        for name in filenames:
            if name.endswith(".lean") or name.startswith("lakefile."):
                path = Path(dirpath) / name
                rel = path.relative_to(root).as_posix()
                files.append((rel, path.read_text(encoding="utf-8", errors="replace")))
    return files


def lean_files_from_git(ref: str, cwd: Path):
    """[(chemin depot posix, texte)] au ``ref`` : un seul ``git archive``, pas de checkout."""
    proc = subprocess.run(
        ["git", "archive", "--format=tar", ref, "--", *LEAN_PATHSPECS],
        capture_output=True, cwd=str(cwd), check=True,
    )
    files = []
    with tarfile.open(fileobj=io.BytesIO(proc.stdout)) as tar:
        for member in tar.getmembers():
            if not member.isfile():
                continue
            name = member.name
            if name.endswith(".lean") or Path(name).name.startswith("lakefile."):
                text = tar.extractfile(member).read().decode("utf-8", errors="replace")
                files.append((name, text))
    return files


def build_lean_index(files):
    """Index Lean derive des fichiers ``[(chemin depot posix, texte)]``.

    Retourne {nom_lake: {owner_path, organ, sources, symbols}} :
    - lake = dossier contenant ``lakefile.lean`` ou ``lakefile.toml`` ;
    - symboles = definitions (structure/class/inductive/def/abbrev) dont le nom
      est declare dans UN SEUL lake de l'arbre (tout genre confondu : un nom de
      theoreme dans un autre lake le rend ambigu), de LEAN_MIN_NAME_LEN
      caracteres au moins ;
    - sources = citations ``R<n> Annexe <X>`` relevees dans les commentaires du lake.
    Pure : aucune E/S, donc testable sur un faux arbre en memoire.
    """
    lake_dirs = {}  # dossier posix -> nom de lake
    lean_files = []
    for rel, text in files:
        parts = rel.split("/")
        if any(_lean_skip_dir(p) for p in parts[:-1]):
            continue
        name = parts[-1]
        if name in ("lakefile.lean", "lakefile.toml"):
            if len(parts) >= 2:
                lake_dirs["/".join(parts[:-1])] = parts[-2]
        elif name.endswith(".lean") and not _lean_is_config(name):
            lean_files.append((rel, text))

    # Nom de lake = nom du dossier ; en cas de doublon, le chemin complet (pas d'echec).
    basenames = list(lake_dirs.values())
    lake_name = {
        path: (base if basenames.count(base) == 1 else path)
        for path, base in lake_dirs.items()
    }

    def owner_of(rel: str):
        parts = rel.split("/")
        for i in range(len(parts) - 1, 0, -1):
            prefix = "/".join(parts[:i])
            if prefix in lake_dirs:
                return prefix
        return None

    decl_owners = defaultdict(set)   # nom -> {lake ou ''} tous genres
    lake_symbols = defaultdict(set)  # lake -> definitions
    lake_sources = defaultdict(set)  # lake -> citations
    for rel, text in lean_files:
        lake_dir = owner_of(rel)
        key = lake_name[lake_dir] if lake_dir is not None else ""
        code_lines, com_lines = mask_lean(text)
        for code, com in zip(code_lines, com_lines):
            decl = LEAN_DECL_RE.match(code)
            if decl:
                decl_owners[decl.group(2)].add(key)
                if key and decl.group(1) in LEAN_INDEX_KINDS:
                    lake_symbols[key].add(decl.group(2))
            if key:
                lake_sources[key].update(lean_cite_keys(com))

    lakes = {}
    for lake_dir, name in sorted(lake_name.items(), key=lambda kv: kv[1]):
        symbols = sorted(
            s for s in lake_symbols[name]
            if len(s) >= LEAN_MIN_NAME_LEN and decl_owners[s] == {name}
        )
        lakes[name] = {
            "owner_path": lake_dir,
            "organ": f"lake Lean {name} -- definitions publiques (index derive, #20210)",
            "sources": sorted(lake_sources[name]),
            "symbols": symbols,
        }
    return lakes


def lean_maps(lakes: dict):
    """(owners, symbol_owners, source_owners) depuis l'index derive, au format de parse_lean."""
    owners, symbol_owners, source_owners = {}, {}, {}
    for name, entry in lakes.items():
        owners[name] = entry["owner_path"]
        for sym in entry["symbols"]:
            symbol_owners.setdefault(sym, name)
        for key in entry["sources"]:
            holders = source_owners.setdefault(key, [])
            if name not in holders:
                holders.append(name)
    return owners, symbol_owners, source_owners


def render_lean_block(lakes: dict) -> str:
    """Rendu YAML de l'index derive (inspection via --emit-lean-index, jamais committe)."""
    out = ["lean_series:"]
    for name in sorted(lakes):
        entry = lakes[name]
        out.append(f"  {name}:")
        out.append(f"    owner_path: {entry['owner_path']}")
        out.append(f"    organ: {json.dumps(entry['organ'], ensure_ascii=False)}")
        if entry["sources"]:
            out.append("    sources:")
            out.extend(f"      - {json.dumps(s, ensure_ascii=False)}" for s in entry["sources"])
        else:
            out.append("    sources: []")
        if entry["symbols"]:
            out.append("    symbols:")
            out.extend(f"      - {json.dumps(s, ensure_ascii=False)}" for s in entry["symbols"])
        else:
            out.append("    symbols: []")
    return "\n".join(out) + "\n"


def git_diff(base: str, head: str, cwd: Path) -> str:
    result = subprocess.run(
        ["git", "diff", f"{base}...{head}", "--unified=0"],
        capture_output=True, text=True, cwd=str(cwd), check=True,
        encoding="utf-8", errors="replace",
    )
    return result.stdout


def git_show(ref: str, path: str, cwd: Path):
    result = subprocess.run(
        ["git", "show", f"{ref}:{path}"], capture_output=True, cwd=str(cwd),
    )
    if result.returncode != 0:
        return None
    return result.stdout.decode("utf-8", errors="replace")


def git_merge_base(base: str, head: str, cwd: Path) -> str:
    result = subprocess.run(
        ["git", "merge-base", base, head], capture_output=True, text=True, cwd=str(cwd),
        encoding="utf-8", errors="replace",
    )
    found = result.stdout.strip()
    return found if result.returncode == 0 and found else base


def lean_source_files(args, cwd: Path):
    """Fichiers Lean de l'arbre de base, d'ou se derive l'index.

    --lean-root : arbre explicite (fixture, inspection). --patch sans --lean-root :
    arbre de travail de ce depot. Mode git : l'ancetre commun de --base et --head,
    lu dans git (l'etat AVANT la PR, jamais le head).
    """
    if args.lean_root is not None:
        return lean_files_from_tree(args.lean_root)
    if args.patch:
        return lean_files_from_tree(REPO_ROOT)
    return lean_files_from_git(git_merge_base(args.base, args.head, cwd), cwd)


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--patch", help="fichier diff unifie a scanner (mode hors git)")
    parser.add_argument("--base", help="ref de base pour git diff (defaut origin/main)")
    parser.add_argument("--head", default="HEAD", help="ref de tete (defaut HEAD)")
    parser.add_argument("--body-file", help="fichier contenant le body de la PR")
    parser.add_argument("--body", help="body de la PR en ligne")
    parser.add_argument("--index", type=Path, default=DEFAULT_INDEX,
                        help="index Python (section series)")
    parser.add_argument("--check", action="store_true",
                        help="exit 1 si collision non declaree")
    parser.add_argument("--cwd", type=Path, default=None)
    parser.add_argument("--lean-root", type=Path, default=None,
                        help="arbre dont l'index Lean est derive (contient MyIA.AI.Notebooks)")
    parser.add_argument("--emit-lean-index", action="store_true",
                        help="imprime l'index Lean derive (--lean-root, defaut ce depot) et sort")
    args = parser.parse_args(argv)

    if args.emit_lean_index:
        root = args.lean_root if args.lean_root is not None else REPO_ROOT
        print(render_lean_block(build_lean_index(lean_files_from_tree(root))), end="")
        return 0

    if not args.patch and not args.base:
        args.base = "origin/main"

    owners, symbol_owners, submodule_names = load_index(args.index)
    cwd = args.cwd or Path.cwd()

    if args.patch:
        patch_text = Path(args.patch).read_text(encoding="utf-8", errors="replace")
        read_full = None
    else:
        patch_text = git_diff(args.base, args.head, cwd)
        read_full = lambda path: git_show(args.head, path, cwd)  # noqa: E731

    body = args.body if args.body is not None else (
        Path(args.body_file).read_text(encoding="utf-8", errors="replace")
        if args.body_file else ""
    )
    declared = is_declared(body)
    payback = is_payback(body)

    collisions = parse_patch(patch_text, owners, symbol_owners)
    blocks = parse_added(patch_text)
    lean_owners = {}
    if any(f.endswith(".lean") for f in blocks):
        # L'index Lean n'est construit que si le diff touche du Lean : un diff Python
        # ne paie ni le parcours de l'arbre ni le masquage.
        lean_owners, lean_symbols, lean_sources = lean_maps(
            build_lean_index(lean_source_files(args, cwd)))
        collisions += parse_lean(blocks, lean_owners, lean_symbols, lean_sources, read_full)

    undeclared = []
    for file, file_series, owner, sym in collisions:
        origin = file_series if file_series else "?"
        if owner in submodule_names:
            # Contrat #13902 : la copie declaree ne suffit pas, seule la
            # section de retour amont blanchit une extraction de sous-module.
            if payback:
                print(f"EXEMPTED {origin} ({file}) -> {owner} ({sym}) [retour amont declare]")
            else:
                print(f"COLLISION {origin} ({file}) -> {owner} ({sym}) "
                      f"[retour amont manquant -- #13902]")
                undeclared.append((file, owner, sym))
        elif declared:
            print(f"EXEMPTED {origin} ({file}) -> {owner} ({sym}) [copie declaree]")
        else:
            print(f"COLLISION {origin} ({file}) -> {owner} ({sym})")
            undeclared.append((file, owner, sym))

    status = "EXEMPTED" if collisions and not undeclared else (
        "BLOCKED" if undeclared else "CLEAN"
    )
    print(f"{status}  {len(collisions)} collision(s), {len(undeclared)} non declaree(s), "
          f"{len(owners) - len(submodule_names)} series + {len(submodule_names)} submodules "
          f"dans l'index, {len(lean_owners)} lakes Lean")

    if args.check and undeclared:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
