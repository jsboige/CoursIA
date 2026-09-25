#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Renommage canonique d'une serie de notebooks (#17784, chantier A de #16231).

PRINCIPE -- organe d'abord : les gardes existants DETECTENT les liens casses
apres coup (`check_duplicate_notebook_index`, `check_notebook_navlinks`,
`check_link_label_agreement`, `check_twin_parity`, `check_kernel_suffix_canon`),
aucun ne FAIT le renommage. Chaque tranche refaisait donc son balayage a la
main, avec la meme classe de defauts a chaque fois (tableau d'ouverture de
#17784). Cet outil fait le renommage en une commande, dans l'ordre qui garde
les gardes verts.

GRAMMAIRE (arbitrage mainteneur 25/09, #16231 c.5829840595) :

    <Prefixe>-<NN><lettre?>-<Titre>[-Part<N>]-<Noyau>[_<langue>].ipynb
    Noyau : Python | CSharp | Lean | Lean-Python

- le suffixe de noyau est TOUJOURS present et TOUJOURS en dernier ;
- le titre ne repete ni le prefixe ni le noyau (infixe redondant retire) ;
- `-Native`, `-Lean-Native`, `-Lean-Companion`, `-Companion` resorbes ;
- un numero ou une lettre ne se propose JAMAIS : la renumerotation reste un acte
  pedagogique (notebook-accretion-numbering). L'outil ne touche qu'au padding
  du numero, au suffixe de noyau et a la redondance du titre.

INVARIANTS DURS -- les defauts du tableau d'ouverture sont des regressions de
ces invariants, pas des details :

  I1  edition AU TEXTE, jamais par re-serialisation JSON : les remplacements
      sont des sous-chaines du fichier tel qu'il est ecrit ; hors ces
      sous-chaines le fichier reste identique OCTET PAR OCTET. C'est par un
      json.load/json.dump qu'une cellule ancienne est revenue en #17363.
      Garde verifiee APRES la passe : re-parse + comparaison structurelle.
  I2  cellules de code : JAMAIS reecrites -- listees, avec la re-execution C.2
      qu'elles demandent. Fail-closed : si un fichier melange referents
      reescrivables et referents en cellule de code, le fichier ENTIER est
      refuse et liste (jamais de remplacement partiel au petit bonheur).
  I3  sorties commitees : JAMAIS touchees (secrets-hygiene regle 6) -- listees.
  I4  historique, catalogue, fixtures declarees : exclus par listes explicites.
  I5  dry-run par defaut ; `--apply` explicite.
  I6  deux commits : 1 = `git mv` seuls, 2 = referents (une PR = un sujet).

USAGE
-----
    python scripts/notebook_tools/rename_notebooks.py --propose MyIA.AI.Notebooks/SymbolicAI/Lean
    python scripts/notebook_tools/rename_notebooks.py --mapping table.tsv            (dry-run)
    python scripts/notebook_tools/rename_notebooks.py --mapping table.tsv --apply
    python scripts/notebook_tools/rename_notebooks.py --mapping issue:16231#5788043716
    python scripts/notebook_tools/rename_notebooks.py --rebase-helper [--apply]

Sortie : 0 = plan/execution completes ; 1 = refus (collision, fichier absent,
surfaces melangees) ; 2 = erreur d'invocation.
"""
from __future__ import annotations

import argparse
import datetime
import json
import os
import re
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

_here = str(Path(__file__).resolve().parent)
if _here not in sys.path:
    sys.path.insert(0, _here)

LEDGER_RELPATH = "docs/reference/rename-ledger.tsv"

# ---------------------------------------------------------------------------
# Grammaire
# ---------------------------------------------------------------------------

# Familles de noyaux -> suffixe canonique. Les noms effectivement presents dans
# l'arbre (mesure naming_canon/check_kernel_suffix_canon). Un kernelspec absent
# de la table tombe en `A TRANCHER`, jamais devine en silence.
PYTHON_KERNELS = {"python3", "python3-wsl", "python3-coursia2", "python3-lean",
                  "coursia-ml-training", "conda-torch", "pyphi", "global-3.13",
                  "pycharm"}
CSHARP_KERNELS = {".net-csharp"}
LEAN_KERNELS = {"lean4", "lean4-wsl", "lean4-wsl-conway", "lean4-wsl-groth16200",
                "lean4-wsl-perc"}

# Queue de titre legacy a resorber quand le noyau est Lean/Lean-Python, au
# profit du suffixe canonique. Ordre : plus long d'abord, resorption repetee.
LEAN_LEGACY_TAILS = ("-lean-native", "-lean-companion", "-native", "-companion", "-lean")

# Temoin qu'un notebook Python PILOTE reellement Lean (suffixe -Lean-Python) :
# appel subprocess d'un binaire lake/lean, wrapper dedie, ou pont LeanDojo/REPL.
LEAN_DRIVE_RES = (
    re.compile(r'subprocess\.\w+\([^)]*["\'](?:lake|lean)["\']', re.S),
    re.compile(r'\brun_lake\s*\('),
    re.compile(r'\bfrom\s+lean_dojo\b|\blean_dojo\b|LeanDojo\.'),
    re.compile(r'lean4_repl|LeanREPL|repl_mode', re.I),
    # Appel lake/lean DANS une chaine de commande (f-string incluse) : le
    # pilotage reel est souvent indirect -- `run_wsl(f"cd {dir} && lake build
    # X")` passe le binaire dans une variable, seul le litteral temoigne
    # (mesure ai-01 : Tweety-02d/3b/5d/5e invisibles aux quatre motifs ci-dessus).
    re.compile(r'["\'][^"\']*\blake\s+(?:build|env|exe|check)\b', re.S),
    re.compile(r'["\'][^"\']*\blean\s+--run\b', re.S),
)

# Un nom qui porte une de ces queues pretend piloter Lean ; sous noyau Python
# SANS preuve citee, la cible ne se devine pas (review #17801 point 2).
LEAN_CLAIM_TAILS = LEAN_LEGACY_TAILS

# Exclusions EXPLICITES (I4) : jamais devinees par heuristique.
EXCLUDED_BASENAMES = {"research.ipynb"}
EXCLUDED_DIR_PARTS = {"_archive", ".lake", "student", "results", "__pycache__",
                      "node_modules", "_peters"}
EXCLUDED_NAME_SUFFIXES = ("_output.ipynb",)
# Chemins dont l'HISTOIRE cite des noms par nature (ledgers, archives) : la
# reecriture y fabriquerait du revisionnisme de registre.
HISTORY_DIR_MARKERS = ("docs/archive", "docs/ledgers", "scripts/results",
                       "_archive", ".lake", ".git")
CATALOG_BASENAME_PREFIX = "COURSE_CATALOG.generated"

# Fixtures a nom volontairement NON reecrit : liste DECLAREE (chemins relatifs
# au depot), remplie par chaque tranche pour ses propres series.
FIXTURES_DECLARED: tuple[str, ...] = ()

STEM_RE = re.compile(r"^(?P<prefix>[A-Za-z][A-Za-z0-9]*)-(?P<num>\d+)(?P<accr>[a-z]?)(?P<sep>[-_])(?P<title>.+)$")
PART_RE = re.compile(r"[-_]Part(\d+)$", re.I)

_CAP_MAP = {"python": "Python", "csharp": "CSharp", "lean": "Lean"}


def _cap(suffix: str) -> str:
    """python->Python, csharp->CSharp, lean-python->Lean-Python."""
    return "-".join(_CAP_MAP.get(p, p.capitalize()) for p in suffix.split("-"))


# ---------------------------------------------------------------------------
# Racine du depot (resolue depuis git, testable sur un depot temporaire)
# ---------------------------------------------------------------------------

def repo_root() -> Path:
    try:
        r = subprocess.run(["git", "rev-parse", "--show-toplevel"],
                           capture_output=True, text=True, encoding="utf-8",
                           errors="replace")
        if r.returncode == 0:
            return Path(r.stdout.strip())
    except OSError:
        pass
    return Path(__file__).resolve().parents[2]


# ---------------------------------------------------------------------------
# Lecture du noyau d'un notebook (lecture seule : json.load OK, c'est la
# RE-ECRITURE de ce qu'on a parse qui est interdite, I1)
# ---------------------------------------------------------------------------

def kernel_of(nb: dict) -> str | None:
    ks = (nb.get("metadata") or {}).get("kernelspec") or {}
    name = ks.get("name")
    return name if isinstance(name, str) else None


def kernel_to_suffix(ks: str | None) -> str | None:
    if not ks:
        return None
    low = ks.strip().lower()
    if low in CSHARP_KERNELS or "csharp" in low:
        return "csharp"
    if low in LEAN_KERNELS or low.startswith("lean4"):
        return "lean"
    if low in PYTHON_KERNELS or low.startswith("python"):
        return "python"
    return None


def lean_drive_proof(nb: dict) -> tuple[int, str] | None:
    """Premier temoin (index de cellule, extrait) qu'un notebook Python pilote Lean."""
    for i, cell in enumerate(nb.get("cells", [])):
        if cell.get("cell_type") != "code":
            continue
        src = "".join(cell.get("source", []))
        for pat in LEAN_DRIVE_RES:
            m = pat.search(src)
            if m:
                excerpt = src[max(0, m.start() - 15):m.end() + 25].replace("\n", " ")
                return i, excerpt.strip()[:90]
    return None


# ---------------------------------------------------------------------------
# Nom canonique
# ---------------------------------------------------------------------------

def canonical_target(filename: str, kernel_suffix: str) -> str:
    """Nom canonique d'un fichier pour un suffixe de noyau donne.

    Ne renumerote JAMAIS : numero et lettre traversent tels quels, seul le
    zero-pad du numero est applique (mise en forme, pas choix d'index).
    """
    stem = re.sub(r"\.ipynb$", "", filename, flags=re.I)
    m = STEM_RE.match(stem)
    if not m:
        # Nom hors grammaire de serie (index nu, prefixe absent) : on se borne
        # a apposer le suffixe de noyau, acte minimal sans risque.
        return f"{stem}-{_cap(kernel_suffix)}.ipynb"
    prefix, num, accr = m.group("prefix"), m.group("num"), m.group("accr")
    title = m.group("title")

    part = ""
    pm = PART_RE.search(title)
    if pm:
        part = f"-Part{pm.group(1)}"
        title = title[: pm.start()]

    if kernel_suffix in ("lean", "lean-python"):
        # Resorption en point fixe : l'ordre des queues n'est pas garanti dans
        # le nom d'origine (`-Native-Companion` doit perdre les deux).
        changed = True
        while changed:
            changed = False
            low = title.lower()
            for leg in LEAN_LEGACY_TAILS:
                if low.endswith(leg):
                    title = title[: -len(leg)]
                    changed = True
                    break
        if prefix.lower() == "lean":             # infixe redondant avec le prefixe
            title = re.sub(r"^Lean[-_]", "", title, flags=re.I)
            title = re.sub(r"[-_]Lean(?=[-_]|$)", "", title, flags=re.I)

    # Le titre ne se termine jamais par le mot du noyau qu'on va apposer --
    # dans N'IMPORTELLE casse heritee (`-Csharp` compte, mesure de l'arbre :
    # 114 fichiers).
    title = re.sub(r"[-_]+(?:lean|python|csharp)$", "", title, flags=re.I)

    title = title.strip("-_ ")
    body = f"{title}{part}" if title else part.lstrip("-")
    return f"{prefix}-{num.zfill(2)}{accr}-{body}-{_cap(kernel_suffix)}.ipynb"


# Mot de noyau en INFIXE de titre : la grammaire l'exclut (le suffixe seul nomme
# le noyau). Une cible qui en porte un sera renommee une seconde fois -- review
# #17801 point 3 : elle tombe en A TRANCHER au lieu d'etre proposee.
_KERNEL_INFIX_RE = re.compile(r"[-_](?:lean|python|csharp)(?=[-_]|$)", re.I)
_FINAL_KERNEL_RE = re.compile(r"[-_]+(?:lean-python|lean|python|csharp)$", re.I)


def target_violation(new_name: str) -> str | None:
    """Pourquoi la cible calculee ne satisfait PAS elle-meme la grammaire.

    Renvoie None si la cible est canonique (STEM_RE + noyau en dernier, jamais
    en infixe), sinon la raison. Une cible non canonique promet un SECOND
    renommage : la ligne de la table doit tomber en A TRANCHER, pas etre livree.
    """
    stem = re.sub(r"\.ipynb$", "", new_name, flags=re.I)
    m = STEM_RE.match(stem)
    if not m:
        return "hors grammaire de serie (prefixe absent, index en tete ou separateur _)"
    core = _FINAL_KERNEL_RE.sub("", m.group("title"))
    core = PART_RE.sub("", core)
    if _KERNEL_INFIX_RE.search(core):
        return "mot de noyau en infixe du titre"
    return None


def is_excluded(rel: str) -> bool:
    parts = rel.split("/")
    name = parts[-1]
    if name in EXCLUDED_BASENAMES or name.startswith(CATALOG_BASENAME_PREFIX):
        return True
    if name.lower().endswith(EXCLUDED_NAME_SUFFIXES):
        return True
    if set(parts[:-1]) & EXCLUDED_DIR_PARTS:
        return True
    return False


def _is_history(rel: str) -> bool:
    parts = rel.split("/")
    if any(marker in parts for marker in HISTORY_DIR_MARKERS):
        return True
    # twin_pairs.d : le PREMIER niveau (paires) se reecrit, l'historique date
    # des sous-dossiers ne se reecrit pas.
    if "twin_pairs.d" in parts:
        i = parts.index("twin_pairs.d")
        if len(parts) > i + 2:
            return True
    return False


# ---------------------------------------------------------------------------
# --propose
# ---------------------------------------------------------------------------

@dataclass
class Row:
    old: str
    new: str
    kernel: str | None
    suffix: str
    verdict: str          # RENOMMAGE | CONFORME | A TRANCHER | EXCLU
    proof: str


def propose(series_dir: str, repo: Path | None = None) -> str:
    repo = repo or repo_root()
    root = repo / series_dir
    rows: list[Row] = []
    for p in sorted(root.rglob("*.ipynb")):
        rel = p.relative_to(repo).as_posix()
        if is_excluded(rel):
            rows.append(Row(rel, rel, None, "—", "EXCLU", "exclusion declaree"))
            continue
        try:
            nb = json.loads(p.read_text(encoding="utf-8"))
        except (OSError, ValueError):
            rows.append(Row(rel, rel, None, "?", "A TRANCHER", "notebook illisible"))
            continue
        ks = kernel_of(nb)
        suffix = kernel_to_suffix(ks)
        if suffix is None:
            rows.append(Row(rel, rel, ks, "?", "A TRANCHER", "noyau hors table"))
            continue
        proof = "—"
        final = suffix
        if suffix == "python":
            d = lean_drive_proof(nb)
            if d:
                final = "lean-python"
                proof = f"cell {d[0]} : `{d[1]}`"
        parent, name = rel.rsplit("/", 1) if "/" in rel else ("", rel)
        stem = re.sub(r"\.ipynb$", "", name, flags=re.I)
        if suffix == "python" and final == "python" \
                and stem.lower().endswith(LEAN_CLAIM_TAILS):
            # Le nom ACTUEL pretend piloter Lean ; sans preuve citee, apposer
            # -Python effacerait l'information et promettrait un second
            # renommage -- l'inverse du garde kernel_suffix de cette meme PR
            # (review #17801 point 2). On ne devine pas : on tranche.
            rows.append(Row(rel, rel, ks, "?", "A TRANCHER",
                            "portait -Lean sous noyau python sans preuve de "
                            "pilotage : trancher -Lean-Python (preuve a citer) "
                            "ou -Python"))
            continue
        new_name = canonical_target(name, final)
        viol = target_violation(new_name)
        if viol:
            rows.append(Row(rel, rel, ks, final, "A TRANCHER",
                            f"cible non canonique : {viol}"))
            continue
        new_rel = f"{parent}/{new_name}" if parent else new_name
        verdict = "CONFORME" if new_rel == rel else "RENOMMAGE"
        rows.append(Row(rel, new_rel, ks, final, verdict, proof))

    seen: dict[str, str] = {}
    for r in rows:
        if r.verdict in ("CONFORME", "EXCLU"):
            continue
        if r.new in seen:
            r.verdict = "A TRANCHER"
            r.proof = f"collision avec {seen[r.new]}"
        seen[r.new] = r.old

    lines = ["| Actuel | Cible | Noyau | Verdict | Preuve -Lean-Python |",
             "|---|---|---|---|---|"]
    for r in rows:
        lines.append(f"| `{r.old}` | `{r.new}` | {r.kernel} | {r.verdict} | {r.proof} |")
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Formes de reference
# ---------------------------------------------------------------------------

_KNOWN_TAILS = ("-lean-python", "-csharp", "-python", "-lean", "_en", "_fr")


@dataclass
class RefForms:
    """Formes textuelles sous lesquelles un ancien nom est cite."""
    old_rel: str
    new_rel: str
    full: str
    filename: str
    stem: str
    urlencoded: str
    abbrev: str            # Prefixe-NN<lettre> nu


def ref_forms(old_rel: str, new_rel: str) -> RefForms:
    filename = old_rel.rsplit("/", 1)[-1]
    stem = re.sub(r"\.ipynb$", "", filename, flags=re.I)
    m = STEM_RE.match(stem)
    abbrev = stem
    if m:
        abbrev = f"{m.group('prefix')}-{m.group('num')}{m.group('accr')}"
    return RefForms(old_rel, new_rel, old_rel, filename, stem,
                    stem.replace(" ", "%20"), abbrev)


def _new_stem(forms: RefForms) -> str:
    return re.sub(r"\.ipynb$", "", forms.new_rel.rsplit("/", 1)[-1], flags=re.I)


def _new_abbrev(forms: RefForms) -> str:
    m = STEM_RE.match(_new_stem(forms))
    return f"{m.group('prefix')}-{m.group('num')}{m.group('accr')}" if m else _new_stem(forms)


def _tail_of(stem: str) -> str:
    """Queue de suffixe de noyau telle qu'ECRITE dans le stem (casse d'origine),
    ou vide."""
    low = stem.lower()
    for t in _KNOWN_TAILS:
        if low.endswith(t):
            return stem[-len(t):]
    return ""


def build_patterns(forms_list: list[RefForms]) -> list[tuple[RefForms, re.Pattern[str], str, str]]:
    """(formes, motif, forme_ancienne, forme_nouvelle), alternatives triees par
    longueur decroissante pour que la forme la plus longue gagne (le chemin
    complet avant le nom de fichier avant le stem avant l'abrege)."""
    out: list[tuple[RefForms, re.Pattern[str], str, str]] = []
    for f in forms_list:
        new_stem = _new_stem(f)
        # Abregee PORTANTE du suffixe (defaut #17784 « abrege rate ») : elle
        # n'existe comme forme ANCIENNE que si l'ancien nom portait deja un
        # suffixe. L'abregee nue `Prefixe-NN` est un IDENTIFIANT DE SERIE
        # invariant : un renommage qui ajoute un suffixe ne la touche pas --
        # la reecrire fabriquerait « S-01-Python » dans chaque mention de
        # serie (mesure : premier jet de l'outil, test TestI1).
        old_tail = _tail_of(f.stem)
        pairs = [
            (f.full, f.new_rel),
            (f.filename, new_stem + ".ipynb"),
            (f.stem, new_stem),
            (f.urlencoded, new_stem.replace(" ", "%20")),
        ]
        if old_tail:
            pairs.append((f.abbrev + old_tail,
                          _new_abbrev(f) + _tail_of(new_stem)))
        for old, new in sorted({(o, n) for o, n in pairs if o != n},
                               key=lambda p: -len(p[0])):
            # Frontieres mot : le lookbehind n'exclut PAS `/` -- un referent
            # embarque dans un chemin relatif (`](sub/Notebook.ipynb)`,
            # `metadata.papermill.input_path`) est un referent comme un autre.
            # L'alternation triee par longueur decroissante fait que la forme
            # complete gagne avant que le stem ne puisse la recouper.
            pat = re.compile(r"(?<![\w-])" + re.escape(old) + r"(?![\w-])")
            out.append((f, pat, old, new))
    return out


# ---------------------------------------------------------------------------
# Scan des referents
# ---------------------------------------------------------------------------

@dataclass
class Plan:
    moves: list[tuple[str, str]] = field(default_factory=list)
    rewrites: dict[str, int] = field(default_factory=dict)      # fichier -> nb
    mixed_refused: list[str] = field(default_factory=list)      # ipynb I2/I3 fail-closed
    code_cells: list[tuple[str, int, str]] = field(default_factory=list)
    outputs: list[tuple[str, int, str]] = field(default_factory=list)
    fragmented: list[tuple[str, int]] = field(default_factory=list)


def scan_referents(forms_list: list[RefForms], repo: Path | None = None) -> Plan:
    repo = repo or repo_root()
    plan = Plan()
    pats = build_patterns(forms_list)
    ls = subprocess.run(["git", "ls-files"], cwd=repo, capture_output=True,
                        text=True, encoding="utf-8", errors="replace", check=True)
    for line in ls.stdout.splitlines():
        rel = line.strip()
        if not rel or _is_history(rel) or rel in FIXTURES_DECLARED:
            continue
        p = repo / rel
        if not p.is_file():
            continue
        try:
            raw = p.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError):
            continue
        raw_total = sum(len(pat.findall(raw)) for _, pat, _, _ in pats)

        if not rel.endswith(".ipynb"):
            if raw_total:
                plan.rewrites[rel] = raw_total
            continue

        try:
            nb = json.loads(raw)
        except ValueError:
            if raw_total:
                plan.mixed_refused.append(rel)
            continue

        # Reference FRAGMENTEE : la source JSON scinde le nom en elements de
        # liste -- la cellule JOINTE cite le nom mais le texte brut ne peut pas
        # le remplacer. Se detecte par ECART de comptage entre la source join
        # et sa serialization par elements, meme quand raw_total vaut 0.
        for i, cell in enumerate(nb.get("cells", [])):
            joined = "".join(cell.get("source", []))
            joined_hits = sum(len(pat.findall(joined)) for _, pat, _, _ in pats)
            if not joined_hits:
                continue
            blob_hits = sum(len(pat.findall(json.dumps(cell.get("source", []),
                                                        ensure_ascii=False)))
                            for _, pat, _, _ in pats)
            if blob_hits < joined_hits:
                plan.fragmented.append((rel, i))
        if not raw_total:
            continue

        # Comptage par surface : markdown + metadata top-niveau = REESCRIRE ;
        # code / sorties = JAMAIS (I2/I3). Un nom ne contient aucun caractere
        # echappable en JSON : chaque occurrence du texte brut vit entierement
        # dans une seule chaine JSON, les deux comptages sont comparables.
        allowed = 0
        for cell in nb.get("cells", []):
            if cell.get("cell_type") == "code":
                continue
            blob = json.dumps(cell, ensure_ascii=False)
            allowed += sum(len(pat.findall(blob)) for _, pat, _, _ in pats)
        meta_blob = json.dumps(nb.get("metadata") or {}, ensure_ascii=False)
        allowed += sum(len(pat.findall(meta_blob)) for _, pat, _, _ in pats)

        if raw_total > allowed:
            # Fail-closed I2/I3 : le fichier melange surfaces reescrivables et
            # protegees, ou porte une occurrence hors zones connues.
            plan.mixed_refused.append(rel)
        elif allowed:
            plan.rewrites[rel] = allowed

        for i, cell in enumerate(nb.get("cells", [])):
            joined = "".join(cell.get("source", []))
            cell_hit = [old for _, pat, old, _ in pats if pat.search(joined)]
            for old in cell_hit[:1]:
                if cell.get("cell_type") == "code":
                    plan.code_cells.append((rel, i, old))
            for out in cell.get("outputs", []) or []:
                blob = json.dumps(out, ensure_ascii=False)
                for _, pat, old, _ in pats:
                    if pat.search(blob):
                        plan.outputs.append((rel, i, old))
                        break
    return plan


# ---------------------------------------------------------------------------
# --mapping : chargement (TSV ou commentaire d'issue)
# ---------------------------------------------------------------------------

MD_ROW_RE = re.compile(r"^\|\s*`([^`]+)`\s*\|\s*`([^`]+)`")


def load_mapping(src: str, repo: Path | None = None) -> list[tuple[str, str]]:
    repo = repo or repo_root()
    if src.startswith("issue:"):
        spec = src[len("issue:"):]
        _issue, _, cid = spec.partition("#")
        if not cid:
            raise SystemExit("forme attendue : issue:<N>#<id-commentaire>")
        r = subprocess.run(
            ["gh", "api", f"repos/jsboige/CoursIA/issues/comments/{cid}",
             "--jq", ".body"],
            cwd=repo, capture_output=True, text=True, encoding="utf-8",
            errors="replace")
        if r.returncode != 0:
            raise SystemExit(f"gh api a echoue : {r.stderr.strip()[:200]}")
        pairs: list[tuple[str, str]] = []
        for line in r.stdout.splitlines():
            m = MD_ROW_RE.match(line)
            if not m:
                continue
            old, new = m.group(1).strip(), m.group(2).strip()
            if old == new or "CONFORME" in line or "A TRANCHER" in line:
                continue
            pairs.append((old, new))
        if not pairs:
            raise SystemExit(f"aucune ligne de table exploitable dans {spec}")
        return pairs
    p = Path(src)
    pairs = []
    for line in p.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        parts = line.split("\t")
        if len(parts) < 2:
            continue
        old, new = parts[0].strip(), parts[1].strip()
        if old and new and old != new:
            pairs.append((old, new))
    if not pairs:
        raise SystemExit(f"aucune ligne exploitable dans {src}")
    return pairs


# ---------------------------------------------------------------------------
# Application des reecritures (I1 : au texte, garde structurelle apres coup)
# ---------------------------------------------------------------------------

def rewrite_file(p: Path, forms_list: list[RefForms]) -> int:
    """Reecrit AU TEXTE un fichier dont toutes les occurrences sont en surfaces
    autorisees. Rend le nombre de remplacements effectues. Leve SystemExit si
    la garde structurelle echoue -- dans ce cas rien n'est ecrit."""
    raw = p.read_text(encoding="utf-8")
    edited = raw
    total = 0
    for _f, pat, _old, new in build_patterns(forms_list):
        edited, k = pat.subn(new, edited)
        total += k
    if total == 0 or edited == raw:
        return 0
    if p.name.lower().endswith(".ipynb"):
        try:
            a, b = json.loads(raw), json.loads(edited)
            assert len(a.get("cells", [])) == len(b.get("cells", []))
            for ca, cb in zip(a.get("cells", []), b.get("cells", [])):
                assert ca.get("cell_type") == cb.get("cell_type")
                assert ca.get("execution_count") == cb.get("execution_count")
                if ca.get("cell_type") == "code":
                    assert ca.get("source") == cb.get("source"), "I2 : source de code modifiee"
                assert ca.get("outputs") == cb.get("outputs"), "I3 : sortie modifiee"
        except (ValueError, AssertionError, KeyError, TypeError) as e:
            raise SystemExit(f"I1/I2/I3 VIOLes sur {p} ({e}) : rien n'est ecrit")
    p.write_text(edited, encoding="utf-8", newline="")
    return total


def append_ledger(pairs: list[tuple[str, str]], lane: str, repo: Path | None = None) -> None:
    repo = repo or repo_root()
    ledger = repo / LEDGER_RELPATH
    ledger.parent.mkdir(parents=True, exist_ok=True)
    new_file = not ledger.exists()
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%d")
    with ledger.open("a", encoding="utf-8", newline="") as fh:
        if new_file:
            fh.write("ancien\tnouveau\tdate\tlane\n")
        for old, new in pairs:
            fh.write(f"{old}\t{new}\t{stamp}\t{lane}\n")


# ---------------------------------------------------------------------------
# Organes de fin de passe
# ---------------------------------------------------------------------------

def organ_argv() -> list[list[str]]:
    py = sys.executable or "python"
    base = "scripts/notebook_tools"
    return [
        [py, f"{base}/check_duplicate_notebook_index.py", "--base", "{BASE}"],
        [py, f"{base}/check_kernel_suffix_canon.py", "--base", "{BASE}"],
        [py, f"{base}/check_link_label_agreement.py", "--fail"],
        [py, f"{base}/check_notebook_navlinks.py", "--check", "--tracked-only"],
        [py, f"{base}/check_twin_parity.py", "--check"],
    ]


def run_organs(base_sha: str, repo: Path | None = None) -> int:
    repo = repo or repo_root()
    worst = 0
    for argv in organ_argv():
        cmd = [a.replace("{BASE}", base_sha) for a in argv]
        r = subprocess.run(cmd, cwd=repo, capture_output=True, text=True,
                           encoding="utf-8", errors="replace")
        tail = (r.stdout or r.stderr or "").strip().splitlines()[-1:]
        print(f"[organe] {Path(cmd[1]).name} -> rc={r.returncode} {' '.join(tail)}")
        worst = max(worst, r.returncode)
    return worst


# ---------------------------------------------------------------------------
# Rapport
# ---------------------------------------------------------------------------

def report(plan: Plan, pairs: list[tuple[str, str]]) -> None:
    print(f"== {len(pairs)} renommage(s) (commit 1 : git mv seuls)")
    for old, new in pairs:
        print(f"   {old}\n     -> {new}")
    print(f"== referents a reecrire (commit 2) : {len(plan.rewrites)} fichier(s)")
    for rel in sorted(plan.rewrites):
        print(f"   {rel} : {plan.rewrites[rel]} occurrence(s)")
    if plan.code_cells:
        print(f"== CELLULES DE CODE (I2 : jamais reecrites, re-execution C.2 due) : {len(plan.code_cells)}")
        for rel, i, old in plan.code_cells:
            print(f"   {rel} cell {i} cite `{old}`")
    if plan.outputs:
        print(f"== SORTIES COMMITTEES (I3 : jamais touchees) : {len(plan.outputs)}")
        for rel, i, old in plan.outputs:
            print(f"   {rel} cell {i} : `{old}`")
    if plan.mixed_refused:
        print(f"== FICHIERS REFUSES (surfaces melangees, fail-closed I2/I3) : {len(plan.mixed_refused)} -- passage manuel requis")
        for rel in plan.mixed_refused:
            print(f"   {rel}")
    if plan.fragmented:
        print(f"== REFERENCES FRAGMENTEES (source JSON scindee en elements) : {len(plan.fragmented)} -- manuel")
        for rel, i in plan.fragmented:
            print(f"   {rel} cell {i}")


# ---------------------------------------------------------------------------
# --rebase-helper : reecrire les lignes AJOUTEES qui citent un ancien nom
# ---------------------------------------------------------------------------

def rebase_helper(apply: bool, repo: Path | None = None) -> int:
    repo = repo or repo_root()
    ledger = repo / LEDGER_RELPATH
    if not ledger.is_file():
        print("aucun registre de renommage : rien a faire")
        return 0
    renames: dict[str, str] = {}
    for line in ledger.read_text(encoding="utf-8").splitlines()[1:]:
        if not line.strip():
            continue
        parts = line.split("\t")
        if len(parts) >= 2:
            renames[parts[0]] = parts[1]
    if not renames:
        return 0
    diff = subprocess.run(
        ["git", "diff", "--unified=0", "origin/main...HEAD"],
        cwd=repo, capture_output=True, text=True, encoding="utf-8",
        errors="replace", check=True).stdout

    forms_list = [ref_forms(o, n) for o, n in renames.items()]
    touched: dict[str, int] = {}
    cur = None
    for line in diff.splitlines():
        if line.startswith("+++ b/"):
            cur = line[6:]
        elif line.startswith("+") and not line.startswith("+++") and cur:
            if any(pat.search(line[1:]) for _, pat, _, _ in build_patterns(forms_list)):
                touched[cur] = touched.get(cur, 0) + 1
    if not touched:
        print("aucune ligne ajoutee ne cite un ancien nom du registre")
        return 0

    total = 0
    for rel in sorted(touched):
        p = repo / rel
        if not p.is_file():
            continue
        if rel == LEDGER_RELPATH:
            # Le registre EST l'historique des renommages : le reecrire
            # reviendrait a effacer la memoire du geste.
            continue
        if rel.endswith(".ipynb"):
            # Fail-closed : sur un notebook en cours d'iteration, la decision
            # d'editer une cellule appartient a la lane qui la re-execute (C.2).
            print(f"   {rel} : {touched[rel]} ligne(s) ajoutee(s) -- MANUEL (notebook)")
            continue
        n = rewrite_file(p, forms_list) if apply else touched[rel]
        total += n
        print(f"   {rel} : {touched[rel]} ligne(s) ajoutee(s)"
              + (f"  [{n} remplacement(s) APPLIQUES]" if apply else "  [dry-run]"))
    print(f"total : {total} remplacement(s)" + ("" if apply else " (dry-run)"))
    return 0


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------

def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(
        description="Renommage canonique d'une serie : proposition, application "
                    "en 2 commits, reecriture des referents au texte.")
    ap.add_argument("--propose", metavar="DOSSIER")
    ap.add_argument("--mapping", metavar="TSV|issue:N#comment")
    ap.add_argument("--apply", action="store_true", help="sinon : dry-run")
    ap.add_argument("--rebase-helper", action="store_true")
    ap.add_argument("--lane", default=os.environ.get("ROOSYNC_LANE", "unknown"))
    a = ap.parse_args(argv)

    repo = repo_root()

    if a.propose:
        print(propose(a.propose, repo))
        return 0
    if a.rebase_helper:
        return rebase_helper(a.apply, repo)
    if not a.mapping:
        ap.error("--propose, --mapping ou --rebase-helper requis")

    pairs = load_mapping(a.mapping, repo)

    missing = [old for old, _ in pairs if not (repo / old).is_file()]
    if missing:
        print("FICHIERS INTROUVABLES (table perimee ?) :")
        for m in missing:
            print("   ", m)
        return 1
    targets = [new for _, new in pairs]
    collisions = sorted({n for n in targets if targets.count(n) > 1})
    if collisions:
        print("COLLISIONS dans la table :", collisions)
        return 1
    exist = [new for _, new in pairs if (repo / new).exists()]
    if exist:
        print("CIBLES DEJA PRESENTES :", exist)
        return 1
    for old, new in pairs:
        viol = target_violation(new)
        if viol:
            # La table est humaine, on execute ; mais une cible non canonique
            # promet un second renommage -- le dire, ne pas le taire.
            print(f"AVERTISSEMENT : {old} -> {new} : {viol} (second renommage attendu)")

    forms_list = [ref_forms(old, new) for old, new in pairs]
    plan = scan_referents(forms_list, repo)
    plan.moves = pairs
    report(plan, pairs)

    if not a.apply:
        print("\n[dry-run] rien n'a ete ecrit. Relancer avec --apply.")
        return 0

    pre = subprocess.run(["git", "rev-parse", "HEAD"], cwd=repo,
                         capture_output=True, text=True, encoding="utf-8",
                         errors="replace", check=True).stdout.strip()

    # Garde d'arbre propre (review #17801 point 1) : un renommage ne committe
    # QUE ses propres fichiers. Tout le reste (scratch, sortie papermill, body
    # de PR, WIP d'une autre session) partirait dans le commit de referents.
    dirty = subprocess.run(["git", "status", "--porcelain"], cwd=repo,
                           capture_output=True, text=True, encoding="utf-8",
                           errors="replace").stdout.strip()
    if dirty:
        print("ARBRE NON PROPRE -- refus d'appliquer. Committer ou retirer avant :")
        print(dirty[:600])
        return 1

    # commit 1 : git mv seuls (R100 visibles, aucun contenu modifie) -- chemins
    # NOMMES, jamais un commit qui attrape l'index entier.
    move_paths: list[str] = []
    for old, new in pairs:
        (repo / new).parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(["git", "mv", old, new], cwd=repo, check=True)
        move_paths += [old, new]
    msg1 = (f"rename(#16231): git mv purs ({len(pairs)} notebooks)\n\n"
            f"Table : {a.mapping}, pilotee par rename_notebooks.py.")
    subprocess.run(["git", "commit", "-m", msg1, "--", *move_paths],
                   cwd=repo, check=True)

    # commit 2 : referents par surface, au texte -- add et commit nommes.
    done = {}
    for rel in sorted(plan.rewrites):
        n = rewrite_file(repo / rel, forms_list)
        if n:
            done[rel] = n
    append_ledger(pairs, a.lane, repo)
    touched2 = sorted(done) + [LEDGER_RELPATH]
    msg2 = (f"rename(#16231): referents reecrits par surface ({len(done)} fichiers)\n\n"
            f"Cellules de code citees : jamais reecrites (re-execution C.2 due).\n"
            f"Sorties commitees : jamais touchees.")
    subprocess.run(["git", "add", "--", *touched2], cwd=repo, check=True)
    r = subprocess.run(["git", "commit", "-m", msg2, "--", *touched2], cwd=repo,
                       capture_output=True, text=True, encoding="utf-8",
                       errors="replace")
    if r.returncode != 0:
        print(f"[commit 2] rien a committer ou echec : {(r.stdout + r.stderr).strip()[:300]}")
    print(f"[commit 2] {len(done)} fichier(s) reecrit(s) au texte")

    rc = run_organs(pre, repo)
    print(f"VERDICT : organes rc={rc} (base = pre-rename {pre[:12]})")
    return rc


if __name__ == "__main__":
    sys.exit(main())
