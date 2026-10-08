#!/usr/bin/env python3
"""Regenerate the Quarto ``project.render`` list in ``_quarto.yml``.

Quarto 1.7 does not expand ``**/README.md`` globs across nested directories in
``project.render`` (the glob matches only the root file). To render every
README of the pedagogical tree as HTML (Axe C of #4211, validated user
2026-07-05), we list every git-tracked ``README.md`` explicitly.

This script is idempotent: it rewrites only the ``project.render`` block,
preserving the rest of ``_quarto.yml`` byte-for-byte. It is meant to be run:
  - locally before ``quarto render`` (a developer check),
  - on CI as a pre-render step of ``quarto-pages-deploy.yml`` (so new READMEs
    appear on the site without a manual regen commit).

The .ipynb notebooks of the pilot subtree (``NOTEBOOK_SUBTREES``, currently
``Search/``) ARE rendered to HTML (EPIC #10921, Phase A #10923): they are
listed explicitly with the same mechanism. Rendering consumes the committed
outputs (rule C.2) without kernel re-execution and shows the code cells: the
root ``execute`` block carries ``enabled: false`` + ``echo: true`` (measured
firsthand on the pilot: a directory-scoped ``_quarto.yml`` is NOT applied to
.ipynb documents in Quarto 1.7.32, only the root project block is).

Usage:
    python scripts/regen_quarto_render.py            # rewrite _quarto.yml in place
    python scripts/regen_quarto_render.py --check    # exit 1 if drift (CI guard)
"""
from __future__ import annotations

import argparse
import json
import posixpath
import re
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
QUARTO_YML = REPO_ROOT / "_quarto.yml"

# Files always rendered first (landing pages). Order matters for build log only.
LANDING_PAGES = [
    "*.qmd",
    "MyIA.AI.Notebooks/index.qmd",
    "MyIA.AI.Notebooks/Search/index.qmd",
    "MyIA.AI.Notebooks/Sudoku/index.qmd",
    "MyIA.AI.Notebooks/GameTheory/index.qmd",
    "MyIA.AI.Notebooks/Probas/index.qmd",
    "docs/index.qmd",
    # COURSE_CATALOG.generated.md est lie depuis index.qmd (L64) mais servi en
    # texte brut sinon : on le REND en HTML (verifie firsthand #10925 Q2 —
    # quarto render standalone -> HTML 176 Ko, exit 0, sans front-matter).
    # Le fichier catalogue lui-meme reste byte-identique (catalog-pr-hygiene R1 :
    # on rend le fichier committe, on ne le regenere jamais sur une branche).
    "COURSE_CATALOG.generated.md",
]

# READMEs in vendored / archived / LFS subtrees that must NOT render.
# - vendored: external Lean/Foundry libs (not our content)
# - archived: internal history (docs/archive, _archive-*, */archive/) — these
#   often start with '---' which Quarto mis-parses as YAML front-matter, and
#   they add no pedagogical value to the public site anyway.
EXCLUDE_MARKERS = (
    ".lake/packages",      # vendored Lean Mathlib checkouts
    "foundry-lib/lib",     # vendored Foundry lib
    "docs/archive",        # internal suivi history
    "_archive-",           # archived docker configs / snapshots
    "/archive/",           # any archive/ subdir (notebook families, scripts)
    "\\archive\\",
)

# Notebooks rendered to HTML (EPIC #10921). Pilot = Search (#10923 Phase A);
# tranche 2 = Sudoku + GameTheory + Probas (#10923, les 3 familles deja
# surfacees par la navbar — la nav ne doit mener a aucun non-rendu). The root
# execute block (_quarto.yml) already carries enabled: false + echo: true for
# every notebook — a directory-scoped _quarto.yml is NOT applied to .ipynb in
# Quarto 1.7.32 (measured firsthand), so no per-subtree override exists.
NOTEBOOK_SUBTREES = (
    "MyIA.AI.Notebooks/Search/",                 # pilote #10923 (111 rendus apres exclusions)
    "MyIA.AI.Notebooks/Sudoku/",                # tranche 2 #10923 (37)
    "MyIA.AI.Notebooks/GameTheory/",            # tranche 2 #10923 (56)
    "MyIA.AI.Notebooks/Probas/",                # tranche 2 #10923 (58)
    "MyIA.AI.Notebooks/CaseStudies/",            # tranche 15 #10923 (6)
    "MyIA.AI.Notebooks/Complexity/",             # tranche 19 #18423 (9 notebooks, complexite computationnelle)
    "MyIA.AI.Notebooks/NLP/",                    # tranche 19 #18423 (5, TAL/TALN)
    "MyIA.AI.Notebooks/QuantConnect/",           # tranche 19 #18423 (203 rendus, 221 git-tracked - 18 sous /archive/ ; sous-familles : projects, Python, research, ML-Training-Pipeline, partner-course-quant-trading, kelly_lean)
    "MyIA.AI.Notebooks/GenAI/00-GenAI-Environment/",  # tranche 19 #18423 (6)
    "MyIA.AI.Notebooks/GenAI/Integrations-DotNet/Aspire/",  # tranche 18 #13581 (9, deplace depuis GenAI/Aspire/ en tranche T2 hub .NET) -- couvert aussi par Integrations-DotNet/ ci-dessous (dedup OK)
    "MyIA.AI.Notebooks/GenAI/Integrations-DotNet/",  # tranche 19 #18423 (15 sur 4 sous-familles : Aspire, CopilotSDK, EFCore, Orleans ; 9 deja couverts via Aspire ci-dessus, 6 nouveaux uniques)
    "MyIA.AI.Notebooks/GenAI/Audio/",            # tranche 15 #10923 (30)
    "MyIA.AI.Notebooks/GenAI/CaseStudies/",      # tranche 15 #10923 (4)
    "MyIA.AI.Notebooks/GenAI/FallacyDetection/", # tranche 13 #10923 (2, deplace depuis top-level FallacyDetection/ en tranche 1 #13581)
    "MyIA.AI.Notebooks/GenAI/FineTuning/",       # tranche 15 #10923 (5)
    "MyIA.AI.Notebooks/GenAI/Image/",            # tranche 15 #10923 (20)
    "MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/",  # tranche 15 #10923 (23)
    "MyIA.AI.Notebooks/GenAI/PostTraining/",     # tranche 15 #10923 (14)
    "MyIA.AI.Notebooks/GenAI/RAG-et-Memoire-Semantique/",  # tranche 15 #10923 (1)
    "MyIA.AI.Notebooks/GenAI/Security/",         # tranche 19 #18423 (6, Control / Oversight / Tooling)
    "MyIA.AI.Notebooks/GenAI/SemanticKernel/",   # tranche 15 #10923 (20)
    "MyIA.AI.Notebooks/GenAI/Texte/",            # tranche 15 #10923 (21)
    "MyIA.AI.Notebooks/GenAI/Vibe-Coding/",      # tranche 15 #10923 (8)
    "MyIA.AI.Notebooks/GenAI/Video/",            # tranche 15 #10923 (21)
    "MyIA.AI.Notebooks/IIT/",                    # tranche 15 #10923 (56)
    "MyIA.AI.Notebooks/ML/",                     # tranche 15 #10923 (48)
    "MyIA.AI.Notebooks/RL/",                     # tranche 15 #10923 (21)
    "MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/",  # tranche 3 #10923 (25, EPITA Argumentum)
    "MyIA.AI.Notebooks/SymbolicAI/SemanticWeb/",         # tranche 5 #10923 (26, RDF/OWL/SPARQL EPITA-Sub-symbolic)
    "MyIA.AI.Notebooks/SymbolicAI/SMT/",               # tranche 14 #10923 (46 notebooks Z3/SMT)
    "MyIA.AI.Notebooks/SymbolicAI/SmartContracts/",    # tranche 14 #10923 (27 notebooks blockchain)
    "MyIA.AI.Notebooks/SymbolicAI/Tweety/",            # tranche 4 #10923 (32, manipulation arguments)
    "MyIA.AI.Notebooks/SymbolicAI/Planners/",          # tranche 6 #10923 (24)
    "MyIA.AI.Notebooks/SymbolicAI/SymbolicLearning/",  # tranche 6 #10923 (23)
    # SymbolicAI/Lean/ couvre aussi Lean/Geometry/ depuis le re-parenting #18601
    # (ex SymbolicAI/Geometry/, tranche 19 #18423).
    "MyIA.AI.Notebooks/SymbolicAI/Lean/",             # tranche 13 #10923 (33 notebooks .ipynb pedagogique Lean)
    "MyIA.AI.Notebooks/cross-series/",                # tranche 13 #10923 (1)
    "MyIA.AI.Notebooks/Compression/",                 # tranche finale #18423 (1, codes prefixes Shannon-Fano -> Huffman)
    # Prefix famille : couvre OR-tools-Stiegler.ipynb au niveau racine de
    # SymbolicAI/ (38 cellules, pedagogique). Les sous-repertoires deja
    # couverts par leurs entrees individuelles ci-dessus restent dedup
    # (precedent Integrations-DotNet/ <- Aspire/, tranche 18 #13581).
    "MyIA.AI.Notebooks/SymbolicAI/",                  # tranche finale #18423 (prefix famille, +1 racine)
)

# Notebook subtrees that must NOT render (archived families only — vendored
# subtrees are never git-tracked under these prefixes).
NOTEBOOK_EXCLUDE_MARKERS = (
    "/_archive/",
    "/archive/",
)

# Notebook files volontairement exclus du rendu HTML, avec raison mesurée.
# Vide depuis 2026-08-14 (issue #10968) : la pathologie qui motivait les 7
# exclusions — le filtre lua de Quarto 1.7.32 qui pend (CPU-bound, aucune
# sortie) sur les cellules echo:true dont une ligne de source se termine par
# \n et qui sont suivies d'un output display_data — est corrigee en Quarto
# 1.10.18 (pin CI mis a jour). Verifie firsthand (2026-08-14, standalone) :
#   - App-9b-EdgeDetection-CSharp.ipynb : 1.7.32 >= 15 min sans progression
#     -> 1.10.18 rend en ~6 s (HTML 4.88 MB).
#   - MGS-09-EverestRelief / MGS-15-LandscapeAnalysis : 1.10.18 rendent en
#     7 s / 3 s (leger vs lourd de la famille MetaGeneticSharp).
#   - Mini-repro minimal (1 cellule code, ligne de source terminant par \n +
#     1 display_data) : 1.7.32 pend, 1.10.18 rend en ~13 s.
# NB : pandoc n'est PAS en cause (reader + writer ipynb<->html en 0 s) ;
# c'est le filtre post-traitement de Quarto 1.7.32 (main.lua:9677, recherche
# de fenced-div ":::") qui boucle sur la combinaison source+display_data.
# L'ancienne liste des 7 (App-9b + MGS-4/8/9/11/14/15) est conservee dans
# l'historique git du fichier. Laisser ce tuple vide sauf raison mesuree.
NOTEBOOK_EXCLUDE_FILES = ()

# Notebooks git-tracks qui restent HORS perimetre de rendu, avec raison
# mesuree (#18423 : « le dire dans le script plutot que laisser implicite »).
# La garde uncovered_notebooks() verifie que c'est exactement la population
# non rendue : tout nouveau .ipynb hors sous-arbres ET hors cette liste fait
# rougir --check (le hole de couverture ne peut plus revenir silencieusement).
NOTEBOOKS_HORS_PERIMETRE = {
    # Outil interne de notation (GradeBookApp), pas un carnet de cours.
    "MyIA.AI.Notebooks/GradeBook.ipynb",
    # Recherche interne (validation e2e quant), hors publication pedagogique.
    "MyIA.AI.Notebooks/GenAI/_research/e2e_quant_validation.ipynb",
    # Sondes d'outillage : reproduction du bug .NET #17361, smoke runtime.
    "scripts/notebook_tools/probes/dotnet-restore-bug-17361.ipynb",
    "scripts/notebook_tools/verify_runtime_smoke.ipynb",
}

# Sous-arbres `docs/` dont les `*.md` non-README sont rendus en HTML par
# Quarto (issue #18422, Axe C #4211 etendu des READMEs aux .md simples).
# Le constat (audit Playwright 2026-09-29) : la page docs/ du site sert ses
# liens .md en markdown brut, alors que les READMEs siblings sont rendus
# HTML. Meme mecanisme : lister explicitement dans project.render car Quarto
# 1.7 n'etend pas `**/*.md` dans project.render (cf. header du fichier).
# La garde `has_hr_separator` (#11451) s'applique a ces .md comme aux
# notebooks : 24.5 % des docs/*.md portent un `---` hr qui declenche
# le meme YAMLException (49 fichiers mesures au 2026-10-01, exclus du rendu).
# Memes EXCLUDE_MARKERS (archive, vendored) que les READMEs.
DOCS_MD_SUBTREES = ("docs/",)

# --- Garde de separateur horizontal `---` (issue #11451) --------------------
#
# Une ligne `---` seule dans une cellule markdown ouvre un bloc
# `yaml_metadata_block` ; le `---` d'une cellule suivante le referme. Quarto
# parse ce bloc en YAML (`readYamlFromMarkdown` -> `extractYaml`). Le contenu
# intermediaire est de la prose et des titres du type `### Interpretation : X`,
# que YAML lit comme des paires cle/valeur : `quarto render` s'arrete sur
# `YAMLException` et AUCUNE page du site n'est publiee.
#
# Mesure (2026-08-18) : au dernier build vert (98c877037, 2026-08-17T19:09Z) la
# render-list portait 118 notebooks ; le rollout #10923 (tranches 6 a 13) l'a
# portee a 348, dont 234 contiennent au moins un `---`. Deux pannes du site le
# meme jour, sur deux notebooks differents de cette classe (FallacyDetection-02
# corrige par #11629, puis SymbolicLearning SL-8). Quarto s'arretant a la
# PREMIERE erreur, les corriger un par un = une panne par notebook.
#
# La garde est SYNTAXIQUE et volontairement conservatrice : elle ne cherche pas
# a rejouer la logique d'appariement de Quarto (un modele js-yaml fidele rendait
# encore 4 faux positifs sur le lot vert de reference, cf. #11451). Elle se
# contente de la condition NECESSAIRE : pas de `---`, pas de bloc, pas de
# panne possible.
#
# Elle est AUTO-RESORBANTE : des qu'une famille est nettoyee (`---` -> `***`,
# meme rendu <hr> en Pandoc, aucune semantique YAML), ses notebooks
# reintegrent la render-list sans toucher a ce script.
_FENCE_RE = re.compile(r"^(```|~~~)")


def has_hr_separator(rel_path: str) -> bool:
    """True si un fichier (notebook .ipynb OU .md) porte un `---` hr separator.

    Detection issue #11451 (notebooks) etendue aux .md par #18422. Un `---`
    seul en debut de cellule-ligne (apres une ligne vide ou au tout debut)
    ouvre un bloc `yaml_metadata_block` que Quarto interprete en YAML ->
    `YAMLException` -> AUCUNE page publiee.

    Regles distinguees :
      - `.ipynb` : on parse le JSON et on itere sur `cells` (markdown uniquement)
      - `.md` : on lit le texte brut ligne par ligne (memes regles setext / fence)

    Dans les deux cas on ignore :
      - les `---` a l'interieur d'un bloc de code fence (``` ou ~~~)
      - les `---` qui SOULIGNENT du texte (titre setext H2) : seul un `---`
        precede d'une ligne vide ou du debut de cellule-ligne ouvre un bloc.
    """
    try:
        content = (REPO_ROOT / rel_path).read_text(encoding="utf-8")
    except OSError:
        return False  # fichier inexistant / illisible : laisser la CI trancher
    # Branche notebook (.ipynb) : JSON, on itere sur les cellules markdown
    if rel_path.endswith(".ipynb"):
        try:
            nb = json.loads(content)
        except ValueError:
            return False  # JSON invalide : laisser la CI trancher
        for cell in nb.get("cells", []):
            if cell.get("cell_type") != "markdown":
                continue
            src = cell.get("source")
            text = "".join(src) if isinstance(src, list) else (src or "")
            if _text_has_hr(text):
                return True
        return False
    # Branche markdown (.md) : texte brut, on scanne ligne a ligne
    if rel_path.endswith(".md"):
        return _text_has_hr(content)
    # Autres extensions : pas de garde
    return False


def _text_has_hr(text: str) -> bool:
    """Helper : True si le texte markdown porte un `---` hr separator.

    Reprend la logique de la garde #11451 : un `---` seul en debut de
    cellule-ligne (apres une ligne vide ou au tout debut) ouvre un bloc
    YAML. Les `---` dans un bloc fence ou en soulignement setext sont ignores.
    """
    lines = text.split("\n")
    in_fence = False
    for i, line in enumerate(lines):
        if _FENCE_RE.match(line.strip()):
            in_fence = not in_fence
            continue
        if in_fence:
            continue
        if line.rstrip() == "---":
            prev = lines[i - 1].strip() if i > 0 else ""
            if prev == "":
                return True
    return False


def git_tracked_notebooks() -> list[str]:
    """Return repo-relative POSIX paths of every git-tracked ``.ipynb`` under
    NOTEBOOK_SUBTREES, excluding archived subtrees.

    Same `git ls-files` + quote handling as ``git_tracked_readmes`` (raw UTF-8
    paths, single YAML wrap stays valid on every machine).
    """
    patterns = []
    for tree in NOTEBOOK_SUBTREES:
        patterns.append(tree + "*.ipynb")
        patterns.append(tree + "**/*.ipynb")
    out = subprocess.run(
        ["git", "-C", str(REPO_ROOT), "-c", "core.quotePath=false", "ls-files", *patterns],
        capture_output=True, text=True, encoding="utf-8", errors="replace", check=True,
    )
    paths = []
    for line in out.stdout.splitlines():
        p = line.strip()
        if not p:
            continue
        if any(bad in p for bad in NOTEBOOK_EXCLUDE_MARKERS):
            continue
        if p in NOTEBOOK_EXCLUDE_FILES:
            continue
        if has_hr_separator(p):
            continue  # cf. garde `---` ci-dessus (#11451)
        paths.append(p)
    # Sort for deterministic diffs (by path, case-insensitive)
    paths.sort(key=lambda s: s.lower())
    return paths


def uncovered_notebooks() -> list[str]:
    """Git-tracked ``.ipynb`` neither rendered nor declared out-of-scope (#18423).

    Diff d'ensemble (un motif qui rate les noms pointes est un faux negatif) :
    enumeration exhaustive ``git ls-files '*.ipynb'``, moins la render-list,
    moins les archives (NOTEBOOK_EXCLUDE_MARKERS), moins
    NOTEBOOKS_HORS_PERIMETRE. Tout residu = trou de couverture : soit un
    sous-arbre a ajouter, soit une exclusion a declarer, soit un carnet
    hr-bloque (#11451) sous sous-arbre rendu.
    """
    out = subprocess.run(
        ["git", "-C", str(REPO_ROOT), "-c", "core.quotePath=false", "ls-files", "*.ipynb"],
        capture_output=True, text=True, encoding="utf-8", errors="replace", check=True,
    )
    rendered = set(git_tracked_notebooks())
    uncovered = []
    for line in out.stdout.splitlines():
        p = line.strip()
        if not p or p in rendered or p in NOTEBOOKS_HORS_PERIMETRE:
            continue
        if any(bad in p for bad in NOTEBOOK_EXCLUDE_MARKERS):
            continue
        uncovered.append(p)
    uncovered.sort(key=str.lower)
    return uncovered


def git_tracked_readmes() -> list[str]:
    """Return repo-relative POSIX paths of every git-tracked README.md,
    excluding vendored and archived subtrees."""
    # `-c core.quotePath=false`: without it, git quotes non-ASCII paths
    # (accents/spaces) as "\303\251..." AND wraps them in double-quotes under
    # CI's default core.quotePath=true. The emitter below wraps again -> doubled
    # quotes ("" ... "") -> broken YAML in _quarto.yml (CI Quarto Pages Deploy
    # failure since 2026-07-05). Forcing false yields raw UTF-8 paths, so the
    # single wrap below stays valid YAML on every machine (CI or local).
    out = subprocess.run(
        ["git", "-C", str(REPO_ROOT), "-c", "core.quotePath=false", "ls-files", "*README.md"],
        capture_output=True, text=True, encoding="utf-8", errors="replace", check=True,
    )
    paths = []
    for line in out.stdout.splitlines():
        p = line.strip()
        if not p or p == "README.md":
            continue  # root handled separately (added with explicit form)
        # Skip vendored / archived subtrees
        if any(bad in p for bad in EXCLUDE_MARKERS):
            continue
        paths.append(p)
    # Sort for deterministic diffs (by path, case-insensitive)
    paths.sort(key=lambda s: s.lower())
    return paths


def git_tracked_docs_md() -> list[str]:
    """Return repo-relative POSIX paths of every git-tracked ``*.md`` under
    DOCS_MD_SUBTREES, excluding vendored/archived subtrees and files with a
    ``---`` hr separator (issue #11451, applique aux .md comme aux notebooks).

    Memes garde-fous que ``git_tracked_readmes`` :
      - ``-c core.quotePath=false`` (paths UTF-8 bruts, cf. commentaires ci-dessus)
      - ``EXCLUDE_MARKERS`` (archive, vendored)
      - ``has_hr_separator`` (#11451) : exclut les 49 fichiers mesurant un hr
        en debut de cellule-ligne (24.5 % du corpus au 2026-10-01). La garde
        est AUTO-RESORBANTE : un futur passage qui convertit `---` en `***`
        reintegre le fichier sans toucher a ce script.
      - Exclusion des README.md (deja comptabilises par ``git_tracked_readmes``
        pour rester single-source-of-truth).
    """
    patterns = []
    for tree in DOCS_MD_SUBTREES:
        patterns.append(tree + "*.md")
        patterns.append(tree + "**/*.md")
    out = subprocess.run(
        ["git", "-C", str(REPO_ROOT), "-c", "core.quotePath=false", "ls-files", *patterns],
        capture_output=True, text=True, encoding="utf-8", errors="replace", check=True,
    )
    paths = []
    for line in out.stdout.splitlines():
        p = line.strip()
        if not p or p == "README.md":
            continue
        if p.endswith("/README.md"):
            continue  # READMEs geres par git_tracked_readmes()
        if any(bad in p for bad in EXCLUDE_MARKERS):
            continue
        if has_hr_separator(p):
            continue  # cf. garde `---` ci-dessus (#11451)
        paths.append(p)
    # Sort for deterministic diffs (by path, case-insensitive)
    paths.sort(key=lambda s: s.lower())
    return paths


def build_render_block() -> list[str]:
    """Build the YAML lines for the project.render list."""
    lines = ["project:", "  type: site", "  output-dir: _site", "  render:"]
    # Landing pages (qmd) + catalogue genere (rendu HTML, cf. LANDING_PAGES)
    lines.append("    # Landing pages (.qmd) + COURSE_CATALOG.generated.md (rendu HTML).")
    for entry in LANDING_PAGES:
        lines.append(f'    - "{entry}"')
    # READMEs (explicit list — globs do not expand in Quarto 1.7, see header)
    readmes = git_tracked_readmes()
    lines.append("    # README.md rendus en HTML (Axe C #4211). Liste explicite")
    lines.append("    # (regeneree par scripts/regen_quarto_render.py) car Quarto 1.7")
    lines.append("    # n'etend pas le glob **/README.md sur les sous-repertoires.")
    lines.append("    # Archives et libs vendored EXCLUES (history interne, non pedagogique).")
    lines.append(f"    # {len(readmes) + 1} READMEs (racine + arborescence, hors archives).")
    lines.append('    - "README.md"')
    for p in readmes:
        lines.append(f'    - "{p}"')
    # docs/*.md (non-README) rendus en HTML (issue #18422, etend Axe C #4211).
    # Meme mecanisme que les READMEs : liste explicite par garde de Quarto 1.7
    # (cf. header). Les fichiers avec `---` hr sont exclus (garde #11451,
    # auto-resorbante : un futur passage `---` -> `***` les reintegre sans
    # toucher a ce script).
    docs_md = git_tracked_docs_md()
    if docs_md:
        lines.append("    # docs/*.md rendus en HTML (issue #18422). Meme mecanisme")
        lines.append("    # que les READMEs : liste explicite (globs non etendus en Quarto 1.7).")
        lines.append("    # Garde `---` (#11451) appliquee auto-resorbante.")
        lines.append(f"    # {len(docs_md)} docs/*.md (sous-arbre docs/, hors README/archive/hr).")
        for p in docs_md:
            lines.append(f'    - "{p}"')
    # Notebooks rendered to HTML (EPIC #10921, pilote Search #10923). Explicit
    # list (globs do not expand in Quarto 1.7, see README comment above).
    notebooks = git_tracked_notebooks()
    if notebooks:
        lines.append("    # Notebooks rendus en HTML (EPIC #10921, pilote Search #10923).")
        lines.append("    # Liste explicite — globs non etendus en Quarto 1.7.")
        lines.append("    # Execution desactivee + echo: true au niveau racine (_quarto.yml).")
        lines.append(f"    # {len(notebooks)} notebooks (sous-arbres: "
                     + ", ".join(sorted(NOTEBOOK_SUBTREES)) + ").")
        for p in notebooks:
            lines.append(f'    - "{p}"')
    return lines


def replace_render_block(yml_text: str, new_block_lines: list[str]) -> str:
    """Replace the project: {...} block at the top of _quarto.yml.

    The block runs from the first ``project:`` line up to (but not including)
    the next top-level key (``site:``). Everything after is preserved.
    """
    lines = yml_text.splitlines(keepends=True)
    start = None
    end = len(lines)
    top_keys = ("site:", "format:", "execute:", "lang:", "notebook-preview:",
                "editor:", "website:", "book:", "manuscript:", "server:")
    for i, line in enumerate(lines):
        if line.startswith("project:"):
            start = i
            continue
        if start is not None and line and not line.startswith((" ", "\t", "#", "-")):
            if any(line.startswith(k) for k in top_keys):
                end = i
                break
    if start is None:
        raise SystemExit("_quarto.yml: no 'project:' block found")
    # Rebuild: new block + original tail (from `end` onward)
    new_block = "\n".join(new_block_lines) + "\n"
    tail = "".join(lines[end:])
    return new_block + tail


# --- Regle render-list-vs-README (#13025, suite audit #10921 c.5418776353) --
#
# Mesure Playwright 2026-08-26 : les READMEs de series continuent de lier les
# .ipynb bruts alors que le site ne sert QUE les rendus (un lien .ipynb sur
# Pages = 404 ; Search : 21 liens .ipynb au README, rendus .html siblings
# presents ; RL : 11 liens, rendus manquants). L'experience apprenant
# dominante etait la page JSON brute -- exactement le defect que l'EPIC
# #10921 demandait d'etreindre, ressuscite a chaque nouvelle serie.
#
# REGLE : la render-list doit couvrir 100% des notebooks listes dans les
# READMEs des series rendues. Concrenement, tout lien notebook d'un README
# sous un NOTEBOOK_SUBTREES doit mener soit a un rendu .html (cible dans la
# render-list), soit rester une source brute EXPLICITE (notebook exclu du
# rendu par la garde `---` #11451 ou hors sous-arbre rendu). Les READMEs hors
# sous-arbres rendus (ex. QuantConnect/) forment la population « source
# brute » documentee -- nonverifies par cette garde.
_IPYNB_LINK_RE = re.compile(r"\]\(([^)#\s]+\.ipynb)\)")
_HTML_LINK_RE = re.compile(r"\]\(([^)#\s]+\.html)\)")


def _normalise_readme_target(base: Path, href: str) -> str:
    """Return a repository-relative POSIX path with ``..`` resolved."""
    return posixpath.normpath((base / href).as_posix())


def readme_link_violations(
    pr_added_files: set[str] | None = None,
) -> list[tuple[str, str, str]]:
    """Return [(readme, class, detail)] for render-list-vs-README drift.

    Classes:
      STALE_LINK  -- the .ipynb target IS in the render list: the README must
                     link the .html sibling instead (the raw .ipynb 404s on
                     Pages -- the #13025 defect).
      BROKEN      -- the .ipynb target does not exist on disk (dead link).
      DEAD_RENDER -- a .html link names an existing notebook excluded from the
                     render list, so the rendered page will not exist.
    UNRENDERED targets (file exists but excluded from the render list by the
    #11451 `---` guard or by an exclude marker) are NOT violations: they are
    the documented raw-source population (reported by --check-readme-links as
    warnings so the sweep stays honest, but the fix is notebook-side).

    ``pr_added_files`` (#19631) : when the readme-ipynb-links-guard workflow
    runs on a PR (cf. `.github/workflows/readme-ipynb-links-guard.yml`), the
    BASE scan finds no STALE_LINK for a link targeting a PR-added notebook
    (the link only exists in the PR scan), producing a false-positive
    "NEW violation" delta. The founding case is #19368 (Origami causal
    CB-00 README) : the notebook `CausalBridges-00-PearlLadder-Intro-Python`
    is ADDED by the same PR (commit 59ea252dd, not yet on main), and the
    README's new link to it is intentional -- the file and its link arrive
    together. The fix : EXCLUDE PR-added files from the STALE_LINK check.
    Both scans then agree (no violation either way) and the delta collapses
    to 0. The link itself remains valid for downstream sweeps; we just stop
    flagging it as a *new* violation introduced by the PR.
    """
    rendered = set(git_tracked_notebooks())
    if pr_added_files:
        # PR-added files are tracked-after-merge; a link targeting one is
        # arriving with the file, so it is not a STALE_LINK introduced by
        # this PR. (cf. founding case #19368 / 59ea252dd).
        rendered -= pr_added_files
    readmes = [p for p in git_tracked_readmes()
               if any(p.startswith(t) for t in NOTEBOOK_SUBTREES)]
    out: list[tuple[str, str, str]] = []
    for rel_readme in sorted(readmes):
        text = (REPO_ROOT / rel_readme).read_text(encoding="utf-8", errors="replace")
        base = Path(rel_readme).parent
        for m in _IPYNB_LINK_RE.finditer(text):
            href = m.group(1)
            if href.startswith(("http://", "https://", "#", "mailto:")):
                continue  # absolute/anchor links are out of scope
            norm = _normalise_readme_target(base, href)
            if norm in rendered:
                out.append((rel_readme, "STALE_LINK", href))
            elif not (REPO_ROOT / norm).exists():
                out.append((rel_readme, "BROKEN", href))
            # else: UNRENDERED -- raw-source population, not a violation
        for m in _HTML_LINK_RE.finditer(text):
            href = m.group(1)
            if href.startswith(("http://", "https://", "#", "mailto:")):
                continue
            source_href = href.removesuffix(".html") + ".ipynb"
            source = _normalise_readme_target(base, source_href)
            if (REPO_ROOT / source).exists() and source not in rendered:
                out.append((rel_readme, "DEAD_RENDER", href))
    return out


def report_readme_links(pr_added_files: set[str] | None = None) -> int:
    """Print the README-link audit and exit 1 on STALE_LINK/BROKEN (#13025).

    ``pr_added_files`` (#19631) : forwarded to ``readme_link_violations`` so the
    delta-vs-base computation of the readme-ipynb-links-guard workflow agrees on
    files added in the same PR as the README link target.
    """
    rendered = set(git_tracked_notebooks())
    if pr_added_files:
        # Mirror the exclusion used in ``readme_link_violations`` so the
        # `unrendered` tally below stays consistent with the violation set.
        rendered -= pr_added_files
    readmes = [p for p in git_tracked_readmes()
               if any(p.startswith(t) for t in NOTEBOOK_SUBTREES)]
    unrendered = 0
    for rel_readme in sorted(readmes):
        text = (REPO_ROOT / rel_readme).read_text(encoding="utf-8", errors="replace")
        base = Path(rel_readme).parent
        for m in _IPYNB_LINK_RE.finditer(text):
            href = m.group(1)
            if href.startswith(("http://", "https://", "#", "mailto:")):
                continue  # absolute/anchor links are out of scope
            norm = _normalise_readme_target(base, href)
            if norm not in rendered and (REPO_ROOT / norm).exists():
                unrendered += 1
    violations = readme_link_violations(pr_added_files=pr_added_files)
    for rel_readme, cls, href in violations:
        print(f"::error::{cls} {rel_readme} -> {href}", file=sys.stderr)
    n_readmes = len(readmes)
    print(f"README-link audit: {n_readmes} rendered-subtree READMEs, "
          f"{len(violations)} violation(s), {unrendered} raw-source link(s) "
          "(excluded from render -- garde #11451 or hors sous-arbre).")
    return 1 if violations else 0


def _load_added_files(path: str | None) -> set[str]:
    """Read PR-added files list (one POSIX path per line, blank lines ignored).

    Used by ``--pr-added-files`` (#19631) so the readme-ipynb-links-guard
    workflow can hand the scanner the set of files added by the PR, so the
    base-vs-head delta collapses to 0 on links targeting PR-added notebooks
    (the founding case : CB-00 README -> CB-00.ipynb added by PR #19310).
    """
    if not path:
        return set()
    added = set()
    with open(path, encoding="utf-8") as f:
        for line in f:
            p = line.strip()
            if p:
                added.add(p)
    return added


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true",
                    help="exit 1 if _quarto.yml render list is stale")
    ap.add_argument("--check-readme-links", action="store_true",
                    help="exit 1 if a rendered-subtree README links a raw "
                         ".ipynb whose render exists (STALE_LINK), a missing "
                         "source (BROKEN), or a .html page whose notebook is "
                         "not rendered (DEAD_RENDER) -- regle #13025")
    ap.add_argument("--pr-added-files", default=None, metavar="PATH",
                    help="file listing PR-added paths (one per line, POSIX). "
                         "Used by the readme-ipynb-links-guard workflow so "
                         "STALE_LINK on a link targeting a PR-added .ipynb "
                         "collapses on both sides of the delta (#19631).")
    args = ap.parse_args()

    if args.check_readme_links:
        return report_readme_links(pr_added_files=_load_added_files(args.pr_added_files))

    new_block = build_render_block()
    current = QUARTO_YML.read_text(encoding="utf-8")
    proposed = replace_render_block(current, new_block)

    if args.check:
        if proposed != current:
            print("::error::_quarto.yml render list is stale. "
                  "Run: python scripts/regen_quarto_render.py", file=sys.stderr)
            return 1
        n = len(git_tracked_readmes()) + 1
        n_docs = len(git_tracked_docs_md())
        nb = len(git_tracked_notebooks())
        uncovered = uncovered_notebooks()
        if uncovered:
            print("::error::notebooks git-tracks ni rendus ni declares hors "
                  "perimetre : " + ", ".join(uncovered)
                  + " -- ajouter le sous-arbre a NOTEBOOK_SUBTREES ou declarer "
                    "l'exclusion dans NOTEBOOKS_HORS_PERIMETRE (#18423)",
                  file=sys.stderr)
            return 1
        print(f"_quarto.yml render list up to date "
              f"({n} READMEs, {n_docs} docs/*.md, {nb} notebooks, "
              f"{len(NOTEBOOKS_HORS_PERIMETRE)} declares hors perimetre).")
        return 0

    QUARTO_YML.write_text(proposed, encoding="utf-8")
    n = len(git_tracked_readmes()) + 1
    n_docs = len(git_tracked_docs_md())
    nb = len(git_tracked_notebooks())
    print(f"_quarto.yml updated: render list now includes "
          f"{n} READMEs, {n_docs} docs/*.md, {nb} notebooks.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
