#!/usr/bin/env python3
"""Detecte les citations VERBATIM FABRIQUEES committes dans les cellules markdown.

Pourquoi cet outil existe
-------------------------
Le sweep Prong-A (#3801) traque les sorties FABRIQUEES : une cellule code qui
pretend avoir execute mais commit un placeholder textuel en lieu et place du
vrai resultat. `detect_fabricated_outputs.py` couvre l'AXE 2 : les sorties
TEXTUELLES fabriquees -- dataframes de backtest avec stats a 0.0 simulant un
backtest qui n'a pas tourne, lignes `Row N` placeholders, listes d'allocations
vides. `detect_blank_figures.py` couvre les images degeneres (axe 1 : le PNG
1x1 de 70 octets emis par matplotlib quand la figure est vide).

Cet outil couvre l'AXE 3 : les verbatims FABRIQUES en cellule markdown.
Classe de defaut mesuree sur trois PRs (cf golden set ci-dessous) : une cellule
markdown annonce une ancre du type "Sortie observee de code[N]" et la fait
suivre d'un fragment verbatim (entre backticks) -- mais ce fragment ne provient
PAS de la sortie reellement commitee de la cellule code[N]. Les signatures
sont inventees, les valeurs numerique sont les "bonnes" selon l'attente de
l'auteur et non celles que le kernel a reellement rendues, et les sous-parties
de la sortie sont elidees de maniere a presenter un fragment legitime mais
absent de l'artefact.

Incident fondateur
------------------
Trois PRs distinctes ont rendu ce type de defaut (les SHAs avant-fix sont le
golden set, voir `tests/notebook_tools/test_detect_fabricated_verbatim.py`) :

  PR #14105 (Lean-22b)
    -- ancres « Sortie observee de code[N] (verbatim) » qui citaient des
       valeurs numeriques inventees :
         «#eval 2 * Float.exp (-(1:Float) ^ 2 / 2)   1.213061»
       la sortie REELLE rendait `0.270671` (le 1.213061 n'etait pas dans
       l'artefact, l'auteur avait reporte une valeur de l'enonce verbal,
       pas la sortie kernel). 9 cellules contaminees au total (la review
       n'en voyait que 2).

  PR #14111 (ASPIC+)
    -- md[24] annoncait « 9 undermines, 5 rebuts, 3 undercuts » contre une
       sortie reelle `{'rebut': 8, 'undercut': 4, 'undermine': 5}`. md[1]
       attribuait le chargement des 42 JARs a `JVM operationnelle : True`
       (retour de `jpype.isJVMStarted()`), en elidant la ligne qui porte
       reellement le decompte.

  PR #14128 (SC-7c)
    -- 5 signatures Lean « verbatim » sur 11 cellules qui omettent toutes le
       `{n : ℕ}` de debut (la sortie reelle du `#check` le contient ; la
       citation fabriquee l'a coupe pour alleger la presentation). Hypothese
       fabriquee, arguments renommes, notation `s \\ {a}` inventee.

Aucun detecteur commite ne couvre cette classe : `scan_cell_ordering.py` couvre
la POSITION des ancres (avant/apres une cellule code), pas leur CONTENU.
`detect_fabricated_outputs.py` regarde les SORTIES (output cells), pas la
correspondance SORTIE-vs-CITATION dans une cellule markdown.

Ce qu'il DETECTE (DETERMINISTE)
-------------------------------
Une cellule markdown contient une citation verbatim si elle inclut, dans la
meme cellule :

  1. une ancre de citation : `code[N]`, `code (ci-dessus|ci-dessous)`,
     `cellule ci-dessus`, `cellule ci-dessous`, `Raw output`, ou similaire ;
  2. un fragment backtick significatif (>= MIN_CITATION_CHARS caracteres
     alphanumeriques consecutifs a l'interieur d'une paire de backticks) ;
  3. la cellule de code ciblee, resolue par voisinage ou par N, produit une
     sortie sur laquelle le fragment n'est PAS retrouvé apres normalisation
     des blancs et strip des prefixes `Raw output :`.

Les seuils sont explicites, comme `detect_fabricated_outputs.py` et
`detect_blank_figures.py`. Pas de ML, pas d'heuristique floue.

Known blind spots (hors scope par design)
-----------------------------------------
- CITATIONS COURTES : un fragment de < MIN_CITATION_CHARS alphanum (typiquement
  un mot-cle isole comme `True`, `42`, `OK`) n'est pas considere -- le taux
  de collision sur les noms courts dans un notebook technique est trop
  eleve. Mitigation : revue a la main du contenu non-flagge.
- CITATIONS DE CHEMINS / URLS : les chaines `https://...`, `/path/to/file`,
  `name.ipynb` sont exclues (pattern PATH_LIKE_RE) parce que les chemins
  n'apparaissent generalement pas dans une sortie kernel.
- INLINE CODE vs SORTIE : une cellule markdown peut mentionner du code source
  -- `x = 42` -- qui n'a rien d'une citation de sortie. Mitigation : on
  exige la PRESENCE d'une ANCRE `code[N]` ou similaire dans la cellule pour
  traiter les fragments comme candidats.
- NOMS D'IDENTIFIANTS ISOLES (FONCTIONS, CLASSES, VARIABLES) : un fragment
  comme `` `AddNoOverlap` `` ou `` `backtracking_improved` `` (single word,
  identifiant C-like sans caractere structurel) est une REFERENCE D'API dans
  la prose, PAS une citation de sortie. Filtre `_is_identifier_only`
  applique en amont -- voir le test
  `TestIdentifierOnlyFilter::test_real_notebook_finds_no_false_positive_on_identifier_citation`.
- NORMALISATION DES BLANCS : on collapse les espaces et on strip
  ponctuation Extreme (Unicode), mais on preserve la casse. Une signature
  `NormTails : ∀ ...` est case-sensitive -- le detecteur ne la confondra
  pas avec une variante `normtails`.
- LEAN RAW OUTPUT : la sortie Alectryon redouble le nom de declaration ;
  le strip `messages[].data['text/plain']` d'un `#check` est un bloc
  multi-ligne ou la premiere ligne reprend le nom du lemme. On normalise
  en JOINANT toutes les lignes de la sortie en un seul texte et en cherchant
  le fragment apres strip des prefixes de redoublement.

Usage
-----
    python detect_fabricated_verbatim.py NB.ipynb                   # un notebook
    python detect_fabricated_verbatim.py --family Search            # une famille
    python detect_fabricated_verbatim.py                            # tous les notebooks
    python detect_fabricated_verbatim.py NB.ipynb --json           # sortie machine
    python detect_fabricated_verbatim.py NB.ipynb --check          # exit 1 si verbatim fabrique (CI-ready)

Exit codes
----------
    0 -- aucune citation verbatim fabriquee (ou mode non --check)
    1 -- une ou plusieurs citations verbatim fabriquees (--check seulement)
    2 -- erreur (notebook illisible, famille introuvable)

Voir aussi
----------
- `detect_fabricated_outputs.py` (#13410) -- axe 2 : sorties fabriquees (Rows N, dataframes 0.0)
- `detect_blank_figures.py` (#6918 MERGED) -- axe 1 : images degeneres (PNG 1x1)
- `scan_cell_ordering.py` (#13410) -- POSITION des ancres, pas leur CONTENU
- `.claude/rules/sota-not-workaround.md` -- Prong-A : vrai outil, pas workaround
- `.claude/rules/secrets-hygiene.md` regle 6 -- Stop&Repair : re-executer
- #14324 -- issue de ce detecteur
- #14105, #14111, #14128 -- golden set (3 PRs avant-fix, 3 classes de defaut)
- #13410 -- vague d'enrichissement d'ou viennent les defectueux

Part of #3801 (EPIC SOTA axe-2).
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path


# Ancres de citation. Motif qui designe qu'une cellule markdown PRETEND citer
# une sortie de cellule code. Compiled en lowercase pour tolerance a la casse.
#
# Quatre familles observees dans le golden set :
#   "Sortie observee de code[N]" / "Sortie de code[N]"
#   "Sortie de la cellule ci-dessous" / "ci-dessus"
#   "Raw output : ..."
#   "Voir (aussi|egalement) la cellule (ci-dessus|ci-dessous)"
#
# On capture : (i) le mot-cle ('code' ou 'cellule'), (ii) l'entier N si
# present, (iii) la direction ('ci-dessus' / 'ci-dessous') si presente.
ANCHOR_RE = re.compile(
    r"""
    (?:
        # code[N] : on capture l'entier N dans le groupe 'code_n'.
        # \b sur 'code' pour eviter de matcher 'barcode[5]' etc.
        \bcode\s*[\[\(]\s*(?P<code_n>\d+)\s*[\]\)]
        |
        # cellule (ci-dessus|ci-dessous) -- pas de N, on capture la
        # direction dans le groupe 'dir_above'.
        \bcellule\s+(?P<dir_above>ci-dessus|ci-dessous|ci-?dessous|ci-?dessus)
        |
        # "Raw output" : pas de cible precise.
        \braw\s+output
    )
    """,
    re.IGNORECASE | re.VERBOSE,
)

# Fragment verbatim backtick : on capture le contenu entre backticks qui
# contient au moins MIN_CITATION_CHARS caracteres alphanumeriques consecutifs.
#
# On exclut les fragments purement des chemins / URLs par filtrage ulterieur
# (PATH_LIKE_RE). On supporte le multiline (les verbatims Lean de type
# signature font 4-8 lignes), mais on n'autorise pas un bloc trop long :
# > MAX_CITATION_CHARS caracteres = vraisemblablement un bloc code pedagogique
# (un notebook entier), pas une citation de sortie.
CITATION_RE = re.compile(r"`([^`]+)`", re.DOTALL)
MIN_CITATION_CHARS = 12
MAX_CITATION_CHARS = 600

# Pattern "path-like" : si le fragment est principalement un chemin / URL /
# nom de fichier, on ne le considere pas comme une citation de sortie.
# Operateur : au moins 60% de caracteres non-alphanum OU contient "://"
# OU commence par "/" OU se termine par une extension connue.
PATH_LIKE_RE = re.compile(r"://|\.ipynb\b|\.py\b|\.lean\b|^\s*/")

# Caracteres utilement verifiables dans une citation. On extrait un *echantillon*
# de la citation (les premiers non-whitespace, longueur bornee) pour eviter
# de comparer des paragraphes entiers -- une citation de 80% de la sortie
# n'est PAS un signal de fabrication, c'est une copie legitime. On exige
# un *fragment* identifiable de MIN_PROBE_CHARS caracteres consecutifs
# alphanum ou ponctuation raisonnable.
MIN_PROBE_CHARS = 12
PROBE_BOUNDARY = re.compile(r"[\s,;()\[\]{}]+")


def _load_notebook(path: Path) -> dict | None:
    """Charge un .ipynb en tolerant les erreurs triviales (NotJSON, vide)."""
    try:
        import nbformat
    except ImportError:
        print("ERROR: nbformat non disponible -- pip install nbformat", file=sys.stderr)
        return None
    try:
        nb = nbformat.read(str(path), as_version=4)
    except Exception as exc:
        print(f"WARN: {path.name} illisible ({exc})", file=sys.stderr)
        return None
    return nb


def _cell_text_outputs(cell: dict) -> str:
    """Concatene TOUTES les sorties text/plain d'une cellule en un seul texte.

    Rejoint stdout, stderr (text), text/plain (data) et text/html simplifiee en
    UN SEUL string. Pour Lean, Alectryon emet la signature en multi-ligne
    messages[].data['text/plain'] ; ici on collapse en un seul bloc pour
    faciliter la recherche substring.
    """
    parts = []
    for out in cell.get("outputs", []) or []:
        if not isinstance(out, dict):
            continue
        data = out.get("data", {}) if "data" in out else {}
        for mime in ("text/plain", "text/html"):
            payload = data.get(mime)
            if payload is None:
                continue
            if isinstance(payload, list):
                payload = "".join(str(x) for x in payload)
            if not isinstance(payload, str):
                payload = str(payload)
            parts.append(payload)
        text = out.get("text")
        if isinstance(text, list):
            text = "".join(str(x) for x in text)
        if isinstance(text, str):
            parts.append(text)
    return "\n".join(parts)


def _normalize(text: str) -> str:
    """Normalisation pour comparaison substring.

    Collapse les espaces multiples, strip les prefixes `Raw output :` et
    variants, enleve les zero-width chars. Preserve la casse (signatures
    Lean case-sensitive). Le but n'est pas un match exact mais une
    tolerance aux differences d'espace et de format communes entre la
    sortie kernel et la citation manuelle.
    """
    # Strip les prefixes "Raw output :" / "raw output :"
    text = re.sub(r"^\s*(?:raw\s+output\s*[:\-]?\s*)", "", text, flags=re.IGNORECASE)
    # Collapse whitespace
    text = re.sub(r"\s+", " ", text)
    # Strip zero-width / BOM
    text = text.replace("", "").replace("﻿", "").replace("", "")
    return text.strip()


def _resolve_code_target(cells: list, anchor_cell_idx: int, code_n: int | None,
                         direction: str | None) -> int | None:
    """Resout la cellule de code visee par une ancre markdown.

    Strategies (du plus precis au plus tolérant) :
      1. `code[N]` -- N est l'index 1-based parmi les cellules CODE.
      2. `cellule ci-dessus` -- premiere cellule code rencontree en remontant.
      3. `cellule ci-dessous` -- premiere cellule code en descendant.
      4. `raw output` -- premiere cellule code non-vide en-dessous.

    Retourne l'index 0-based dans `cells`, ou None si non resolu.
    """
    if code_n is not None:
        # Index 1-based parmi les CODE cells. On enumere toutes les cellules
        # code et on prend la N-ieme.
        code_idxs = [i for i, c in enumerate(cells) if c.get("cell_type") == "code"]
        if 1 <= code_n <= len(code_idxs):
            return code_idxs[code_n - 1]
        return None

    if direction in ("ci-dessus", "ci-dessus", "ci-dessus"):
        for i in range(anchor_cell_idx - 1, -1, -1):
            if cells[i].get("cell_type") == "code":
                return i
        return None

    if direction in ("ci-dessous", "ci-dessous", "ci-dessous"):
        for i in range(anchor_cell_idx + 1, len(cells)):
            if cells[i].get("cell_type") == "code":
                return i
        return None

    # raw output : premiere cellule code avec sortie non-vide en-dessous.
    for i in range(anchor_cell_idx + 1, len(cells)):
        c = cells[i]
        if c.get("cell_type") != "code":
            continue
        if c.get("outputs"):
            return i
    return None


def _extract_citation_probe(fragment: str) -> str:
    """Extrait une *probe* (chaine identifiable) d'un fragment verbatim.

    La probe est le PREMIER mot significatif de >= MIN_PROBE_CHARS caracteres
    alphanumeriques consecutifs (apres strip des prefixes operateurs).
    Une probe plus courte que MIN_PROBE_CHARS ne donne rien.

    Exemples :
      "(f : ERC20.Address n → ℕ) (s : ...) ..." -> probe = "ERC20.Address"
      "1.213061" -> probe = "1.213061"
      "JVM operationnelle : True" -> probe = "operationnelle"
    """
    # Mots consecutifs alphanumeric + underscore, en detaillant les separateurs
    for word in PROBE_BOUNDARY.split(fragment):
        cleaned = re.sub(r"^[^\w]+|[^\w]+$", "", word)
        if len(cleaned) >= MIN_PROBE_CHARS:
            return cleaned
    # Repli : retourner le fragment nettoye si >= MIN_PROBE_CHARS au total
    cleaned_all = re.sub(r"\s+", "", fragment)
    if len(cleaned_all) >= MIN_PROBE_CHARS:
        return cleaned_all[:60]
    return ""


def _find_probes_in_fragment(fragment: str) -> list[str]:
    """Renvoie TOUTES les probes (>= MIN_PROBE_CHARS) d'un fragment verbatim.

    Une citation peut etre SCINDABLE en plusieurs probes -- par exemple une
    signature Lean qui cite `{n : ℕ} (f : ...)` produit plusieurs tokens
    identifiables. On teste chacune : si UNE seule probe est retrouvee
    dans la sortie normalisee, la citation est consideree comme legitime
    (presence partielle suffit -- le verbatim peut avoir reformate).
    """
    probes = []
    for word in PROBE_BOUNDARY.split(fragment):
        cleaned = re.sub(r"^[^\w]+|[^\w]+$", "", word)
        if len(cleaned) >= MIN_PROBE_CHARS and not cleaned.startswith("//"):
            probes.append(cleaned)
    if not probes:
        cleaned_all = re.sub(r"\s+", "", fragment)
        if len(cleaned_all) >= MIN_PROBE_CHARS:
            probes.append(cleaned_all[:60])
    return probes[:6]  # plafond pour eviter explosion


def _is_path_like(fragment: str) -> bool:
    """True si le fragment ressemble a un chemin / URL et n'est pas une
    citation de sortie."""
    if PATH_LIKE_RE.search(fragment):
        return True
    # Majorite de non-alphanum = code inline / chemin
    alnum = sum(c.isalnum() for c in fragment)
    if len(fragment) > 8 and alnum / len(fragment) < 0.5:
        return True
    return False


# Identifiant simple (nom de fonction, classe, module) = PAS un verbatim de
# sortie. Une cellule markdown qui ecrit "nous utilisons `AddNoOverlap` pour
# la contrainte" cite du CODE SOURCE (un nom API), pas la SORTIE d'une cellule
# code. Le detecteur n'a pas vocation a flagger les references d'API ; c'est
# une confusion de categorie.
#
# Heuristique : un fragment est "identifier-only" si :
#   - c'est un seul mot (pas d'espace, pas de retour a la ligne) ; ET
#   - tous les caracteres sont dans `[A-Za-z0-9_]` (identifiant C-like) ; ET
#   - il ne contient AUCUN caractere structurel de sortie (`:`, `=`, `(`, `)`,
#     `{`, `}`, `[`, `]`, `"`, `'`, `,`, `;`, `.` suivi d'un espace, `\`).
#
# Si les trois conditions sont reunies, ce n'est PAS une citation de sortie,
# c'est un nom. On l'ignore.
IDENTIFIER_ONLY_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")
OUTPUT_STRUCTURE_CHARS = set(":={}[]()\"',;.\\")


def _is_identifier_only(fragment: str) -> bool:
    """True si le fragment est un simple nom d'identifiant (fonction, classe,
    variable). Ces fragments NE SONT PAS des citations de sortie : ce sont des
    references d'API documentees en prose.

    Exemples retenus (identifier-only = VRAI) :
      "AddNoOverlap", "backtracking_improved", "AllDifferent"
    Exemples rejetes (output-like = FAUX) :
      "AddNoOverlap(capacity)", "JDK portable: True", "0.2706705664732254"
      "(f : ERC20.Address n)", "{n : Nat}"
    """
    stripped = fragment.strip()
    if "\n" in stripped or " " in stripped:
        return False  # multi-word = sortie multi-ligne probable
    if any(c in OUTPUT_STRUCTURE_CHARS for c in stripped):
        return False  # caractere structurel de sortie
    return bool(IDENTIFIER_ONLY_RE.match(stripped))


def _scan_notebook(path: Path, threshold: int = 1) -> dict:
    """Scan un notebook ; renvoie {"findings": [...], "anchors_total": N,
    "citations_total": N, "fabricated": int}.

    `threshold` est le nombre MIN de probes retrouvees dans la sortie pour
    declarer une citation legitime. 1 = match d'au moins une probe suffit.
    """
    nb = _load_notebook(path)
    if nb is None:
        return {"path": str(path), "error": "load_failed"}

    cells = nb.get("cells", []) or []
    findings = []
    anchors_total = 0
    citations_total = 0

    for idx, cell in enumerate(cells):
        if cell.get("cell_type") != "markdown":
            continue
        src = cell.get("source", "")
        if isinstance(src, list):
            src = "".join(src)

        # 1. Detecter les ancres de citation dans la cellule.
        anchors = []
        for m in ANCHOR_RE.finditer(src):
            anchors.append({
                "code_n": int(m.group("code_n")) if m.group("code_n") else None,
                "direction": m.group("dir_above"),
                "span": m.span(),
            })
        if not anchors:
            continue
        anchors_total += len(anchors)

        # 2. Detecter les fragments backtick.
        citations = []
        for m in CITATION_RE.finditer(src):
            frag = m.group(1)
            if not isinstance(frag, str):
                continue
            stripped = frag.strip()
            if len(stripped) < MIN_CITATION_CHARS:
                continue
            if len(stripped) > MAX_CITATION_CHARS:
                continue
            if _is_path_like(stripped):
                continue
            if _is_identifier_only(stripped):
                # Nom de fonction / classe / variable = reference d'API en
                # prose, pas une citation de sortie. On ne flague pas.
                continue
            citations.append({"fragment": stripped, "span": m.span()})
        if not citations:
            continue
        citations_total += len(citations)

        # 3. Pour chaque citation, tenter de trouver la sortie reelle
        #    correspondante. Une citation est "pres de" une ancre si elle
        #    est dans la meme cellule (les verbatims fabriques sont TOUS
        #    intra-cellules sur les 3 PRs du golden set).
        for c in citations:
            for a in anchors:
                target_idx = _resolve_code_target(
                    cells, idx, a["code_n"], a["direction"]
                )
                if target_idx is None:
                    continue
                target_cell = cells[target_idx]
                outputs_text = _cell_text_outputs(target_cell)
                normalized = _normalize(outputs_text)
                if not normalized:
                    continue
                probes = _find_probes_in_fragment(c["fragment"])
                if not probes:
                    continue
                hits = sum(1 for p in probes if p in normalized)
                if hits < threshold:
                    findings.append({
                        "kind": "fabricated_verbatim",
                        "notebook": str(path),
                        "markdown_cell_idx": idx,
                        "code_cell_idx": target_idx,
                        "fragment": c["fragment"][:200],
                        "probes_unchecked": probes,
                        "hits_in_output": hits,
                        "hint": "anchor={}".format(
                            "code[{}]".format(a["code_n"])
                            if a["code_n"] is not None
                            else a["direction"] or "raw_output"
                        ),
                    })

    return {
        "path": str(path),
        "anchors_total": anchors_total,
        "citations_total": citations_total,
        "findings": findings,
    }


def _iter_notebooks(roots: list[Path], family: str | None) -> list[Path]:
    """Enumere les .ipynb a scanner. Si family donne, scanne uniquement cette
    sous-arborescence ; sinon, scanne `MyIA.AI.Notebooks/`."""
    if family:
        base = Path("MyIA.AI.Notebooks") / family
        if not base.exists():
            return []
        return sorted(base.rglob("*.ipynb"))
    return sorted(Path("MyIA.AI.Notebooks").rglob("*.ipynb"))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("paths", nargs="*", help="notebooks ou familles à scanner")
    parser.add_argument("--family", help="famille (sous MyIA.AI.Notebooks/)")
    parser.add_argument("--json", action="store_true", help="sortie JSON")
    parser.add_argument("--check", action="store_true",
                        help="exit 1 si citations verbatim fabriquées détectées")
    args = parser.parse_args()

    if args.paths:
        targets = [Path(p) for p in args.paths]
    else:
        targets = _iter_notebooks([], args.family)

    notebooks = []
    for t in targets:
        if t.is_dir() or (not t.exists() and "/" in str(t)):
            # Famille ou sous-arborescence
            for nb in sorted(t.rglob("*.ipynb")):
                notebooks.append(nb)
        else:
            notebooks.append(t)

    aggregated = {"notebooks_scanned": 0, "findings": [], "anchors_total": 0,
                  "citations_total": 0}

    for nb_path in notebooks:
        aggregated["notebooks_scanned"] += 1
        r = _scan_notebook(nb_path)
        if "error" in r:
            continue
        aggregated["anchors_total"] += r["anchors_total"]
        aggregated["citations_total"] += r["citations_total"]
        for f in r["findings"]:
            aggregated["findings"].append(f)

    if args.json:
        print(json.dumps(aggregated, indent=2, ensure_ascii=False))
    else:
        n = len(aggregated["findings"])
        print(f"Notebooks scanned : {aggregated['notebooks_scanned']}")
        print(f"Anchors found     : {aggregated['anchors_total']}")
        print(f"Citations scanned : {aggregated['citations_total']}")
        print(f"Findings          : {n}")
        if n:
            print()
            for f in aggregated["findings"][:20]:
                print(f"  - {f['notebook']} md[{f['markdown_cell_idx']}] -> "
                      f"code[{f['code_cell_idx']}] hint={f['hint']} "
                      f"probes={len(f['probes_unchecked'])} hits={f['hits_in_output']}")
                print(f"      fragment: {f['fragment'][:120]}")

    if args.check:
        return 1 if aggregated["findings"] else 0
    return 0


if __name__ == "__main__":
    sys.exit(main())
