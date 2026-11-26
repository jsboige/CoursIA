#!/usr/bin/env python3
"""Ratchet prose<->sorties : tout nombre de mesure cite dans la prose de lecture
doit exister dans les sorties commitees du meme carnet.

Origine : issue #27231 (réserve 1 de la review NanoClaw sur PR #27206). La prose
de lecture d'ICT-38 citait les valeurs d'un run antérieur non commite (0.0742 /
0.0625 / 0.1953) alors que la sortie commitee rendait d'autres mesures (0.0859 /
0.0547 / 0.2109) -- un decalage invisible a toutes les gardes existantes : le
contenu existe, la sortie existe, seule la CORRESPONDANCE entre les deux manque.

Classe de defaut mesuree et distincte des organes voisins :
- ``check_prose_quantitative_claims.py`` cible les COMPTEURS d'artefacts du depot
  (« 140 lignes », « 47 carnets ») ; ici ce sont les VALEURS DE MESURE citees.
- ``check_output_collapse.py`` / ``check_source_collapse.py`` mesurent la perte de
  volume de sortie ou de source ; ici le volume est intact, c'est l'alignement
  numerique qui derive.

Perimetre (v1, calibre sur ICT-35 + ICT-38 pre/post #27206) :
- Cellules markdown de LECTURE : cellule dont l'entete (`#...`) matche un marqueur
  d'interpretation (Lecture, Interpretation, Ce que, A retenir, Bilan, Conclusion),
  plus les cellules markdown sans entete qui la suivent immediatement (prose de
  continuation du meme bloc de lecture).
- Seuls les nombres a >= 3 decimales sont verifies : une valeur a 3+ decimales est
  une mesure copiee, pas un calcul de tete. Les seuils (>= 0,5), rapports
  (« 2,5 fois »), arrondis de narration (0,33) et compteurs restent hors champ
  (mesure : seuls les 4-decimales d'ICT-38 portaient le defaut).
- Exemptions documentees, chacune issue d'un cas mesure du jeu de reference :
  * derivee fractionnaire inline « 1/16 = 0.0625 » (ICT-38 post-fix) : la prose
    porte elle-meme la preuve du calcul ;
  * nombres entre backticks : identifiants de code / parametres, pas des mesures ;
  * annees 1900-2100.
- Correspondance numerique (pas sous-chaine) : Decimal en egalite exacte, OU
  arrondi/troncature d'un nombre de sortie PLUS precis a la precision de la
  citation (« 0.0859 » correspond a une sortie « 0.0859375 » ; « 1,000 » a
  « 1.0000 »). Les sorties lues : stream + text/plain + text/markdown + text/html
  de toutes les cellules code.

Modes :
- positionnel ``base``      : ratchet PR -- carnets .ipynb changes sous
                              MyIA.AI.Notebooks, citations dont la ligne source
                              n'existe pas dans la version base ; findings => exit 1.
- ``--all``                 : balayage complet, rapport seul, TOUJOURS exit 0
                              (advisory par construction, tient le sweep cron).
- ``--notebook PATH``       : un carnet, findings => exit 1 (calibration, tests).
- ``--self-test``           : fixtures embarquees (pre-controle, avant tout argv).
- ``--json``                : sortie machine.

Statut : garde ADVISORY de la voie rapide (fast_lane_registry, blocking=False),
enregistree sous « Prose-numbers vs outputs ratchet (base vs PR, advisory) » --
voie WARN tracee par #8053/#15901 : un detecteur neuf commence advisory, la
promotion suit la fournee de remediation (plan Q162 d dans le body de la PR).
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import unicodedata
from dataclasses import dataclass, field
from decimal import Decimal, InvalidOperation, ROUND_DOWN, ROUND_HALF_EVEN
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
NOTEBOOK_GLOB = "MyIA.AI.Notebooks/**/*.ipynb"

# --- Perimetre prose de lecture ---------------------------------------------

LECTURE_HEADING_RE = re.compile(
    r"^#{1,6}\s.*\b(Lecture|Interpr[eé]tation|Interpretation|Ce que|[AÀ] retenir|Bilan|Conclusion)\b",
    re.MULTILINE,
)

# --- Nombres -----------------------------------------------------------------
# Separateurs de milliers frances (espace, insecable, fine, fine insecable)
# neutralises entre deux chiffres avant tokenisation.
_THIN_SPACES = "    "

_NUM_RE = re.compile(r"[-−]?\d+(?:[.,]\d+)?")
_FRACTION_DERIVATION_RE = re.compile(
    r"\d+\s*/\s*\d+\s*=\s*([-−]?\d+(?:[.,]\d+)?)"
)
_BACKTICK_RE = re.compile(r"`[^`\n]*`")
# Identifiants, pas des mesures : numeros arXiv (2202.05822), DOI, dates --
# mesurés dans les liens markdown de la bibliographie (CLIPasso, census
# initial). Le texte du lien ET sa cible sont exemptes, plus les URLs nues.
_LINK_RE = re.compile(r"!?\[[^\]]*\]\([^)]*\)")
_URL_RE = re.compile(r"https?://\S+")
# DOI en texte nu (identifiant bibliographique, pas une mesure) : mesure sur
# QC-Py-08 cellule 71 -- l'extracteur y lisait 10.3905, 4.060, 10.1111,
# -6261.1952 et 10.1086 comme des valeurs, fragments des tokens
# « DOI 10.3905/jpm.2010.36.4.060 », « DOI 10.1111/j.1540-6261.1952.tb01525.x »,
# « DOI 10.1086/294846 » hors de tout lien. Le token ENTIER (prefixe 10.xxxx +
# suffixe) est exempt, comme une URL ; une mesure a 3+ decimales SANS slash
# apres le prefixe reste verifiee.
_DOI_RE = re.compile(r"\b10\.\d{4,9}/\S+")
# Valeur DECLAREE citee (litterature/theorie), pas mesuree : l'auteur dit lui-meme
# que le nombre n'est pas le sien (« la prediction 4,267 ... est citee », seuil
# 3-SAT de Complexity-02b/02c, mesure dans le census initial). L'exemption porte
# sur le nombre GOUVERNE par le mot-cle (fenetre _QUOTED_WINDOW), jamais sur la
# ligne entiere (sonde Hermes #27233, faux negatif 1 : « l'article rapporte
# 0.0742, notre run rend 0.0859 » ne doit exempter que 0.0742).
_QUOTED_VALUE_RE = re.compile(
    r"\b(cit[eé]e?s?|papier|article|litt[eé]rature|literature|"
    r"th[eé]or[eè]me|theorem|conjecture|pr[eé]diction|prediction)\b",
    re.IGNORECASE,
)
_QUOTED_WINDOW = 40
_MIN_DECIMALS = 3
_YEAR_MIN, YEAR_MAX = 1900, 2100


def _normalize_digits(text: str) -> str:
    """Espaces de milliers francaises (famille insecable) entre chiffres -> rien.

    L'espace ORDINAIRE n'est PAS neutralisee : « F1 0.217 » (ICT-35, mesure) doit
    rester deux tokens, pas fusionner en 10.217. Les vrais separateurs de milliers
    typographiques (insecable, fine, fine insecable) le sont.
    """
    out = []
    for i, ch in enumerate(text):
        if ch in _THIN_SPACES:
            prev_digit = i > 0 and text[i - 1].isdigit()
            nxt_digit = i + 1 < len(text) and text[i + 1].isdigit()
            if prev_digit and nxt_digit:
                continue
        if ch == "−":
            ch = "-"
        out.append(ch)
    return "".join(out)


@dataclass
class NumToken:
    value: Decimal
    decimals: int
    raw: str


def _decimals_of(raw: str) -> int:
    sep = "," if "," in raw else ("." if "." in raw else "")
    return len(raw.split(sep)[1]) if sep else 0


def _to_decimal(raw: str) -> Decimal | None:
    try:
        return Decimal(raw.replace(",", "."))
    except InvalidOperation:
        return None


def extract_numbers(text: str) -> list[NumToken]:
    """Tous les nombres decimaux du texte, normalises (cote prose ET cote sorties)."""
    tokens = []
    for m in _NUM_RE.finditer(_normalize_digits(text)):
        raw = m.group(0)
        val = _to_decimal(raw)
        if val is None:
            continue
        tokens.append(NumToken(value=val, decimals=_decimals_of(raw), raw=raw))
    return tokens


# --- Cote sorties commitees --------------------------------------------------


_HTML_TAG_RE = re.compile(r"<[^>]+>")
_HTML_ENTITY_RE = re.compile(r"&[a-zA-Z#0-9]+;")
# Blocs invisibles au lecteur : le contenu de <style>/<script> n'est jamais
# rendu comme valeur -- un nombre qui n'y vit QUE la ne peut pas ancrer une
# citation (reserve ai-01 sur la fournee 8 ML-04). Retires ENTIERS, contenu
# compris, avant le depouillement des balises.
_HTML_INVISIBLE_RE = re.compile(
    r"<(style|script)\b[^>]*>.*?</\1\s*>", re.IGNORECASE | re.DOTALL
)


def output_numbers(nb: dict) -> list[NumToken]:
    """Nombres de toutes les sorties (stream + text/plain + text/markdown + text/html) des cellules code.

    ``text/markdown`` est lu depuis #27231 fournée 5 : les carnets de la série
    App-* (Search) rendent leurs mesures via ``display(Markdown(...))``, dont le
    ``text/plain`` est l'objet-repr ``<IPython.core.display.Markdown object>``
    (aucun nombre). Sans ce mime, 25 citations ancrées du stock étaient
    rapportées findings (App-18 : 25/29). Précédents multipart : check_equivalence,
    regression_scan, scan_enrich_quality lisent déjà ce mime.

    ``text/html`` est lu depuis la fournée 8 (ML-04) : les tables riches .NET
    Interactive portent leurs valeurs dans le texte des balises
    (``<pre>1.3080</pre>``), pas dans le ``text/plain`` -- les balises sont
    dépouillées avant extraction.
    """
    pool: list[NumToken] = []
    for cell in nb.get("cells", []):
        if cell.get("cell_type") != "code":
            continue
        for out in cell.get("outputs", []) or []:
            chunks: list[str] = []
            text = out.get("text")
            if isinstance(text, str):
                chunks.append(text)
            elif isinstance(text, list):
                chunks.extend(t for t in text if isinstance(t, str))
            data = out.get("data") or {}
            for mime in ("text/plain", "text/markdown"):
                payload = data.get(mime)
                if isinstance(payload, str):
                    chunks.append(payload)
                elif isinstance(payload, list):
                    chunks.extend(t for t in payload if isinstance(t, str))
            html = data.get("text/html")
            if isinstance(html, str):
                html_chunks = [html]
            elif isinstance(html, list):
                html_chunks = [t for t in html if isinstance(t, str)]
            else:
                html_chunks = []
            for chunk in html_chunks:
                # Tables riches .NET Interactive : les valeurs vivent dans le
                # texte des balises (<pre>1.3080861318665928</pre>), pas dans
                # le balisage -- on lit le texte hors balises. Les blocs
                # <style>/<script> sont retires avec leur contenu : leur
                # texte n'est pas rendu au lecteur (nombres invisibles).
                visible = _HTML_INVISIBLE_RE.sub(" ", chunk)
                text_only = _HTML_ENTITY_RE.sub(" ", _HTML_TAG_RE.sub(" ", visible))
                pool.extend(extract_numbers(text_only))
            for chunk in chunks:
                pool.extend(extract_numbers(chunk))
    return pool


# --- Correspondance numerique ------------------------------------------------


def _quantized(val: Decimal, prec: int, rounding: str) -> Decimal:
    return val.quantize(Decimal(1).scaleb(-prec), rounding=rounding)


def citation_matches(cit: NumToken, pool: list[NumToken], *, magnitude: bool = False) -> bool:
    """Egalite exacte, ou arrondi/troncature d'une sortie PLUS PRECISE.

    « 0.0859 » correspond a une sortie 0.0859375 (print formate), « 1,000 » a
    1.0000. Le sens inverse (citation plus precise que le print, p.ex. 1.99923
    vs 1.9992, Complexity-03e) est REFUSE : mesure sur le cas fondateur, la
    correspondance par extension de prefixe MASQUE le defaut -- la citation
    perimee 0.1953 matchait par prefixe une sortie 0.195 d'une AUTRE quantite.
    Ce residu reste un bruit du sweep report-only, jamais un masquage.

    ``magnitude=True`` (prose « ±0.002 ») : la citation est une AMPLITUDE, la
    sortie porte souvent la valeur SIGNEE (« +-0.002 pres », extrait -0.002) --
    la correspondance se joue alors sur |x| (2.11-Regularisation, 4 faux
    positifs du sweep #27233 : la sortie committee dit elle-meme « suit LASSO
    a +-0.002 pres »). Egalite de magnitude EXACTE, jamais floue.
    """
    for out in pool:
        candidates = (out.value, -out.value) if magnitude else (out.value,)
        for v in candidates:
            if v == cit.value:
                return True
            if out.decimals > cit.decimals:
                for rounding in (ROUND_HALF_EVEN, ROUND_DOWN):
                    try:
                        if _quantized(v, cit.decimals, rounding) == cit.value:
                            return True
                    except InvalidOperation:
                        continue
    return False


# --- Cote prose ---------------------------------------------------------------


@dataclass
class Finding:
    file: str
    cell_index: int
    line_no: int
    value: str
    line: str
    nearest: str | None = None


@dataclass
class NotebookResult:
    file: str
    citations_checked: int = 0
    findings: list[Finding] = field(default_factory=list)


def _nearest(cit: Decimal, pool: list[NumToken]) -> str | None:
    """Valeur de sortie la plus proche, pour le rapport (diagnostic, pas preuve)."""
    best = None
    best_gap = None
    for out in pool:
        gap = abs(out.value - cit)
        if best_gap is None or gap < best_gap:
            best, best_gap = out, gap
    return str(best.value) if best is not None else None


def lecture_cells(nb: dict) -> set[int]:
    """Indices des cellules markdown de lecture (entete marque + continuation)."""
    in_scope: set[int] = set()
    prev_in_scope = False
    for i, cell in enumerate(nb.get("cells", [])):
        if cell.get("cell_type") != "markdown":
            prev_in_scope = False
            continue
        src = "".join(cell.get("source", []))
        has_heading = bool(re.match(r"\s*#{1,6}\s", src))
        if LECTURE_HEADING_RE.search(src):
            in_scope.add(i)
            prev_in_scope = True
        elif prev_in_scope and not has_heading:
            # Prose de continuation du bloc de lecture (pas une nouvelle section).
            in_scope.add(i)
            prev_in_scope = True
        else:
            prev_in_scope = False
    return in_scope


def _quoted_governed_spans(line_norm: str) -> list[tuple[int, int]]:
    """Spans des nombres GOUVERNES par un mot-cle bibliographique.

    Premier nombre apres le mot-cle, dernier nombre avant, dans une fenetre
    bornee et sans nombre intermediaire : « l'article rapporte 0.0742, notre
    run rend 0.0859 » n'exempte que 0.0742 — les mesures du run restent
    verifiees (sonde Hermes #27233, faux negatif 1 ; l'ancien `search(line)`
    exemptait la ligne entiere et rendait le defaut fondateur invisible).
    """
    spans: list[tuple[int, int]] = []
    nums = list(_NUM_RE.finditer(line_norm))
    for kw in _QUOTED_VALUE_RE.finditer(line_norm):
        for n in nums:
            if n.start() >= kw.end() and n.start() - kw.end() <= _QUOTED_WINDOW:
                spans.append(n.span())
                break
        for n in reversed(nums):
            if n.end() <= kw.start() and kw.start() - n.end() <= _QUOTED_WINDOW:
                spans.append(n.span())
                break
    return spans


def analyze_notebook(nb: dict, rel_path: str) -> NotebookResult:
    result = NotebookResult(file=rel_path)
    pool = output_numbers(nb)
    for i in lecture_cells(nb):
        cell = nb["cells"][i]
        src = cell.get("source", [])
        # Exemptions calculees sur la cellule entiere, en coordonnees de la
        # MEME chaine normalisee que les positions cote nombres : calculer les
        # spans sur le texte brut faisait glisser les positions des nombres
        # (les separateurs de milliers NBSP sont retires cote nombres, pas cote
        # spans) et exempter a tort une mesure voisine d'un lien (sonde Hermes
        # #27233, faux negatif 2).
        cell_text = "".join(src)
        cell_norm = _normalize_digits(cell_text)
        exempt_spans = [m.span() for m in _BACKTICK_RE.finditer(cell_norm)]
        exempt_spans += [m.span() for m in _LINK_RE.finditer(cell_norm)]
        exempt_spans += [m.span() for m in _URL_RE.finditer(cell_norm)]
        exempt_spans += [m.span() for m in _DOI_RE.finditer(cell_norm)]
        derived_values = {
            _to_decimal(m.group(1))
            for m in _FRACTION_DERIVATION_RE.finditer(cell_text)
        }
        derived_values.discard(None)
        # Position de chaque ligne dans le texte concatene NORMALISE (les
        # spans sont en coordonnees de cell_norm, pas de la ligne brute).
        offset = 0
        for line_no, line in enumerate(src):
            line_norm = _normalize_digits(line)
            line_start, line_end = offset, offset + len(line_norm)
            offset = line_end
            # Exemption « valeur citee » bornee au nombre gouverne par le
            # mot-cle, pas a la ligne entiere (sonde Hermes #27233, FN 1).
            quoted_spans = _quoted_governed_spans(line_norm)
            for m in _NUM_RE.finditer(line_norm):
                raw = m.group(0)
                decimals = _decimals_of(raw)
                val = _to_decimal(raw)
                if val is None or decimals < _MIN_DECIMALS:
                    continue
                if _YEAR_MIN <= val <= YEAR_MAX and val == val.to_integral_value():
                    continue
                if val in derived_values:
                    continue
                abs_pos = line_start + m.start()
                if any(s <= abs_pos < e for s, e in exempt_spans):
                    continue
                if any(s <= m.start() < e for s, e in quoted_spans):
                    continue
                result.citations_checked += 1
                # « ±0.002 pres » : amplitude -- la sortie porte la valeur
                # signee, la correspondance se joue sur |x| (cf docstring).
                is_pm = line_norm[: m.start()].rstrip().endswith("±")
                if not citation_matches(
                    NumToken(val, decimals, raw), pool, magnitude=is_pm
                ):
                    result.findings.append(
                        Finding(
                            file=rel_path,
                            cell_index=i,
                            line_no=line_no,
                            value=raw,
                            line=line.strip(),
                            nearest=_nearest(val, pool),
                        )
                    )
    return result


# --- Entrees : carnets + git --------------------------------------------------


def _load_notebook(path: Path) -> dict | None:
    try:
        with open(path, encoding="utf-8") as fh:
            return json.load(fh)
    except (OSError, json.JSONDecodeError) as exc:
        print(f"WARN: {path}: illisible ({exc})", file=sys.stderr)
        return None


def _git(args: list[str], cwd: Path) -> str:
    import subprocess

    proc = subprocess.run(
        ["git", "-C", str(cwd), *args], capture_output=True, text=True,
        encoding="utf-8", errors="replace",
    )
    if proc.returncode != 0:
        raise RuntimeError(f"git {' '.join(args)}: {proc.stderr.strip()}")
    return proc.stdout


def _changed_notebooks(base: str, cwd: Path) -> list[str]:
    out = _git(["diff", "--name-only", base, "--", "MyIA.AI.Notebooks"], cwd)
    return [p for p in out.splitlines() if p.endswith(".ipynb")]


def _base_lines(base: str, rel: str, cwd: Path) -> set[str]:
    """Lignes sources des cellules markdown de la version base (ratchet ligne)."""
    try:
        raw = _git(["show", f"{base}:{rel}"], cwd)
    except RuntimeError:
        return set()
    try:
        nb = json.loads(raw)
    except json.JSONDecodeError:
        return set()
    lines: set[str] = set()
    for cell in nb.get("cells", []):
        if cell.get("cell_type") == "markdown":
            lines.update(l.strip() for l in cell.get("source", []))
    return lines


def scan_all(root: Path) -> list[NotebookResult]:
    results = []
    for path in sorted(root.glob("MyIA.AI.Notebooks/**/*.ipynb")):
        nb = _load_notebook(path)
        if nb is not None:
            results.append(analyze_notebook(nb, path.relative_to(root).as_posix()))
    return results


def scan_diff(base: str, root: Path) -> list[NotebookResult]:
    results = []
    for rel in _changed_notebooks(base, root):
        path = root / rel
        if not path.exists():
            continue
        nb = _load_notebook(path)
        if nb is None:
            continue
        result = analyze_notebook(nb, rel)
        base_lines = _base_lines(base, rel, root)
        # Ratchet : seules les lignes de prose NOUVELLES (absentes de la base)
        # sont re-litigees ; la prose pre-existante releve du sweep --all.
        result.findings = [
            f for f in result.findings if f.line.strip() not in base_lines
        ]
        results.append(result)
    return results


def scan_notebook(path: Path, root: Path) -> NotebookResult:
    nb = _load_notebook(path)
    if nb is None:
        raise SystemExit(f"illisible : {path}")
    return analyze_notebook(nb, path.resolve().relative_to(root).as_posix())


# --- Rapport -------------------------------------------------------------------


def _print_report(results: list[NotebookResult], as_json: bool) -> int:
    findings = [f for r in results for f in r.findings]
    checked = sum(r.citations_checked for r in results)
    if as_json:
        print(json.dumps({
            "status": "OK" if not findings else "MISMATCH",
            "notebooks_scanned": len(results),
            "citations_checked": checked,
            "findings_count": len(findings),
            "findings": [{
                "file": f.file, "cell": f.cell_index, "line": f.line_no,
                "value": f.value, "nearest_output": f.nearest,
                "context": f.line[:160],
            } for f in findings],
        }, ensure_ascii=False, indent=2))
    else:
        for f in findings:
            near = f" (plus proche en sortie : {f.nearest})" if f.nearest else ""
            print(
                f"MISMATCH {f.file} cell {f.cell_index} ligne {f.line_no} : "
                f"valeur citee {f.value} absente des sorties{near}"
            )
            print(f"    > {f.line[:160]}")
        print(
            f"prose_num_targets: {findings and len(findings) or 0} | "
            f"notebooks_scanned: {len(results)} | citations_checked: {checked}"
        )
    return 1 if findings else 0


# --- Self-test (pre-controle) ---------------------------------------------------


def self_test() -> int:
    def nb(md_cells: list[str], outputs: list[str]) -> dict:
        return {
            "cells": [
                *[{"cell_type": "markdown", "source": [c]} for c in md_cells],
                {"cell_type": "code", "source": ["x = 1"], "outputs": [
                    {"output_type": "stream", "text": [o]} for o in outputs
                ]},
            ]
        }

    def citations(result: NotebookResult) -> list[str]:
        return [f.value for f in result.findings]

    failures = []

    # 1. Detection du defaut fondateur : cite 0.0742, la sortie rend 0.0859.
    r = analyze_notebook(
        nb(["## Lecture -- resultat : 0.0742 contre 0.1953"],
           ["suivi du donneur : 0.0859\nsham : 0.2109"]),
        "t.ipynb",
    )
    if sorted(citations(r)) != ["0.0742", "0.1953"]:
        failures.append(f"detection attendue [0.0742, 0.1953], rendue {citations(r)}")

    # 2. FP zero post-fix : valeurs re-alignees toutes presentes.
    r = analyze_notebook(
        nb(["## Lecture -- resultat : 0.0859 contre 0.2109"],
           ["suivi du donneur : 0.0859\nsham : 0.2109"]),
        "t.ipynb",
    )
    if citations(r):
        failures.append(f"FP post-fix : {citations(r)}")

    # 3. Normalisation francaise + egalite numerique 1,000 == 1.0000.
    r = analyze_notebook(
        nb(["### Lecture du resultat : exactitude 1,000, reste 0,2109"],
           ["accuracy: 1.0000\nsham: 0.2109"]),
        "t.ipynb",
    )
    if citations(r):
        failures.append(f"normalisation FR : {citations(r)}")

    # 4. Arrondi/troncature : 0.0859 correspond a 0.0859375.
    r = analyze_notebook(
        nb(["### Interprétation : effet a 0.0859"],
           ["follow_donor : 0.0859375"]),
        "t.ipynb",
    )
    if citations(r):
        failures.append(f"arrondi : {citations(r)}")

    # 5. Derivee fractionnaire inline : 1/16 = 0.0625 exempt (cas ICT-38 post-fix).
    r = analyze_notebook(
        nb(["## Lecture : colle a 0.0547, au hasard par valeur (1/16 = 0.0625)"],
           ["random_target : 0.0547"]),
        "t.ipynb",
    )
    if "0.0625" in citations(r):
        failures.append(f"derivee fractionnaire non exempee : {citations(r)}")

    # 6. Porte de precision : seuils, rapports et arrondis de narration exemptes.
    r = analyze_notebook(
        nb(["## Bilan : effet >= 0,5, ecart >= 0,25, soit 2,5 fois ; "
            "l'ancien banc donnait 0,33"],
           ["x : 0.2109"]),
        "t.ipynb",
    )
    if r.citations_checked != 0:
        failures.append(f"porte precision : {r.citations_checked} citations verifiees")

    # 7. Backticks : identifiant de code, pas une mesure.
    r = analyze_notebook(
        nb(["## Conclusion : le seuil `0.7500` du papier interne"],
           ["x : 0.2109"]),
        "t.ipynb",
    )
    if citations(r):
        failures.append(f"backticks non exemptes : {citations(r)}")

    # 8. Perimetre : commentaires de cellule code hors champ (pas de la prose).
    r = analyze_notebook(
        nb(["## Lecture : valeur 0.2109 confirmee"],
           ["# ancienne valeur 0.0742\nx : 0.2109"]),
        "t.ipynb",
    )
    if citations(r):
        failures.append(f"perimetre code : {citations(r)}")

    # 9. Continuation sans entete apres une entete de lecture.
    r = analyze_notebook(
        nb(["## Lecture", "prose de continuation citant 0.0742"],
           ["x : 0.0859"]),
        "t.ipynb",
    )
    if citations(r) != ["0.0742"]:
        failures.append(f"continuation : {citations(r)}")

    # 10. Annees et compteurs exemptes.
    r = analyze_notebook(
        nb(["## Bilan : depuis 2019, 47 carnets, exactitude 0.9999"],
           ["acc: 0.9999"]),
        "t.ipynb",
    )
    if citations(r):
        failures.append(f"annees/compteurs : {citations(r)}")

    # 11. Exemption « valeur citee » bornee au nombre gouverne (sonde Hermes
    # #27233, faux negatif 1) : le mot-cle bibliographique n'exempte PAS la
    # ligne entiere — seule la valeur qu'il gouverne est exemptee, la
    # reprise de 0.0742 comme « notre lecture » reste verifiee.
    r = analyze_notebook(
        nb(["## Lecture : l'article rapporte 0.0742, notre run rend 0.0859 "
            "et 0.0742 reste notre lecture"],
           ["suivi du donneur : 0.0859"]),
        "t.ipynb",
    )
    if sorted(citations(r)) != ["0.0742"] or r.citations_checked != 2:
        failures.append(
            f"exemption citee bornee : {citations(r)} / checked={r.citations_checked}"
        )

    # 12. Spans et positions sur la MEME chaine normalisee (sonde Hermes
    # #27233, faux negatif 2) : les separateurs de milliers NBSP ne font
    # plus glisser la position de 0.0742 dans le span du lien.
    nbsp = " "
    r = analyze_notebook(
        nb(["## Bilan : total 1" + nbsp + "000 et 2" + nbsp + "500 unites, "
            "[ref](https://arxiv.org/abs/2202.05822) 0.0742 tire"],
           ["suivi : 0.0859"]),
        "t.ipynb",
    )
    if citations(r) != ["0.0742"]:
        failures.append(f"spans normalises : {citations(r)}")

    # 13. Sorties HTML riches (.NET Interactive) : la valeur ancre vit dans
    # data.text/html (<pre>0.8785</pre>) -- le pool doit la lire (ML-04 C#,
    # sonde #27233 : 0,878 / 0,894 faux positifs tant que le HTML etait muet).
    def nb_html(md_cells: list[str], html: str) -> dict:
        return {
            "cells": [
                *[{"cell_type": "markdown", "source": [c]} for c in md_cells],
                {"cell_type": "code", "source": ["x = 1"], "outputs": [
                    {"output_type": "display_data",
                     "data": {"text/html": [html]}},
                ]},
            ]
        }

    r = analyze_notebook(
        nb_html(
            ["### Lecture : R2 de 0,878 a 0,894 d'un fold a l'autre"],
            '<table><tr><td>RSquared</td><td><div class="dni-plaintext">'
            "<pre>0.8785</pre></div></td></tr><tr><td>RSquared</td>"
            '<td><div class="dni-plaintext"><pre>0.8944</pre></div></td></tr></table>',
        ),
        "t.ipynb",
    )
    if citations(r):
        failures.append(f"HTML muet : {citations(r)}")

    # 14. Controle : une valeur absente du HTML reste un finding.
    r = analyze_notebook(
        nb_html(
            ["### Lecture : R2 de 0,912 sur ce fold"],
            '<table><tr><td>RSquared</td><td><div class="dni-plaintext">'
            "<pre>0.8785</pre></div></td></tr></table>",
        ),
        "t.ipynb",
    )
    if citations(r) != ["0,912"]:
        failures.append(f"controle HTML : {citations(r)}")

    # 15. Controle nombres INVISIBLES (reserve ai-01, fournee 8 ML-04) : un
    # nombre qui ne vit que dans un bloc <style> ou <script> n'est pas rendu
    # au lecteur -- il ne peut pas ancrer la citation. Temoin exact de la
    # reserve : une sortie HTML dont le seul 0.912 est dans le style.
    r = analyze_notebook(
        nb_html(
            ["### Lecture : R2 de 0,912 sur ce fold"],
            '<style>.dial { value: 0.912 }</style>'
            '<table><tr><td>RSquared</td><td><div class="dni-plaintext">'
            "<pre>0.8785</pre></div></td></tr></table>",
        ),
        "t.ipynb",
    )
    if citations(r) != ["0,912"]:
        failures.append(f"controle style invisible : {citations(r)}")

    # Variante <script> : meme temoin, bloc script multi-ligne.
    r = analyze_notebook(
        nb_html(
            ["### Lecture : R2 de 0,912 sur ce fold"],
            '<script type="text/javascript">\nvar dial = { value: 0.912 };\n'
            "</script>"
            '<table><tr><td>RSquared</td><td><div class="dni-plaintext">'
            "<pre>0.8785</pre></div></td></tr></table>",
        ),
        "t.ipynb",
    )
    if citations(r) != ["0,912"]:
        failures.append(f"controle script invisible : {citations(r)}")

    # 16. DOI en texte nu : le token entier est un identifiant, pas une mesure
    # (QC-Py-08 cellule 71, fountee 2 plan Q162 d). Les fragments 10.1111 et
    # 6261.1952 du token sont exemptes ; la mesure voisine 0.3189, absente des
    # sorties, reste signalee.
    r = analyze_notebook(
        nb(["## A retenir : cf. Markowitz (1952), DOI 10.1111/j.1540-6261.1952.tb01525.x, "
            "Sharpe mesure 0.3189"],
           ["sharpe: 0.3201"]),
        "t.ipynb",
    )
    if citations(r) != ["0.3189"]:
        failures.append(f"doi nu non exemptes : {citations(r)}")

    # 17. Semantique ± : « ±0.002 pres » correspond a la sortie signee
    # « +-0.002 pres » (2.11-Regularisation, sweep #27233).
    r = analyze_notebook(
        nb(["### Lecture : ElasticNet suit LASSO a ±0.002 pres"],
           ["elasticnet suit lasso a +-0.002 pres"]),
        "t.ipynb",
    )
    if citations(r):
        failures.append(f"semantique ± : {citations(r)}")

    # 18. Controle : magnitude FAUSSE reste un finding (« ±0.003 » vs -0.002).
    r = analyze_notebook(
        nb(["### Lecture : ElasticNet suit LASSO a ±0.003 pres"],
           ["elasticnet suit lasso a +-0.002 pres"]),
        "t.ipynb",
    )
    if citations(r) != ["0.003"]:
        failures.append(f"controle ± fausse magnitude : {citations(r)}")

    if failures:
        for f in failures:
            print(f"SELFTEST FAIL: {f}")
        return 1
    print("selftest: OK (18 fixtures)")
    return 0


# --- CLI -------------------------------------------------------------------------


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "base", nargs="?",
        help="ref de base du ratchet PR (carnets changes, lignes nouvelles)",
    )
    parser.add_argument("--all", action="store_true", help="balayage complet (exit 0)")
    parser.add_argument("--notebook", help="un seul carnet (findings => exit 1)")
    parser.add_argument("--self-test", action="store_true", help="fixtures embarquees")
    parser.add_argument("--json", action="store_true", help="sortie machine")
    args = parser.parse_args(argv)

    if args.self_test:
        return self_test()

    root = REPO_ROOT
    if args.all:
        results = scan_all(root)
        rc = _print_report(results, args.json)
        return 0  # balayage : rapport seul, jamais de rouge CI
    if args.notebook:
        results = [scan_notebook(Path(args.notebook), root)]
        return _print_report(results, args.json)
    if args.base:
        results = scan_diff(args.base, root)
        return _print_report(results, args.json)
    parser.error("donner <base>, --all, --notebook ou --self-test")
    return 2


if __name__ == "__main__":
    sys.exit(main())
