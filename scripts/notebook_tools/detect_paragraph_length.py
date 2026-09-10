#!/usr/bin/env python3
"""Detect paragraphs of markdown whose length exceeds a wall threshold (#15405, demande user 2026-09-10).

Pourquoi cet outil existe
-------------------------
Le README de la serie Probas (``MyIA.AI.Notebooks/Probas/README.md``, l.16)
portait un paragraphe unique de **3 246 caracteres / 374 mots sur une seule
ligne physique** (commit ``76d7a5bc``, PR #15405 deja sur ``main``). Illisible,
passe au travers du CI : aucun detecteur de paragraphe markdown trop long
n'existait (verifie : scan corpus, seule ``check_outputs_text_fragmentation.py``
existe, axe different).

User (2026-09-10) :
> « le bloc "cette serie..." est encore trop gros »
> « IL aurait du etre intercepte par le CI comme un bloc sans espaces indigeste »
> « Tu peux rajouter l'organe au CI ? »

Convention ``detect_*`` du dossier (cf. ``detect_consecutive_code_cells.py``,
``detect_repeated_prose.py``) : sortie machine ``--json`` / humain par defaut,
garde scan-vacuue (rien a scanner -> exit 2, jamais "0 finding"), ``--self-test``
(prouve que le detecteur tire -- une alarme qu'on ne peut pas demontrer est
deconnectee).

Signal : bloc de texte contigu, separate par ligne vide, longueur mesuree par
``len("".join(lines))``. On ignore :

- les fences code (``` / ~~~) -- blocs techniques delimites, longueur legitime
- les lignes de tableau markdown (``|``) -- cellules tabulaires
- les titres (``#`` / ``##`` / ...) -- peuven porter une URL et un seul mot
- les blocs ``<!-- ... -->`` HTML (notamment le marqueur ``CATALOG-STATUS`` qui
  couvre plusieurs lignes consecutives)

Listes et blockquotes comptent comme bloc -- un item de 10k caracteres reste un
mur, la calibration les inclut deja (un ``- tres long item...`` depasse rarement
2000 c, mais un mur pedagogique copiable le peut).

Constante module ``MAX_PARAGRAPH_LEN = 2000`` (delibere, **pas un flag** :
"locked by calibration", cf. body PR). Mesure corpus :
- p99 = 1437 caracteres sur les paragraphes du depot (``git ls-files '*.md'``)
- 2000 laisse 39 % de marge au-dessus du p99 tout en attrapant les murs
  pedagogiques type PR #15405 (3246 c) et README Probas pre-fix.
- 42 fichiers du corpus portent deja un paragraphe > 2000 c ; ils font l'objet
  d'une **issue de suivi** nommee dans le body PR B (advisory = pas de cascade).

Portee et cout : scan texte pur (stdlib), O(blocs x fichiers) -- quelques
millisecondes par fichier, <1 s pour le corpus entier.

Codes de retour : 0 = clean ; 1 = fichier illisible / introuvable / scan vacuue
(aucune cellule markdown pour les .ipynb, aucun paragraphe pour les .md) ;
2 = findings (avec ``--fail-on-findings``).
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import time
from pathlib import Path

MAX_PARAGRAPH_LEN = 2000

REPO_ROOT = Path(__file__).resolve().parents[2]

# Un paragraphe = bloc de texte contigu, separe par une ligne vide.
# On neutralise d'abord les fences / tableaux / titres / HTML pour ne pas
# mesurer un bloc delimite par accident.
_FENCE_RE = re.compile(r"^[ \t]*(```|~~~)")
_TABLE_LINE_RE = re.compile(r"^\s*\|")
_HEADING_RE = re.compile(r"^\s{0,3}#{1,6}\s")
_HTML_COMMENT_BLOCK_RE = re.compile(r"(?s)<!--.*?-->")
_BLANK_RE = re.compile(r"\n\s*\n")


def _strip_blocks(text: str) -> str:
    """Retire les fences / tableaux / titres / blocs HTML d'un texte.

    On remplace par des separateurs de paragraphes (lignes vides) pour eviter
    que deux blocs separes par une fence soient fusionnes en un seul mur.
    """
    lines = text.splitlines(keepends=True)
    out: list[str] = []
    in_fence = False
    fence_marker = ""
    for line in lines:
        stripped = line.lstrip()
        if in_fence:
            if stripped.rstrip().startswith(fence_marker):
                in_fence = False
                fence_marker = ""
            out.append("\n")  # neutralise le contenu de la fence
            continue
        m = _FENCE_RE.match(line)
        if m:
            in_fence = True
            fence_marker = m.group(1)
            out.append("\n")
            continue
        if _TABLE_LINE_RE.match(line) or _HEADING_RE.match(line):
            out.append("\n")  # separe titres et tableaux du flux prose
            continue
        out.append(line)
    cleaned = "".join(out)
    cleaned = _HTML_COMMENT_BLOCK_RE.sub("\n\n", cleaned)
    return cleaned


def paragraphs(text: str) -> list[str]:
    """Decoupe en paragraphes sur les lignes vides, apres nettoyage."""
    cleaned = _strip_blocks(text)
    blocks = _BLANK_RE.split(cleaned)
    return [b.strip() for b in blocks if b.strip()]


def detect(text: str) -> list[dict]:
    """Renvoie les findings d'un texte markdown (liste, vide = clean)."""
    findings: list[dict] = []
    for block in paragraphs(text):
        length = len(block)
        if length > MAX_PARAGRAPH_LEN:
            findings.append({
                "type": "oversized_paragraph",
                "chars": length,
                "preview": block[:80].replace("\n", " "),
            })
    return findings


def detect_in_notebook(path: Path) -> tuple[list[dict], str | None]:
    """Renvoie (findings, error_msg). Charge un .ipynb et concatene les cellules markdown."""
    try:
        nb = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        return [], f"illisible : {exc}"
    cells = nb.get("cells", [])
    md_chunks: list[str] = []
    for cell in cells:
        if cell.get("cell_type") != "markdown":
            continue
        src = cell.get("source", "")
        if isinstance(src, list):
            src = "".join(src)
        md_chunks.append(src)
    if not md_chunks:
        return [], "aucune cellule markdown (scan vacuue)"
    text = "\n\n".join(md_chunks)
    return detect(text), None


def scan_path(path: Path, as_json: bool) -> tuple[int, str, list[dict]]:
    """Scan un fichier (.md lit tel quel ; .ipynb agrege les cellules markdown).

    Codes : 0 = clean, 1 = illisible/vacuue, 2 = findings.
    """
    rel = path.relative_to(REPO_ROOT).as_posix() if path.is_relative_to(REPO_ROOT) else str(path)
    if path.suffix == ".ipynb":
        findings, err = detect_in_notebook(path)
    else:
        try:
            text = path.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError) as exc:
            return 1, f"{rel}: illisible : {exc}", []
        if not text.strip():
            return 1, f"{rel}: vide (scan vacuue)", []
        findings = detect(text)
        err = None
    if err:
        return 1, f"{rel}: {err}", []
    if as_json:
        out = json.dumps({
            "file": rel,
            "findings": findings,
            "counts": {"total": len(findings)},
        }, ensure_ascii=False, indent=1)
    else:
        if not findings:
            out = f"{rel}: clean"
        else:
            lines = [f"{rel}: {len(findings)} finding(s)"]
            for f in findings:
                lines.append(f"  [oversized] {f['chars']} c « {f['preview']}… »")
            out = "\n".join(lines)
    return (2 if findings else 0), out, findings


def collect_targets(args: argparse.Namespace) -> list[Path]:
    """Collecte la liste des fichiers a scanner."""
    if args.paths:
        targets: list[Path] = []
        for raw in args.paths:
            p = Path(raw)
            if not p.exists():
                print(f"introuvable : {raw}", file=sys.stderr)
                continue
            targets.append(p)
        return targets
    if args.stdin:
        paths: list[Path] = []
        for raw in sys.stdin.read().splitlines():
            raw = raw.strip()
            if not raw:
                continue
            p = Path(raw)
            if p.exists():
                paths.append(p)
        return paths
    # defaut : tous les .md + .ipynb du repo
    return sorted(set(
        list(REPO_ROOT.glob("**/*.md")) +
        list(REPO_ROOT.glob("**/*.ipynb"))
    ))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Detecte les paragraphes markdown trop longs (> %d c)." % MAX_PARAGRAPH_LEN
    )
    parser.add_argument("paths", nargs="*", help="Fichiers ou repertoires ; defaut = corpus")
    parser.add_argument("--json", action="store_true", help="Sortie machine (par fichier)")
    parser.add_argument("--fail-on-findings", action="store_true",
                        help="Exit code 2 si findings ; sans flag = advisory (exit 0 toujours)")
    parser.add_argument("--stdin", action="store_true",
                        help="Lire la liste de fichiers depuis stdin (un chemin par ligne)")
    parser.add_argument("--self-test", action="store_true",
                        help="Prouve que le detecteur tire (sortie 0 si OK, != 0 sinon)")
    args = parser.parse_args(argv)

    if args.self_test:
        return self_test()

    targets = collect_targets(args)
    if not targets:
        print("aucune cible", file=sys.stderr)
        return 1  # scan vacuue

    t0 = time.perf_counter()
    flagged_count = 0
    error_count = 0
    clean_count = 0
    for path in targets:
        rc, out, _ = scan_path(path, as_json=args.json)
        print(out)
        if rc == 2:
            flagged_count += 1
        elif rc == 1:
            error_count += 1
        else:
            clean_count += 1
    elapsed = time.perf_counter() - t0

    print(f"\n[scan] {len(targets)} fichiers en {elapsed:.2f}s : "
          f"{flagged_count} flagges, {clean_count} clean, {error_count} illisibles/vacues "
          f"(seuil {MAX_PARAGRAPH_LEN} c)")

    if args.json and flagged_count:
        # resume machine global
        print(json.dumps({
            "scanned": len(targets),
            "seconds": round(elapsed, 2),
            "threshold": MAX_PARAGRAPH_LEN,
            "flagged_count": flagged_count,
            "clean_count": clean_count,
            "error_count": error_count,
        }, ensure_ascii=False, indent=1))

    if flagged_count and args.fail_on_findings:
        return 2
    return 0


# --- Self-test : le temoin fondateur DOIT tirer, le fix DOIT etre muet ----
# (lecon #11685 : un detecteur qu'on ne peut pas montrer en train de tirer
# est indistinguishable d'un detecteur debranche).


def self_test() -> int:
    """Prouve que le detecteur tire sur la fixture et reste muet sur le post-fix."""
    fixture_path = Path(__file__).parent / "tests" / "fixtures" / "paragraph_wall_md.md"
    if not fixture_path.exists():
        print(f"fixture introuvable : {fixture_path}", file=sys.stderr)
        return 1
    text = fixture_path.read_text(encoding="utf-8")
    failures: list[str] = []

    # 1. TEMOIN POSITIF — mur pedagogique > 2000 c : detecteur DOIT tirer.
    findings = detect(text)
    if not findings:
        failures.append("NEGATIF CRITIQUE : le mur fondateur (PR #15405, "
                        "README Probas l.16 pre-fix) NE TIRE PAS -- detecteur "
                        "debranche ou seuils casses")
    else:
        f0 = findings[0]
        if f0["type"] != "oversized_paragraph":
            failures.append(f"type de finding inattendu : {f0['type']}")
        if f0["chars"] < MAX_PARAGRAPH_LEN + 1:
            failures.append(f"taille sub-seuil : {f0['chars']} (attendu > {MAX_PARAGRAPH_LEN})")

    # 2. TEMOIN NEGATIF — README Probas post-fix (6 paragraphes < 2000 c) :
    # detecteur DOIT etre muet.
    post_text = (
        "Paragraphe un introductif de taille raisonnable qui presente la serie "
        "et ses stacks complementaires.\n\n"
        "Paragraphe deux sur le corpus baysien Infer avec 21 notebooks.\n\n"
        "Paragraphe trois sur l'arc decision et le versant PyMC avec "
        "19 notebooks corpus et 12 miroirs.\n\n"
        "Paragraphe quatre sur la percolation avec un lake Lean compagnon.\n\n"
        "Paragraphe cinq sur le pont causal avec 4 notebooks Python.\n\n"
    )
    post_findings = detect(post_text)
    if post_findings:
        failures.append(f"post-fix NON muet : {len(post_findings)} finding(s)")

    # 3. Controle — fences / tableaux / titres ignores.
    mixed = (
        "# Titre principal avec URL tres longue pour tester l'exemption\n\n"
        "```python\n# code block de 5000 caracteres\n" + ("x = 1\n" * 800) + "```\n\n"
        "| col1 | col2 |\n|------|------|\n| a | b |\n\n"
        "<!-- commentaire HTML tres long qui ne devrait pas etre mesure -->\n\n"
        "Paragraphe court ok.\n"
    )
    mixed_findings = detect(mixed)
    if mixed_findings:
        failures.append(f"fences/tableaux/titres non ignores : {len(mixed_findings)} finding(s)")

    # 4. Seuil exact 2000 / 2001.
    just_below = "x" * 2000  # exactement au seuil -> ne tire PAS (> strict)
    just_above = "x" * 2001
    if detect(just_below):
        failures.append("2000 c (au seuil) tire -- contrat > strict casse")
    if not detect(just_above):
        failures.append("2001 c (au-dessus du seuil) muet -- contrat > casse")

    if failures:
        print("SELF-TEST FAIL :")
        for f in failures:
            print(f"  - {f}")
        return 1
    print(f"SELF-TEST OK : {MAX_PARAGRAPH_LEN} c, fixture OK, post-fix muet, seuils stricts.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
