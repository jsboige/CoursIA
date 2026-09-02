#!/usr/bin/env python3
"""Detect desaccented words in notebook markdown prose.

A "desaccented" word is an unaccented surface form whose accent-stripped twin
exists (accented) elsewhere in the *same* notebook -- the internal positive
control: without an accented twin, nothing is asserted. E.g. `theoreme` is
flagged only if `theoreme`'s strip equals `theoreme` (no accents) and an
accented `theoreme` (the `theoreme` spelling, stripped) was seen in that
notebook.

This is the family seated by #14064: the user's coquille `individaux` was the
visible tip of a systematic markdown desaccentuation. The historical,
unhardened detector (the inline script in the issue) reported a raw
`37 286 occurrences` across `946/1219` notebooks -- but that count is a
*ceiling of candidates*, not a defect count. The three biggest hits
(`des` -> `des`, `sur` -> `sur`, `mesure` -> `mesure`) are legitimate
homographs / partitive articles / nouns that are genuinely different French
words, not typos, and together accounted for `6 084` (16%) of the ceiling.

Hardening therefore does NOT try to raise precision by scoring context (that
would overfit). It does two things, and validates by FALSE NEGATIVES (never by
hits):

1. **Exclusion lists.** A closed set of unaccented forms that are either (a)
   legitimate homographs of a distinct French word (`des`/`dès`, `sur`/`sûr`,
   `mesure`/`mesuré`, `cote`/`côté`, `tache`/`tâche`, `marche`/`marché`,
   `base`/`basé`, `type`/`typé`, ...), or (b) English technical cognats that
   legitimately survive unaccented in French prose (`inference`, `decision`,
   `precision`, `reference`, `regression`, `detection`, `generation`, `video`,
   `regime`, `complete`). These are reported in a separate "excluded" bucket,
   never as auto-flagged candidates.
2. **FR/EN prose gate.** A notebook whose markdown is English-dominant is not a
   French-desaccentuation candidate at all; it is skipped with `language=en`.

Acceptance is by the forms it MUST catch, written as tests, never by its hit
count: `theoreme`, `etat`, `donnees`, `equilibre`, `entrainement` must be
flagged in a French notebook, and must NOT be flagged in an English one or when
the word is a homograph that only looks desaccented.

Usage: python detect_markdown_deaccent.py <notebook-or-dir> [more...] [--json]
                                   [--fail-on-findings]

Output: one line per notebook `COUNT TOTAL (AUTO auto / HOM homograph / COG
en-cognat), PATH`, then a machine-readable summary. A scan that matches no
notebook is an error (exit 1) -- a vacuous `0/0` is never a clean scan (the
scan_md_hierarchy.py lesson, #3968). `--fail-on-findings` exits 2 when any
notebook has auto-flagged candidates (PR-gate use).
"""
import argparse
import json
import re
import sys
import unicodedata
from pathlib import Path

_WORD_RE = re.compile(r"[A-Za-zÀ-ÿ]{3,}")
# Inline code, fenced code blocks, and inline math. Desaccented words inside
# code/math are not prose defects; stripping them mirrors the issue's
# `re.sub(r"`[^`]*`", " ", text)` guard and extends it to fenced blocks.
_CODE_RE = re.compile(r"`[^`]*`|```.*?```|\$\$.*?\$\$|\$[^$]*\$", re.DOTALL)


def _strip_accents(s: str) -> str:
    """Remove combining diaeresis marks (NFD, drop category Mn)."""
    return "".join(
        c for c in unicodedata.normalize("NFD", s) if unicodedata.category(c) != "Mn"
    )


# Unaccented forms that are a *legitimately different* French word from their
# accented twin -- an homograph, not a desaccentuation typo. `des` (partitive)
# vs `dès` (since), `sur` (preposition) vs `sûr` (sure), `mesure` (noun) vs
# `mesuré` (participle). The issue named these as the guaranteed false
# positives (16% of the raw ceiling). Add a form here rather than teach the
# detector to read context.
HOMOGRAPH_EXCLUSIONS = {
    "des", "sur", "mesure", "mesures",
    "cote", "cotes", "tache", "taches",
    "marche", "marches", "base", "bases",
    "type", "types", "structure", "structures",
    "analyse", "analyses", "attaque", "attaques",
    "complete", "completes", "utilise", "utilises",
}

# English technical cognats that legitimately survive unaccented in French
# prose. Not defects either (e.g. "l'algorithme de detection").
EN_COGNAT_EXCLUSIONS = {
    "inference", "decision", "decisions", "precision", "reference",
    "references", "regression", "regressions", "detection", "generation",
    "video", "regime", "complete", "algorithm", "implementation",
}

FR_STOPWORDS = {
    "le", "la", "les", "des", "une", "un", "est", "sont", "pour", "avec",
    "dans", "par", "sur", "que", "qui", "cette", "ces", "ce", "il", "elle",
    "nous", "vous", "ils", "elles", "se", "ne", "pas", "plus", "comme", "ou",
    "si", "mais", "donc", "ainsi", "etre", "avoir", "fait", "faire", "entre",
    "toute", "tout", "meme", "on", "au", "aux", "du", "de", "en", "une",
}
EN_STOPWORDS = {
    "the", "of", "and", "to", "in", "is", "are", "for", "on", "with", "that",
    "it", "as", "at", "by", "an", "be", "this", "from", "or", "we", "they",
    "not", "can", "but", "what", "have", "has", "was", "were", "which", "will",
    "their", "if", "when", "into", "these", "then", "than", "its",
}


def _classify_language(texts: list[str]) -> str:
    """Return 'fr' or 'en' by counting stopword occurrences in the prose."""
    fr = en = 0
    for t in texts:
        for word in _WORD_RE.findall(t):
            w = word.lower()
            if w in FR_STOPWORDS:
                fr += 1
            elif w in EN_STOPWORDS:
                en += 1
    return "fr" if fr >= en else "en"


def _markdown_texts(nb: dict) -> list[str]:
    """Collect de-coded markdown cell text from a notebook dict."""
    texts = []
    for cell in nb.get("cells", []):
        if cell.get("cell_type") != "markdown":
            continue
        source = cell.get("source", "")
        if isinstance(source, list):
            source = "".join(source)
        texts.append(_CODE_RE.sub(" ", source))
    return texts


def find_candidates(nb: dict) -> dict:
    """Return {language, auto, homograph, en_cognat} candidate word->count maps.

    Each bucket maps the *stripped lowercase key* to the number of unaccented
    surface occurrences. `auto` only, is what a PR gate should fail on; the
    other buckets are transparency, not defects.
    """
    texts = _markdown_texts(nb)
    # Internal positive control: strip(key) -> an accented surface form.
    accented = {}
    for t in texts:
        for m in _WORD_RE.finditer(t):
            word = m.group(0)
            if word != _strip_accents(word):
                accented.setdefault(_strip_accents(word).lower(), word)

    result = {"language": _classify_language(texts), "auto": {}, "homograph": {},
              "en_cognat": {}}
    if result["language"] != "fr":
        return result

    for t in texts:
        for m in _WORD_RE.finditer(t):
            word = m.group(0)
            if word != _strip_accents(word):
                continue
            key = word.lower()
            if key not in accented:
                continue
            bucket = (
                "auto"
                if key not in HOMOGRAPH_EXCLUSIONS and key not in EN_COGNAT_EXCLUSIONS
                else ("homograph" if key in HOMOGRAPH_EXCLUSIONS else "en_cognat")
            )
            result[bucket][key] = result[bucket].get(key, 0) + 1
    return result


def _total(counts: dict) -> int:
    return sum(v for v in counts.values())


def analyze_notebook(path: Path) -> tuple[dict, bool]:
    """Return (result, discovered) -- discovered=False on a vacuous/empty scan."""
    try:
        nb = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError) as exc:
        raise ValueError(f"{path}: cannot read notebook: {exc}")
    result = find_candidates(nb)
    return result, True


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("paths", nargs="*", help="notebook(s) or directory(ies)")
    parser.add_argument("--json", action="store_true", help="emit JSON report")
    parser.add_argument("--fail-on-findings", action="store_true",
                        help="exit 2 when any notebook has auto-flagged candidates")
    args = parser.parse_args(argv)

    if not args.paths:
        print("error: no path given (a vacuous /0 is never a clean scan)",
              file=sys.stderr)
        return 1

    files: list[Path] = []
    for raw in args.paths:
        p = Path(raw)
        if p.is_dir():
            files.extend(sorted(p.rglob("*.ipynb")))
        elif p.is_file():
            files.append(p)

    if not files:
        print(f"error: no notebooks under {args.paths} (vacuous scan)",
              file=sys.stderr)
        return 1

    report = {}
    exit_code = 0
    for path in files:
        try:
            result, _ = analyze_notebook(path)
        except ValueError as exc:
            print(f"error: {exc}", file=sys.stderr)
            exit_code = 1
            continue
        rel = path.as_posix()
        report[rel] = result
        n_auto = _total(result["auto"])
        n_hom = _total(result["homograph"])
        n_cog = _total(result["en_cognat"])
        n_tot = n_auto + n_hom + n_cog
        if not args.json:
            print(f"{n_tot} TOTAL ({n_auto} auto / {n_hom} hom / {n_cog} cog) "
                  f"[{result['language']}], {rel}")
        if n_auto and args.fail_on_findings:
            exit_code = 2

    if args.json:
        print(json.dumps(report, ensure_ascii=False, indent=2))
    return exit_code


if __name__ == "__main__":
    sys.exit(main())
