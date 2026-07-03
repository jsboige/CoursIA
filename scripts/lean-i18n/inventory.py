#!/usr/bin/env python3
"""Decompose SymbolicAI/Lean into 3-level groups (per actual lake)."""
from __future__ import annotations
import re
from pathlib import Path
from collections import defaultdict

ROOT = Path("MyIA.AI.Notebooks")
FR_ACCENTS = re.compile(r"[àâçéèêëîïôûùüÿœæÀÂÇÉÈÊËÎÏÔÛÙÜŸŒÆ]")
FR_HEAVY = re.compile(r"\b(théorème|lemme|corollaire|preuve|définition|hypothèse|propriété|proposition|remarque|exemple|exercice|montrer|démontrer|supposer|considérer|alors|donc|soit|ainsi|nous|montrons|supposons|d'où|voilà|démonstration|preuve de|est vrai|il existe|on a|si et seulement si)\b", re.IGNORECASE)
EN_HEAVY = re.compile(r"\b(theorem|lemma|corollary|proof|definition|hypothesis|property|proposition|remark|example|exercise|show|demonstrate|suppose|consider|then|hence|therefore|so|now|thus|where)\b", re.IGNORECASE)
FR_STOP = re.compile(r"\b(le|la|les|un|une|des|du|est|sont|dans|avec|pour|et|ce|cette|que|qui|par|sur|ne|pas|ou|a|au|aux|nous|vous|je|tu|il|elle|on|se|leur|leurs)\b", re.IGNORECASE)
EN_STOP = re.compile(r"\b(the|of|and|is|are|in|with|for|that|this|theorem|lemma|definition|proof|corollary|by|on|or|not|as|at|be|it|to|which)\b", re.IGNORECASE)
DOC_RE = re.compile(r"/--(.*?)-/", re.DOTALL)
CMT_RE = re.compile(r"--\s?(.+)$", re.MULTILINE)

def score(text):
    if not text.strip():
        return 0, 0
    fr = 5*len(FR_ACCENTS.findall(text)) + 3*len(FR_HEAVY.findall(text)) + len(FR_STOP.findall(text.lower()))
    en = 3*len(EN_HEAVY.findall(text)) + len(EN_STOP.findall(text.lower()))
    return fr, en

lean_files = sorted(ROOT.rglob("*.lean"))
lean_files = [p for p in lean_files if ".lake" not in p.parts]

# Group by 3-level for Symbolicai/Lean, 2-level elsewhere
by_grp = defaultdict(lambda: dict(files=0, d_fr=0, d_en=0, c_fr=0, c_en=0, d_n=0, c_n=0))
for p in lean_files:
    parts = p.relative_to(ROOT).parts
    if "SymbolicAI" in parts and "Lean" in parts:
        # Use 3-level: SymbolicAI/Lean/<lake_name>
        lake_idx = parts.index("Lean")
        if lake_idx + 1 < len(parts):
            grp = str(Path("SymbolicAI", "Lean", parts[lake_idx + 1]))
        else:
            grp = str(Path("SymbolicAI", "Lean"))
    else:
        # 2-level
        grp = str(Path(*parts[:2])) if len(parts) >= 2 else str(p.parent)
    content = p.read_text(encoding="utf-8")
    agg = by_grp[grp]
    agg["files"] += 1
    for d in DOC_RE.findall(content):
        fr, en = score(d)
        agg["d_fr"] += fr; agg["d_en"] += en; agg["d_n"] += 1
    for m in CMT_RE.finditer(content):
        c = m.group(1).strip()
        if len(c) > 3:
            fr, en = score(c)
            agg["c_fr"] += fr; agg["c_en"] += en; agg["c_n"] += 1

print(f"## Inventaire 3-niveaux (SymbolicAI/Lean décomposé)")
print()
print("| Lake | Files | DocFR | DocEN | CmtFR | CmtEN | %FR | Verdict |")
print("|------|------:|------:|------:|------:|------:|---:|---------|")
rows = []
for grp, agg in by_grp.items():
    fr_t = agg["d_fr"] + agg["c_fr"]
    en_t = agg["d_en"] + agg["c_en"]
    pct = 100 * fr_t / (fr_t + en_t) if (fr_t + en_t) > 0 else 50
    rows.append((grp, agg, fr_t, en_t, pct))
rows.sort(key=lambda r: r[4])
for grp, agg, fr_t, en_t, pct in rows:
    if pct >= 80:
        v = "FR-majeure"
    elif pct <= 20:
        v = "EN-majeure"
    elif pct >= 50:
        v = "mixte-FR+"
    else:
        v = "mixte-EN"
    print(f"| `{grp}` | {agg['files']} | {agg['d_fr']} | {agg['d_en']} | {agg['c_fr']} | {agg['c_en']} | {pct:.0f}% | {v} |")
