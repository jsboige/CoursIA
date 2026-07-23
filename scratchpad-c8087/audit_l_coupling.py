#!/usr/bin/env python3
"""Audit coupling MEMORY.md leçons (L-NNN) ↔ .claude/rules/*.md citations.

Read-only. Sortie : rapport markdown + JSON pour vérifiabilité.

Méthode :
  1. Parse MEMORY.md → set(L_xxx) leçons citées (format `L\d+` ou `L\d+-L\d+`)
  2. Parse tous .claude/rules/*.md → set(L_xxx) leçons citées + map(rule_file → set)
  3. Parse CLAUDE.md → set(L_xxx) leçons citées (auto-loaded)
  4. Cross-match :
     - ORPHELINES MEMORY : Leçon L-NNN citée en MEMORY mais pas dans rules ni CLAUDE.md
     - ORPHELINES RULES : Leçon L-NNN citée en rule mais pas dans MEMORY
     - ANCRÉES : Leçon L-NNN citée en MEMORY ET dans rules/CLAUDE.md
  5. Verdict par leçon : ancrée / orpheline-memory / orpheline-rule / non-citée
"""
import re
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MEMORY = Path("C:/Users/jsboi/.claude/projects/c--dev-CoursIA-2/memory/MEMORY.md")
RULES = ROOT / ".claude/rules"
CLAUDE_MD = ROOT / "CLAUDE.md"

L_RE = re.compile(r"L(\d{3,4})(?:[-L](\d{1,4}))?")


def parse_lessons(text: str) -> set[str]:
    """Extrait tous les identifiants L-NNN (et plages L-NNN-L-MM)."""
    out = set()
    for m in L_RE.finditer(text):
        a = m.group(1)
        b = m.group(2)
        if b:
            # Plage L{start}-L{end} → ajoute tous entre
            try:
                start, end = int(a), int(b)
                for n in range(min(start, end), max(start, end) + 1):
                    out.add(f"L{n}")
            except ValueError:
                pass
        else:
            out.add(f"L{a}")
    return out


def main() -> int:
    if not MEMORY.exists():
        print(f"ERROR: MEMORY not found at {MEMORY}", file=sys.stderr)
        return 1

    memory_lessons = parse_lessons(MEMORY.read_text(encoding="utf-8"))

    rule_lessons_global: set[str] = set()
    rule_lessons_by_file: dict[str, set[str]] = {}

    for f in sorted(RULES.glob("*.md")):
        text = f.read_text(encoding="utf-8")
        ll = parse_lessons(text)
        rule_lessons_by_file[f.name] = ll
        rule_lessons_global |= ll

    claude_lessons = parse_lessons(CLAUDE_MD.read_text(encoding="utf-8")) if CLAUDE_MD.exists() else set()

    # Cross-match
    all_cited = memory_lessons | rule_lessons_global | claude_lessons
    anchored = memory_lessons & (rule_lessons_global | claude_lessons)
    orphan_memory = memory_lessons - rule_lessons_global - claude_lessons
    orphan_rule = (rule_lessons_global | claude_lessons) - memory_lessons

    # Sortie
    report = {
        "memory_total": len(memory_lessons),
        "rules_total": len(rule_lessons_global),
        "claude_total": len(claude_lessons),
        "rules_files_count": len(rule_lessons_by_file),
        "anchored_count": len(anchored),
        "orphan_memory_count": len(orphan_memory),
        "orphan_rule_count": len(orphan_rule),
        "anchored": sorted(anchored),
        "orphan_memory": sorted(orphan_memory),
        "orphan_rule": sorted(orphan_rule),
        "by_rule_file": {k: sorted(v) for k, v in rule_lessons_by_file.items() if v},
    }

    out_json = ROOT / "scratchpad-c8087" / "audit_l_coupling.json"
    out_json.parent.mkdir(exist_ok=True)
    out_json.write_text(json.dumps(report, indent=2, ensure_ascii=False), encoding="utf-8")

    print(f"=== AUDIT L-COUPLING ===")
    print(f"MEMORY.md leçons uniques : {len(memory_lessons)}")
    print(f".claude/rules/ leçons uniques (tous fichiers) : {len(rule_lessons_global)}")
    print(f"CLAUDE.md leçons uniques : {len(claude_lessons)}")
    print(f"Ancrées (MEMORY ∩ rules ∪ claude) : {len(anchored)}")
    print(f"Orphelines MEMORY (citée MEMORY, pas dans rules/CLAUDE) : {len(orphan_memory)}")
    print(f"Orphelines RULES (citée rules/CLAUDE, pas dans MEMORY) : {len(orphan_rule)}")
    print()
    print(f"--- Sample orphelines MEMORY (top 20) ---")
    for l in sorted(orphan_memory)[:20]:
        print(f"  {l}")
    print()
    print(f"--- Sample orphelines RULES (top 20) ---")
    for l in sorted(orphan_rule)[:20]:
        print(f"  {l}")
    print()
    print(f"--- Distribution règles ↔ leçons ---")
    for fname, ll in sorted(rule_lessons_by_file.items(), key=lambda x: -len(x[1])):
        if ll:
            print(f"  {fname:40s} : {len(ll):3d} leçons → {sorted(ll)[:5]}{'...' if len(ll) > 5 else ''}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
