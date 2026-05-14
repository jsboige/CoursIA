"""Proof Knowledge Base — persistent storage of successful proof patterns.

Version 2: supports tactic_cookbook, failed_approaches, mathlib_api sections
from proof_knowledge.json v3, in addition to the legacy entries format.

B.1 from issue #820: cross-session knowledge persistence.
"""

import json
from pathlib import Path
from typing import Dict, List, Optional
from datetime import datetime


DEFAULT_KB_PATH = Path(__file__).parent / "proof_knowledge.json"


class ProofKnowledgeBase:
    """Persistent knowledge base for successful proof patterns.

    Supports proof_knowledge.json v3 with sections:
    - entries: goal_signature → tactic mapping (legacy, v1)
    - tactic_cookbook: structured patterns with when/after/not/examples
    - failed_approaches: documented failures with root causes
    - mathlib_api: API discoveries for Mathlib lemmas/structures
    """

    def __init__(self, path: Path = None):
        self._path = path or DEFAULT_KB_PATH
        self._data: Dict = {
            "version": 3, "last_updated": "", "entries": {},
            "tactic_cookbook": {"patterns": []},
            "failed_approaches": [],
            "mathlib_api": {},
        }
        self._load()

    def _load(self):
        if self._path.exists():
            try:
                self._data = json.loads(self._path.read_text(encoding="utf-8"))
                if "entries" not in self._data:
                    self._data["entries"] = {}
            except (json.JSONDecodeError, OSError):
                self._data = {
                    "version": 3, "last_updated": "", "entries": {},
                    "tactic_cookbook": {"patterns": []},
                    "failed_approaches": [], "mathlib_api": {},
                }

    def _save(self):
        self._data["last_updated"] = datetime.now().isoformat()
        self._path.write_text(
            json.dumps(self._data, indent=2, ensure_ascii=False),
            encoding="utf-8",
        )

    # --- Cookbook access (v3) ---

    @property
    def cookbook_patterns(self) -> List[Dict]:
        """All tactic cookbook patterns from proof_knowledge.json."""
        return self._data.get("tactic_cookbook", {}).get("patterns", [])

    def cookbook_by_category(self, category: str) -> List[Dict]:
        """Filter cookbook patterns by category."""
        return [p for p in self.cookbook_patterns
                if p.get("category") == category]

    def cookbook_for_goal(self, goal: str) -> List[Dict]:
        """Find cookbook patterns relevant to a goal using keyword matching."""
        goal_words = set(goal.lower().replace("(", " ").replace(")", " ").split())
        scored = []
        for p in self.cookbook_patterns:
            when = p.get("when", "").lower()
            name = p.get("name", "").lower()
            pat_words = set((when + " " + name).split())
            overlap = len(goal_words & pat_words)
            if overlap >= 2:
                scored.append((overlap, p))
        scored.sort(key=lambda x: x[0], reverse=True)
        return [p for _, p in scored[:5]]

    # --- Failed approaches (v3) ---

    @property
    def failed_approaches(self) -> List[Dict]:
        """Documented failed approaches with root causes."""
        return self._data.get("failed_approaches", [])

    def check_avoided(self, tactic: str) -> Optional[Dict]:
        """Check if a tactic resembles a known failed approach."""
        tactic_lower = tactic.lower().strip()
        for fa in self.failed_approaches:
            what = fa.get("what_failed", "").lower()
            if any(kw in tactic_lower for kw in what.split() if len(kw) > 4):
                return fa
        return None

    # --- Mathlib API (v3) ---

    @property
    def mathlib_api(self) -> Dict[str, str]:
        """Mathlib API discoveries (key → description)."""
        return self._data.get("mathlib_api", {})

    def api_lookup(self, name: str) -> Optional[str]:
        """Look up a Mathlib API entry by approximate name."""
        name_lower = name.lower()
        for key, desc in self.mathlib_api.items():
            if name_lower in key.lower() or key.lower() in name_lower:
                return desc
        return None

    # --- Context generation for prover ---

    def generate_prover_context(self, goal: str = "", max_chars: int = 3000) -> str:
        """Generate a context string for injection into prover agent prompts.

        Includes relevant cookbook patterns, avoided approaches, and Mathlib API.
        """
        sections = []

        # Relevant cookbook patterns
        if goal:
            relevant = self.cookbook_for_goal(goal)
        else:
            relevant = self.cookbook_patterns[:10]

        if relevant:
            lines = ["## Relevant Tactic Patterns (from KB)"]
            for p in relevant:
                lines.append(f"- **{p.get('name', '?')}** ({p.get('category', '?')}): {p.get('when', '')}")
                tactic = p.get("tactic", "")
                if tactic:
                    lines.append(f"  Tactic: `{tactic}`")
                nots = p.get("not", [])
                if nots:
                    lines.append(f"  Avoid: {nots}")
            sections.append("\n".join(lines))

        # Key failed approaches
        if self.failed_approaches:
            lines = ["## Known Failed Approaches (DO NOT repeat)"]
            for fa in self.failed_approaches[:8]:
                lines.append(f"- {fa.get('what_failed', '?')}: {fa.get('lesson', fa.get('why', ''))}")
            sections.append("\n".join(lines))

        # Critical Mathlib API
        if self.mathlib_api:
            lines = ["## Mathlib API Notes"]
            for key, desc in list(self.mathlib_api.items())[:10]:
                lines.append(f"- {key}: {desc}")
            sections.append("\n".join(lines))

        result = "\n\n".join(sections)
        if len(result) > max_chars:
            result = result[:max_chars] + "\n... (truncated)"
        return result

    # --- Legacy methods (v1 compatible) ---

    @staticmethod
    def goal_signature(goal: str) -> str:
        """Create a normalized signature from a goal for matching."""
        sig = goal.strip()
        for noise in ["⊢ ", "| "]:
            if sig.startswith(noise):
                sig = sig[len(noise):]
        return sig[:200].lower()

    def record_success(self, goal: str, tactic: str, theorem: str = "",
                       file: str = ""):
        """Record a successful proof pattern."""
        sig = self.goal_signature(goal)
        existing = self._data["entries"].get(sig)
        if existing:
            existing["uses"] = existing.get("uses", 0) + 1
            existing["tactic"] = tactic
            existing["timestamp"] = datetime.now().isoformat()
        else:
            self._data["entries"][sig] = {
                "tactic": tactic,
                "theorem": theorem,
                "file": file,
                "timestamp": datetime.now().isoformat(),
                "uses": 1,
            }
        self._save()

    def lookup(self, goal: str) -> Optional[Dict]:
        """Look up a previously successful tactic for a goal."""
        sig = self.goal_signature(goal)
        return self._data["entries"].get(sig)

    def search_similar(self, goal: str, max_results: int = 5) -> List[Dict]:
        """Search for similar goals using keyword overlap."""
        sig = self.goal_signature(goal)
        keywords = set(sig.replace("(", " ").replace(")", " ").split())
        results = []

        for entry_sig, entry in self._data["entries"].items():
            entry_kw = set(entry_sig.replace("(", " ").replace(")", " ").split())
            overlap = len(keywords & entry_kw)
            if overlap >= 3:
                results.append({
                    **entry,
                    "goal_signature": entry_sig,
                    "relevance": overlap / max(len(keywords), 1),
                })

        results.sort(key=lambda x: x["relevance"], reverse=True)
        return results[:max_results]

    @property
    def size(self) -> int:
        return len(self._data["entries"])

    def stats(self) -> Dict:
        """Return knowledge base statistics."""
        entries = self._data["entries"]
        total_uses = sum(e.get("uses", 1) for e in entries.values())
        files = set(e.get("file", "") for e in entries.values())
        return {
            "entries": len(entries),
            "cookbook_patterns": len(self.cookbook_patterns),
            "failed_approaches": len(self.failed_approaches),
            "mathlib_api_entries": len(self.mathlib_api),
            "total_uses": total_uses,
            "files": sorted(f for f in files if f),
            "last_updated": self._data.get("last_updated", ""),
        }
