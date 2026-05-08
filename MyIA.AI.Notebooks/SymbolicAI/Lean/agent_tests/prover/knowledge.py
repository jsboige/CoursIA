"""Proof Knowledge Base — persistent storage of successful proof patterns.

Stores tactic patterns that worked (goal_signature -> tactic) in a JSON file
so future sessions can warm-start from past successes.

B.1 from issue #820: cross-session knowledge persistence.
"""

import json
from pathlib import Path
from typing import Dict, List, Optional
from datetime import datetime


DEFAULT_KB_PATH = Path(__file__).parent / "proof_knowledge.json"


class ProofKnowledgeBase:
    """Persistent knowledge base for successful proof patterns.

    Structure:
        {
            "version": 1,
            "last_updated": "2026-05-08T...",
            "entries": {
                "<goal_signature>": {
                    "tactic": "exact ...",
                    "theorem": "theorem_name",
                    "file": "Voting.lean",
                    "timestamp": "...",
                    "uses": 3
                }
            }
        }
    """

    def __init__(self, path: Path = None):
        self._path = path or DEFAULT_KB_PATH
        self._data: Dict = {"version": 1, "last_updated": "", "entries": {}}
        self._load()

    def _load(self):
        if self._path.exists():
            try:
                self._data = json.loads(self._path.read_text(encoding="utf-8"))
                if "entries" not in self._data:
                    self._data["entries"] = {}
            except (json.JSONDecodeError, OSError):
                self._data = {"version": 1, "last_updated": "", "entries": {}}

    def _save(self):
        self._data["last_updated"] = datetime.now().isoformat()
        self._path.write_text(
            json.dumps(self._data, indent=2, ensure_ascii=False),
            encoding="utf-8",
        )

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
            "total_uses": total_uses,
            "files": sorted(f for f in files if f),
            "last_updated": self._data.get("last_updated", ""),
        }
