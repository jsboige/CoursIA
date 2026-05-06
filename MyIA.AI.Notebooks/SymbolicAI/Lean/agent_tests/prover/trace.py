"""Trace logger for multi-agent proof sessions."""

import json
import time
from pathlib import Path
from datetime import datetime
from typing import Dict


class TraceLogger:
    """Captures full multi-agent conversation traces with timing."""

    def __init__(self, output_dir: str = "traces"):
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(exist_ok=True)
        self.entries = []
        self.session_start = time.time()
        self.phase_timings: Dict[str, float] = {}

    def log(self, agent: str, role: str, content: str, duration_s: float = 0,
            tool_name: str = None, tool_args: dict = None, tool_result: str = None,
            model: str = None, tokens: dict = None, phase: str = None,
            state_snapshot: dict = None):
        entry = {
            "timestamp": round(time.time() - self.session_start, 3),
            "agent": agent,
            "role": role,
            "content": content,
            "duration_s": round(duration_s, 3),
        }
        if tool_name:
            entry["tool_call"] = tool_name
            entry["tool_args"] = tool_args
            entry["tool_result"] = (tool_result or "")[:500]
        if model:
            entry["model"] = model
        if tokens:
            entry["tokens"] = tokens
        if phase:
            entry["phase"] = phase
        if state_snapshot:
            entry["state"] = state_snapshot
        self.entries.append(entry)

        if phase:
            self.phase_timings[phase] = self.phase_timings.get(phase, 0) + duration_s

        ts = f"[+{entry['timestamp']:.1f}s]"
        if tool_name:
            print(f"  {ts} {agent} -> {tool_name}({json.dumps(tool_args or {})[:80]}) -> {duration_s:.2f}s")
        else:
            preview = (content or "")[:120].replace("\n", " ")
            print(f"  {ts} {agent} [{role}]: {preview}...")

    def save(self, name: str = None):
        if not name:
            name = f"trace_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
        path = self.output_dir / f"{name}.json"
        with open(path, "w", encoding="utf-8") as f:
            json.dump(self.entries, f, indent=2, ensure_ascii=False)
        print(f"Trace saved: {path} ({len(self.entries)} entries)")
        return str(path)

    def summary(self):
        agents = {}
        for e in self.entries:
            a = e["agent"]
            if a not in agents:
                agents[a] = {"calls": 0, "tool_calls": 0, "total_s": 0, "tokens": 0}
            agents[a]["calls"] += 1
            if e.get("tool_call"):
                agents[a]["tool_calls"] += 1
            agents[a]["total_s"] += e.get("duration_s", 0)
            if e.get("tokens"):
                agents[a]["tokens"] += e["tokens"].get("total", 0)
        return agents
