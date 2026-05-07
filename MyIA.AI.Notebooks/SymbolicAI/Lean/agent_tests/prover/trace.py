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
            state_snapshot: dict = None, thinking: str = None):
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
        if thinking:
            entry["thinking"] = thinking
        self.entries.append(entry)

        if phase:
            self.phase_timings[phase] = self.phase_timings.get(phase, 0) + duration_s

        ts = f"[+{entry['timestamp']:.1f}s]"
        if role == "thinking":
            preview = (thinking or "")[:150].replace("\n", " ")
            print(f"  {ts} {agent} [THINKING]: {preview}...")
        elif tool_name:
            print(f"  {ts} {agent} -> {tool_name}({json.dumps(tool_args or {})[:80]}) -> {duration_s:.2f}s")
        else:
            preview = (content or "")[:120].replace("\n", " ")
            print(f"  {ts} {agent} [{role}]: {preview}...")

    def log_agent_response(self, agent: str, response, duration_s: float = 0,
                           iteration: int = 0):
        """Extract and log ALL content from an AgentResponse: thinking, text, tool calls."""
        if not hasattr(response, 'messages') or not response.messages:
            self.log(agent=agent, role="empty_response",
                     content="(no messages in response)", duration_s=duration_s)
            return

        for msg_idx, msg in enumerate(response.messages):
            if not hasattr(msg, 'contents') or not msg.contents:
                continue

            for content in msg.contents:
                content_type = getattr(content, 'type', 'unknown')

                if content_type == "text_reasoning":
                    reasoning_text = self._extract_reasoning_text(content)
                    self.log(
                        agent=agent, role="thinking",
                        content=f"[reasoning {len(reasoning_text)} chars]",
                        duration_s=0,
                        thinking=reasoning_text,
                    )

                elif content_type == "text":
                    text = getattr(content, 'text', '') or ''
                    if text.strip():
                        self.log(
                            agent=agent, role="text_response",
                            content=text[:2000],
                            duration_s=0,
                        )

                elif content_type == "function_call":
                    fc_name = getattr(content, 'name', '') or ''
                    fc_args = getattr(content, 'arguments', '') or ''
                    fc_id = getattr(content, 'call_id', '') or ''
                    self.log(
                        agent=agent, role="tool_call",
                        content=f"call {fc_name}({str(fc_args)[:200]})",
                        duration_s=0,
                        tool_name=fc_name,
                        tool_args={"call_id": fc_id, "arguments": str(fc_args)[:1000]},
                    )

                elif content_type == "function_result":
                    fr_text = getattr(content, 'text', '') or ''
                    fr_id = getattr(content, 'call_id', '') or ''
                    self.log(
                        agent=agent, role="tool_result",
                        content=fr_text[:500] if fr_text else "(empty)",
                        duration_s=0,
                        tool_name=f"result_{fr_id}",
                        tool_result=fr_text[:1000],
                    )

                elif content_type == "usage":
                    pass  # Handled via tokens field

        # Log usage if available
        if hasattr(response, 'usage_details') and response.usage_details:
            usage = response.usage_details
            self.log(
                agent=agent, role="usage",
                content=f"tokens: in={usage.input_token_count}, out={usage.output_token_count}",
                duration_s=duration_s,
                tokens={"input": usage.input_token_count,
                        "output": usage.output_token_count,
                        "total": (usage.input_token_count or 0) + (usage.output_token_count or 0)},
            )

    def _extract_reasoning_text(self, content) -> str:
        """Extract reasoning text from a text_reasoning Content item."""
        # Try direct text attribute
        text = getattr(content, 'text', None)
        if text:
            return text

        # Try protected_data (JSON-encoded reasoning details)
        protected = getattr(content, 'protected_data', None)
        if protected:
            try:
                import json as _json
                data = _json.loads(protected)
                # Could be a list of reasoning items or a single dict
                if isinstance(data, list):
                    parts = []
                    for item in data:
                        if isinstance(item, dict):
                            parts.append(item.get('text', '') or item.get('content', '') or str(item))
                    return '\n'.join(parts)
                elif isinstance(data, dict):
                    return data.get('text', '') or data.get('content', '') or _json.dumps(data)
            except Exception:
                return str(protected)[:2000]

        # Try additional_properties
        props = getattr(content, 'additional_properties', None)
        if props and isinstance(props, dict):
            return props.get('reasoning_text', '') or ''

        return "(protected reasoning)"

    def save_full_trace(self, name: str = None):
        """Save complete trace with thinking content to a separate file."""
        if not name:
            name = f"full_trace_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
        path = self.output_dir / f"{name}.json"
        with open(path, "w", encoding="utf-8") as f:
            json.dump(self.entries, f, indent=2, ensure_ascii=False)
        return str(path)

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
