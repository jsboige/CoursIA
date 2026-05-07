"""Trace logger for multi-agent proof sessions.

B.12: Integrates OpenTelemetry spans alongside JSON trace entries.
Uses agent_framework.observability when available, graceful fallback otherwise.
"""

import json
import time
from pathlib import Path
from datetime import datetime
from typing import Dict, Optional

# B.12: OTel integration — optional, graceful degradation
_otel_tracer = None
_otel_meter = None
try:
    from agent_framework.observability import get_tracer, get_meter
    _otel_tracer = get_tracer("lean-prover")
    _otel_meter = get_meter("lean-prover")
except Exception:
    pass


class TraceLogger:
    """Captures full multi-agent conversation traces with timing.

    B.12: Also emits OTel spans for each agent interaction and proof iteration.
    """

    def __init__(self, output_dir: str = "traces", enable_otel: bool = True):
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(exist_ok=True)
        self.entries = []
        self.session_start = time.time()
        self.phase_timings: Dict[str, float] = {}
        self._otel_enabled = enable_otel and _otel_tracer is not None
        self._otel_tracer = _otel_tracer
        self._otel_meter = _otel_meter
        self._active_spans: Dict[str, object] = {}

        # B.12: OTel counters
        if _otel_meter and self._otel_enabled:
            self._counter_iterations = _otel_meter.create_counter(
                "prover.iterations", description="Proof iterations"
            )
            self._counter_tactic_attempts = _otel_meter.create_counter(
                "prover.tactic_attempts", description="Tactic attempts"
            )
            self._histogram_duration = _otel_meter.create_histogram(
                "prover.agent_duration", description="Agent call duration"
            )
        else:
            self._counter_iterations = None
            self._counter_tactic_attempts = None
            self._histogram_duration = None

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

        # B.12: Emit OTel span and metrics
        if self._otel_enabled:
            self._emit_otel(agent, role, content, duration_s, tool_name)

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
            try:
                if isinstance(usage, dict):
                    in_tok = usage.get('input_token_count') or usage.get('input_tokens', 0)
                    out_tok = usage.get('output_token_count') or usage.get('output_tokens', 0)
                else:
                    in_tok = getattr(usage, 'input_token_count', None) or 0
                    out_tok = getattr(usage, 'output_token_count', None) or 0
                self.log(
                    agent=agent, role="usage",
                    content=f"tokens: in={in_tok}, out={out_tok}",
                    duration_s=duration_s,
                    tokens={"input": in_tok, "output": out_tok, "total": in_tok + out_tok},
                )
            except Exception:
                pass

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

    # ── B.12: OTel integration ──

    def _emit_otel(self, agent: str, role: str, content: str,
                   duration_s: float, tool_name: Optional[str] = None):
        """Emit OTel span and metrics for a trace entry."""
        if not self._otel_tracer:
            return

        span_name = f"{agent}.{role}"
        if tool_name:
            span_name += f".{tool_name}"

        try:
            with self._otel_tracer.start_as_current_span(span_name) as span:
                span.set_attribute("agent", agent)
                span.set_attribute("role", role)
                span.set_attribute("duration_s", duration_s)
                if tool_name:
                    span.set_attribute("tool", tool_name)
                span.set_attribute("content.preview", content[:200])
        except Exception:
            pass

        if self._histogram_duration:
            try:
                self._histogram_duration.record(
                    duration_s, {"agent": agent, "role": role}
                )
            except Exception:
                pass

        if self._counter_tactic_attempts and role == "tool_call":
            try:
                self._counter_tactic_attempts.add(1, {"agent": agent, "tool": tool_name or ""})
            except Exception:
                pass

    def start_session_span(self, theorem: str, prover: str) -> Optional[object]:
        """Start a top-level OTel span for a proof session. Returns span or None."""
        if not self._otel_enabled or not self._otel_tracer:
            return None

        try:
            span = self._otel_tracer.start_span(
                f"proof_session.{prover}",
                attributes={"theorem": theorem, "prover": prover},
            )
            self._active_spans["session"] = span
            return span
        except Exception:
            return None

    def end_session_span(self, success: bool, sorry_evolution: str = ""):
        """End the top-level proof session span."""
        span = self._active_spans.pop("session", None)
        if not span:
            return
        try:
            span.set_attribute("success", success)
            span.set_attribute("sorry_evolution", sorry_evolution)
            span.end()
        except Exception:
            pass
