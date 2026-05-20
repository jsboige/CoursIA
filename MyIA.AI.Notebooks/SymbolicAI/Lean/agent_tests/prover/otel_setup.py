"""OpenTelemetry wiring for the multi-agent prover.

Sets up MS Agent Framework's `enable_instrumentation` plus a JSONL span
exporter so every agent run, tool call, and LLM completion emits a
structured span we can replay offline.

Why we own the exporter:
- The framework's default console exporter dumps to stdout — unusable when
  the prover is iterating on multi-page Lean errors.
- We need durable evidence of WHAT each agent saw and WHAT it produced
  (including reasoning tokens) so the user can ask "why did the model loop
  on `omega`?" days later.

Usage::

    from .otel_setup import enable_prover_otel
    trace_path = enable_prover_otel(session_name="demo9_zai")
    # ... run prover ...
    # spans land in agent_tests/prover/baselines/traces/<session_name>.jsonl
"""

from __future__ import annotations

import json
import os
import threading
from datetime import datetime, timezone
from pathlib import Path
from typing import Optional, Sequence

from opentelemetry.sdk.trace.export import (
    ReadableSpan,
    SpanExporter,
    SpanExportResult,
)


_BASELINES_DIR = Path(__file__).resolve().parent / "baselines" / "traces"
_BASELINES_DIR.mkdir(parents=True, exist_ok=True)


class JsonlSpanExporter(SpanExporter):
    """Append spans as JSONL — one line per span — to a single file.

    Each line is self-contained JSON with all attributes captured by the
    framework's instrumentation (including ``gen_ai.*`` semantic conventions
    when sensitive-data is enabled), plus events (which carry the prompt /
    completion / tool-call payloads).
    """

    def __init__(self, output_path: Path):
        self._path = output_path
        self._path.parent.mkdir(parents=True, exist_ok=True)
        self._lock = threading.Lock()
        self._is_shutdown = False

    def export(self, spans: Sequence[ReadableSpan]) -> SpanExportResult:
        if self._is_shutdown:
            return SpanExportResult.FAILURE
        try:
            with self._lock, self._path.open("a", encoding="utf-8") as f:
                for span in spans:
                    f.write(json.dumps(_span_to_dict(span), ensure_ascii=False))
                    f.write("\n")
            return SpanExportResult.SUCCESS
        except Exception:
            return SpanExportResult.FAILURE

    def shutdown(self) -> None:
        self._is_shutdown = True


def _span_to_dict(span: ReadableSpan) -> dict:
    ctx = span.context
    parent = span.parent
    return {
        "name": span.name,
        "trace_id": format(ctx.trace_id, "032x") if ctx else None,
        "span_id": format(ctx.span_id, "016x") if ctx else None,
        "parent_span_id": format(parent.span_id, "016x") if parent else None,
        "start_time_ns": span.start_time,
        "end_time_ns": span.end_time,
        "duration_ms": (
            (span.end_time - span.start_time) / 1e6
            if span.start_time and span.end_time
            else None
        ),
        "status": str(span.status.status_code.name) if span.status else None,
        "attributes": dict(span.attributes or {}),
        "events": [
            {
                "name": ev.name,
                "timestamp_ns": ev.timestamp,
                "attributes": dict(ev.attributes or {}),
            }
            for ev in (span.events or [])
        ],
        "scope": (
            span.instrumentation_scope.name
            if span.instrumentation_scope
            else None
        ),
    }


_otel_state = {"setup": False, "exporter": None, "path": None}


def enable_prover_otel(
    session_name: Optional[str] = None,
    *,
    capture_sensitive: bool = True,
    also_console: bool = False,
) -> Path:
    """Configure OTel providers and return the JSONL trace path.

    Idempotent across calls within a single process: the framework's
    ``configure_otel_providers`` setup runs once; subsequent calls simply
    rotate the JSONL output to a new session file.

    Args:
        session_name: Suffix for the output file. Defaults to a timestamp.
        capture_sensitive: When True, the framework will record prompts,
            completions, and tool arguments in span attributes. The user
            asked for full trace delivery — keep this on for prover work.
        also_console: When True, still print spans to console (useful for
            interactive debugging).
    """
    if session_name is None:
        session_name = datetime.now(timezone.utc).strftime("session_%Y%m%dT%H%M%SZ")

    output_path = _BASELINES_DIR / f"{session_name}.spans.jsonl"
    exporter = JsonlSpanExporter(output_path)

    # Avoid the framework noisy "OTel SDK is not installed" warning.
    os.environ.setdefault("ENABLE_OTEL", "true")
    os.environ.setdefault("ENABLE_SENSITIVE_DATA", "true" if capture_sensitive else "false")

    if not _otel_state["setup"]:
        from agent_framework.observability import configure_otel_providers

        configure_otel_providers(
            enable_sensitive_data=capture_sensitive,
            enable_console_exporters=also_console,
            exporters=[exporter],
        )
        _otel_state["setup"] = True
    else:
        # Already configured — just attach a new exporter alongside.
        try:
            from opentelemetry import trace as ot_trace
            from opentelemetry.sdk.trace import TracerProvider
            from opentelemetry.sdk.trace.export import SimpleSpanProcessor

            provider = ot_trace.get_tracer_provider()
            if isinstance(provider, TracerProvider):
                provider.add_span_processor(SimpleSpanProcessor(exporter))
        except Exception:
            pass

    _otel_state["exporter"] = exporter
    _otel_state["path"] = output_path
    return output_path


def current_trace_path() -> Optional[Path]:
    """Return the path of the currently active JSONL trace, if any."""
    return _otel_state.get("path")
