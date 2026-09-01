#!/usr/bin/env python3
"""Bounded user cache for raw GitHub JSON payloads.

The cache is deliberately transport-agnostic: callers provide a fetch function
and keep all domain derivation outside this module. Entries live outside the
repository, are written atomically, and may be served stale only when a fresh
fetch fails. Every read returns an explicit status so stale data cannot look
fresh.
"""

from __future__ import annotations

import hashlib
import json
import os
import pathlib
import tempfile
import time
from dataclasses import dataclass
from typing import Any, Callable

SCHEMA_VERSION = 1
DEFAULT_MAX_ENTRIES = 32


@dataclass(frozen=True)
class CacheResult:
    """Payload plus the observable cache decision that produced it."""

    payload: Any
    status: str
    fetched_at: float | None
    age_seconds: float | None
    error: str | None = None

    def as_dict(self) -> dict[str, Any]:
        return {
            "status": self.status,
            "fetched_at": self.fetched_at,
            "age_seconds": self.age_seconds,
            "error": self.error,
        }


def default_cache_dir(platform_name: str | None = None) -> pathlib.Path:
    """Return the platform user-cache location, never a repository path."""
    platform_name = platform_name or os.name
    local = os.environ.get("LOCALAPPDATA")
    if platform_name == "nt" and local:
        return pathlib.Path(local) / "CoursIA" / "cache" / "pick_idle_grain"
    xdg = os.environ.get("XDG_CACHE_HOME")
    base = pathlib.Path(xdg) if xdg else pathlib.Path.home() / ".cache"
    return base / "coursia" / "pick_idle_grain"


def cache_key(repository: str, name: str, command: list[str]) -> str:
    """Build a stable key from repository, schema, measurement and query."""
    material = json.dumps(
        {
            "repository": repository,
            "schema": SCHEMA_VERSION,
            "name": name,
            "command": command,
        },
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    )
    digest = hashlib.sha256(material.encode("utf-8")).hexdigest()
    safe_name = "".join(c if c.isalnum() or c in "-_" else "-" for c in name)
    return f"{safe_name}-{digest[:24]}"


class PayloadCache:
    """Small file cache with atomic writes and bounded retention."""

    def __init__(
        self,
        directory: pathlib.Path | str | None = None,
        *,
        max_entries: int = DEFAULT_MAX_ENTRIES,
        clock: Callable[[], float] = time.time,
    ) -> None:
        self.directory = pathlib.Path(directory) if directory else default_cache_dir()
        self.max_entries = max(1, max_entries)
        self.clock = clock

    def _path(self, key: str) -> pathlib.Path:
        return self.directory / f"{key}.json"

    def _read(self, key: str) -> tuple[Any, float] | None:
        path = self._path(key)
        try:
            envelope = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, UnicodeError, json.JSONDecodeError):
            return None
        if not isinstance(envelope, dict):
            return None
        if envelope.get("schema") != SCHEMA_VERSION:
            return None
        fetched_at = envelope.get("fetched_at")
        if not isinstance(fetched_at, (int, float)) or "payload" not in envelope:
            return None
        return envelope["payload"], float(fetched_at)

    def _write(self, key: str, payload: Any, fetched_at: float) -> None:
        self.directory.mkdir(parents=True, exist_ok=True)
        envelope = {
            "schema": SCHEMA_VERSION,
            "fetched_at": fetched_at,
            "payload": payload,
        }
        fd, raw_path = tempfile.mkstemp(
            prefix=f".{key}-", suffix=".tmp", dir=self.directory
        )
        tmp = pathlib.Path(raw_path)
        try:
            with os.fdopen(fd, "w", encoding="utf-8", newline="\n") as stream:
                json.dump(envelope, stream, ensure_ascii=False, separators=(",", ":"))
                stream.flush()
                os.fsync(stream.fileno())
            os.replace(tmp, self._path(key))
        finally:
            try:
                tmp.unlink()
            except FileNotFoundError:
                pass
        self._prune()

    def _prune(self) -> None:
        try:
            paths = sorted(
                self.directory.glob("*.json"),
                key=lambda path: path.stat().st_mtime,
                reverse=True,
            )
        except OSError:
            return
        for path in paths[self.max_entries :]:
            try:
                path.unlink()
            except OSError:
                pass

    def get_or_fetch(
        self,
        key: str,
        ttl_seconds: float,
        fetch: Callable[[], Any],
        *,
        mode: str = "auto",
    ) -> CacheResult:
        """Read or refresh one entry.

        ``off`` bypasses disk entirely. ``refresh`` always calls ``fetch`` but
        can still return an explicitly stale entry if that call fails.
        """
        if mode not in {"auto", "off", "refresh"}:
            raise ValueError(f"unsupported cache mode: {mode}")
        if mode == "off":
            payload = fetch()
            return CacheResult(payload, "bypass", None, None)

        now = self.clock()
        cached = self._read(key)
        if cached is not None:
            payload, fetched_at = cached
            age = max(0.0, now - fetched_at)
            if mode == "auto" and age <= ttl_seconds:
                return CacheResult(payload, "hit", fetched_at, age)
        else:
            payload, fetched_at, age = None, None, None

        try:
            fresh = fetch()
        except Exception as exc:
            if cached is None:
                raise
            return CacheResult(
                payload,
                "stale",
                fetched_at,
                age,
                f"{type(exc).__name__}: {exc}",
            )

        try:
            self._write(key, fresh, now)
        except OSError as exc:
            return CacheResult(
                fresh,
                "bypass",
                now,
                0.0,
                f"{type(exc).__name__}: {exc}",
            )
        status = "refresh" if mode == "refresh" else "miss"
        return CacheResult(fresh, status, now, 0.0)
