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
    """Payload plus the observable cache decision that produced it.

    ``verified`` says whether the payload was *measured* current, not merely
    believed current: a live fetch, or a TTL-valid entry whose freshness probe
    confirmed that the remote has not moved past ``fetched_at``. An unverified
    hit is a normal outcome (no probe was supplied, or the probe could not
    measure) -- but it must never be reported as if it had been checked.
    """

    payload: Any
    status: str
    fetched_at: float | None
    age_seconds: float | None
    error: str | None = None
    verified: bool = False
    probe_delta_seconds: float | None = None

    def as_dict(self) -> dict[str, Any]:
        return {
            "status": self.status,
            "fetched_at": self.fetched_at,
            "age_seconds": self.age_seconds,
            "error": self.error,
            "verified": self.verified,
            "probe_delta_seconds": self.probe_delta_seconds,
        }


def _measure(probe: Callable[[], float | None] | None) -> tuple[float | None, bool]:
    """Run a freshness probe, returning ``(newest_remote_timestamp, measured)``.

    A probe is a *cheap* question asked to the remote ("what is the timestamp of
    the most recently updated item?") whose answer is compared against the
    snapshot's ``fetched_at``. It is the only sound staleness detector: a cached
    payload can never prove its own staleness, because every field it carries --
    ``updatedAt`` included -- was read at fetch time, so ``updatedAt <=
    fetched_at`` holds by construction. A probe that raises, or that answers
    with something that is not a timestamp, is *unmeasured*, not fatal: the
    caller keeps a usable payload and loses only the verification.
    """
    if probe is None:
        return None, False
    try:
        value = probe()
    except Exception:
        return None, False
    if isinstance(value, (int, float)) and not isinstance(value, bool):
        return float(value), True
    return None, False


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
        probe: Callable[[], float | None] | None = None,
    ) -> CacheResult:
        """Read or refresh one entry.

        ``off`` bypasses disk entirely. ``refresh`` always calls ``fetch`` but
        can still return an explicitly stale entry if that call fails.

        ``probe`` is an optional cheap freshness measurement (see ``_measure``).
        Without it, ``auto`` is a pure TTL bet: a fresh-looking entry is served
        with ``verified=False``, and the caller is expected to say so instead of
        letting an unchecked payload circulate as if it had been checked (#17096).
        With it, a TTL-valid entry that the probe proves outdated is refreshed
        without operator intervention.
        """
        if mode not in {"auto", "off", "refresh"}:
            raise ValueError(f"unsupported cache mode: {mode}")
        if mode == "off":
            payload = fetch()
            return CacheResult(payload, "bypass", None, None, verified=True)

        now = self.clock()
        cached = self._read(key)
        probe_value: float | None = None
        measured = False
        if cached is not None:
            payload, fetched_at = cached
            age = max(0.0, now - fetched_at)
            if mode == "auto" and age <= ttl_seconds:
                probe_value, measured = _measure(probe)
                if not measured or probe_value <= fetched_at:
                    # Soit le distant n'a pas bouge depuis notre snapshot (mesure),
                    # soit on n'a pas su le mesurer (pas de sonde, ou sonde muette).
                    return CacheResult(
                        payload,
                        "hit",
                        fetched_at,
                        age,
                        verified=measured,
                        probe_delta_seconds=(
                            probe_value - fetched_at if measured else None
                        ),
                    )
                # La sonde PROUVE que le distant a bouge apres notre snapshot :
                # on rafraichit sans intervention, au lieu de servir du perime.
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
                # `fetched_at` est garanti non None ici (on vient de lire une
                # entree), donc la seule condition est la mesure elle-meme :
                # tester la valeur de l'horodatage serait faux a l'epoque 0.
                probe_delta_seconds=(
                    probe_value - fetched_at if measured else None
                ),
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
                verified=True,
            )
        status = "refresh" if mode == "refresh" else "miss"
        return CacheResult(
            fresh,
            status,
            now,
            0.0,
            verified=True,
            probe_delta_seconds=(
                probe_value - fetched_at
                if measured and fetched_at is not None
                else None
            ),
        )
