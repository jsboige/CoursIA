#!/usr/bin/env python3
"""
Lazy Model Manager - Auto-unload models after inactivity

Usage:
    from lazy_model import LazyModelManager

    manager = LazyModelManager(
        model_name="whisper",
        load_fn=lambda: WhisperModel(...),
        idle_timeout=300,  # 5 minutes
        device="cuda"
    )

    # In your endpoint:
    model = manager.get_model()
    result = model.transcribe(...)

    # Background task handles auto-unload
"""

import os
import time
import logging
import threading
import asyncio
from typing import Callable, Optional, Any
from functools import wraps

logger = logging.getLogger("lazy-model")

# Global registry of all managers for monitoring
_managers: dict[str, "LazyModelManager"] = {}


class LazyModelManager:
    """
    Manages lazy loading and auto-unloading of ML models.

    Features:
    - Load on first request
    - Track last usage time
    - Auto-unload after idle timeout
    - Thread-safe operations
    """

    def __init__(
        self,
        model_name: str,
        load_fn: Callable[[], Any],
        unload_fn: Optional[Callable[[Any], None]] = None,
        idle_timeout: int = 300,  # 5 minutes default
        device: str = "cuda",
        preload: bool = False
    ):
        """
        Args:
            model_name: Human-readable name for logging
            load_fn: Function that loads and returns the model
            unload_fn: Optional custom unload function (default: del + gc)
            idle_timeout: Seconds of inactivity before unload (0 = never unload)
            device: Device for GPU memory cleanup
            preload: Load model immediately on startup
        """
        self.model_name = model_name
        self.load_fn = load_fn
        self.unload_fn = unload_fn
        self.idle_timeout = idle_timeout
        self.device = device

        self._model: Optional[Any] = None
        self._last_used: Optional[float] = None
        self._lock = threading.Lock()
        self._load_time: Optional[float] = None
        self._unload_count = 0

        # Register for monitoring
        _managers[model_name] = self

        if preload:
            self.get_model()

    def get_model(self) -> Any:
        """Get the model, loading it if necessary."""
        with self._lock:
            if self._model is None:
                logger.info(f"Loading model: {self.model_name}")
                start = time.time()
                self._model = self.load_fn()
                self._load_time = time.time() - start
                logger.info(f"Model {self.model_name} loaded in {self._load_time:.1f}s")

            self._last_used = time.time()
            return self._model

    def unload_if_idle(self) -> bool:
        """Check if model is idle and unload it. Returns True if unloaded."""
        with self._lock:
            if self._model is None:
                return False

            if self.idle_timeout <= 0:
                return False

            if self._last_used is None:
                return False

            idle_time = time.time() - self._last_used
            if idle_time > self.idle_timeout:
                logger.info(f"Unloading idle model: {self.model_name} (idle for {idle_time:.0f}s)")
                self._do_unload()
                return True

            return False

    def force_unload(self) -> bool:
        """Force unload the model regardless of idle time."""
        with self._lock:
            if self._model is None:
                return False
            logger.info(f"Force unloading model: {self.model_name}")
            self._do_unload()
            return True

    def _do_unload(self):
        """Internal unload logic. Must be called with lock held."""
        if self.unload_fn:
            self.unload_fn(self._model)
        else:
            # Default unload: delete and cleanup GPU memory
            del self._model

            # Try to cleanup GPU memory
            try:
                import torch
                if self.device == "cuda" and torch.cuda.is_available():
                    torch.cuda.empty_cache()
                    logger.debug(f"GPU cache cleared for {self.model_name}")
            except ImportError:
                pass
            except Exception as e:
                logger.warning(f"Error clearing GPU cache: {e}")

        self._model = None
        self._unload_count += 1
        logger.info(f"Model {self.model_name} unloaded (total unloads: {self._unload_count})")

    @property
    def is_loaded(self) -> bool:
        return self._model is not None

    @property
    def status(self) -> dict:
        """Get current status for health checks."""
        idle_time = None
        if self._last_used:
            idle_time = time.time() - self._last_used

        return {
            "model_name": self.model_name,
            "loaded": self._model is not None,
            "load_time": self._load_time,
            "last_used": self._last_used,
            "idle_seconds": round(idle_time, 1) if idle_time else None,
            "idle_timeout": self.idle_timeout,
            "unload_count": self._unload_count
        }


async def idle_checker_task(interval: int = 60):
    """
    Background task that periodically checks for idle models.

    Args:
        interval: Check interval in seconds
    """
    logger.info(f"Starting idle checker task (interval: {interval}s)")

    while True:
        try:
            await asyncio.sleep(interval)

            unloaded = []
            for name, manager in _managers.items():
                if manager.unload_if_idle():
                    unloaded.append(name)

            if unloaded:
                logger.info(f"Auto-unloaded models: {unloaded}")

        except asyncio.CancelledError:
            logger.info("Idle checker task cancelled")
            break
        except Exception as e:
            logger.error(f"Error in idle checker: {e}")


def get_all_status() -> dict:
    """Get status of all registered model managers."""
    return {
        "managers": {name: m.status for name, m in _managers.items()},
        "total_models": len(_managers),
        "loaded_models": sum(1 for m in _managers.values() if m.is_loaded)
    }


# Convenience decorator for FastAPI endpoints
def with_model(manager: LazyModelManager):
    """
    Decorator that ensures model is loaded before endpoint execution.

    Usage:
        @app.post("/transcribe")
        @with_model(whisper_manager)
        async def transcribe(...):
            model = whisper_manager.get_model()
            ...
    """
    def decorator(func):
        @wraps(func)
        async def wrapper(*args, **kwargs):
            # Just accessing get_model() updates the last_used timestamp
            manager.get_model()
            return await func(*args, **kwargs)
        return wrapper
    return decorator
