#!/usr/bin/env python3
"""
ComfyUI Idle Monitor - Auto-unload models after inactivity

This script monitors a ComfyUI instance and calls the /free API endpoint
after a configurable period of inactivity to release GPU memory.

Usage:
    python comfyui_idle_monitor.py --url http://localhost:8188 --timeout 1200

Environment variables:
    COMFYUI_URL: ComfyUI API URL (default: http://localhost:8188)
    IDLE_TIMEOUT: Idle timeout in seconds (default: 1200 = 20 min)
    CHECK_INTERVAL: Check interval in seconds (default: 60)
    LOG_LEVEL: Logging level (default: INFO)
"""

import os
import time
import logging
import argparse
import threading
from datetime import datetime
from typing import Optional
from functools import wraps

try:
    import requests
except ImportError:
    print("Error: requests library required. Install with: pip install requests")
    exit(1)

logger = logging.getLogger("comfyui-idle-monitor")


class ComfyUIIdleMonitor:
    """
    Monitors ComfyUI activity and unloads models after idle timeout.

    Features:
    - Tracks last prompt execution via /history endpoint
    - Calls /free endpoint to unload models
    - Thread-safe operation
    - Health check endpoint for monitoring
    """

    def __init__(
        self,
        comfyui_url: str = "http://localhost:8188",
        idle_timeout: int = 1200,  # 20 minutes default
        check_interval: int = 60,   # Check every minute
        auth_token: Optional[str] = None
    ):
        self.comfyui_url = comfyui_url.rstrip("/")
        self.idle_timeout = idle_timeout
        self.check_interval = check_interval
        self.auth_token = auth_token

        self._last_activity: Optional[float] = None
        self._last_check: Optional[float] = None
        self._running = False
        self._monitor_thread: Optional[threading.Thread] = None
        self._unload_count = 0
        self._error_count = 0

        # Setup session with optional auth
        self.session = requests.Session()
        if auth_token:
            self.session.headers["Authorization"] = f"Bearer {auth_token}"

    def _get_headers(self) -> dict:
        """Get request headers with optional auth."""
        headers = {"Content-Type": "application/json"}
        if self.auth_token:
            headers["Authorization"] = f"Bearer {self.auth_token}"
        return headers

    def get_running_prompts(self) -> list:
        """Get list of currently running prompt IDs."""
        try:
            resp = self.session.get(
                f"{self.comfyui_url}/queue",
                headers=self._get_headers(),
                timeout=10
            )
            resp.raise_for_status()
            data = resp.json()
            # Return running prompts (queue_running)
            return data.get("queue_running", [])
        except Exception as e:
            logger.warning(f"Failed to get queue status: {e}")
            return []

    def get_recent_history(self, max_items: int = 10) -> dict:
        """Get recent prompt execution history."""
        try:
            resp = self.session.get(
                f"{self.comfyui_url}/history?max_items={max_items}",
                headers=self._get_headers(),
                timeout=10
            )
            resp.raise_for_status()
            return resp.json()
        except Exception as e:
            logger.warning(f"Failed to get history: {e}")
            return {}

    def get_last_activity_time(self) -> Optional[float]:
        """
        Get timestamp of last activity from ComfyUI.

        Returns the most recent prompt execution time, or None if unable to determine.
        """
        try:
            # Check if something is running right now
            running = self.get_running_prompts()
            if running:
                logger.debug(f"Found {len(running)} running prompts")
                return time.time()  # Active right now

            # Check recent history for last execution
            history = self.get_recent_history(max_items=5)
            if not history:
                return None

            # Find most recent prompt end time
            latest_time = None
            for prompt_id, prompt_data in history.items():
                # Look for end_time in outputs or status
                if "outputs" in prompt_data:
                    # Prompt completed, check timestamp
                    for node_id, node_output in prompt_data["outputs"].items():
                        if isinstance(node_output, dict):
                            # Some outputs have timestamps
                            pass  # ComfyUI doesn't include timestamps in outputs

                # Check status for timing info
                status = prompt_data.get("status", {})
                if "end_time" in status:
                    end_time = status["end_time"] / 1000.0  # Convert ms to seconds
                    if latest_time is None or end_time > latest_time:
                        latest_time = end_time

            return latest_time

        except Exception as e:
            logger.error(f"Error getting last activity: {e}")
            self._error_count += 1
            return None

    def unload_models(self) -> bool:
        """Call ComfyUI /free endpoint to unload models and free VRAM."""
        try:
            logger.info("Calling /free to unload models...")

            # /free with unload_models=true unloads all models
            resp = self.session.post(
                f"{self.comfyui_url}/free",
                json={"unload_models": True},
                headers=self._get_headers(),
                timeout=30
            )
            resp.raise_for_status()

            self._unload_count += 1
            logger.info(f"Models unloaded successfully (total unloads: {self._unload_count})")
            return True

        except Exception as e:
            logger.error(f"Failed to unload models: {e}")
            self._error_count += 1
            return False

    def check_and_unload(self) -> bool:
        """
        Check if idle timeout has been reached and unload if necessary.

        Returns True if models were unloaded.
        """
        current_time = time.time()
        self._last_check = current_time

        # Get last activity
        last_activity = self.get_last_activity_time()

        if last_activity is None:
            # No activity recorded yet
            logger.debug("No activity recorded, skipping unload check")
            return False

        self._last_activity = last_activity
        idle_time = current_time - last_activity

        logger.debug(f"Idle time: {idle_time:.0f}s / {self.idle_timeout}s")

        if idle_time >= self.idle_timeout:
            logger.info(f"Idle timeout reached ({idle_time:.0f}s >= {self.idle_timeout}s)")
            return self.unload_models()

        return False

    def _monitor_loop(self):
        """Background thread that periodically checks for idle timeout."""
        logger.info(f"Monitor thread started (interval: {self.check_interval}s, timeout: {self.idle_timeout}s)")

        while self._running:
            try:
                self.check_and_unload()
            except Exception as e:
                logger.error(f"Error in monitor loop: {e}")

            # Sleep in small increments to allow quick shutdown
            for _ in range(self.check_interval):
                if not self._running:
                    break
                time.sleep(1)

        logger.info("Monitor thread stopped")

    def start(self):
        """Start the idle monitor in a background thread."""
        if self._running:
            logger.warning("Monitor already running")
            return

        self._running = True
        self._monitor_thread = threading.Thread(target=self._monitor_loop, daemon=True)
        self._monitor_thread.start()
        logger.info("ComfyUI Idle Monitor started")

    def stop(self):
        """Stop the idle monitor."""
        self._running = False
        if self._monitor_thread:
            self._monitor_thread.join(timeout=5)
        logger.info("ComfyUI Idle Monitor stopped")

    @property
    def status(self) -> dict:
        """Get current monitor status."""
        idle_time = None
        if self._last_activity:
            idle_time = time.time() - self._last_activity

        return {
            "running": self._running,
            "comfyui_url": self.comfyui_url,
            "idle_timeout": self.idle_timeout,
            "check_interval": self.check_interval,
            "last_activity": self._last_activity,
            "idle_seconds": round(idle_time, 1) if idle_time else None,
            "last_check": self._last_check,
            "unload_count": self._unload_count,
            "error_count": self._error_count
        }


def run_standalone():
    """Run as standalone script."""
    parser = argparse.ArgumentParser(
        description="ComfyUI Idle Monitor - Auto-unload models after inactivity"
    )
    parser.add_argument(
        "--url",
        default=os.environ.get("COMFYUI_URL", "http://localhost:8188"),
        help="ComfyUI API URL (default: http://localhost:8188)"
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=int(os.environ.get("IDLE_TIMEOUT", "1200")),
        help="Idle timeout in seconds (default: 1200 = 20 min)"
    )
    parser.add_argument(
        "--interval",
        type=int,
        default=int(os.environ.get("CHECK_INTERVAL", "60")),
        help="Check interval in seconds (default: 60)"
    )
    parser.add_argument(
        "--token",
        default=os.environ.get("COMFYUI_AUTH_TOKEN"),
        help="Authentication token (optional)"
    )
    parser.add_argument(
        "--log-level",
        default=os.environ.get("LOG_LEVEL", "INFO"),
        choices=["DEBUG", "INFO", "WARNING", "ERROR"],
        help="Logging level (default: INFO)"
    )

    args = parser.parse_args()

    # Setup logging
    logging.basicConfig(
        level=getattr(logging, args.log_level),
        format="%(asctime)s [%(levelname)s] %(name)s: %(message)s",
        datefmt="%Y-%m-%d %H:%M:%S"
    )

    # Create and start monitor
    monitor = ComfyUIIdleMonitor(
        comfyui_url=args.url,
        idle_timeout=args.timeout,
        check_interval=args.interval,
        auth_token=args.token
    )

    logger.info(f"Starting ComfyUI Idle Monitor")
    logger.info(f"  URL: {args.url}")
    logger.info(f"  Timeout: {args.timeout}s ({args.timeout // 60} min)")
    logger.info(f"  Interval: {args.interval}s")

    try:
        monitor.start()

        # Keep main thread alive
        while True:
            time.sleep(1)

    except KeyboardInterrupt:
        logger.info("Shutting down...")
        monitor.stop()


if __name__ == "__main__":
    run_standalone()
