#!/usr/bin/env python3
"""
Generic Service Idle Monitor - Stop Docker containers after inactivity

Unlike comfyui_idle_monitor.py which calls /free to unload models,
this monitor stops the entire Docker container when idle, and the
container's restart policy (unless-stopped) keeps it ready for manual
restart.

Use for services without built-in idle unload:
- tts-fishaudio (FishAudio S2-Pro)
- vllm-zimage (vLLM image generation)
- sd-forge-main (Stable Diffusion Forge)

Usage:
    python service_idle_monitor.py \
        --health-url http://localhost:8197/v1/health \
        --container-name tts-fishaudio \
        --timeout 1200

Environment variables:
    HEALTH_URL: HTTP endpoint to check for activity
    CONTAINER_NAME: Docker container name to stop when idle
    IDLE_TIMEOUT: Idle timeout in seconds (default: 1200 = 20 min)
    CHECK_INTERVAL: Check interval in seconds (default: 60)
    STARTUP_GRACE: Seconds after container start before monitoring (default: 300)
    LOG_LEVEL: Logging level (default: INFO)
"""

import os
import time
import logging
import argparse
import subprocess
import json
from datetime import datetime
from typing import Optional

try:
    import requests
except ImportError:
    print("Error: requests library required. Install with: pip install requests")
    exit(1)

DOCKER_SOCKET = os.environ.get("DOCKER_SOCKET", "/var/run/docker.sock")

logger = logging.getLogger("service-idle-monitor")


class ServiceIdleMonitor:
    """
    Monitors an HTTP service and stops its Docker container when idle.

    Detection methods:
    1. If service returns activity data (e.g. request count), track changes
    2. If health endpoint only returns 200, track time since last request
    3. If service is unreachable, assume container is already stopped
    """

    def __init__(
        self,
        health_url: str,
        container_name: str,
        idle_timeout: int = 1200,
        check_interval: int = 60,
        startup_grace: int = 300,
        activity_fn: Optional[callable] = None,
    ):
        self.health_url = health_url.rstrip("/")
        self.container_name = container_name
        self.idle_timeout = idle_timeout
        self.check_interval = check_interval
        self.startup_grace = startup_grace
        self.activity_fn = activity_fn

        self._last_activity: Optional[float] = None
        self._last_response_hash: Optional[str] = None
        self._running = False
        self._stop_count = 0
        self._container_start_time: Optional[float] = None

    def _docker_api_get(self, path: str) -> Optional[dict]:
        """Query Docker Engine API via unix socket using curl."""
        try:
            result = subprocess.run(
                ["curl", "-sf", "--unix-socket", DOCKER_SOCKET,
                 f"http://localhost{path}"],
                capture_output=True, text=True, timeout=10
            )
            if result.returncode == 0 and result.stdout:
                return json.loads(result.stdout)
        except Exception:
            pass
        return None

    def _docker_api_post(self, path: str) -> bool:
        """POST to Docker Engine API via unix socket using curl."""
        try:
            result = subprocess.run(
                ["curl", "-sf", "-X", "POST", "--unix-socket", DOCKER_SOCKET,
                 f"http://localhost{path}"],
                capture_output=True, text=True, timeout=60
            )
            return result.returncode == 0
        except Exception:
            return False

    def _is_container_running(self) -> bool:
        """Check if the Docker container is running."""
        data = self._docker_api_get(f"/containers/{self.container_name}/json")
        if data:
            return data.get("State", {}).get("Running", False)
        return False

    def _get_container_uptime(self) -> Optional[float]:
        """Get container uptime in seconds."""
        data = self._docker_api_get(f"/containers/{self.container_name}/json")
        if not data:
            return None
        started_at = data.get("State", {}).get("StartedAt", "")
        if not started_at:
            return None
        started_at = started_at.rstrip("Z").split(".")[0]
        dt = datetime.fromisoformat(started_at)
        return (datetime.utcnow() - dt).total_seconds()

    def _stop_container(self) -> bool:
        """Stop the Docker container via Docker Engine API."""
        try:
            logger.info(f"Stopping container: {self.container_name}")
            if self._docker_api_post(f"/containers/{self.container_name}/stop"):
                self._stop_count += 1
                logger.info(f"Container {self.container_name} stopped (total stops: {self._stop_count})")
                return True
            else:
                logger.error(f"Failed to stop container {self.container_name}")
                return False
        except Exception as e:
            logger.error(f"Error stopping container: {e}")
            return False

    def check_service_activity(self) -> Optional[float]:
        """
        Check if the service is active by hitting its health endpoint.
        Returns timestamp of last activity, or None if unable to determine.
        """
        # First check if container is running
        if not self._is_container_running():
            logger.debug(f"Container {self.container_name} is not running")
            return None

        # Check startup grace period
        uptime = self._get_container_uptime()
        if uptime is not None and uptime < self.startup_grace:
            logger.debug(f"Container in startup grace period ({uptime:.0f}s < {self.startup_grace}s)")
            return time.time()  # Consider as active during startup

        try:
            resp = requests.get(self.health_url, timeout=10)
            if resp.status_code == 200:
                # Service is responding = it's loaded and potentially active
                # Use custom activity detection if available
                if self.activity_fn:
                    return self.activity_fn(resp)
                # Default: compare response content to detect changes
                response_hash = str(hash(resp.text))
                if response_hash != self._last_response_hash:
                    self._last_response_hash = response_hash
                    return time.time()
                # Response unchanged - return previous activity time
                return self._last_activity
            else:
                logger.debug(f"Health check returned {resp.status_code}")
                return self._last_activity

        except requests.exceptions.ConnectionError:
            # Service unreachable but container running = loading
            logger.debug("Service unreachable (still loading?)")
            return time.time()  # Don't count loading as idle
        except Exception as e:
            logger.warning(f"Health check error: {e}")
            return self._last_activity

    def check_and_stop(self) -> bool:
        """
        Check if idle timeout has been reached and stop container if necessary.
        Returns True if container was stopped.
        """
        current_time = time.time()

        last_activity = self.check_service_activity()

        if last_activity is None:
            # Container not running, nothing to do
            return False

        self._last_activity = last_activity
        idle_time = current_time - last_activity

        logger.debug(f"Idle time: {idle_time:.0f}s / {self.idle_timeout}s")

        if idle_time >= self.idle_timeout:
            logger.info(f"Idle timeout reached ({idle_time:.0f}s >= {self.idle_timeout}s)")
            return self._stop_container()

        return False

    def run(self):
        """Main monitoring loop."""
        logger.info(f"Service Idle Monitor started")
        logger.info(f"  Health URL: {self.health_url}")
        logger.info(f"  Container: {self.container_name}")
        logger.info(f"  Timeout: {self.idle_timeout}s ({self.idle_timeout // 60} min)")
        logger.info(f"  Interval: {self.check_interval}s")
        logger.info(f"  Startup grace: {self.startup_grace}s")

        while True:
            try:
                self.check_and_stop()
            except Exception as e:
                logger.error(f"Error in monitor loop: {e}")

            # Sleep in small increments for responsive shutdown
            for _ in range(self.check_interval):
                time.sleep(1)


def fishaudio_activity(resp: requests.Response) -> Optional[float]:
    """Custom activity detector for FishAudio TTS."""
    try:
        data = resp.json()
        # FishAudio health returns model info when loaded
        # If we can detect active requests, use that
        # For now, any successful response = active
        return time.time()
    except Exception:
        return time.time()


def main():
    parser = argparse.ArgumentParser(
        description="Service Idle Monitor - Stop Docker containers after inactivity"
    )
    parser.add_argument(
        "--health-url",
        default=os.environ.get("HEALTH_URL", "http://localhost:8080/health"),
        help="Health check URL"
    )
    parser.add_argument(
        "--container-name",
        default=os.environ.get("CONTAINER_NAME", "service"),
        help="Docker container name to stop"
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=int(os.environ.get("IDLE_TIMEOUT", "1200")),
        help="Idle timeout in seconds (default: 1200)"
    )
    parser.add_argument(
        "--interval",
        type=int,
        default=int(os.environ.get("CHECK_INTERVAL", "60")),
        help="Check interval in seconds (default: 60)"
    )
    parser.add_argument(
        "--startup-grace",
        type=int,
        default=int(os.environ.get("STARTUP_GRACE", "300")),
        help="Grace period after container start (default: 300)"
    )
    parser.add_argument(
        "--log-level",
        default=os.environ.get("LOG_LEVEL", "INFO"),
        choices=["DEBUG", "INFO", "WARNING", "ERROR"],
        help="Logging level"
    )

    args = parser.parse_args()

    logging.basicConfig(
        level=getattr(logging, args.log_level),
        format="%(asctime)s [%(levelname)s] %(name)s: %(message)s",
        datefmt="%Y-%m-%d %H:%M:%S"
    )

    monitor = ServiceIdleMonitor(
        health_url=args.health_url,
        container_name=args.container_name,
        idle_timeout=args.timeout,
        check_interval=args.interval,
        startup_grace=args.startup_grace,
    )

    try:
        monitor.run()
    except KeyboardInterrupt:
        logger.info("Shutting down...")


if __name__ == "__main__":
    main()
