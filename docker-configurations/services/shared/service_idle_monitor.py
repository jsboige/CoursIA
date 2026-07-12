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
    AUTH_USER: Username for HTTP Basic Auth or Gradio session auth
    AUTH_PASSWORD: Password for HTTP Basic Auth or Gradio session auth
    GRADIO_LOGIN_URL: Gradio login endpoint (e.g. http://host:1111/login)
                      When set, uses Gradio session auth instead of HTTP Basic Auth
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
        idle_action: str = "stop",
        sleep_url: Optional[str] = None,
        auth_user: Optional[str] = None,
        auth_password: Optional[str] = None,
        gradio_login_url: Optional[str] = None,
    ):
        self.health_url = health_url.rstrip("/")
        self.container_name = container_name
        self.idle_timeout = idle_timeout
        self.check_interval = check_interval
        self.startup_grace = startup_grace
        self.activity_fn = activity_fn
        self.idle_action = idle_action
        self.sleep_url = sleep_url or self.health_url.rsplit("/", 1)[0] + "/sleep"
        self.wake_url = self.health_url.rsplit("/", 1)[0] + "/wake_up"
        self.is_sleeping_url = self.health_url.rsplit("/", 1)[0] + "/is_sleeping"
        self.auth_user = auth_user
        self.auth_password = auth_password
        self.gradio_login_url = gradio_login_url

        self._last_activity: Optional[float] = None
        self._last_response_hash: Optional[str] = None
        self._running = False
        self._stop_count = 0
        self._container_start_time: Optional[float] = None
        self._ever_responded: bool = False
        self._gradio_logged_in: bool = False

        self.session = requests.Session()

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

    def _sleep_service(self) -> bool:
        """Put service to sleep via native API (vLLM sleep mode)."""
        try:
            logger.info(f"Putting service to sleep: {self.sleep_url}")
            resp = requests.post(self.sleep_url, params={"level": 1}, timeout=30)
            resp.raise_for_status()
            self._stop_count += 1
            logger.info(f"Service asleep (GPU VRAM freed, total sleeps: {self._stop_count})")
            return True
        except Exception as e:
            logger.error(f"Failed to sleep service: {e}")
            return False

    def _is_service_sleeping(self) -> bool:
        """Check if service is in native sleep mode."""
        try:
            resp = requests.get(self.is_sleeping_url, timeout=10)
            if resp.status_code == 200:
                return resp.json().get("is_sleeping", False)
        except Exception:
            pass
        return False

    def _gradio_login(self) -> bool:
        """Authenticate with Gradio session auth (e.g. sd-forge-main).

        Gradio uses form-based login at an internal port (e.g. :1111)
        which returns a session cookie valid for the Caddy-proxied port.
        """
        if not self.gradio_login_url or not self.auth_user or not self.auth_password:
            return False

        try:
            resp = self.session.post(
                self.gradio_login_url,
                data={"user": self.auth_user, "password": self.auth_password},
                allow_redirects=False,
                timeout=10,
            )
            # Gradio returns 303 on success with session cookie, redirects to /
            if resp.status_code == 303 and self.session.cookies:
                self._gradio_logged_in = True
                logger.info(f"Gradio login successful as {self.auth_user}")
                return True

            logger.warning(f"Gradio login failed: status={resp.status_code}")
            return False
        except Exception as e:
            logger.warning(f"Gradio login error: {e}")
            return False

    def _ensure_gradio_auth(self) -> bool:
        """Ensure Gradio session is authenticated, re-login if needed."""
        if not self.gradio_login_url:
            return True  # Not using Gradio auth
        if self._gradio_logged_in:
            return True
        return self._gradio_login()

    def check_service_activity(self) -> Optional[float]:
        """
        Check if the service is active by hitting its health endpoint.
        Returns timestamp of last activity, or None if unable to determine.
        """
        # If service is in native sleep mode, don't count as idle
        # (it's intentionally sleeping, GPU already freed)
        if self.idle_action == "sleep" and self._is_service_sleeping():
            logger.debug("Service is in sleep mode (GPU freed)")
            return time.time()

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
            req_kwargs = {"timeout": 10, "allow_redirects": False}

            if self.gradio_login_url:
                # Gradio session auth: use cookies from login
                if not self._ensure_gradio_auth():
                    logger.debug("Gradio auth not available, skipping check")
                    return self._last_activity
            elif self.auth_user and self.auth_password:
                req_kwargs["auth"] = (self.auth_user, self.auth_password)

            resp = self.session.get(self.health_url, **req_kwargs)

            if resp.status_code == 200:
                self._ever_responded = True
                if self.activity_fn:
                    return self.activity_fn(resp)
                response_hash = str(hash(resp.text))
                if response_hash != self._last_response_hash:
                    self._last_response_hash = response_hash
                    return time.time()
                return self._last_activity

            if resp.status_code in (301, 302, 303, 307, 308):
                # Redirect = service is up but needs auth
                # Only treat as "loading" if we never got a 200 before
                if not self._ever_responded:
                    logger.debug(f"Service redirecting ({resp.status_code}), still loading or needs auth")
                    return time.time()
                # If using Gradio auth, session may have expired
                if self.gradio_login_url:
                    self._gradio_logged_in = False
                logger.debug(f"Service redirecting ({resp.status_code}), auth issue?")
                return self._last_activity

            logger.debug(f"Health check returned {resp.status_code}")
            return self._last_activity

        except requests.exceptions.ConnectionError:
            # Only treat as "loading" during startup or if never responded
            if not self._ever_responded:
                logger.debug("Service unreachable (still loading?)")
                return time.time()
            logger.debug("Service unreachable after previous success")
            return self._last_activity
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

        logger.info(f"Idle: {idle_time:.0f}s / {self.idle_timeout}s ({self.container_name})")

        if idle_time >= self.idle_timeout:
            logger.info(f"Idle timeout reached ({idle_time:.0f}s >= {self.idle_timeout}s)")
            if self.idle_action == "sleep":
                return self._sleep_service()
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
    parser.add_argument(
        "--idle-action",
        default=os.environ.get("IDLE_ACTION", "stop"),
        choices=["stop", "sleep"],
        help="Idle action: stop (docker stop) or sleep (native API sleep mode)"
    )
    parser.add_argument(
        "--auth-user",
        default=os.environ.get("AUTH_USER"),
        help="HTTP Basic Auth username (optional)"
    )
    parser.add_argument(
        "--auth-password",
        default=os.environ.get("AUTH_PASSWORD"),
        help="HTTP Basic Auth password (optional)"
    )
    parser.add_argument(
        "--gradio-login-url",
        default=os.environ.get("GRADIO_LOGIN_URL"),
        help="Gradio session auth login URL (e.g. http://host:1111/login)"
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
        idle_action=args.idle_action,
        auth_user=args.auth_user,
        auth_password=args.auth_password,
        gradio_login_url=args.gradio_login_url,
    )

    try:
        monitor.run()
    except KeyboardInterrupt:
        logger.info("Shutting down...")


if __name__ == "__main__":
    main()
