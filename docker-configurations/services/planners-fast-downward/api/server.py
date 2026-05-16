"""Minimal HTTP API for Fast Downward planner."""
import json
import os
import subprocess
import tempfile
from http.server import HTTPServer, BaseHTTPRequestHandler

FD_SCRIPT = "/opt/fast-downward/fast-downward.py"


class PlannerHandler(BaseHTTPRequestHandler):
    def do_GET(self):
        if self.path == "/health":
            self._json_response({
                "status": "healthy",
                "planner": "fast-downward",
                "version": "24.06.1",
            })
        else:
            self._json_response({"error": "not found"}, 404)

    def do_POST(self):
        if self.path == "/plan":
            content_length = int(self.headers.get("Content-Length", 0))
            body = json.loads(self.rfile.read(content_length))

            domain = body.get("domain", "")
            problem = body.get("problem", "")
            search = body.get("search", "astar(lmcut())")

            if not domain or not problem:
                self._json_response({"error": "domain and problem PDDL required"}, 400)
                return

            with tempfile.TemporaryDirectory() as tmpdir:
                domain_file = os.path.join(tmpdir, "domain.pddl")
                problem_file = os.path.join(tmpdir, "problem.pddl")

                with open(domain_file, "w") as f:
                    f.write(domain)
                with open(problem_file, "w") as f:
                    f.write(problem)

                try:
                    result = subprocess.run(
                        ["python3", FD_SCRIPT, domain_file, problem_file, "--search", search],
                        capture_output=True, text=True, timeout=300,
                        cwd="/opt/fast-downward",
                    )
                    self._json_response({
                        "returncode": result.returncode,
                        "stdout": result.stdout[-5000:] if result.stdout else "",
                        "stderr": result.stderr[-5000:] if result.stderr else "",
                        "search": search,
                    })
                except subprocess.TimeoutExpired:
                    self._json_response({"error": "planning timeout (300s)"}, 504)
                except Exception as e:
                    self._json_response({"error": str(e)}, 500)
        else:
            self._json_response({"error": "not found"}, 404)

    def _json_response(self, data, code=200):
        self.send_response(code)
        self.send_header("Content-Type", "application/json")
        self.end_headers()
        self.wfile.write(json.dumps(data).encode())

    def log_message(self, format, *args):
        print(f"[planner-api] {args[0]}")


if __name__ == "__main__":
    port = int(os.environ.get("PLANNER_PORT", 8200))
    server = HTTPServer(("0.0.0.0", port), PlannerHandler)
    print(f"Fast Downward API server running on port {port}")
    server.serve_forever()
