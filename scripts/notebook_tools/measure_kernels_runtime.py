#!/usr/bin/env python3
"""Mesure les runtimes des kernelspecs Jupyter en lançant leurs noyaux.

La sortie JSON contient la déclaration (argv[0]) et les valeurs observées dans
le processus vivant. Les erreurs sont structurelles : le texte des exceptions
et les environnements des noyaux ne sont jamais journalisés.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

PROBE = r'''import importlib.util, json, os, sys
result = {
    "python_version": sys.version.split()[0],
    "executable": os.path.realpath(sys.executable),
    "numpy_version": None,
    "numpy_status": "absent",
}
if importlib.util.find_spec("numpy") is not None:
    try:
        import numpy
        result["numpy_version"] = str(numpy.__version__)
        result["numpy_status"] = "ok"
    except Exception as exc:
        result["numpy_status"] = "error"
        result["numpy_error_type"] = type(exc).__name__
print("COURSIA_KERNEL_RUNTIME=" + json.dumps(result, sort_keys=True))
'''


def _spec_argv0(spec: Any) -> str | None:
    argv = spec.get("argv") if isinstance(spec, dict) else None
    return argv[0] if isinstance(argv, list) and argv and isinstance(argv[0], str) else None


def _valid_probe_data(data: Any) -> bool:
    """N'accepter que les champs et les états produits par la sonde Python."""
    if not isinstance(data, dict):
        return False
    required = {"python_version", "executable", "numpy_version", "numpy_status"}
    if not required <= data.keys() or data.keys() - (required | {"numpy_error_type"}):
        return False
    def nonempty(value: Any) -> bool:
        return isinstance(value, str) and bool(value.strip())

    if not nonempty(data["python_version"]) or not nonempty(data["executable"]):
        return False
    status = data["numpy_status"]
    if status == "ok":
        return nonempty(data["numpy_version"]) and "numpy_error_type" not in data
    if status == "absent":
        return data["numpy_version"] is None and "numpy_error_type" not in data
    if status == "error":
        return data["numpy_version"] is None and nonempty(data.get("numpy_error_type"))
    return False


def _probe_kernel(name: str, timeout: float, manager_factory=None) -> dict[str, Any]:
    """Démarre uniquement le kernelspec demandé et renvoie sa mesure effective."""
    if manager_factory is None:
        from jupyter_client import KernelManager
        manager_factory = KernelManager

    manager = manager_factory(kernel_name=name)
    started = False
    client = None
    try:
        # Les noyaux peuvent écrire des diagnostics arbitraires sur leurs
        # descripteurs de processus ; le protocole Jupyter passe par les
        # canaux ZMQ et reste intact. Garder stdout comme JSON pur.
        manager.start_kernel(stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        started = True
        client = manager.client()
        client.start_channels()
        try:
            client.wait_for_ready(timeout=timeout)
        except RuntimeError as exc:
            # jupyter_client signale son délai par RuntimeError, comme la mort
            # du noyau. Ne reconnaître que ses messages précis de délai.
            if re.fullmatch(
                r"Kernel didn't respond (?:to heartbeats )?in \d+ seconds(?: and timed out)?",
                str(exc),
            ):
                return {"status": "timeout", "error_type": "TimeoutError",
                        "stage": "readiness"}
            raise
        info_id = client.kernel_info()
        deadline = __import__("time").monotonic() + timeout
        while True:
            remaining = deadline - __import__("time").monotonic()
            if remaining <= 0:
                return {"status": "timeout", "error_type": "TimeoutError",
                        "stage": "kernel_info"}
            try:
                info_msg = client.get_shell_msg(timeout=remaining)
            except Exception as exc:
                if type(exc).__name__ == "Empty":
                    return {"status": "timeout", "error_type": "TimeoutError",
                            "stage": "kernel_info"}
                raise
            if info_msg.get("parent_header", {}).get("msg_id") == info_id:
                break
        language_info = info_msg.get("content", {}).get("language_info", {})
        language = language_info.get("name")
        if not isinstance(language, str) or not language.strip():
            return {"status": "kernel_info_error", "error_type": "MissingLanguageInfo"}
        if language.strip().lower() not in {"python", "python2", "python3"}:
            return {"status": "not_python", "kernel_language": language}

        msg_id = client.execute(PROBE)
        deadline = __import__("time").monotonic() + timeout
        output = ""
        while True:
            remaining = deadline - __import__("time").monotonic()
            if remaining <= 0:
                return {"status": "timeout", "error_type": "TimeoutError"}
            try:
                msg = client.get_iopub_msg(timeout=remaining)
            except Exception as exc:
                if type(exc).__name__ == "Empty":
                    return {"status": "timeout", "error_type": "TimeoutError"}
                raise
            if msg.get("parent_header", {}).get("msg_id") != msg_id:
                continue
            kind = msg.get("msg_type")
            content = msg.get("content", {})
            if kind == "error":
                return {"status": "probe_error", "error_type": "KernelExecutionError"}
            if kind == "stream":
                output += content.get("text", "")
            if kind == "status" and content.get("execution_state") == "idle":
                for line in output.splitlines():
                    if line.startswith("COURSIA_KERNEL_RUNTIME="):
                        try:
                            data = json.loads(line.split("=", 1)[1])
                        except (ValueError, TypeError):
                            return {"status": "invalid_probe_output",
                                    "error_type": "JSONDecodeError"}
                        if not _valid_probe_data(data):
                            return {"status": "invalid_probe_output",
                                    "error_type": "InvalidProbeData"}
                        return {"status": "ok", "kernel_language": language, **data}
                return {"status": "probe_output_missing",
                        "error_type": "MissingProbeOutput", "kernel_language": language}
    except Exception as exc:
        # Ne pas journaliser str(exc) : des implementations peuvent y inclure
        # des arguments de lancement ou des chemins sensibles.
        timeout_error = isinstance(exc, TimeoutError) or type(exc).__name__ == "TimeoutError"
        return {"status": "timeout" if timeout_error else "startup_error",
                "error_type": type(exc).__name__}
    finally:
        if client is not None:
            try:
                client.stop_channels()
            except Exception:
                pass
        if started:
            try:
                manager.shutdown_kernel(now=True)
            except Exception:
                pass


def collect(timeout: float = 60, names: list[str] | None = None) -> dict[str, Any]:
    """Mesure tous les kernelspecs enregistrés, ou une sélection par nom."""
    from jupyter_client.kernelspec import KernelSpecManager

    specs = KernelSpecManager().get_all_specs()
    selected = sorted(names if names is not None else specs)
    rows = []
    for name in selected:
        info = specs.get(name)
        if info is None:
            rows.append({"name": name, "argv0_declared": None,
                         "status": "kernelspec_missing", "error_type": "KeyError"})
            continue
        spec = info.get("spec", {})
        row = {"name": name, "argv0_declared": _spec_argv0(spec)}
        row.update(_probe_kernel(name, timeout))
        rows.append(row)
    return {
        "schema_version": 1,
        "measured_at_utc": datetime.now(timezone.utc).isoformat(),
        "machine": __import__("platform").node(),
        "collector": "scripts/notebook_tools/measure_kernels_runtime.py",
        "kernels": rows,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--timeout", type=float, default=60,
                        help="délai en secondes par démarrage et exécution (défaut: 60)")
    parser.add_argument("--kernel", action="append", dest="kernels",
                        help="nom à mesurer (répétable ; défaut : tous les kernelspecs)")
    parser.add_argument("--output", type=Path,
                        help="fichier JSON (défaut : stdout)")
    args = parser.parse_args(argv)
    if args.timeout <= 0:
        parser.error("--timeout doit être positif")
    result = collect(args.timeout, args.kernels)
    rendered = json.dumps(result, ensure_ascii=False, indent=2) + "\n"
    if args.output:
        args.output.write_text(rendered, encoding="utf-8")
    else:
        sys.stdout.write(rendered)
    acceptable = {"ok", "not_python"}
    return 0 if all(row["status"] in acceptable for row in result["kernels"]) else 1


if __name__ == "__main__":
    raise SystemExit(main())
