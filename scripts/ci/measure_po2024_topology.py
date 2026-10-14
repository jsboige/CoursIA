"""Mesure topologique OS-level d'un hôte self-hosted.

Sous-grain borné de #15574 (variance 3-4x du pool self-hosted `coursia-ephemeral`).
Le commentaire ai-01 sur #issuecomment-5645345667 dit explicitement :

    « Le nombre de conteneurs par hôte **physique** et le plafond de
      jobs concurrents de l'hôte. Ces deux nombres restent à écrire
      depuis la machine, et je ne les devine pas. »

Ce script livre le **complément** mesurable **localement** depuis l'OS :
- CPU modèle + cores physiques + logical processors + load instantané
- RAM totale + slots + mémoire libre
- Daemon docker (CPU/memory plafonnés, conteneurs actifs)

Les DEUX nombres non atteignables localement (conteneurs éphémères
par hôte **physique** managés par GitHub Actions + plafond de jobs
concurrents de l'hôte côté registration `self-hosted runner`) restent
la responsabilité du coordinateur ai-01 (console d'admin du runner pool).
L'instrument les **nomme explicitement** plutôt que de les inventer.

Cross-platform : Linux (procfs), Windows (WMI via CIM), macOS (sysctl).
Aucune dépendance externe ; module standard uniquement.
"""
from __future__ import annotations

import json
import platform
import shutil
import subprocess
import sys
from dataclasses import asdict, dataclass, field
from typing import Any


SYSTEM = platform.system()  # 'Linux' | 'Windows' | 'Darwin'


@dataclass
class HostTopology:
    hostname: str
    os_name: str
    kernel: str
    cpu_model: str
    cpu_cores_physical: int | None
    cpu_logical_processors: int | None
    cpu_load_instant_pct: int | None
    ram_total_gib: float | None
    ram_free_gib: float | None
    ram_slots: list[dict[str, Any]] = field(default_factory=list)
    manufacturer: str | None = None
    model: str | None = None

    docker_cpus: int | None = None
    docker_memory_gib: float | None = None
    docker_containers_running: int | None = None
    docker_containers_total: int | None = None
    docker_kernel: str | None = None
    docker_os: str | None = None

    out_of_scope_first_hand: list[str] = field(default_factory=list)


OUT_OF_SCOPE = [
    "Nombre de conteneurs éphémères GitHub Actions par hôte physique — managé par la console d'admin du runner pool, pas mesurable OS-localement.",
    "Plafond de jobs concurrents de l'hôte — paramètre d'enregistrement `self-hosted runner` côté GitHub org, pas paramètre OS.",
]


def _safe_run(cmd: list[str], timeout_s: int = 10) -> str | None:
    if shutil.which(cmd[0]) is None and SYSTEM != "Windows":
        return None
    try:
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout_s)
        if result.returncode != 0:
            return None
        return result.stdout
    except (FileNotFoundError, subprocess.TimeoutExpired, OSError, ValueError):
        return None


def _ps_run(script: str) -> str | None:
    """Exécute un script PowerShell et capture stdout (Windows)."""
    if shutil.which("powershell") is None:
        return None
    try:
        result = subprocess.run(
            ["powershell", "-NoProfile", "-Command", script],
            capture_output=True, text=True, timeout=15,
        )
        if result.returncode != 0:
            return None
        return result.stdout
    except (FileNotFoundError, subprocess.TimeoutExpired, OSError):
        return None


def measure_windows() -> dict[str, Any]:
    """Topologie Windows via WMI CIM (PowerShell)."""
    out: dict[str, Any] = {
        "hostname": platform.node(),
        "os_name": f"Windows {platform.release()} ({platform.version()})",
        "kernel": platform.release(),
        "manufacturer": None,
        "model": None,
        "cpu_model": "unknown",
        "cpu_cores_physical": None,
        "cpu_logical_processors": None,
        "cpu_load_instant_pct": None,
        "ram_total_gib": None,
        "ram_free_gib": None,
        "ram_slots": [],
    }
    ps = _ps_run(
        "Get-CimInstance Win32_Processor | "
        "Select-Object Name, NumberOfCores, NumberOfLogicalProcessors, LoadPercentage | "
        "ConvertTo-Json -Compress"
    )
    if ps:
        try:
            j = json.loads(ps)
            if isinstance(j, list):
                j = j[0] if j else {}
            out["cpu_model"] = j.get("Name", "unknown")
            out["cpu_cores_physical"] = j.get("NumberOfCores")
            out["cpu_logical_processors"] = j.get("NumberOfLogicalProcessors")
            out["cpu_load_instant_pct"] = j.get("LoadPercentage")
        except (json.JSONDecodeError, IndexError, TypeError):
            pass

    ps = _ps_run(
        "Get-CimInstance Win32_ComputerSystem | "
        "Select-Object Manufacturer, Model, TotalPhysicalMemory | "
        "ConvertTo-Json -Compress"
    )
    if ps:
        try:
            j = json.loads(ps)
            if isinstance(j, list):
                j = j[0] if j else {}
            out["manufacturer"] = j.get("Manufacturer")
            out["model"] = j.get("Model")
            if j.get("TotalPhysicalMemory"):
                out["ram_total_gib"] = round(j["TotalPhysicalMemory"] / (1024**3), 2)
        except (json.JSONDecodeError, IndexError, TypeError):
            pass

    ps = _ps_run(
        "Get-CimInstance Win32_OperatingSystem | "
        "Select-Object FreePhysicalMemory, TotalVisibleMemorySize | "
        "ConvertTo-Json -Compress"
    )
    if ps:
        try:
            j = json.loads(ps)
            if isinstance(j, list):
                j = j[0] if j else {}
            # WMI: FreePhysicalMemory en KiB. On stocke en GiB pour
            # cohérence avec `ram_total_gib` (sortie de Win32_ComputerSystem).
            if j.get("FreePhysicalMemory") is not None:
                out["ram_free_gib"] = round(j["FreePhysicalMemory"] / 1024 / 1024, 2)
        except (json.JSONDecodeError, IndexError, TypeError):
            pass

    ps = _ps_run(
        "Get-CimInstance Win32_PhysicalMemory | "
        "Select-Object Capacity, Speed | "
        "ConvertTo-Json -Compress"
    )
    if ps:
        try:
            arr = json.loads(ps)
            if isinstance(arr, dict):
                arr = [arr]
            out["ram_slots"] = [
                {"capacity_gib": round(s["Capacity"] / (1024**3), 2), "speed_mhz": s.get("Speed")}
                for s in arr if s.get("Capacity")
            ]
        except (json.JSONDecodeError, TypeError):
            pass
    return out


def measure_linux() -> dict[str, Any]:
    """Topologie Linux via /proc et sysfs."""
    out: dict[str, Any] = {
        "hostname": platform.node(),
        "os_name": " ".join(platform.linux_distribution()) if hasattr(platform, "linux_distribution") else platform.platform(),
        "kernel": platform.release(),
        "manufacturer": None,
        "model": None,
        "cpu_model": "unknown",
        "cpu_cores_physical": None,
        "cpu_logical_processors": None,
        "cpu_load_instant_pct": None,
        "ram_total_gib": None,
        "ram_free_gib": None,
        "ram_slots": [],
    }
    cpuinfo = _safe_run(["cat", "/proc/cpuinfo"]) or ""
    model_lines: list[str] = []
    cores_phys = cores_log = None
    for line in cpuinfo.splitlines():
        if line.startswith("model name"):
            model_lines.append(line.split(":", 1)[1].strip())
        if line.startswith("cpu cores"):
            try:
                cores_phys = int(line.split(":", 1)[1].strip())
            except ValueError:
                pass
        if line.startswith("processor"):
            try:
                cores_log = max(cores_log or 0, int(line.split(":", 1)[1].strip()) + 1)
            except ValueError:
                pass
    out["cpu_model"] = model_lines[0] if model_lines else "unknown"
    out["cpu_cores_physical"] = cores_phys
    out["cpu_logical_processors"] = cores_log

    loadavg = _safe_run(["cat", "/proc/loadavg"])
    if loadavg and cores_log:
        try:
            load1 = float(loadavg.split()[0])
            out["cpu_load_instant_pct"] = int(round(load1 * 100 / cores_log))
        except (ValueError, IndexError):
            pass

    meminfo = _safe_run(["cat", "/proc/meminfo"]) or ""
    mem_total = mem_avail = None
    for line in meminfo.splitlines():
        if line.startswith("MemTotal:"):
            try:
                mem_total = int(line.split()[1])
            except (ValueError, IndexError):
                pass
        if line.startswith("MemAvailable:"):
            try:
                mem_avail = int(line.split()[1])
            except (ValueError, IndexError):
                pass
    if mem_total:
        out["ram_total_gib"] = round(mem_total / 1024 / 1024, 2)
    if mem_avail:
        out["ram_free_gib"] = round(mem_avail / 1024 / 1024, 2)

    for path, key in (
        ("/sys/class/dmi/id/sys_vendor", "manufacturer"),
        ("/sys/class/dmi/id/product_name", "model"),
    ):
        out[key] = _safe_run(["cat", path])

    return out


def measure_darwin() -> dict[str, Any]:
    """Topologie macOS via sysctl/sw_vers."""
    out: dict[str, Any] = {
        "hostname": platform.node(),
        "os_name": platform.mac_ver()[0] or "macOS",
        "kernel": platform.release(),
        "manufacturer": "Apple",
        "model": None,
        "cpu_model": "unknown",
        "cpu_cores_physical": None,
        "cpu_logical_processors": None,
        "cpu_load_instant_pct": None,
        "ram_total_gib": None,
        "ram_free_gib": None,
        "ram_slots": [],
    }
    sw = _safe_run(["sw_vers", "-productName"]) or ""
    out["model"] = sw.strip() or None
    name = _safe_run(["sysctl", "-n", "machdep.cpu.brand_string"])
    if name:
        out["cpu_model"] = name.strip()
    cores_phys = _safe_run(["sysctl", "-n", "hw.physicalcpu"])
    if cores_phys and cores_phys.strip().isdigit():
        out["cpu_cores_physical"] = int(cores_phys.strip())
    cores_log = _safe_run(["sysctl", "-n", "hw.logicalcpu"])
    if cores_log and cores_log.strip().isdigit():
        out["cpu_logical_processors"] = int(cores_log.strip())
    ram_bytes = _safe_run(["sysctl", "-n", "hw.memsize"])
    if ram_bytes and ram_bytes.strip().isdigit():
        out["ram_total_gib"] = round(int(ram_bytes.strip()) / 1024**3, 2)
    return out


def measure_docker() -> dict[str, Any]:
    """Mesure docker info cross-platform."""
    empty = {
        "docker_cpus": None,
        "docker_memory_gib": None,
        "docker_containers_running": None,
        "docker_containers_total": None,
        "docker_kernel": None,
        "docker_os": None,
    }
    info = _safe_run(["docker", "info", "--format", "{{json .}}"])
    if not info:
        return empty
    try:
        j = json.loads(info)
    except json.JSONDecodeError:
        return empty
    return {
        "docker_cpus": j.get("NCPU"),
        "docker_memory_gib": round(j.get("MemTotal", 0) / 1024**3, 2) if j.get("MemTotal") else None,
        "docker_containers_running": j.get("ContainersRunning"),
        "docker_containers_total": j.get("Containers"),
        "docker_kernel": j.get("KernelVersion"),
        "docker_os": j.get("OperatingSystem"),
    }


def measure() -> HostTopology:
    if SYSTEM == "Windows":
        base = measure_windows()
    elif SYSTEM == "Darwin":
        base = measure_darwin()
    else:
        base = measure_linux()
    docker_block = measure_docker()
    return HostTopology(
        **base,
        **docker_block,
        out_of_scope_first_hand=list(OUT_OF_SCOPE),
    )


def main() -> int:
    topo = measure()
    print(json.dumps(asdict(topo), indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    sys.exit(main())
