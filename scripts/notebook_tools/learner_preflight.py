"""Préflight par parcours : vérifie qu'une machine satisfait le profil choisi
avant d'ouvrir le premier notebook. Aucune valeur de secret n'est lue, ni
journalisée — l'outil constate la présence, rien de plus.

Usage:
    python scripts/notebook_tools/learner_preflight.py --parcours <profil> [--json]

Profils alignés sur parcours.qmd :
    - local     : Python 3.10+, Jupyter, sans GPU, sans .NET, sans Docker
    - dotnet    : local + .NET 9 SDK + Lean 4 sous WSL (kernel ML.NET)
    - genai     : dotnet + Docker + GPU NVIDIA + clés d'API présentes

Code retour :
    0  -> premier palier prêt (l'apprenant peut ouvrir le premier notebook)
    1  -> au moins un manque ; le message est nommé et pointe vers la doc
    2  -> erreur d'invocation (profil inconnu, --json mal formé)

Le script n'installe rien. Réfère à docs/reference/kernels-runtime.md et
à la règle F (réparer, ne pas contourner).
"""
from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable


PROFILES = ("local", "dotnet", "genai")

# Cles d'API dont la PRESENCE est verifiee (jamais la valeur).
PROFILE_KEYS: dict[str, tuple[str, ...]] = {
    "local": (),
    "dotnet": (),
    "genai": ("HF_TOKEN", "OPENAI_API_KEY"),
}

# Noyaux Jupyter attendus par profil. Le script ne lance PAS jupyter pour
# les decouvrir : il lit `jupyter kernelspec list` et verifie que le nom
# est present (la sortie textuelle suffit pour un premier palier).
PROFILE_KERNELS: dict[str, tuple[str, ...]] = {
    "local": ("python3",),
    "dotnet": ("python3", ".net-csharp"),
    "genai": ("python3", ".net-csharp"),
}

# Services Docker attendus par profil (presence du binaire docker + test
# rapide `docker info` ; on ne demarre rien).
PROFILE_DOCKER: dict[str, bool] = {
    "local": False,
    "dotnet": False,
    "genai": True,
}

# GPU NVIDIA exige pour le profil genai. Detection par `nvidia-smi`.
PROFILE_GPU: dict[str, bool] = {
    "local": False,
    "dotnet": False,
    "genai": True,
}


@dataclass
class Finding:
    """Un manque ou une garantie releve par le preflight."""

    name: str
    ok: bool
    detail: str
    repair: str = ""

    def to_dict(self) -> dict:
        return {
            "name": self.name,
            "ok": self.ok,
            "detail": self.detail,
            "repair": self.repair,
        }


@dataclass
class Report:
    profile: str
    findings: list[Finding] = field(default_factory=list)

    @property
    def ready(self) -> bool:
        return all(f.ok for f in self.findings)

    def to_dict(self) -> dict:
        return {
            "profile": self.profile,
            "ready": self.ready,
            "findings": [f.to_dict() for f in self.findings],
        }


def _python_version_ok(minimum: str = "3.10") -> Finding:
    major, minor = sys.version_info.major, sys.version_info.minor
    needed = tuple(int(p) for p in minimum.split("."))
    actual = (major, minor)
    ok = actual >= needed
    detail = f"Python {major}.{minor} (requis : >= {minimum})"
    return Finding(
        name="python_version",
        ok=ok,
        detail=detail,
        repair=(
            "Installer Python 3.10+ via conda, pyenv ou le binaire officiel."
            " Voir docs/reference/kernels-runtime.md §Python."
        ) if not ok else "",
    )


def _jupyter_present() -> Finding:
    ok = shutil.which("jupyter") is not None
    return Finding(
        name="jupyter_cli",
        ok=ok,
        detail="`jupyter` trouvé dans PATH" if ok else "`jupyter` absent du PATH",
        repair=(
            "Activer l'env Python qui contient Jupyter (`pip install jupyter` "
            "sinon) ; voir docs/reference/kernels-runtime.md."
        ) if not ok else "",
    )


def _kernels_present(expected: Iterable[str]) -> list[Finding]:
    expected_list = list(expected)
    try:
        out = subprocess.run(
            ["jupyter", "kernelspec", "list"],
            check=False,
            capture_output=True,
            text=True, encoding="utf-8", errors="replace",
            timeout=10,
        )
    except (subprocess.TimeoutExpired, FileNotFoundError) as exc:
        return [Finding(
            name="kernels",
            ok=False,
            detail=f"`jupyter kernelspec list` a échoué : {exc}",
            repair="Réinstaller Jupyter : `pip install jupyter ipykernel`.",
        )]
    text = (out.stdout or "") + (out.stderr or "")
    installed = set()
    for line in text.splitlines():
        line = line.strip()
        if not line or line.startswith("Available"):
            continue
        # Format : "<kernel_name><whitespace><kernel_dir>". Le nom est le
        # premier token, le chemin contient au moins un séparateur (slash
        # Unix ou antislash Windows).
        first = line.split()[0] if line.split() else ""
        if not first:
            continue
        # Filtre les en-têtes de colonnes parasites si le format change.
        if first.lower() in {"kernel"}:
            continue
        installed.add(first)
    missing = [k for k in expected_list if k not in installed]
    if not missing:
        return [Finding(
            name="kernels",
            ok=True,
            detail=f"Kernels présents : {', '.join(expected_list)}",
        )]
    return [Finding(
        name="kernels",
        ok=False,
        detail=f"Kernels manquants : {', '.join(missing)} (requis : {', '.join(expected_list)})",
        repair=(
            "Voir docs/reference/kernels-runtime.md pour la pose du noyau "
            "manquant (Python, .NET Interactive, Lean 4)."
        ),
    )]


def _dotnet_sdk_present() -> Finding:
    ok = shutil.which("dotnet") is not None
    if not ok:
        return Finding(
            name="dotnet_sdk",
            ok=False,
            detail="`dotnet` absent du PATH",
            repair="Installer .NET 9 SDK (https://dot.net) puis vérifier `dotnet --version`.",
        )
    try:
        out = subprocess.run(
            ["dotnet", "--version"],
            check=False, capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=10,
        )
    except subprocess.TimeoutExpired:
        return Finding(
            name="dotnet_sdk",
            ok=False,
            detail="`dotnet --version` timeout",
            repair="Vérifier l'installation .NET ; voir docs/reference/kernels-runtime.md §.NET.",
        )
    version = (out.stdout or "").strip() or "?"
    return Finding(
        name="dotnet_sdk",
        ok=True,
        detail=f"dotnet {version}",
    )


def _lean_present() -> Finding:
    """Lean 4 sous WSL : on regarde `wsl --status` puis `lake --version` dans WSL."""
    if shutil.which("wsl") is None:
        return Finding(
            name="lean4_wsl",
            ok=False,
            detail="WSL absent (requis pour Lean 4 sur Windows)",
            repair="Installer WSL : `wsl --install`. Voir docs/reference/kernels-runtime.md §Lean.",
        )
    try:
        out = subprocess.run(
            ["wsl", "--status"],
            check=False,
            capture_output=True, text=True, encoding="utf-8",
            errors="replace", timeout=10,
        )
    except subprocess.TimeoutExpired:
        return Finding(
            name="lean4_wsl",
            ok=False,
            detail="`wsl --status` timeout",
            repair="Voir docs/reference/kernels-runtime.md §Lean.",
        )
    try:
        out2 = subprocess.run(
            ["wsl", "bash", "-lc", "lake --version"],
            check=False, capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=10,
        )
    except subprocess.TimeoutExpired:
        return Finding(
            name="lean4_wsl",
            ok=False,
            detail="`wsl bash -lc 'lake --version'` timeout",
            repair="Vérifier l'install Lean via elan dans WSL ; voir docs/reference/kernels-runtime.md.",
        )
    ver = (out2.stdout or "").strip() or "?"
    return Finding(
        name="lean4_wsl",
        ok=True,
        detail=f"Lean 4 (lake) {ver}",
    )


def _gpu_present() -> Finding:
    if shutil.which("nvidia-smi") is None:
        return Finding(
            name="gpu_nvidia",
            ok=False,
            detail="`nvidia-smi` absent",
            repair=(
                "Installer le driver GPU NVIDIA + `nvidia-smi` (Windows : "
                "GeForce Experience / NVIDIA App)."
            ),
        )
    try:
        out = subprocess.run(
            ["nvidia-smi", "--query-gpu=name,memory.total", "--format=csv,noheader"],
            check=False, capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=10,
        )
    except subprocess.TimeoutExpired:
        return Finding(
            name="gpu_nvidia",
            ok=False, detail="`nvidia-smi` timeout",
            repair="Vérifier le driver NVIDIA.",
        )
    if out.returncode != 0 or not out.stdout.strip():
        return Finding(
            name="gpu_nvidia",
            ok=False,
            detail=f"`nvidia-smi` n'a rien rendu : rc={out.returncode}",
            repair="Vérifier le driver NVIDIA.",
        )
    first = out.stdout.strip().splitlines()[0]
    return Finding(name="gpu_nvidia", ok=True, detail=first)


def _docker_present() -> Finding:
    if shutil.which("docker") is None:
        return Finding(
            name="docker",
            ok=False,
            detail="`docker` absent du PATH",
            repair="Installer Docker Desktop : https://docker.com/products/docker-desktop",
        )
    try:
        out = subprocess.run(
            ["docker", "info"],
            check=False, capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=15,
        )
    except subprocess.TimeoutExpired:
        return Finding(
            name="docker",
            ok=False, detail="`docker info` timeout",
            repair="Démarrer Docker Desktop.",
        )
    if out.returncode != 0:
        return Finding(
            name="docker",
            ok=False,
            detail=f"`docker info` rc={out.returncode} : {out.stderr.strip()[:120]}",
            repair="Démarrer Docker Desktop et patienter le temps que le daemon réponde.",
        )
    return Finding(name="docker", ok=True, detail="docker daemon répond")


def _api_keys_present(names: Iterable[str]) -> list[Finding]:
    out = []
    for n in names:
        present = bool(os.environ.get(n)) or _has_dotenv_key(n)
        out.append(Finding(
            name=f"env_{n}",
            ok=present,
            detail=("présente" if present else "absente"),
            repair=(
                "Définir la variable d'environnement (sans valeur ici). "
                "Voir secrets-hygiene.md et master.env."
            ) if not present else "",
        ))
    if not out:
        out.append(Finding(
            name="env_keys", ok=True,
            detail="Aucune clé requise pour ce profil",
        ))
    return out


def _has_dotenv_key(name: str) -> bool:
    """Vérifie la présence (jamais la valeur) de la clé dans le .env du répertoire courant."""
    env_file = Path.cwd() / ".env"
    if not env_file.exists():
        return False
    try:
        text = env_file.read_text(encoding="utf-8", errors="ignore")
    except OSError:
        return False
    for line in text.splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        key, sep, _ = line.partition("=")
        if sep and key.strip() == name:
            return True
    return False


def run_preflight(profile: str) -> Report:
    if profile not in PROFILES:
        raise ValueError(f"Profil inconnu : {profile!r} (attendu : {', '.join(PROFILES)})")

    report = Report(profile=profile)
    report.findings.append(_python_version_ok())
    report.findings.append(_jupyter_present())
    report.findings.extend(_kernels_present(PROFILE_KERNELS[profile]))

    if profile in ("dotnet", "genai"):
        report.findings.append(_dotnet_sdk_present())
        report.findings.append(_lean_present())

    if profile == "genai":
        report.findings.append(_gpu_present())
        report.findings.append(_docker_present())
        report.findings.extend(_api_keys_present(PROFILE_KEYS[profile]))

    return report


def _render_human(report: Report) -> str:
    lines = [f"Préflight parcours : {report.profile}", "=" * 40]
    for f in report.findings:
        marker = "OK " if f.ok else "KO "
        lines.append(f"  [{marker}] {f.name}: {f.detail}")
        if not f.ok and f.repair:
            lines.append(f"        -> {f.repair}")
    lines.append("")
    lines.append("Résultat : " + ("premier palier prêt" if report.ready else
                                  "au moins un manque ; voir ci-dessus"))
    return "\n".join(lines) + "\n"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Préflight par parcours avant le premier notebook.",
    )
    parser.add_argument(
        "--parcours", required=True, choices=PROFILES,
        help=f"Profil visé : {', '.join(PROFILES)}",
    )
    parser.add_argument(
        "--json", action="store_true",
        help="Sortie JSON (destinée au site #10921 et à la CI).",
    )
    args = parser.parse_args(argv)

    try:
        report = run_preflight(args.parcours)
    except ValueError as exc:
        print(f"Erreur : {exc}", file=sys.stderr)
        return 2

    if args.json:
        print(json.dumps(report.to_dict(), ensure_ascii=False, indent=2))
    else:
        sys.stdout.write(_render_human(report))

    return 0 if report.ready else 1


if __name__ == "__main__":
    raise SystemExit(main())