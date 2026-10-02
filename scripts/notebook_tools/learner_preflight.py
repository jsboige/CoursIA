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

# Services Docker attendus par profil : `docker info` doit repondre ET au
# moins un service declare du profil doit etre joignable (sonde HTTP sur
# `/v1/health` ou equivalent). Cf. arbitrage adjoint 2026-10-02T03:01:43Z
# sur #18208 : un daemon repond mais aucun service joignable = pas pret.
PROFILE_DOCKER: dict[str, bool] = {
    "local": False,
    "dotnet": False,
    "genai": True,
}

# Services a sonder par profil (URL de sante). Le probe est un `curl -sf`
# avec timeout 5s ; le service doit retourner HTTP 2xx/3xx pour etre dit
# joignable. Cf. docker-configurations/services/<svc>/docker-compose.yml pour
# le port reel.
PROFILE_DOCKER_SERVICES: dict[str, tuple[str, ...]] = {
    "local": (),
    "dotnet": (),
    "genai": ("http://127.0.0.1:8196/v1/health", "http://127.0.0.1:8180/health"),
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
    # `stage` indexes into STAGES[profile] : 0 = preflight pas lance, 1..n = palier
    # courant. Le report est pret si tous les findings du palier courant sont OK.
    stage: int = 0

    @property
    def ready(self) -> bool:
        """Pret si TOUS les findings collectes sont OK.

        Pas seulement les findings du palier courant : `run_preflight` ajoute
        les findings dans l'ordre des paliers et s'arrete au premier KO. Cela
        evite qu'un clement absente pour un carnet tardif fasse echouer le
        palier 1 (premier notebook). Cf. commentaire d'arbitrage adjoint
        2026-10-02T03:01:43Z sur #18208.
        """
        return bool(self.findings) and all(f.ok for f in self.findings)

    def stage_label(self) -> str:
        stages = STAGES.get(self.profile, ())
        if 0 < self.stage <= len(stages):
            return stages[self.stage - 1]
        return f"stage {self.stage}"

    def to_dict(self) -> dict:
        return {
            "profile": self.profile,
            "stage": self.stage,
            "stage_label": self.stage_label(),
            "ready": self.ready,
            "findings": [f.to_dict() for f in self.findings],
        }


# Ordre des paliers par profil. Chaque palier regroupe les findings necessaires
# pour ouvrir le carnet suivant du parcours. Le premier palier est toujour le
# nombre (local) : python + jupyter + kernels.
STAGES: dict[str, tuple[str, ...]] = {
    "local":  ("Premier notebook (Python + Jupyter)",),
    "dotnet": ("Premier notebook (Python + Jupyter)",
              "Carnets .NET / Lean (SDK + WSL + lake)"),
    "genai":  ("Premier notebook (Python + Jupyter)",
               "Carnets .NET / Lean (SDK + WSL + lake)",
               "Carnets GenAI (GPU + Docker + cles API)"),
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


def _dotnet_sdk_present(minimum: str = "9.0") -> Finding:
    """Le binaire `dotnet` doit etre dans le PATH ET repondre OK a `--version`
    ET etre >= minimum (defaut 9.0, voir docs/reference/kernels-runtime.md).

    Avant : le code rendait `ok=True` des que `dotnet` etait dans le PATH,
    sans verifier le code retour ni la version. Un SDK casse etait declare
    pret. Cf. arbitrage adjoint 2026-10-02T03:01:43Z sur #18208.
    """
    if shutil.which("dotnet") is None:
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
    if out.returncode != 0:
        return Finding(
            name="dotnet_sdk",
            ok=False,
            detail=f"`dotnet --version` rc={out.returncode} : {(out.stderr or out.stdout or '').strip()[:120]}",
            repair="Réinstaller .NET 9 SDK ; voir docs/reference/kernels-runtime.md §.NET.",
        )
    version_str = (out.stdout or "").strip() or "?"
    # Compare numeric prefix (e.g. "9.0.203") au minimum requis.
    try:
        actual = tuple(int(p) for p in version_str.split(".")[:2])
        needed = tuple(int(p) for p in minimum.split(".")[:2])
        version_ok = actual >= needed
    except ValueError:
        version_ok = False
    if not version_ok:
        return Finding(
            name="dotnet_sdk",
            ok=False,
            detail=f"dotnet {version_str} (requis : >= {minimum})",
            repair=f"Mettre à jour .NET vers >= {minimum} ; voir docs/reference/kernels-runtime.md §.NET.",
        )
    return Finding(
        name="dotnet_sdk",
        ok=True,
        detail=f"dotnet {version_str}",
    )


def _lean_present() -> Finding:
    """Lean 4 sous WSL : on regarde `wsl --status` puis `lake --version` dans WSL.

    Avant : `ok=True` etait rendu des que `wsl --status` retournait (meme avec
    rc != 0). Un lake casse etait declare pret. Cf. arbitrage adjoint
    2026-10-02T03:01:43Z sur #18208 : tester les rc explicitemtement.
    """
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
    if out.returncode != 0:
        return Finding(
            name="lean4_wsl",
            ok=False,
            detail=f"`wsl --status` rc={out.returncode} : {(out.stderr or out.stdout or '').strip()[:120]}",
            repair="Démarrer WSL (`wsl --install` puis reboot) ; voir docs/reference/kernels-runtime.md §Lean.",
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
    if out2.returncode != 0:
        return Finding(
            name="lean4_wsl",
            ok=False,
            detail=f"`lake --version` rc={out2.returncode} : {(out2.stderr or out2.stdout or '').strip()[:120]}",
            repair="Réinstaller Lean via elan : `elan toolchain install stable` ; voir docs/reference/kernels-runtime.md §Lean.",
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


def _docker_present(profile: str = "local") -> Finding:
    """Docker daemon + sonde des services declares par profil.

    Cf. arbitrage adjoint 2026-10-02T03:01:43Z sur #18208 : un daemon repond
    mais aucun service joignable ne declare pret. La sonde HTTP est faite sur
    `PROFILE_DOCKER_SERVICES[profile]` : un seul service joignable suffit.
    """
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
            detail=f"`docker info` rc={out.returncode} : {(out.stderr or out.stdout or '').strip()[:120]}",
            repair="Démarrer Docker Desktop et patienter le temps que le daemon réponde.",
        )

    # Sonde des services declares par profil. Le probe est `curl -sf` ; tout
    # HTTP 2xx/3xx est dit joignable. On ne demarre rien, on constate.
    services = PROFILE_DOCKER_SERVICES.get(profile, ())
    if not services:
        return Finding(name="docker", ok=True, detail="docker daemon répond (aucun service à sonder)")
    for url in services:
        if shutil.which("curl") is None:
            break
        try:
            probe = subprocess.run(
                ["curl", "-sf", "--max-time", "5", url],
                check=False, capture_output=True, timeout=8,
            )
        except subprocess.TimeoutExpired:
            continue
        if probe.returncode == 0:
            return Finding(
                name="docker",
                ok=True,
                detail=f"docker daemon répond + service joignable ({url})",
            )
    # Aucun service joignable : on declare KO avec une repair documentee.
    detail_services = ", ".join(s.rsplit("/", 2)[-2] for s in services)
    return Finding(
        name="docker",
        ok=False,
        detail=f"docker daemon répond, mais aucun service joignable ({detail_services})",
        repair=(
            "Démarrer les services GenAI requis (par ex. `docker compose up -d tts-multiqanai-orchestrator` "
            f"pour les services declares : {detail_services}). Voir docker-configurations/services/."
        ),
    )


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
    """Construit le report par paliers : palier 1 = premier notebook, palier 2
    = carnets du profile (dotnet/lean), palier 3 = genai (gpu/docker/cles).

    La cle de distinction : `Report.stage` indexe le **palier courant**. On
    collecte les findings du palier 1 ; si tout est OK, on passe au palier 2 ;
    etc. Le report final peut avoir 1, 2 ou 3 paliers couverts selon ou le
    preflight s'est arrete. `Report.ready` est True si on a couvert TOUS les
    paliers du profil.

    Cf. arbitrage adjoint 2026-10-02T03:01:43Z sur #18208 : une cle absente
    pour un carnet tardif ne doit pas faire echouer le palier 1.
    """
    if profile not in PROFILES:
        raise ValueError(f"Profil inconnu : {profile!r} (attendu : {', '.join(PROFILES)})")

    report = Report(profile=profile)

    # Palier 1 : premier notebook (commun a tous les profils).
    report.stage = 1
    report.findings.append(_python_version_ok())
    report.findings.append(_jupyter_present())
    report.findings.extend(_kernels_present(PROFILE_KERNELS[profile]))
    if not report.ready:
        return report

    # Palier 2 : carnets du profil (dotnet/lean) -- profils dotnet et genai.
    if profile in ("dotnet", "genai"):
        report.stage = 2
        report.findings.append(_dotnet_sdk_present())
        report.findings.append(_lean_present())
        if not report.ready:
            return report

    # Palier 3 : carnets GenAI (gpu + docker + cles) -- profil genai.
    if profile == "genai":
        report.stage = 3
        report.findings.append(_gpu_present())
        report.findings.append(_docker_present(profile))
        report.findings.extend(_api_keys_present(PROFILE_KEYS[profile]))
        if not report.ready:
            return report

    return report


def _render_human(report: Report) -> str:
    lines = [f"Préflight parcours : {report.profile}", "=" * 40]
    lines.append(f"Palier couvert : {report.stage_label()}")
    for f in report.findings:
        marker = "OK " if f.ok else "KO "
        lines.append(f"  [{marker}] {f.name}: {f.detail}")
        if not f.ok and f.repair:
            lines.append(f"        -> {f.repair}")
    lines.append("")
    n_stages = len(STAGES.get(report.profile, ()))
    if report.ready and report.stage >= n_stages:
        verdict = f"parcours complet pret (palier {report.stage}/{n_stages})"
    elif report.ready:
        verdict = f"palier {report.stage}/{n_stages} pret (carniers plus tardifs non verifies)"
    else:
        verdict = f"manque au palier {report.stage}/{n_stages} ; voir ci-dessus"
    lines.append("Résultat : " + verdict)
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