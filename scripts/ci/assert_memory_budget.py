"""Organe de garde -- composition memoire vs RAM de la VM (po-2024 #19805).

Issue #19805 : `fix(runners): budget memoire po-2024 incoherent avec la VM --
42 Go declares pour 24 032 Mo disponibles`. Le budget de la CI (somme des
caps par conteneur x effectifs) etait superieur a la RAM de la VM WSL, et
rien dans l'instrumentation existante ne le detectait. `measure_po2024_topology`
mesure la topologie OS mais ne confronte pas la composition au budget
declare, et le garde `assert_memory_budget` precedent ne connaissait que
le budget declare -- il ne pouvait pas rougir sur une composition
incoherente avec la machine.

Cet organe comble ce trou :
- RAM VM : **declaree** pour la machine-cible (`PO2024_VM_RAM_GIB`), jamais
  mesuree sur l'hote qui execute l'organe -- cf. le bloc dedie plus bas.
- Composition : **derivee des unites DEPLOYEES** (`persist/<machine>/<unite>.d/`
  puis `persist/<unite>`) : effectif = argument entier de l'`ExecStart` du
  wrapper de jambe, cap = `Environment=` de la meme unite. L'organe mesure le
  deploiement, pas un instantane ecrit a la main ni les valeurs documentees.
- Plafond dur declare : MemoryMax de la slice `coursia-ci.slice`, surcharge
  `persist/<machine>/coursia-ci.slice` d'abord, generique en repli.
- Marge : 0,5 GiB absorbe les arrondis d'unite (1024 vs 1000) et la memoire
  reservee au systeme hote (Windows hote / WSL overhead).

Verdict :
- exit 0 si `composition + marge <= min(MemoryMax, RAM VM)`.
- exit 1 si la composition depasse la borne la plus contraignante
  (plafond slice declare ou RAM VM reelle). Sortie JSON sur stdout
  + un resume 1 ligne sur stderr.

Le script n'invoque pas docker, ne touche pas a la machine cible, et peut
tourner depuis n'importe quelle machine du cluster (cross-platform via
`measure_po2024_topology`).
"""
from __future__ import annotations

import argparse
import json
import os
import re
import sys
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
DEFAULT_BUDGET = REPO_ROOT / "docker-configurations" / "runners" / "po2024_budget.json"
DEFAULT_SLICE = REPO_ROOT / "scripts" / "ci" / "docker" / "linux-runner" / "persist" / "coursia-ci.slice"
DEFAULT_SUPERVISE = REPO_ROOT / "scripts" / "ci" / "docker" / "linux-runner" / "supervise.sh"
PERSIST_DIR = REPO_ROOT / "scripts" / "ci" / "docker" / "linux-runner" / "persist"

# Les trois jambes du pool CI, telles que le deploiement les installe :
# (nom de famille, unite systemd, script du wrapper, variable de cap memoire,
#  cap par defaut en MiB si l'unite ne le declare pas).
#
# L'effectif N n'est PAS dans une constante : il est lu dans l'argument entier
# de l'`ExecStart=` de l'unite. C'est le point de la revue coordinateur du
# 2026-10-08 (defaut 1) : le meme nombre ecrit a la main dans un snapshot ou
# dans un en-tete de documentation derive silencieusement du deploiement.
RUNNER_LEGS: tuple[tuple[str, str, str, str, int], ...] = (
    ("start", "coursia-runner.service", "coursia-runner-start.sh",
     "COURSIA_RUNNER_MEMORY", 1536),
    ("waiters", "coursia-waiters.service", "coursia-waiters-start.sh",
     "COURSIA_RUNNER_WAITER_MEMORY", 512),
    ("lean", "coursia-lean.service", "coursia-lean-start.sh",
     "COURSIA_LEAN_RUNNER_MEMORY", 6 * 1024),
)

# Marge de securite en GiB : arrondis d'unite (1 GiB = 1024 MiB mais
# declare parfois comme 1000 MB) + memoire reservee a l'hote (Windows +
# WSL overhead, ~200-400 MiB mesures).
DEFAULT_MARGE_GIB = 0.5

# Memoire pour les services NON-CI sur l'hote Windows. La slice plafonne
# a 16 Go, ce qui laisse >100 Go a l'hote (cf. commentaire en tete de
# coursia-ci.slice). On accepte ce partage : l'organe ne rougit que sur
# la composition CI vs la borne la plus contraignante.
HOST_RESERVED_GIB = 0.5

# RAM VM de la machine-CIBLE, declaree comme constante (issue #19805 revue
# coordinateur 2026-10-08, defaut 3).
#
# Pourquoi constante, pas mesuree : l'organe peut tourner depuis N'IMPORTE
# QUELLE machine du cluster (ai-01 191.8 GiB, po-2027 63.6 GiB, po-2024 ~24
# GiB) et c'est la machine-CIBLE qui plafonne, pas celle qui execute. Mesurer
# la RAM de l'hote de l'organe rend un verdict incoherent : un organe sur
# ai-01 dirait "VM po-2024 = 191.8 GiB, composition 27 GiB, OK" alors que
# la VM reelle est 24 GiB -- c'est exactement le defaut fondateur que
# `assert_memory_budget` est cense fermer.
#
# Source de verite : PR #19802 (allocation VM 24 GiB sur po-2024). Si une
# autre machine-cible est ajoutee, etendre ce mapping.
PO2024_VM_RAM_GIB = 24.0
_MACHINE_VM_RAM_GIB: dict[str, float] = {
    "po-2024": PO2024_VM_RAM_GIB,
}


def lookup_vm_ram_gib(machine: str) -> float | None:
    """RAM VM declaree pour la machine-cible, ou None si inconnue.

    L'organe refuse de mesurer l'hote sur lequel il tourne (cf. PO2024_VM_RAM_GIB).
    La RAM est une propriete de la machine VERIFIEE, pas de la machine
    EXECUTANT l'organe.
    """
    return _MACHINE_VM_RAM_GIB.get(machine)


def lookup_slice(machine: str) -> Path:
    """Cherche la surcharge de slice pour la machine, fallback sur la generique.

    #19802 a introduit le motif `persist/<machine>/coursia-ci.slice` pour
    permettre un plafond memoire DIFFERENT par machine-cible. La generique
    `persist/coursia-ci.slice` reste le fallback historique.
    """
    machine_slice = (
        REPO_ROOT
        / "scripts"
        / "ci"
        / "docker"
        / "linux-runner"
        / "persist"
        / machine
        / "coursia-ci.slice"
    )
    if machine_slice.is_file():
        return machine_slice
    return DEFAULT_SLICE


def _deployed_unit_text(machine: str, unit: str, persist_dir: Path) -> tuple[str, list[Path]]:
    """Texte de l'unite telle que DEPLOYEE pour `machine`, + les fichiers lus.

    Ordre systemd : le drop-in de la machine est lu APRES l'unite et peut la
    surcharger ; on retourne donc les deux, le drop-in en dernier, et
    l'appelant resout « derniere definition gagne ». Un drop-in qui ne
    redefinit pas un champ ne l'efface pas -- d'ou la concatenation plutot
    qu'un choix exclusif.
    """
    parts: list[str] = []
    read: list[Path] = []
    base = persist_dir / unit
    if base.is_file():
        parts.append(base.read_text(encoding="utf-8"))
        read.append(base)
    dropin_dir = persist_dir / machine / f"{unit}.d"
    if dropin_dir.is_dir():
        for dropin in sorted(dropin_dir.glob("*.conf")):
            parts.append(dropin.read_text(encoding="utf-8"))
            read.append(dropin)
    return "\n".join(parts), read


def _execstart_instances(text: str, script: str) -> int | None:
    """Effectif N lu dans l'`ExecStart` du wrapper `script`.

    Formes rencontrees dans le deploiement : `... <script> 12` et
    `... <script> start 4`. Le N est le DERNIER jeton entier de la ligne --
    l'unite `start` porte un sous-commande textuelle avant lui. Derniere
    definition gagne (un drop-in peut redefinir l'ExecStart).
    """
    found: int | None = None
    for m in re.finditer(rf"^ExecStart=.*{re.escape(script)}\s+(.+)$", text, re.MULTILINE):
        tail = m.group(1).strip().split("#", 1)[0].strip()
        for tok in reversed(tail.split()):
            if tok.isdigit():
                found = int(tok)
                break
    return found


def _cap_gib_from_env(text: str, var: str, default_mib: int) -> float:
    """Cap memoire unitaire (GiB) lu dans `Environment=<var>=<valeur>`.

    Derniere definition gagne. Sans declaration, le defaut de l'unite est pris
    (le cap par defaut est documente en tete du wrapper, il ne derive pas au
    meme rythme que l'effectif).
    """
    value: str | None = None
    for m in re.finditer(rf'^Environment="?{re.escape(var)}=([^"\s]+)"?', text, re.MULTILINE):
        value = m.group(1)
    if value is None:
        return default_mib / 1024
    m = re.match(r"^(\d+)([gGmM])?$", value.strip())
    if not m:
        return default_mib / 1024
    n = int(m.group(1))
    return float(n) if (m.group(2) or "").lower() == "g" else n / 1024


@dataclass
class CompositionFamily:
    instances: int
    cap_gib: float
    total_gib: float


@dataclass
class BudgetSnapshot:
    machine: str
    composition: dict[str, CompositionFamily]
    composition_total_gib: float
    notes: str = ""

    @classmethod
    def from_json(cls, path: Path) -> BudgetSnapshot:
        data = json.loads(path.read_text(encoding="utf-8"))
        comp: dict[str, CompositionFamily] = {}
        for name, fam in data.get("composition", {}).items():
            comp[name] = CompositionFamily(
                instances=int(fam["instances"]),
                cap_gib=float(fam["cap_gib"]),
                total_gib=float(fam["total_gib"]),
            )
        return cls(
            machine=data["machine"],
            composition=comp,
            composition_total_gib=float(data["composition_total_gib"]),
            notes=data.get("notes", ""),
        )

    @classmethod
    def from_supervise_defaults(cls, supervise_path: Path, machine: str) -> BudgetSnapshot:
        """Derive la composition depuis les defauts `supervise.sh`.

        #19805 revue coordinateur 2026-10-08 (defaut 1) : le snapshot JSON
        maintenu a la main derive a chaque push supervise.sh, et l'organe
        mesurait alors son propre instantane, pas le deploiement. Lecture
        directe des defauts (MEMORY/CPUS par famille, N par defaut documente
        en tete du fichier) -- la composition suit les caps reels.

        Le nombre de slots par defaut est lu dans l'en-tete USAGE du fichier
        (le superviseur documente `defaut 2`, `defaut 24`, `defaut 2` pour
        start/waiters/lean) ; un override par machine vit dans le wrapper
        `persist/<machine>/coursia-runner.service.d/10-sizing.conf` et
        n'est PAS releve ici (l'organe mesure le DEFAUT, l'override est
        verifie par l'operateur ou un autre organe).
        """
        text = supervise_path.read_text(encoding="utf-8")

        def _cap_gib(var: str, default_mb: int) -> float:
            m = re.search(rf'^{var}="?(\d+)([gGmM])"?', text, re.MULTILINE)
            if not m:
                return default_mb / 1024
            val = int(m.group(1))
            unit = m.group(2).lower()
            if unit == "g":
                return float(val)
            return val / 1024

        start_cap = _cap_gib("COURSIA_RUNNER_MEMORY", 1536)
        waiters_cap = _cap_gib("COURSIA_RUNNER_WAITER_MEMORY", 512)
        lean_cap = _cap_gib("COURSIA_LEAN_RUNNER_MEMORY", 6 * 1024)

        # N par defaut documente en tete du fichier :
        #   "N slots (defaut 2)" (start)
        #   "N slots d'attente PR-gate (label coursia-waiter, defaut 24)"
        #   "N slots Lean specialises (..., defaut 2)"
        n_start = 2
        n_waiters = 24
        n_lean = 2

        comp = {
            "start": CompositionFamily(
                instances=n_start,
                cap_gib=start_cap,
                total_gib=round(n_start * start_cap, 3),
            ),
            "waiters": CompositionFamily(
                instances=n_waiters,
                cap_gib=waiters_cap,
                total_gib=round(n_waiters * waiters_cap, 3),
            ),
            "lean": CompositionFamily(
                instances=n_lean,
                cap_gib=lean_cap,
                total_gib=round(n_lean * lean_cap, 3),
            ),
        }
        total = round(sum(f.total_gib for f in comp.values()), 3)
        # Le chemin peut etre hors-repo (tests, run ad-hoc) : on note l'absolu
        # en repli, pas un crash sur relative_to.
        try:
            rel = supervise_path.relative_to(REPO_ROOT)
            notes = f"derive de {rel} (defauts)"
        except ValueError:
            notes = f"derive de {supervise_path} (defauts, hors-repo)"
        return cls(
            machine=machine,
            composition=comp,
            composition_total_gib=total,
            notes=notes,
        )

    @classmethod
    def from_deployed_units(
        cls, machine: str, persist_dir: Path | None = None
    ) -> BudgetSnapshot:
        """Composition derivee des unites DEPLOYEES pour `machine`.

        #19805 revue coordinateur 2026-10-08 (defaut 1) : la composition doit
        suivre ce que la machine EXECUTE. Ni le snapshot JSON ni les valeurs
        documentees en en-tete de `supervise.sh` ne sont le deploiement -- le
        premier est recopie a la main, les secondes ont derive (24 slots
        d'attente documentes quand l'unite en lance 12, et 6 sur po-2024).

        Resolution par jambe : le drop-in `persist/<machine>/<unite>.d/*.conf`
        s'il redefinit l'`ExecStart`, sinon l'unite de base `persist/<unite>`.
        L'effectif vient de l'`ExecStart` (dernier jeton entier), le cap de
        l'`Environment=` de la meme unite, avec le defaut de la jambe en repli.
        """
        root = persist_dir if persist_dir is not None else PERSIST_DIR
        comp: dict[str, CompositionFamily] = {}
        sources: list[str] = []
        missing: list[str] = []

        for name, unit, script, var, default_mib in RUNNER_LEGS:
            text, files = _deployed_unit_text(machine, unit, root)
            if not files:
                missing.append(str(root / unit))
                continue
            instances = _execstart_instances(text, script)
            if instances is None:
                missing.append(f"{root / unit} (ExecStart {script} illisible)")
                continue
            cap = _cap_gib_from_env(text, var, default_mib)
            sources.append(f"{name}={instances}x{cap:g}G")
            comp[name] = CompositionFamily(
                instances=instances,
                cap_gib=cap,
                total_gib=round(instances * cap, 3),
            )

        if missing:
            raise FileNotFoundError(
                "unite(s) de jambe introuvable(s) ou illisible(s) : "
                + ", ".join(missing)
            )

        total = round(sum(f.total_gib for f in comp.values()), 3)
        return cls(
            machine=machine,
            composition=comp,
            composition_total_gib=total,
            notes=(
                f"derive des unites deployees ({machine}) : "
                + ", ".join(sources)
            ),
        )


def parse_memory_max_gib(slice_path: Path) -> float | None:
    """Lit `MemoryMax=` (ou `MemoryHigh=`) depuis une unit slice systemd.

    Le format attendu est `MemoryMax=16G`, `MemoryMax=2048M`, `MemoryMax=infinity`.
    Renvoie None si absent ou si valeur = infinity.
    """
    if not slice_path.is_file():
        return None
    text = slice_path.read_text(encoding="utf-8")
    # MemoryMax prime (plafond dur). Si absent, fallback MemoryHigh.
    for key in ("MemoryMax", "MemoryHigh"):
        m = re.search(rf"^{key}=(.+)$", text, re.MULTILINE)
        if m:
            raw = m.group(1).strip()
            if raw.lower() in ("infinity", "max"):
                continue
            unit = raw[-1]
            try:
                val = float(raw[:-1])
            except ValueError:
                continue
            if unit == "G":
                return val
            if unit == "M":
                return round(val / 1024, 3)
            if unit == "K":
                return round(val / (1024 * 1024), 6)
            if unit == "T":
                return val * 1024
    return None


@dataclass
class AssertResult:
    machine: str
    vm_total_gib: float | None
    composition_total_gib: float
    slice_memory_max_gib: float | None
    borne_gib: float
    marge_gib: float
    verdict: str  # "OK" | "INCOHERENT"
    # Provenance de la composition (unites deployees / supervise.sh / JSON).
    # Portee au verdict pour que le lecteur sache CE QUI a ete mesure : un
    # organe qui confronte une composition doit dire d'ou elle vient, sinon
    # « 15 GiB » ne se distingue pas de « 27 GiB » comme resultat.
    source: str = ""
    details: list[str] = field(default_factory=list)


def assert_memory_budget(
    budget: BudgetSnapshot,
    vm_total_gib: float | None,
    slice_memory_max_gib: float | None,
    marge_gib: float = DEFAULT_MARGE_GIB,
) -> AssertResult:
    # Borne la plus contraignante = min(slice_max, RAM VM).
    bornes: list[float] = []
    if slice_memory_max_gib is not None:
        bornes.append(slice_memory_max_gib)
    if vm_total_gib is not None:
        # On reserve HOST_RESERVED_GIB a l'hote non-CI (mesure po-2024 :
        # la VM est partagee avec d'autres services via Docker Desktop).
        bornes.append(max(0.0, vm_total_gib - HOST_RESERVED_GIB))
    borne_gib = min(bornes) if bornes else float("inf")

    seuil = borne_gib - marge_gib
    incoherence = budget.composition_total_gib > seuil

    details: list[str] = []
    for name, fam in budget.composition.items():
        details.append(
            f"  {name:>10s} : {fam.instances:>3d} x {fam.cap_gib:>5.1f} GiB "
            f"= {fam.total_gib:>6.1f} GiB"
        )
    details.append(f"  {'TOTAL':>10s} : {'':>3s}   {'':>6s}   {budget.composition_total_gib:>6.1f} GiB")
    if vm_total_gib is not None:
        details.append(f"  VM RAM        : {vm_total_gib:>6.1f} GiB  (hote reserve {HOST_RESERVED_GIB} GiB)")
    if slice_memory_max_gib is not None:
        details.append(f"  Slice MemoryMax: {slice_memory_max_gib:>6.1f} GiB")
    details.append(f"  Borne         : {borne_gib:>6.1f} GiB  (marge {marge_gib} GiB, seuil {seuil:.1f} GiB)")

    return AssertResult(
        machine=budget.machine,
        vm_total_gib=vm_total_gib,
        composition_total_gib=budget.composition_total_gib,
        slice_memory_max_gib=slice_memory_max_gib,
        borne_gib=borne_gib,
        marge_gib=marge_gib,
        verdict="INCOHERENT" if incoherence else "OK",
        source=budget.notes,
        details=details,
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument(
        "--budget",
        type=Path,
        default=DEFAULT_BUDGET,
        help=f"Snapshot JSON de la composition, lu seulement avec --from-json "
             f"(defaut: {DEFAULT_BUDGET.relative_to(REPO_ROOT)})",
    )
    parser.add_argument(
        "--slice",
        type=Path,
        default=DEFAULT_SLICE,
        help=f"Unit slice systemd (defaut: {DEFAULT_SLICE.relative_to(REPO_ROOT)})",
    )
    parser.add_argument(
        "--marge",
        type=float,
        default=DEFAULT_MARGE_GIB,
        help=f"Marge de securite en GiB (defaut: {DEFAULT_MARGE_GIB})",
    )
    parser.add_argument(
        "--from-json",
        action="store_true",
        help="Composition depuis le snapshot JSON (--budget). Comparaison/audit "
             "seulement : le snapshot est recopie a la main et derive.",
    )
    parser.add_argument(
        "--from-supervise",
        action="store_true",
        help="Composition depuis les defauts documentes de supervise.sh. Repli "
             "pour une machine sans unites deployees au depot.",
    )
    parser.add_argument(
        "--machine",
        default="po-2024",
        help="Machine-cible verifiee (defaut: po-2024). Definit la surcharge slice et la RAM VM.",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Sortie JSON sur stdout (sinon texte)",
    )
    args = parser.parse_args(argv)

    # Composition : les unites DEPLOYEES par defaut (#19805 revue coordinateur
    # 2026-10-08, defaut 1). Ni le snapshot JSON (recopie a la main) ni les
    # valeurs documentees de supervise.sh ne sont le deploiement : les deux ont
    # derive. Les deux restent disponibles pour l'audit et le repli, jamais
    # comme voie par defaut -- un organe qui mesure sa propre constante ne
    # mesure rien.
    if args.from_json:
        if not args.budget.is_file():
            print(f"Budget snapshot introuvable: {args.budget}", file=sys.stderr)
            return 2
        budget = BudgetSnapshot.from_json(args.budget)
    elif args.from_supervise:
        if not DEFAULT_SUPERVISE.is_file():
            print(f"supervise.sh introuvable: {DEFAULT_SUPERVISE}", file=sys.stderr)
            return 2
        budget = BudgetSnapshot.from_supervise_defaults(DEFAULT_SUPERVISE, args.machine)
    else:
        try:
            budget = BudgetSnapshot.from_deployed_units(args.machine)
        except FileNotFoundError as exc:
            print(f"{exc}", file=sys.stderr)
            return 2

    # RAM VM de la machine-CIBLE (#19805 revue coordinateur 2026-10-08,
    # defaut 3) : declaree comme constante, PAS mesuree sur l'hote de l'organe.
    # Mesurer l'hote rend un verdict incoherent (cf. PO2024_VM_RAM_GIB).
    vm_total_gib = lookup_vm_ram_gib(budget.machine)
    if vm_total_gib is None:
        # Machine inconnue : l'organe ne peut pas verifier une borne VM. Il
        # fonctionne en mode "slice seule", la borne est la MemoryMax de la
        # surcharge de slice. C'est un sous-ensemble du verdict -- le marquer.
        print(
            f"[WARN] RAM VM non declaree pour machine='{budget.machine}' -- "
            f"verdict sur slice seule. Etendre _MACHINE_VM_RAM_GIB.",
            file=sys.stderr,
        )

    # Surcharge slice machine d'abord, generique en repli (#19805 revue
    # coordinateur 2026-10-08, defaut 2).
    slice_path = lookup_slice(budget.machine)
    slice_max = parse_memory_max_gib(slice_path)

    result = assert_memory_budget(budget, vm_total_gib, slice_max, args.marge)

    if args.json:
        print(json.dumps(asdict(result), indent=2, ensure_ascii=False))
    else:
        print(f"[{result.verdict}] {result.machine} : "
              f"composition {result.composition_total_gib:.1f} GiB vs "
              f"borne {result.borne_gib:.1f} GiB (marge {result.marge_gib} GiB)")
        if result.source:
            print(f"  Source        : {result.source}")
        for line in result.details:
            print(line)

    return 1 if result.verdict == "INCOHERENT" else 0


if __name__ == "__main__":
    sys.exit(main())
