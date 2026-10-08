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
- RAM VM reelle : lue via `measure_po2024_topology.measure()` (WMI / procfs / sysctl).
- Composition declaree : lue depuis `docker-configurations/runners/<host>_budget.json`,
  snapshot des effectifs x caps par famille. Le JSON est la source de verite
  auditable, et il evolue avec le deploiement.
- Plafond dur declare : MemoryMax de la slice `coursia-ci.slice`, parse depuis
  `scripts/ci/docker/linux-runner/persist/coursia-ci.slice` (champ `MemoryMax=`).
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

# Marge de securite en GiB : arrondis d'unite (1 GiB = 1024 MiB mais
# declare parfois comme 1000 MB) + memoire reservee a l'hote (Windows +
# WSL overhead, ~200-400 MiB mesures).
DEFAULT_MARGE_GIB = 0.5

# Memoire pour les services NON-CI sur l'hote Windows. La slice plafonne
# a 16 Go, ce qui laisse >100 Go a l'hote (cf. commentaire en tete de
# coursia-ci.slice). On accepte ce partage : l'organe ne rougit que sur
# la composition CI vs la borne la plus contraignante.
HOST_RESERVED_GIB = 0.5


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
        details=details,
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument(
        "--budget",
        type=Path,
        default=DEFAULT_BUDGET,
        help=f"Snapshot JSON de la composition (defaut: {DEFAULT_BUDGET.relative_to(REPO_ROOT)})",
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
        "--json",
        action="store_true",
        help="Sortie JSON sur stdout (sinon texte)",
    )
    args = parser.parse_args(argv)

    if not args.budget.is_file():
        print(f"Budget snapshot introuvable: {args.budget}", file=sys.stderr)
        return 2
    budget = BudgetSnapshot.from_json(args.budget)

    # RAM VM reelle : on importe en local pour eviter une dependance dure.
    sys.path.insert(0, str(REPO_ROOT / "scripts" / "ci"))
    from measure_po2024_topology import measure  # type: ignore

    try:
        topo = measure()
    except Exception as exc:  # pragma: no cover
        print(f"Topologie OS illisible: {exc}", file=sys.stderr)
        return 2
    vm_total_gib = topo.ram_total_gib

    slice_max = parse_memory_max_gib(args.slice)

    result = assert_memory_budget(budget, vm_total_gib, slice_max, args.marge)

    if args.json:
        print(json.dumps(asdict(result), indent=2, ensure_ascii=False))
    else:
        print(f"[{result.verdict}] {result.machine} : "
              f"composition {result.composition_total_gib:.1f} GiB vs "
              f"borne {result.borne_gib:.1f} GiB (marge {result.marge_gib} GiB)")
        for line in result.details:
            print(line)

    return 1 if result.verdict == "INCOHERENT" else 0


if __name__ == "__main__":
    sys.exit(main())
