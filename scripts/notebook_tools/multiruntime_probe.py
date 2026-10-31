#!/usr/bin/env python3
"""Mesurer une cellule de carnet .NET sous plusieurs runtimes, et comparer.

Probleme resolu
---------------
Les organes d'execution existants du depot (`dotnet_executor.py`,
`exec_single_cell.py`) demarrent un kernel .NET Interactive qui herite de
l'environnement du process appelant, mais **aucun ne permet de choisir le
runtime** : `dotnet_executor.py` ne fait que *reparer* un `DOTNET_ROOT` sans
SDK (pour que `dotnet restore` fonctionne), et `exec_single_cell.py` ne recable
jamais l'environnement. Mesurer un carnet sous un runtime isole releve donc de
la plomberie manuelle : copie de travail, `DOTNET_ROOT` dedie, roll-forward,
relecture a la main de la metrique dans la sortie.

Cet organe rend la mesure reproductible :

- **un seul build de kernel**, execute tel quel sous N runtimes : seul le
  `DOTNET_ROOT` change (le roll-forward est pose une fois, identiquement pour
  tous les runtimes) ;
- **le runtime effectif est PROUVE dans la sortie** : apres la cellule
  mesuree, une cellule de provenance est executee *dans le meme kernel* et
  imprime `RuntimeInformation.FrameworkDescription`, `Environment.Version` et
  le repertoire de runtime charge ;
- **la metrique est extraite automatiquement** de la sortie (series `runs = [...]`,
  medianes, identites de thread), puis **agregée** sur plusieurs executions ;
- **un verdict est declare** : `DELTA ETABLI` si les intervalles [min,max] des
  deux runtimes sont disjoints, `INCONCLUSIF` sinon. Un verdict `INCONCLUSIF` est
  un resultat declare, pas un echec de l'outil.

Le carnet du depot n'est **jamais** modifie : l'organe lit la cellule source,
execute dans un kernel jetable, et garde les sorties en memoire.

Usage
-----
    python multiruntime_probe.py --notebook <nb.ipynb> --index 8 \\
        --runtime net10="C:/Program Files/dotnet" \\
        --runtime net11="C:/Users/<user>/.dotnet-r11" \\
        --repeats 5 --kernel .net-csharp --timeout 900 --json <out.json>

Le format de sortie textuelle est un tableau Markdown (une ligne par
configuration mesuree), le format JSON est la donnee brute (par runtime, par
configuration, par execution).
"""
from __future__ import annotations

import argparse
import json
import os
import queue
import re
import statistics
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from notebook_helpers import bound_native_thread_pools  # noqa: E402

# Roll-forward pose une fois pour tous les runtimes : le kernel est le meme
# build dans tous les cas, seul le runtime disponible change. La version
# prerelease est explicitement autorisee (le runtime .NET 11 de mesure est une
# RC) ; sans elle, `LatestMajor` ignorerait la RC et le demarrage echouerait.
ROLL_FORWARD = "LatestMajor"
ROLL_FORWARD_TO_PRERELEASE = "1"

# La cellule de provenance : prouve le runtime DANS la sortie, dans le meme
# kernel que la cellule mesuree (le runtime est charge au demarrage du kernel,
# l'ordre des cellules n'y change rien).
PROVENANCE_CSHARP = """Console.WriteLine("RUNTIME_DESCRIPTION " + System.Runtime.InteropServices.RuntimeInformation.FrameworkDescription);
Console.WriteLine("RUNTIME_VERSION " + Environment.Version);
Console.WriteLine("RUNTIME_DIR " + System.Runtime.InteropServices.RuntimeEnvironment.GetRuntimeDirectory());
"""

LABEL_RE = re.compile(r"^\[(?P<label>[^\]]+)\]")
RUNS_RE = re.compile(r"runs\s*=\s*\[(?P<vals>[^\]]*)\]\s*ms")
MEDIAN_RE = re.compile(r"mediane\s*=\s*(?P<val>[0-9]+(?:[.,][0-9]+)?)\s*ms")
MINMAX_RE = re.compile(r"min/max\s*=\s*(?P<lo>[0-9]+(?:[.,][0-9]+)?)\s*/\s*(?P<hi>[0-9]+(?:[.,][0-9]+)?)\s*ms")
THREADS_RE = re.compile(r"^\s*\[(?P<pairs>[0-9]+/[0-9]+(?:,\s*[0-9]+/[0-9]+)*)\]\s*$")
# Nombre en culture locale (FR ou EN) : "171,09" et "1.83" sont tous deux
# acceptes, mais la virgule seule ("171, 206") reste un separateur de liste.
NUMBER_RE = re.compile(r"\d+(?:[.,]\d+)?")
MECHANISM_RE = re.compile(r"->\s*(?P<mech>identiques|differents)")


def to_float(token: str) -> float:
    """Nombre decimalFR ou EN -> float (le kernel .NET rend la culture locale)."""
    return float(token.strip().replace(",", "."))


def outputs_to_text(outputs: list[dict]) -> str:
    """Sorties d'une cellule -> texte brut (streams + execute_result)."""
    chunks: list[str] = []
    for out in outputs:
        if out.get("output_type") == "stream":
            chunks.append("".join(out.get("text", [])))
        elif out.get("output_type") == "execute_result":
            data = out.get("data", {})
            plain = data.get("text/plain", "")
            chunks.append("".join(plain) if isinstance(plain, list) else str(plain))
    return "\n".join(chunks)


def parse_block(text: str) -> dict[str, dict]:
    """Extrait, par configuration etiquettee, les mesures d'une sortie de cellule.

    Format attendu (celui de l'instrument §4 des carnets Aspire) : une ligne
    `[X] <libelle>` ouvre un bloc, suivi de `runs = [...] ms`, `mediane = X ms`,
    `min/max = a / b ms`, puis d'une ligne d'identites de thread.
    """
    blocks: dict[str, dict] = {}
    current: str | None = None
    for line in text.splitlines():
        label = LABEL_RE.match(line)
        if label and "=" not in line.split("]")[0]:
            current = label.group("label").strip()
            blocks.setdefault(current, {"runs": [], "threads": [], "mechanism": None})
        if current is None:
            continue
        block = blocks[current]
        runs = RUNS_RE.search(line)
        if runs:
            # Le kernel rend les nombres dans la culture locale : le separateur
            # decimal peut etre la VIRGULE, qui est aussi le separateur de la
            # liste ("171,09, 206,23"). Un split sur "," casserait chaque
            # nombre en deux ; l'extraction par motif prend le nombre complet
            # ("171,09") et laisse le separateur ", " de cote.
            raw = NUMBER_RE.findall(runs.group("vals"))
            block["runs"].extend(to_float(tok) for tok in raw)
        median = MEDIAN_RE.search(line)
        if median:
            block["median"] = to_float(median.group("val"))
        minmax = MINMAX_RE.search(line)
        if minmax:
            block["min"] = to_float(minmax.group("lo"))
            block["max"] = to_float(minmax.group("hi"))
        threads = THREADS_RE.match(line)
        if threads:
            block["threads"] = [tok.strip() for tok in threads.group("pairs").split(",")]
        mechanism = MECHANISM_RE.search(line)
        if mechanism:
            block["mechanism"] = mechanism.group("mech")
    return blocks


def parse_provenance(text: str) -> dict[str, str]:
    """Sortie de la cellule de provenance -> {'description':..., 'version':..., 'dir':...}."""
    proof: dict[str, str] = {}
    for line in text.splitlines():
        if line.startswith("RUNTIME_DESCRIPTION "):
            proof["description"] = line.split(" ", 1)[1].strip()
        elif line.startswith("RUNTIME_VERSION "):
            proof["version"] = line.split(" ", 1)[1].strip()
        elif line.startswith("RUNTIME_DIR "):
            proof["dir"] = line.split(" ", 1)[1].strip()
    return proof


def read_cell_source(notebook: str, index: int | None, cell_id: str | None) -> str:
    """Source de la cellule cible. Le carnet n'est ouvert qu'en lecture."""
    with open(notebook, encoding="utf-8") as handle:
        nb = json.load(handle)
    for position, cell in enumerate(nb["cells"]):
        if cell.get("cell_type") != "code":
            continue
        if cell_id is not None and cell.get("id") == cell_id:
            source = cell["source"]
            return "".join(source) if isinstance(source, list) else source
        if index is not None and position == index:
            source = cell["source"]
            return "".join(source) if isinstance(source, list) else source
    raise SystemExit(f"cellule introuvable (index={index}, cell-id={cell_id})")


def run_once(kernel: str, source: str, provenance_source: str,
             env: dict[str, str], timeout: int) -> tuple[str, str]:
    """Execute la cellule mesuree puis la cellule de provenance dans UN kernel."""
    # Imports différés : `exec_single_cell` et `jupyter_client` tirent la pile
    # kernel, inutile à la logique pure (parsing, verdict) que les tests
    # pinnent. L'organe réutilise `collect_outputs` — il ne le réimplémente pas.
    from exec_single_cell import collect_outputs  # noqa: PLC0415
    from jupyter_client.manager import start_new_kernel  # noqa: PLC0415

    bound_native_thread_pools()
    manager, client = start_new_kernel(kernel_name=kernel, env=env)
    try:
        message_id = client.execute(source)
        outputs, _ = collect_outputs(client, message_id, timeout)
        errors = [o for o in outputs if o.get("output_type") == "error"]
        if errors:
            raise RuntimeError(f"erreur dans la cellule mesuree : {errors[0].get('ename')}")
        measured = outputs_to_text(outputs)

        message_id = client.execute(provenance_source)
        outputs, _ = collect_outputs(client, message_id, timeout)
        errors = [o for o in outputs if o.get("output_type") == "error"]
        if errors:
            raise RuntimeError(f"erreur dans la cellule de provenance : {errors[0].get('ename')}")
        proof = outputs_to_text(outputs)
        return measured, proof
    finally:
        client.stop_channels()
        manager.shutdown_kernel(now=True)


def verdict_for(label: str, first: dict, second: dict,
                resolution_floor_ms: float = 0.5) -> tuple[str, float | None]:
    """Verdict de comparaison entre deux runtimes pour une configuration.

    `DELTA ETABLI` exige des intervalles [min,max] DISJOINTS : c'est le critere
    conservatoire, il ne declare rien que les donnees ne portent pas. Sinon le
    verdict est `INCONCLUSIF` -- declare, et non masque.

    Une grandeur SOUS le plancher de resolution n'est pas comparable : le bruit
    de la mesure (et non le runtime) y decide de l'ecart. Le plancher est
    explicite et configurable (`--resolution-floor-ms`), jamais deduit de la
    donnee -- un seuil deduit des series ne ferait que confirmer l'ecart qu'il
    est charge de contredire.
    """
    if first is None or second is None:
        return "INCONCLUSIF (mesure absente)", None
    median_first, median_second = first.get("median"), second.get("median")
    if median_first is None or median_second is None:
        return "INCONCLUSIF (mediane absente)", None
    delta = (median_second - median_first) / median_first * 100.0 if median_first else None
    if max(median_first, median_second) < resolution_floor_ms:
        return "NON RESOLU (grandeur sous le plancher de resolution)", delta
    low_first, high_first = first.get("min"), first.get("max")
    low_second, high_second = second.get("min"), second.get("max")
    if None in (low_first, high_first, low_second, high_second):
        return "INCONCLUSIF (intervalle absent)", delta
    disjoint = high_first < low_second or high_second < low_first
    if disjoint:
        return "DELTA ETABLI", delta
    return "INCONCLUSIF (intervalles chevauchants)", delta


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--notebook", required=True, help="carnet .ipynb (lu, jamais modifie)")
    parser.add_argument("--index", type=int, help="index absolu de la cellule a mesurer")
    parser.add_argument("--cell-id", help="id de la cellule a mesurer")
    parser.add_argument("--runtime", action="append", required=True, metavar="LABEL=ROOT",
                        help="racine DOTNET_ROOT du runtime, repetable "
                             "(ex. --runtime net10=\"C:/Program Files/dotnet\")")
    parser.add_argument("--repeats", type=int, default=1,
                        help="executions par runtime (la mediane est prise sur l'ensemble)")
    parser.add_argument("--kernel", default=".net-csharp", help="nom du kernel Jupyter")
    parser.add_argument("--timeout", type=int, default=900, help="timeout d'une cellule, en secondes")
    parser.add_argument("--provenance-file",
                        help="fichier .cs de provenance (par defaut : version .NET embarquee)")
    parser.add_argument("--json", help="fichier de sortie JSON (donnee brute)")
    parser.add_argument("--label", help="libelle de la premiere configuration, pour le verdict")
    parser.add_argument("--resolution-floor-ms", type=float, default=0.5,
                        help="plancher de resolution : sous cette valeur, la grandeur "
                             "n'est pas comparable d'un runtime a l'autre (defaut : 0.5)")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    if args.index is None and args.cell_id is None:
        raise SystemExit("fournir --index ou --cell-id")
    if args.repeats < 1:
        raise SystemExit("--repeats doit valoir au moins 1")

    runtimes: list[tuple[str, str]] = []
    for spec in args.runtime:
        if "=" not in spec:
            raise SystemExit(f"--runtime attendu LABEL=ROOT, reçu {spec!r}")
        label, root = spec.split("=", 1)
        runtimes.append((label.strip(), root.strip()))
    if len(runtimes) < 2:
        raise SystemExit("au moins deux runtimes sont necessaires pour comparer")

    source = read_cell_source(args.notebook, args.index, args.cell_id)
    provenance_source = (Path(args.provenance_file).read_text(encoding="utf-8")
                         if args.provenance_file else PROVENANCE_CSHARP)

    collected: dict[str, list[dict]] = {label: [] for label, _ in runtimes}
    proofs: dict[str, dict] = {}
    for label, root in runtimes:
        env = dict(os.environ)
        env["DOTNET_ROOT"] = root
        env["DOTNET_ROLL_FORWARD"] = ROLL_FORWARD
        env["DOTNET_ROLL_FORWARD_TO_PRERELEASE"] = ROLL_FORWARD_TO_PRERELEASE
        for attempt in range(1, args.repeats + 1):
            measured, proof = run_once(args.kernel, source, provenance_source, env, args.timeout)
            blocks = parse_block(measured)
            proofs.setdefault(label, {}).update(parse_provenance(proof))
            collected[label].append({"attempt": attempt, "blocks": blocks})
            print(f"[{label}] execution {attempt}/{args.repeats} : "
                  f"{ {k: v.get('median') for k, v in blocks.items()} }", file=sys.stderr)

    # Agregation : toutes les series d'un runtime sont mises bout a bout, et la
    # mediane est reprise sur l'ensemble -- c'est la repetition qui rend la
    # comparaison citable, pas la repetition du carnet lui-meme.
    aggregated: dict[str, dict[str, dict]] = {}
    for label, _ in runtimes:
        per_config: dict[str, dict] = {}
        for execution in collected[label]:
            for config, block in execution["blocks"].items():
                bucket = per_config.setdefault(config, {"runs": [], "medians": [], "mechanisms": []})
                bucket["runs"].extend(block.get("runs", []))
                if block.get("median") is not None:
                    bucket["medians"].append(block["median"])
                if block.get("mechanism"):
                    bucket["mechanisms"].append(block["mechanism"])
        for config, bucket in per_config.items():
            runs = bucket["runs"]
            bucket["n"] = len(runs)
            bucket["median"] = statistics.median(runs) if runs else None
            bucket["min"] = min(runs) if runs else None
            bucket["max"] = max(runs) if runs else None
            bucket["median_of_medians"] = (statistics.median(bucket["medians"])
                                            if bucket["medians"] else None)
        aggregated[label] = per_config

    first_label, second_label = runtimes[0][0], runtimes[1][0]
    verdicts: dict[str, dict] = {}
    for config in sorted(set(aggregated[first_label]) | set(aggregated[second_label])):
        first = aggregated[first_label].get(config)
        second = aggregated[second_label].get(config)
        verdict, delta = verdict_for(config, first, second, args.resolution_floor_ms)
        verdicts[config] = {"verdict": verdict, "delta_percent": delta}

    payload = {
        "notebook": args.notebook,
        "cell_index": args.index,
        "cell_id": args.cell_id,
        "kernel": args.kernel,
        "repeats": args.repeats,
        "roll_forward": ROLL_FORWARD,
        "roll_forward_to_prerelease": ROLL_FORWARD_TO_PRERELEASE,
        "runtimes": {label: {"root": root} for label, root in runtimes},
        "proofs": proofs,
        "aggregated": aggregated,
        "verdicts": verdicts,
        "executions": collected,
    }
    if args.json:
        Path(args.json).write_text(json.dumps(payload, ensure_ascii=False, indent=2),
                                   encoding="utf-8")

    # Sortie lisible : une ligne par configuration, avec la preuve de runtime.
    print()
    print("| configuration | " + " | ".join(
        f"{label} : mediane [min-max] (n={aggregated[label].get(config, {}).get('n', 0)})"
        for label, _ in runtimes)
        + " | verdict | delta |")
    print("|---" * (len(runtimes) + 3) + "|")
    for config in sorted(set(aggregated[first_label]) | set(aggregated[second_label])):
        cells = []
        for label, _ in runtimes:
            block = aggregated[label].get(config, {})
            median = block.get("median")
            if median is None:
                cells.append("-")
                continue
            cells.append(f"{median:.2f} ms [{block.get('min', 0):.2f} - "
                         f"{block.get('max', 0):.2f}]")
        verdict = verdicts[config]
        delta = verdict["delta_percent"]
        print(f"| {config} | " + " | ".join(cells)
              + f" | {verdict['verdict']}"
              + f" | {'-' if delta is None else f'{delta:+.2f} %'} |")
    print()
    for label, _ in runtimes:
        proof = proofs.get(label, {})
        print(f"runtime {label} : {proof.get('description', '?')} "
              f"({proof.get('version', '?')}) — chargé depuis {proof.get('dir', '?')}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
