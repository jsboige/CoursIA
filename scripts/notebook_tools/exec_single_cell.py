#!/usr/bin/env python3
"""Execute a SINGLE notebook cell on a named Jupyter kernel and write its
execution_count + outputs back, leaving every other cell byte-identical.

Use case (rule C.2/C.3/H.3 compliant): a notebook has heavy or unavailable
dependencies in most cells (jpype/JVM, GPU, network downloads) but you added a
single self-contained cell (e.g. a terminal exercise stub) that must carry real
execution_count + outputs. Re-running the whole notebook would either fail on
the heavy cells or churn the already-valid outputs of the unchanged cells. This
tool runs only the target cell on a fresh kernel and persists just that cell.

It reads/writes with the raw ``json`` module (NOT nbformat) so the on-disk key
order of every other cell is preserved exactly: only the target cell's
``execution_count``, ``outputs`` and stale per-cell papermill/execution blocks
are mutated. This avoids the whole-file key-order churn nbformat.write()
introduces on notebooks that were saved by VS Code / dotnet-interactive
(non nbformat-canonical key order), and the mass metadata deletion a global
``strip_stale_papermill_metadata`` call caused (mesure du 14/11 : 70 cellules
strippées pour une seule exécutée, +50/-716 au lieu de +50/-7).

For .NET (.net-csharp) kernels, the dotnet-interactive HTTP-port bootstrap
``<div>`` that a fresh kernel injects on the first executed cell (a
session-specific port, e.g. 44528) is filtered out: it is session noise, not a
real cell output.

Usage:
  python exec_single_cell.py <notebook.ipynb> --cell-id <id>  [--kernel python3] [--timeout 120]
  python exec_single_cell.py <notebook.ipynb> --index   <n>   [--kernel python3] [--timeout 120]

Exit code: 0 if the cell executed without an error output, 1 otherwise.
"""
import argparse
import json
import queue
import sys
import time

from jupyter_client.manager import start_new_kernel

from _papermill_meta import strip_stale_papermill_metadata
from notebook_helpers import bound_native_thread_pools


def _source(cell) -> str:
    src = cell["source"]
    return "".join(src) if isinstance(src, list) else src


def _is_dotnet_bootstrap(output) -> bool:
    """Detect the dotnet-interactive HTTP-port bootstrap div (session noise)."""
    if output.get("output_type") not in ("display_data", "execute_result"):
        return False
    data = output.get("data", {})
    html = data.get("text/html", "")
    if isinstance(html, list):
        html = "".join(html)
    return "dotnet-interactive-this-cell" in html or "HttpPort" in html


def collect_outputs(kc, msg_id, timeout):
    """Drain iopub for the given execution, returning nbformat-shaped dicts."""
    outputs = []
    exec_count = None
    while True:
        try:
            msg = kc.get_iopub_msg(timeout=timeout)
        except queue.Empty:
            break
        if msg["parent_header"].get("msg_id") != msg_id:
            continue
        mt = msg["msg_type"]
        content = msg["content"]
        if mt == "status":
            if content["execution_state"] == "idle":
                break
        elif mt == "execute_input":
            exec_count = content.get("execution_count", exec_count)
        elif mt == "stream":
            outputs.append({
                "output_type": "stream",
                "name": content["name"],
                # nbformat canonical : une sortie stream porte son texte en
                # liste de lignes, pas en chaine unique -- c'est la forme que
                # produisent papermill et Jupyter, donc celle des autres
                # cellules du carnet (#25188).
                "text": content["text"].splitlines(keepends=True),
            })
        elif mt == "execute_result":
            exec_count = content.get("execution_count", exec_count)
            outputs.append({
                "output_type": "execute_result",
                "execution_count": exec_count,
                "data": content["data"],
                "metadata": content.get("metadata", {}),
            })
        elif mt == "display_data":
            outputs.append({
                "output_type": "display_data",
                "data": content["data"],
                "metadata": content.get("metadata", {}),
            })
        elif mt == "error":
            outputs.append({
                "output_type": "error",
                "ename": content["ename"],
                "evalue": content["evalue"],
                "traceback": content["traceback"],
            })
    outputs = [o for o in outputs if not _is_dotnet_bootstrap(o)]
    return outputs, exec_count


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("notebook")
    ap.add_argument("--cell-id", help="id of the code cell to execute")
    ap.add_argument("--index", type=int, help="absolute cell index to execute")
    ap.add_argument("--kernel", default="python3", help="registered kernel name")
    ap.add_argument("--cwd", default=None,
                    help="working directory of the kernel (default: the working "
                         "directory of this process). A notebook that resolves its "
                         "project from Path.cwd() (ex. the Lean series) needs it.")
    ap.add_argument("--prelude-cell-id", action="append", default=None,
                    help="id of a code cell to execute BEFORE the target, in the "
                         "SAME kernel (repeatable, order preserved). Its outputs "
                         "are discarded: it exists only to build the namespace the "
                         "target depends on (ex. a setup cell defining a path "
                         "constant).")
    ap.add_argument("--timeout", type=int, default=120)
    ap.add_argument("--set-ec", type=int, default=None,
                    help="override the written execution_count with this value. "
                         "Useful when running one cell on a fresh kernel (kernel "
                         "reports ec=1) but the cell's sequential position in the "
                         "notebook is N: the output is identical, only the display "
                         "counter is set to its real position.")
    args = ap.parse_args()

    if not args.cell_id and args.index is None:
        ap.error("provide --cell-id or --index")

    with open(args.notebook, "rb") as f:
        raw = f.read()
    # Un carnet sans saut de ligne final doit le rester : l'ecriture en
    # ajouterait un octet (bruit de diff sur la derniere ligne du fichier).
    trailing_newline = raw.endswith(b"\n")
    nb = json.loads(raw.decode("utf-8"))

    target = None
    for i, c in enumerate(nb["cells"]):
        if c.get("cell_type") != "code":
            continue
        if args.cell_id and c.get("id") == args.cell_id:
            target = c
            break
        if args.index is not None and i == args.index:
            target = c
            break
    if target is None:
        print(f"ERROR: code cell not found (cell-id={args.cell_id} index={args.index})")
        sys.exit(2)

    prelude_cells = []
    for cid in (args.prelude_cell_id or []):
        pre = next((c for c in nb["cells"]
                    if c.get("cell_type") == "code" and c.get("id") == cid), None)
        if pre is None:
            print(f"ERROR: prelude code cell not found (id={cid})")
            sys.exit(2)
        prelude_cells.append(pre)

    # Bound OpenMP/BLAS pools: native training cells oversubscribe many-core
    # hosts and look frozen (#11111). Kernel inherits env.
    bound_native_thread_pools()
    km, kc = start_new_kernel(kernel_name=args.kernel, cwd=args.cwd)
    status = "unknown"
    try:
        for pre in prelude_cells:
            pre_id = kc.execute(_source(pre))
            # Drain and discard: the prelude only builds the namespace.
            collect_outputs(kc, pre_id, args.timeout)
        msg_id = kc.execute(_source(target))
        outputs, exec_count = collect_outputs(kc, msg_id, args.timeout)
        # The shell channel carries one reply per execution: the preludes'
        # replies come first and must be skipped, not mistaken for the target's.
        deadline = time.monotonic() + args.timeout
        while True:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                break
            try:
                reply = kc.get_shell_msg(timeout=remaining)
            except queue.Empty:
                break
            if reply["parent_header"].get("msg_id") == msg_id:
                status = reply["content"].get("status", status)
                ec = reply["content"].get("execution_count")
                if ec is not None:
                    exec_count = ec
                break
    finally:
        kc.stop_channels()
        km.shutdown_kernel(now=True)

    written_ec = args.set_ec if args.set_ec is not None else exec_count
    target["execution_count"] = written_ec
    # execute_result outputs carry their own execution_count: keep it aligned.
    for o in outputs:
        if o.get("output_type") == "execute_result":
            o["execution_count"] = written_ec
    target["outputs"] = outputs

    # Les sorties/ec fraîchement écrits décrivent CE run : un bloc papermill
    # hérité d'une passe antérieure les daterait au mauvais run (#12722). Le
    # strip est BORNÉ à la cellule cible : les blocs des cellules non
    # ré-exécutées décrivent le run qui a produit leurs sorties intactes —
    # les retirer détruit une provenance valide (mesure du 14/11 : 70 cellules
    # strippées pour une seule exécutée, +50/-716 au lieu de +50/-7 ; même
    # classe que #24434 sur le writer générique). Le niveau carnet part bien :
    # le ratchet #11155 autorise son absence (BLOCK_REMOVED), pas sa survie
    # sur des sorties changées (STALE_BLOCK).
    strip_stale_papermill_metadata(nb, cells=[target])
    with open(args.notebook, "w", encoding="utf-8", newline="\n") as f:
        json.dump(nb, f, ensure_ascii=False, indent=1)
        if trailing_newline:
            f.write("\n")

    has_err = any(o.get("output_type") == "error" for o in outputs)
    print(f"Executed cell kernel_ec={exec_count} written_ec={written_ec} "
          f"status={status} outputs={len(outputs)} error={has_err}")
    for o in outputs:
        if o.get("output_type") == "stream":
            print("  STREAM:", "".join(o["text"]).strip()[:200])
        elif o.get("output_type") == "error":
            print("  ERROR:", o["ename"], o["evalue"])
    sys.exit(1 if has_err else 0)


if __name__ == "__main__":
    main()
