#!/usr/bin/env python3
"""Unlock native lean4-wsl import of Mathlib lakes (patch lean4_jupyter repl.py).

BACKGROUND
----------
The lean4-wsl Jupyter kernel launches its REPL via ``lake env repl``
(``lean4_jupyter/repl.py:Lean4ReplWrapper.launch``). Under ``lake env`` the REPL
binary loses its sysroot (it cannot find ``Init``), so ``#check Nat`` returns
"Unknown identifier" and importing a Mathlib lake is impossible in-kernel.
``lake env lean`` (the compiler) does NOT have this problem (pattern #4388), but
that route is python3 + subprocess, which the user finds hard to read.

FIX
---
Patch ``launch()`` to run the REPL binary *directly* (not via ``lake env``) with
``LEAN_PATH`` captured from ``lake env`` (sysroot + deps + junctioned Mathlib +
lake build dir). With this, a lean4-wsl kernel launched inside a lake workspace
natively ``import``s the lake and renders ``#check`` signatures in-kernel (real
Alectryon HTML output), zero Python. The fallback ``lake env repl`` is kept for
Mathlib-free stub lakes (lean_game_defs, notebook_context).

A matched REPL binary is required per lake toolchain (``~/.elan/bin/repl`` is
stable-locked; rc1/rc2 lakes need a matched REPL — see ``build-repl``).

USAGE
-----
    python scripts/lean/setup_native_lean4_import.py status        # what's patched/installed
    python scripts/lean/setup_native_lean4_import.py patch         # patch repl.py (idempotent, backup)
    python scripts/lean/setup_native_lean4_import.py build-repl v4.30.0-rc2
    python scripts/lean/setup_native_lean4_import.py --check

Probe evidence (2026-06, sensitivity_lean): ``import Sensitivity`` +
``#check huang_degree_theorem`` in a lean4-wsl kernel render the real signature,
``#print axioms`` -> [propext, Classical.choice, Quot.sound] (0 sorry). See
docs/reference/wsl-kernels-detail.md.
"""

import argparse
import shutil
import subprocess
import sys
from pathlib import Path

WSL_DISTRO = "Ubuntu"
# Canonical matched-REPL install paths (one per toolchain tag).
REPL_TOOLCHAIN_TAGS = {
    "v4.30.0-rc2": "repl-4.30.0-rc2",
    "v4.31.0-rc1": "repl-4.31.0-rc1",
}
# Marker present in repl.py once patched (idempotency check).
PATCH_MARKER = "_find_lake_root"

REPL_PY_PATCH = '''    @staticmethod
    def _find_lake_root(start='.'):
        d = os.path.abspath(start)
        for _ in range(12):
            if os.path.isfile(os.path.join(d, 'lakefile.lean')) or \\
               os.path.isfile(os.path.join(d, 'lakefile.toml')):
                return d
            p = os.path.dirname(d)
            if p == d:
                return None
            d = p
        return None

    @staticmethod
    def _repl_for_toolchain(lake_root):
        """Pick a REPL binary matching the lake's toolchain.
        ``~/.elan/bin/repl`` is stable-locked; rc1/rc2 lakes need a matched REPL
        (built via ``setup_native_lean4_import.py build-repl <tag>``)."""
        default = os.path.expanduser('~/.elan/bin/repl')
        # toolchain tag -> canonical matched-REPL name (inlined; keep in sync
        # with REPL_TOOLCHAIN_TAGS in setup_native_lean4_import.py).
        mapping = {'v4.30.0-rc2': 'repl-4.30.0-rc2',
                   'v4.31.0-rc1': 'repl-4.31.0-rc1'}
        try:
            tc_file = os.path.join(lake_root, 'lean-toolchain')
            tc = open(tc_file).read().strip() if os.path.isfile(tc_file) else ''
        except OSError:
            tc = ''
        elan_bin = os.path.expanduser('~/.elan/bin')
        for tag, name in mapping.items():
            if tag in tc:
                p = os.path.join(elan_bin, name)
                if os.path.isfile(p):
                    return p
        return default

    @classmethod
    def launch(cls):
        """Native-import path: launch the REPL binary DIRECT (not via ``lake env``)
        with the lake's LEAN_PATH when running inside a lake workspace. ``lake env
        repl`` clobbers the REPL sysroot (loses Init); direct launch with
        LEAN_PATH=sysroot+deps+Mathlib restores native Mathlib-lake import."""
        try:
            lake_root = cls._find_lake_root(os.getcwd())
            if lake_root:
                import subprocess as _sp
                out = _sp.run(
                    ['lake', 'env', 'python3', '-c',
                     'import os; print(os.environ.get("LEAN_PATH",""))'],
                    capture_output=True, text=True, timeout=60, cwd=lake_root,
                    env={**os.environ,
                         'PATH': os.path.expanduser('~/.elan/bin') + ':/usr/local/bin:/usr/bin:/bin'}
                ).stdout
                lean_path = '\\n'.join(
                    l for l in out.splitlines() if 'local changes' not in l).strip()
                repl_bin = cls._repl_for_toolchain(lake_root)
                if lean_path and os.path.isfile(repl_bin):
                    env = {**os.environ, 'LEAN_PATH': lean_path,
                           'PATH': os.path.expanduser('~/.elan/bin') + ':/usr/local/bin:/usr/bin:/bin'}
                    return pexpect.spawn(repl_bin, echo=False, encoding='utf-8',
                                         codec_errors='replace', env=env)
        except Exception:
            pass
        return pexpect.spawn("lake env repl",
                             echo=False, encoding='utf-8', codec_errors='replace')
'''

REPL_PY_ORIGINAL = '''    @classmethod
    def launch(cls):
        return pexpect.spawn("lake env repl",
                             echo=False, encoding='utf-8', codec_errors='replace')'''


def _wsl(cmd, timeout=120):
    """Run a command inside WSL, return CompletedProcess."""
    full = ["wsl.exe", "-d", WSL_DISTRO, "--", "bash", "-lc", cmd]
    return subprocess.run(full, capture_output=True, text=True, timeout=timeout)


def _find_repl_py():
    """Locate lean4_jupyter/repl.py inside the WSL lean4 venv."""
    r = _wsl("ls /home/*/.lean4-venv/lib/python3.*/site-packages/lean4_jupyter/repl.py "
             "2>/dev/null | head -1", timeout=30)
    path = r.stdout.strip()
    return path or None


def cmd_status():
    rp = _find_repl_py()
    print("== native lean4-wsl Mathlib import — status ==")
    if not rp:
        print("lean4_jupyter/repl.py: NOT FOUND (lean4 venv missing?)")
        return 1
    print("repl.py:", rp)
    r = _wsl(f"grep -q '{PATCH_MARKER}' {rp} && echo PATCHED || echo UNPATCHED", timeout=20)
    print("patch state:", r.stdout.strip())
    print("matched REPL binaries:")
    for tag, name in REPL_TOOLCHAIN_TAGS.items():
        rr = _wsl(f"test -f ~/.elan/bin/{name} && echo '  {name}: present' "
                  f"|| echo '  {name}: MISSING (run: build-repl {tag})'", timeout=15)
        print(rr.stdout.strip())
    return 0


def cmd_patch():
    rp = _find_repl_py()
    if not rp:
        print("ERROR: lean4_jupyter/repl.py not found", file=sys.stderr)
        return 1
    # Idempotency: already patched?
    r = _wsl(f"grep -q '{PATCH_MARKER}' {rp} && echo yes || echo no", timeout=20)
    if r.stdout.strip() == "yes":
        print("repl.py already patched (idempotent) — nothing to do.")
        return 0
    # Backup.
    _wsl(f"cp {rp} {rp}.bak.native 2>/dev/null", timeout=20)
    # Write the patcher to a temp file and run it inside WSL (avoids the
    # bash -lc quoting nightmare of a multi-line python -c with apostrophes).
    import tempfile, os
    patcher = (
        "import sys\n"
        f"p = {rp!r}\n"
        "src = open(p, encoding='utf-8').read()\n"
        "if '_find_lake_root' in src:\n"
        "    print('already'); sys.exit(0)\n"
        "OLD = " + repr(REPL_PY_ORIGINAL) + "\n"
        "NEW = " + repr(REPL_PY_PATCH) + "\n"
        "if OLD not in src:\n"
        "    print('ERROR: original launch() block not found (upstream changed)'); sys.exit(2)\n"
        "open(p, 'w', encoding='utf-8').write(src.replace(OLD, NEW, 1))\n"
        "print('PATCHED')\n"
    )
    with tempfile.NamedTemporaryFile("w", suffix=".py", delete=False, encoding="utf-8") as f:
        f.write(patcher)
        tmp_win = f.name
    # Convert Windows temp path -> WSL path and copy into /tmp.
    win_drive = tmp_win[0].lower()
    tmp_unix_src = "/mnt/" + win_drive + tmp_win[2:].replace("\\", "/")
    tmp_wsl = "/tmp/_lean4_native_patcher.py"
    _wsl(f"cp '{tmp_unix_src}' {tmp_wsl}", timeout=20)
    os.unlink(tmp_win)
    r = _wsl(f"/home/*/.lean4-venv/bin/python3 {tmp_wsl}", timeout=40)
    out = (r.stdout or r.stderr or "").strip()
    _wsl(f"rm -f {tmp_wsl}", timeout=10)
    print("patch:", out)
    # Compile check.
    rc = _wsl(f"/home/*/.lean4-venv/bin/python3 -m py_compile {rp} && echo OK", timeout=30)
    print("py_compile:", (rc.stdout or rc.stderr or "").strip())
    return 0 if ("PATCHED" in out or "already" in out) else 1


def cmd_build_repl(tag):
    if tag not in REPL_TOOLCHAIN_TAGS:
        print(f"ERROR: unknown tag {tag}. Known: {list(REPL_TOOLCHAIN_TAGS)}", file=sys.stderr)
        return 1
    name = REPL_TOOLCHAIN_TAGS[tag]
    cmds = (
        f"export PATH=/home/*/.elan/bin:/usr/local/bin:/usr/bin:/bin; "
        f"mkdir -p ~/repl-build && cd ~/repl-build && "
        f"if [ ! -d repl ]; then git clone --depth 1 https://github.com/leanprover-community/repl.git; fi && "
        f"cd repl && git checkout {tag} 2>&1 | tail -1 && "
        f"lake clean >/dev/null 2>&1; lake build repl 2>&1 | tail -3; "
        f"if [ -f .lake/build/bin/repl ]; then cp .lake/build/bin/repl ~/.elan/bin/{name} "
        f"&& echo INSTALLED-{name}; else echo BUILD-FAILED; fi"
    )
    print(f"building repl {tag} -> ~/.elan/bin/{name} (this takes a few minutes)...")
    r = _wsl(cmds, timeout=600)
    print(r.stdout.strip()[-800:])
    return 0 if f"INSTALLED-{name}" in r.stdout else 1


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("command", nargs="?", choices=["status", "patch", "build-repl"],
                    default="status")
    ap.add_argument("tag", nargs="?", help="toolchain tag for build-repl (e.g. v4.30.0-rc2)")
    ap.add_argument("--check", action="store_true", help="alias for status")
    args = ap.parse_args()
    if args.check or args.command == "status":
        return cmd_status()
    if args.command == "patch":
        return cmd_patch()
    if args.command == "build-repl":
        if not args.tag:
            print("ERROR: build-repl requires a tag", file=sys.stderr)
            return 1
        return cmd_build_repl(args.tag)
    return 0


if __name__ == "__main__":
    sys.exit(main())
