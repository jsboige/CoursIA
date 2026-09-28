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
    python scripts/lean/setup_native_lean4_import.py install       # install durable fork (replaces in-place patch)
    python scripts/lean/setup_native_lean4_import.py patch         # [legacy] patch repl.py in-place (offline fallback)
    python scripts/lean/setup_native_lean4_import.py sync-repl-table  # align installed toolchain table (#18120)
    python scripts/lean/setup_native_lean4_import.py build-repl v4.30.0-rc2
    python scripts/lean/setup_native_lean4_import.py --check

Probe evidence (2026-06, sensitivity_lean): ``import Sensitivity`` +
``#check huang_degree_theorem`` in a lean4-wsl kernel render the real signature,
``#print axioms`` -> [propext, Classical.choice, Quot.sound] (0 sorry). See
docs/reference/wsl-kernels-detail.md.
"""

import argparse
import base64
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

# The Windows console stdout is cp1252, while WSL/lake output carries glyphs it
# cannot encode (the build stamps ``✔ [n/m] Built ...``, and Lean echoes ∀ / ↦).
# Unreconciled, ``print(r.stdout...)`` raises UnicodeEncodeError *after* the
# build has already succeeded, so the run reports a failure that did not happen
# (same class as #13140). Reconcile stdout once here instead of at each print.
if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")

WSL_DISTRO = "Ubuntu"
# Canonical matched-REPL install paths (one per toolchain tag).
REPL_TOOLCHAIN_TAGS = {
    "v4.30.0-rc2": "repl-4.30.0-rc2",
    "v4.31.0-rc1": "repl-4.31.0-rc1",
    "v4.32.0": "repl-4.32.0",
    "v4.32.1": "repl-4.32.1",
    "v4.33.0": "repl-4.33.0",
    "v4.33.1": "repl-4.33.1",
    "v4.34.0-rc1": "repl-4.34.0-rc1",
}
# Durable fork of utensil/lean4_jupyter baking the direct-launch patch directly into
# repl.py (survives a clean ``pip install``/reinstall, closing the durability gap of the
# in-place ``patch``). The fork repl.py is the single runtime source of the patch; the
# ``REPL_PY_PATCH`` constant below mirrors it verbatim for the legacy offline fallback.
# See issue #4394.
FORK_URL = "git+https://github.com/jsboige/lean4_jupyter.git"
FORK_TAG = "v0.0.1-native-import"
# Marker present in repl.py once patched (idempotency check).
# Note: as of v0.0.1-native-import the durably-installed fork already bakes
# `_find_lake_root` + `_repl_for_toolchain` into repl.py — so the marker matches
# the upstream fork, not the legacy in-place patch. The in-place patcher is kept
# as an offline fallback for users who cannot install the fork (e.g. no network).
PATCH_MARKER = "_find_lake_root"
# Drift marker for the DrvFS wedge fix (c.1331p319 #12061): the upstream fork
# at v0.0.1-native-import does NOT contain this string; presence in repl.py means
# a host-side re-patch (or a newer fork tag) has applied the sysroot-first
# reorder. Re-running `patch` after restoring the upstream repl.py is the
# supported way to re-apply on evolution.
PATCH_MARKER_DRVFS = "sysroot_first_reorder"

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
                   'v4.31.0-rc1': 'repl-4.31.0-rc1',
                   'v4.32.0': 'repl-4.32.0',
                   'v4.32.1': 'repl-4.32.1',
                   'v4.33.0': 'repl-4.33.0',
                   'v4.33.1': 'repl-4.33.1',
                   'v4.34.0-rc1': 'repl-4.34.0-rc1'}
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
                    # timeout=240 (not 60): on rc1 lakes whose Mathlib is an NTFS
                    # junction, `lake env` re-verifies the junction ("has local
                    # changes") and takes ~111-125s (measured c.129). timeout=60
                    # tripped RC1-TIMEOUT -> empty LEAN_PATH -> broken `lake env
                    # repl` fallback -> silent kernel failure. 240s = ~2x margin.
                    capture_output=True, text=True, timeout=240, cwd=lake_root,
                    env={**os.environ,
                         'PATH': os.path.expanduser('~/.elan/bin') + ':/usr/local/bin:/usr/bin:/bin'}
                ).stdout
                lean_path = '\\n'.join(
                    l for l in out.splitlines() if 'local changes' not in l).strip()
                # DrvFS wedge mitigation (c.1331p319 #12061): on NTFS-Dr vFS
                # (e.g. /mnt/d), `lake env` returns LEAN_PATH with the elan
                # sysroot LAST, forcing the REPL to scan every package directory
                # on the slow DrvFS mount BEFORE finding `Init` in the sysroot
                # -> hang >16 min on `#check`. Reorder puts sysroot FIRST.
                # Pure-function counterpart: _reorder_lean_path_drvfs_first in
                # setup_native_lean4_import.py (same logic, no WSL deps).
                # Marker: sysroot_first_reorder (PATCH_MARKER_DRVFS).
                if lean_path:
                    _elan_root = os.path.expanduser('~/.elan/toolchains')
                    _entries = [e for e in lean_path.split(':') if e]
                    _sysroot_entries = [e for e in _entries
                                        if e.startswith(_elan_root)]
                    if _sysroot_entries and _entries[0] != _sysroot_entries[0]:
                        _non_sysroot = [e for e in _entries
                                        if e not in _sysroot_entries]
                        lean_path = ':'.join(_sysroot_entries + _non_sysroot)
                # sysroot_first_reorder (DrvFS marker)
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


def _reorder_lean_path_drvfs_first(lean_path, elan_root):
    """Reorder a colon-separated LEAN_PATH so that elan-toolchain sysroot entries
    come before the per-lake packages. Pure function (testable without WSL).

    Why: on DrvFS-mounted lakes (NTFS via WSL, e.g. /mnt/d), the REPL scans every
    package directory for Init before reaching the sysroot at the end of
    LEAN_PATH — this wedges the kernel for >16 min on `#check` (c.1331p319
    #12061). Putting the sysroot first short-circuits the scan.

    Args:
        lean_path: colon-separated LEAN_PATH string from `lake env`.
        elan_root: the elan toolchains root (e.g. ``/home/user/.elan/toolchains``).

    Returns:
        Reordered LEAN_PATH string. No-op when the sysroot is already first,
        when no sysroot entries are present, or when the input is empty.
    """
    if not lean_path:
        return lean_path
    entries = [e for e in lean_path.split(':') if e]
    sysroot_entries = [e for e in entries if e.startswith(elan_root)]
    if not sysroot_entries or entries[0] == sysroot_entries[0]:
        return lean_path
    non_sysroot = [e for e in entries if e not in sysroot_entries]
    return ':'.join(sysroot_entries + non_sysroot)


def _wsl(cmd, timeout=120):
    """Run a command inside WSL, return CompletedProcess.

    cwd is forced to a neutral directory, and the GIT_* repo-redirection vars are
    dropped. wsl.exe already puts the WSL process in the *Windows* cwd, and every
    ``_wsl`` command is self-contained (each one ``cd`` where it needs to). When
    the caller runs from a git WORKTREE that matters: the worktree's ``.git`` is a
    FILE holding ``gitdir: D:/.../.git/worktrees/<name>``, a Windows path WSL
    resolves into ``<wsl-cwd>/D:/.../...`` -- git then dies with "not a git
    repository" and returns an EMPTY stdout, which ``_resolve_repl_source_tag``
    reads as "no tag <= want" and reports as a misleading ``NO-SOURCE-TAG``.
    Workers are mandated to work in worktrees, so this made ``build-repl``
    silently unusable exactly where it is needed (measured 2026-09-12: v4.33.0
    resolution returned None from a worktree, and the same silent empty-stdout
    path is why the ``repl-4.33.1`` key was advertised but never built).
    """
    full = ["wsl.exe", "-d", WSL_DISTRO, "--", "bash", "-lc", cmd]
    env = {k: v for k, v in os.environ.items()
           if k not in ("GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE", "GIT_COMMON_DIR")}
    # encoding explicite : la sortie WSL porte de l'unicode Lean (forall, mapsto).
    # text=True seul decode via la locale -> crash sur hote cp1252 (#12811).
    return subprocess.run(full, capture_output=True, text=True, timeout=timeout,
                          encoding="utf-8", errors="replace",
                          cwd=os.path.expanduser("~"), env=env)


def _find_repl_py():
    """Locate lean4_jupyter/repl.py inside the WSL lean4 venv."""
    r = _wsl("ls /home/*/.lean4-venv/lib/python3.*/site-packages/lean4_jupyter/repl.py "
             "2>/dev/null | head -1", timeout=30)
    path = r.stdout.strip()
    return path or None


def cmd_install():
    """Install the durable fork ``jsboige/lean4_jupyter@v0.0.1-native-import`` into the
    WSL lean4 venv. The fork bakes the direct-launch patch into ``lean4_jupyter/repl.py``
    itself, so native Mathlib-lake import survives a clean reinstall — this replaces the
    in-place ``patch`` (which was lost on every ``pip install``)."""
    spec = f"{FORK_URL}@{FORK_TAG}"
    # --force-reinstall: the patched fork must replace any prior upstream lean4_jupyter.
    # --no-deps: pexpect etc. are already satisfied in ~/.lean4-venv; avoid dependency churn.
    cmd = f"~/.lean4-venv/bin/pip install --force-reinstall --no-deps {spec}"
    print(f"installing durable fork {spec} ...")
    r = _wsl(cmd, timeout=300)
    print((r.stdout or r.stderr or "").strip()[-1200:])
    rp = _find_repl_py()
    if not rp:
        print("ERROR: lean4_jupyter/repl.py not found after install", file=sys.stderr)
        return 1
    chk = _wsl(f"grep -q '{PATCH_MARKER}' {rp} && echo PATCHED || echo UNPATCHED", timeout=20)
    state = chk.stdout.strip()
    print("post-install patch state:", state)
    rc = _wsl(f"/home/*/.lean4-venv/bin/python3 -m py_compile {rp} && echo OK", timeout=30)
    print("py_compile:", (rc.stdout or rc.stderr or "").strip())
    return 0 if state == "PATCHED" else 1


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
    # #18120: the installed table comes from the frozen fork and can lag behind
    # REPL_TOOLCHAIN_TAGS — a lake on a missing tag silently falls back to the
    # stable REPL (``Unknown identifier`` on core names, no version error). The
    # gap was invisible; status now compares both tables and fails on the
    # harmful classes so agents/checks can act on it.
    installed = _read_installed_repl_table(rp)
    drift_detected = False
    if installed is None:
        print("installed REPL table: no _repl_for_toolchain mapping found (upstream?)")
    else:
        drift = _repl_table_drift(installed, REPL_TOOLCHAIN_TAGS)
        print(f"installed REPL table: {len(installed)} tags "
              f"(repo reference: {len(REPL_TOOLCHAIN_TAGS)})")
        for t in drift["missing"]:
            print(f"  WARNING — '{t}' missing from installed table")
        for t in drift["extra"]:
            print(f"  (note — '{t}' in installed table, not in repo reference)")
        for t, (old, new) in drift["changed"].items():
            print(f"  WARNING — '{t}': installed '{old}' != repo '{new}'")
        if drift["missing"] or drift["changed"]:
            drift_detected = True
            print("  -> lakes on these toolchains silently use the STABLE repl: "
                  "'Unknown identifier' on core names, no version error. "
                  "Fix: setup_native_lean4_import.py sync-repl-table")
    return 1 if drift_detected else 0


def _read_installed_repl_table(rp):
    """Installed table read losslessly: base64 transport keeps bytes exact
    through the utf-8/replace-decoding ``_wsl`` pipe (#18120)."""
    r = _wsl(f"base64 -w0 {rp}", timeout=20)
    if not r.stdout.strip():
        return None
    src = base64.b64decode(r.stdout.strip()).decode("utf-8")
    return _extract_repl_table(src)


def cmd_patch():
    rp = _find_repl_py()
    if not rp:
        print("ERROR: lean4_jupyter/repl.py not found", file=sys.stderr)
        return 1
    # Idempotency: if marker present, the file is already patched. Caller that
    # wants to re-apply (e.g. after REPL_PY_PATCH evolved, as in c.1331p319
    # #12061) must restore the upstream repl.py first (cp *.bak.native repl.py).
    r = _wsl(f"grep -q '{PATCH_MARKER}' {rp} && echo yes || echo no", timeout=20)
    if r.stdout.strip() == "yes":
        print("repl.py already patched (idempotent) — nothing to do. "
              "To re-apply over an evolved REPL_PY_PATCH, restore first: "
              f"cp {rp}.bak.native {rp}")
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


def cmd_sync_repl_table():
    """Align the installed ``lean4_jupyter/repl.py`` toolchain table on
    ``REPL_TOOLCHAIN_TAGS`` (#18120).

    The fork ``v0.0.1-native-import`` is frozen: its baked table cannot follow
    the repo constant, and ``patch`` refuses to touch a file that already
    carries the marker — so until now the only remedy was a manual venv edit
    (done once by hand on 2026-09-27 to unblock #17714, backup
    ``repl.py.bak.c913``). This command reproduces that gesture safely:
    timestamped backup, formatting-independent literal replacement, py_compile,
    and a re-read verification that refuses silent success. Idempotent — a
    no-op when the tables already agree.
    """
    rp = _find_repl_py()
    if not rp:
        print("ERROR: lean4_jupyter/repl.py not found", file=sys.stderr)
        return 1
    # Lossless read (base64 transport — see _read_installed_repl_table).
    r = _wsl(f"base64 -w0 {rp}", timeout=20)
    if not r.stdout.strip():
        print("ERROR: could not read installed repl.py", file=sys.stderr)
        return 1
    src = base64.b64decode(r.stdout.strip()).decode("utf-8")
    new_src, drift = _apply_repl_table_sync(src, REPL_TOOLCHAIN_TAGS)
    if not (drift["missing"] or drift["extra"] or drift["changed"]):
        print("installed REPL table already in sync with REPL_TOOLCHAIN_TAGS — nothing to do")
        return 0
    if new_src is None:
        print("ERROR: no `_repl_for_toolchain` mapping literal found in installed "
              "repl.py — refusing to write (upstream file? run `install` first)",
              file=sys.stderr)
        return 2
    ts = time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
    bak = f"{rp}.bak.repltable-{ts}"
    _wsl(f"cp {rp} {bak}", timeout=20)
    print("backup:", bak)
    # Ship the new source as exact bytes: binary temp file (no newline
    # translation), then cp inside WSL. All table logic stays in this module
    # (unit-testable); WSL only carries bytes and compiles.
    import tempfile
    with tempfile.NamedTemporaryFile("wb", suffix=".py", delete=False) as f:
        f.write(new_src.encode("utf-8"))
        tmp_win = f.name
    tmp_unix_src = "/mnt/" + tmp_win[0].lower() + tmp_win[2:].replace("\\", "/")
    tmp_wsl = "/tmp/_lean4_repl_table_sync.py"
    _wsl(f"cp '{tmp_unix_src}' {tmp_wsl}", timeout=20)
    os.unlink(tmp_win)
    _wsl(f"cp {tmp_wsl} {rp}", timeout=20)
    _wsl(f"rm -f {tmp_wsl}", timeout=10)
    rc = _wsl(f"/home/*/.lean4-venv/bin/python3 -m py_compile {rp} && echo OK", timeout=30)
    compile_out = (rc.stdout or rc.stderr or "").strip()
    print("py_compile:", compile_out)
    # Verify by re-reading — a write is never trusted silent (#18120).
    after = _read_installed_repl_table(rp)
    drift_after = _repl_table_drift(after or {}, REPL_TOOLCHAIN_TAGS)
    if "OK" not in compile_out or after is None or drift_after["missing"] or drift_after["changed"]:
        print("ERROR: post-sync verification failed — restore with: "
              f"cp {bak} {rp}", file=sys.stderr)
        return 1
    for t in drift["missing"]:
        print(f"  + {t} -> {REPL_TOOLCHAIN_TAGS[t]}")
    for t in drift["extra"]:
        print(f"  - {t} (not in repo reference)")
    for t, (old, new) in drift["changed"].items():
        print(f"  ~ {t}: {old} -> {new}")
    print(f"synced: installed REPL table now matches REPL_TOOLCHAIN_TAGS "
          f"({len(REPL_TOOLCHAIN_TAGS)} tags); backup: {bak}")
    return 0


def _repl_tag_sort_key(t):
    """Total order over repl tags: (maj, min, patch, is_release, rcN).

    #12168: the key must be total over ``-rcN`` suffixes too -- the script's
    own docstring advertises ``build-repl v4.30.0-rc2`` and REPL_TOOLCHAIN_TAGS
    carries rc keys. rcN < release for the same triple (v4.30.0-rc2 precedes
    v4.30.0): an rc is the candidate OF that release, so resolving "nearest
    tag <= v4.30.0-rc2" must be able to land on the rc itself, never skip it.
    Anything malformed sorts below everything rather than raising -- the old
    ``int()`` KeyError/ValueError path silently degraded the resolver to None
    (the misleading NO-SOURCE-TAG of #12168).
    """
    m = re.fullmatch(r"v(\d+)\.(\d+)\.(\d+)(?:-rc(\d+))?", t)
    if not m:
        return (-1, -1, -1, 0, 0)
    maj, minor, patch, rc = m.groups()
    return (int(maj), int(minor), int(patch), 0 if rc is not None else 1,
            int(rc) if rc is not None else 0)


def _extract_repl_table(src):
    """Installed ``_repl_for_toolchain`` mapping from repl.py source, formatting-
    independent (#18120).

    The installed copy comes from the frozen fork ``v0.0.1-native-import`` whose
    formatting already diverges from ``REPL_PY_PATCH`` (entries packed two per
    line vs one per line), so extraction must not depend on layout. The mapping
    literal is flat (no nested braces), so the first ``}`` after ``mapping = {``
    closes it. Returns ``{}`` when the function exists but no entry parses, and
    ``None`` when repl.py carries no ``_repl_for_toolchain`` at all (upstream,
    unpatched) — callers treat ``None`` as fail-closed.
    """
    m = re.search(r"def _repl_for_toolchain\(.*?mapping = \{", src, re.DOTALL)
    if not m:
        return None
    body = src[m.end():src.index("}", m.end())]
    return dict(re.findall(r"'(v[0-9][^']*)'\s*:\s*'(repl-[^']*)'", body))


def _repl_table_drift(installed, reference):
    """Drift report between the installed table and ``REPL_TOOLCHAIN_TAGS``.

    Returns ``{"missing": [...], "extra": [...], "changed": {tag: (old, new)}}``
    with tag lists sorted by ``_repl_tag_sort_key``. ``missing``/``changed`` are
    the harmful classes (the lake silently falls back to the stable REPL);
    ``extra`` is informational (routing more lakes correctly).
    """
    missing = sorted(set(reference) - set(installed), key=_repl_tag_sort_key)
    extra = sorted(set(installed) - set(reference), key=_repl_tag_sort_key)
    changed = {t: (installed[t], reference[t])
               for t in sorted(set(installed) & set(reference), key=_repl_tag_sort_key)
               if installed[t] != reference[t]}
    return {"missing": missing, "extra": extra, "changed": changed}


def _render_repl_table(table):
    """Render the ``mapping`` braces-literal, one entry per line, tags sorted.

    Drop-in replacement for the literal regardless of the installed copy's
    formatting (repo payload one-per-line, fork two-per-line).
    """
    items = sorted(table.items(), key=lambda kv: _repl_tag_sort_key(kv[0]))
    return "{\n" + ",\n".join(f"                   '{t}': '{n}'" for t, n in items) + "}"


def _apply_repl_table_sync(src, reference):
    """Return ``(new_src, drift)`` with the installed mapping literal replaced by
    ``reference``. Idempotent: when the tables already agree, ``new_src`` is
    ``src`` untouched. Fail-closed: when repl.py carries no
    ``_repl_for_toolchain`` mapping literal, returns ``(None, drift)`` and the
    caller must not write anything (#18120 — never blind-write the venv).
    """
    installed = _extract_repl_table(src)
    drift = _repl_table_drift(installed or {}, reference)
    if not (drift["missing"] or drift["extra"] or drift["changed"]):
        return src, drift
    m = re.search(r"(def _repl_for_toolchain\(.*?mapping = )\{[^{}]*\}", src, re.DOTALL)
    if not m:
        return None, drift
    return src[:m.end(1)] + _render_repl_table(reference) + src[m.end():], drift


def _resolve_repl_source_tag(tag):
    """Nearest repl-repo tag <= the requested toolchain tag, or None.

    Runs in Python on purpose: shell one-liners piped through wsl.exe ->
    bash -lc lose their single quotes at the argument boundary, which once
    made the awk version filter return v4.33.0 for tag v4.32.1.
    """
    r = _wsl("git ls-remote --tags https://github.com/leanprover-community/repl.git",
             timeout=60)
    # #12168: the filter used to drop rc tags outright -- while the docstring
    # and REPL_TOOLCHAIN_TAGS both advertise them.
    tags = {m.group(1) for m in re.finditer(
        r"refs/tags/(v[0-9]+\.[0-9]+\.[0-9]+(?:-rc[0-9]+)?)$",
        r.stdout or "", re.M)}

    key = _repl_tag_sort_key
    want = key(tag)
    if want[0] < 0:
        return None
    lower = sorted((t for t in tags if key(t) <= want), key=key)
    return lower[-1] if lower else None


def cmd_build_repl(tag, default=False):
    if tag not in REPL_TOOLCHAIN_TAGS:
        print(f"ERROR: unknown tag {tag}. Known: {list(REPL_TOOLCHAIN_TAGS)}", file=sys.stderr)
        return 1
    name = REPL_TOOLCHAIN_TAGS[tag]
    # $HOME, not /home/*: WSL distros running as root keep elan under /root/.elan
    # (a literal /home/* glob in PATH never expands there -> lake not found).
    # The repl repo does not tag every Lean patch release (e.g. v4.32.1 has no
    # tag). When the exact tag is absent, check out the nearest LOWER tag and
    # override lean-toolchain to the requested version (upstream bumps the
    # toolchain file the same way per release). The checkout MUST be verified:
    # a silently-failed checkout leaves HEAD on the previous tag and builds a
    # version-skewed repl whose only symptom is "incompatible header" /
    # Unknown identifier at import time (incident 2026-08-21: repl-4.32.1 was
    # actually v4.31.0).
    # Tag selection happens in Python, not in a shell pipeline: single quotes
    # do not survive the wsl.exe argument boundary (bash -lc receives an
    # unquoted awk program, expands $0 itself and the version filter silently
    # selects the wrong tag — measured: v4.33.0 returned for tag v4.32.1).
    src_tag = _resolve_repl_source_tag(tag)
    if not src_tag:
        print(f"NO-SOURCE-TAG: repl repo has no tag <= {tag}")
        return 1
    override = src_tag != tag
    print(f"building repl {tag} from repl source tag {src_tag}"
          f"{' (nearest lower tag, toolchain overridden)' if override else ''} "
          f"-> ~/.elan/bin/{name}{' (also as default repl)' if default else ''} "
          "(this takes a few minutes)...")
    # Phase 1: fetch + checkout. The checkout is verified afterwards by
    # comparing git rev-parse output IN PYTHON: command substitution and
    # test brackets piped through wsl.exe -> bash -lc get mangled at the
    # argument boundary (a [ \"$(...)\" = tag ] check reported a mismatch on
    # a checkout that was in fact correct).
    #
    # ``git checkout --force`` (not the bare form): when the requested tag has
    # no exact repl source tag, the build overrides ``lean-toolchain`` in place
    # (see ``override`` above) and leaves the checkout DIRTY. A later
    # ``build-repl`` then aborts mid-sequence with "Your local changes to the
    # following files would be overwritten by checkout: lean-toolchain" -- and
    # because the old form piped through ``| tail -1``, the abort was silent and
    # the operator only saw a bare CHECKOUT-MISMATCH with no cause. That is how
    # the ``v4.33.1`` key came to be advertised in REPL_TOOLCHAIN_TAGS yet never
    # built. The override is the script's own artifact and is regenerated on
    # every build, so discarding it here is the intended semantics; the failure
    # is now surfaced instead of swallowed.
    prep = _wsl(
        f"export PATH=$HOME/.elan/bin:/usr/local/bin:/usr/bin:/bin; "
        f"mkdir -p ~/repl-build && cd ~/repl-build && "
        f"if [ ! -d repl ]; then git clone https://github.com/leanprover-community/repl.git; fi && "
        f"cd repl && git fetch --tags --force -q origin && "
        f"git checkout --force {src_tag} && echo CHECKOUT-OK",
        timeout=300)
    if "CHECKOUT-OK" not in (prep.stdout or ""):
        print("CHECKOUT-FAILED: "
              + " ".join(((prep.stdout or "") + " " + (prep.stderr or "")).split())[-600:])
        return 1
    head = (_wsl("cd ~/repl-build/repl && git rev-parse HEAD", timeout=30).stdout or "").strip()
    tagc = (_wsl(f"cd ~/repl-build/repl && git rev-parse {src_tag}^{{commit}}",
                 timeout=30).stdout or "").strip()
    if not tagc or head != tagc:
        print(f"CHECKOUT-MISMATCH: HEAD={head or '<empty>'} != {src_tag}^{tagc or '<empty>'}")
        return 1
    # Phase 2: toolchain override + build + install.
    cmds = (
        f"export PATH=$HOME/.elan/bin:/usr/local/bin:/usr/bin:/bin; cd ~/repl-build/repl; "
        + (f"echo leanprover/lean4:{tag} > lean-toolchain && echo TOOLCHAIN-OVERRIDE-{src_tag}-TO-{tag}; " if override else "")
        + f"grep -q {tag} lean-toolchain || {{ echo TOOLCHAIN-MISMATCH: $(cat lean-toolchain); exit 1; }}; "
        f"lake clean >/dev/null 2>&1; lake build repl 2>&1 | tail -3; "
        f"if [ -f .lake/build/bin/repl ]; then cp .lake/build/bin/repl ~/.elan/bin/{name} "
        f"&& echo INSTALLED-{name}"
        + (" && cp .lake/build/bin/repl ~/.elan/bin/repl && echo INSTALLED-DEFAULT" if default else "")
        + "; else echo BUILD-FAILED; fi"
    )
    r = _wsl(cmds, timeout=900)
    print(r.stdout.strip()[-800:])
    ok = f"INSTALLED-{name}" in r.stdout and (not default or "INSTALLED-DEFAULT" in r.stdout)
    return 0 if ok else 1


def cmd_test():
    """Unit tests for the pure-function patch logic (no WSL, no GPU).

    Run via: python scripts/lean/setup_native_lean4_import.py test
    """
    sysroot = "/home/u/.elan/toolchains/v4.32.1/lib/lean"
    pkg = "/mnt/d/dev/CoursIA-2/MyIA.AI.Notebooks/SymbolicAI/Lean/dt_lean/.lake/packages"
    other = "/mnt/d/dev/CoursIA-2/MyIA.AI.Notebooks/SymbolicAI/Lean/dt_lean/.lake/build/lib"
    # 1. sysroot already first -> no-op.
    path = f"{sysroot}:{pkg}:{other}"
    assert _reorder_lean_path_drvfs_first(path, "/home/u/.elan/toolchains") == path, (
        "sysroot-first path should be unchanged")
    # 2. sysroot last -> reorder.
    path = f"{pkg}:{other}:{sysroot}"
    expected = f"{sysroot}:{pkg}:{other}"
    assert _reorder_lean_path_drvfs_first(path, "/home/u/.elan/toolchains") == expected, (
        f"sysroot-last path should be reordered; got {path!r}")
    # 3. multiple sysroot entries (e.g. multi-toolchain) -> all sysroots first.
    sysroot2 = "/home/u/.elan/toolchains/v4.34.0-rc1/lib/lean"
    path = f"{pkg}:{sysroot}:{other}:{sysroot2}"
    expected = f"{sysroot}:{sysroot2}:{pkg}:{other}"
    assert _reorder_lean_path_drvfs_first(path, "/home/u/.elan/toolchains") == expected, (
        f"multi-sysroot path should have all sysroots first; got {path!r}")
    # 4. no sysroot at all -> no-op.
    path = f"{pkg}:{other}"
    assert _reorder_lean_path_drvfs_first(path, "/home/u/.elan/toolchains") == path, (
        "path without sysroot should be unchanged")
    # 5. empty input -> no-op.
    assert _reorder_lean_path_drvfs_first("", "/home/u/.elan/toolchains") == "", (
        "empty path should be unchanged")
    # 6. elan_root with trailing slash mismatch should not match.
    pkg2 = "/home/u/.elan/toolchains-other/x/lib/lean"  # not under elan/toolchains
    path = f"{pkg2}:{pkg}"
    assert _reorder_lean_path_drvfs_first(path, "/home/u/.elan/toolchains") == path, (
        "non-elan-toolchain-named path should not be moved")
    # 7-13: _repl_for_toolchain table sync (#18120) — pure functions, no WSL.
    # 7. extraction is formatting-independent (repo payload vs frozen-fork layout).
    repo_layout = ("    def _repl_for_toolchain(lake_root):\n"
                   "        mapping = {'v4.30.0-rc2': 'repl-4.30.0-rc2',\n"
                   "                   'v4.32.1': 'repl-4.32.1'}\n")
    fork_layout = ("    def _repl_for_toolchain(lake_root):\n"
                   "        mapping = {'v4.30.0-rc2': 'repl-4.30.0-rc2', 'v4.32.1': 'repl-4.32.1'}\n")
    assert _extract_repl_table(repo_layout) == _extract_repl_table(fork_layout) == {
        "v4.30.0-rc2": "repl-4.30.0-rc2", "v4.32.1": "repl-4.32.1"}, (
        "extraction must not depend on entry layout")
    # 8. upstream repl.py (no _repl_for_toolchain) -> None (fail-closed signal).
    assert _extract_repl_table("class Lean4ReplWrapper:\n    pass\n") is None, (
        "upstream source must extract as None")
    # 9. drift: missing / extra / changed classes.
    drift = _repl_table_drift({"v4.32.1": "repl-4.32.1", "v4.33.0": "repl-WRONG"},
                              {"v4.32.1": "repl-4.32.1", "v4.33.0": "repl-4.33.0",
                               "v4.34.0-rc1": "repl-4.34.0-rc1"})
    assert drift["missing"] == ["v4.34.0-rc1"] and drift["extra"] == [] and (
        drift["changed"] == {"v4.33.0": ("repl-WRONG", "repl-4.33.0")}), (
        f"drift classes wrong: {drift}")
    # 10. render -> extract round-trip identity.
    rendered_src = "def _repl_for_toolchain(x):\n    mapping = " + \
        _render_repl_table({"v4.32.1": "repl-4.32.1", "v4.30.0-rc2": "repl-4.30.0-rc2"}) + "\n"
    assert _extract_repl_table(rendered_src) == {
        "v4.30.0-rc2": "repl-4.30.0-rc2", "v4.32.1": "repl-4.32.1"}, (
        "rendered literal must re-extract to the same table")
    # 11. sync on a stale fork-layout file: replaces only the literal, adds the tag.
    stale = ("    def _repl_for_toolchain(lake_root):\n"
             "        mapping = {'v4.32.1': 'repl-4.32.1'}\n"
             "        return mapping.get(lake_root, 'repl')\n")
    new_src, d = _apply_repl_table_sync(stale, {"v4.32.1": "repl-4.32.1",
                                                "v4.34.0-rc1": "repl-4.34.0-rc1"})
    assert new_src is not None and d["missing"] == ["v4.34.0-rc1"], "sync must report the add"
    assert _extract_repl_table(new_src) == {"v4.32.1": "repl-4.32.1",
                                            "v4.34.0-rc1": "repl-4.34.0-rc1"}, (
        "synced source must carry the full reference table")
    assert "return mapping.get(lake_root, 'repl')" in new_src, (
        "sync must not touch code outside the literal")
    # 12. sync is idempotent: in-sync source comes back untouched.
    same = "def _repl_for_toolchain(x):\n    mapping = " + \
        _render_repl_table({"v4.32.1": "repl-4.32.1"}) + "\n"
    out2, d2 = _apply_repl_table_sync(same, {"v4.32.1": "repl-4.32.1"})
    assert out2 == same and not (d2["missing"] or d2["extra"] or d2["changed"]), (
        "in-sync source must be a no-op")
    # 13. fail-closed: no mapping literal anywhere -> None, never a write.
    out3, d3 = _apply_repl_table_sync("print('upstream')\n", {"v4.32.1": "repl-4.32.1"})
    assert out3 is None and d3["missing"] == ["v4.32.1"], (
        "upstream source must fail closed")
    print("test: 6/6 PASS (_reorder_lean_path_drvfs_first)")
    print("test: 7/7 PASS (_extract_repl_table/_repl_table_drift/"
          "_render_repl_table/_apply_repl_table_sync)")
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("command", nargs="?",
                    choices=["install", "status", "patch", "sync-repl-table", "build-repl", "test"],
                    default="status")
    ap.add_argument("tag", nargs="?", help="toolchain tag for build-repl (e.g. v4.30.0-rc2)")
    ap.add_argument("--check", action="store_true", help="alias for status")
    ap.add_argument("--default", action="store_true",
                    help="build-repl: also install as ~/.elan/bin/repl (kernel default)")
    args = ap.parse_args()
    if args.check or args.command == "status":
        return cmd_status()
    if args.command == "install":
        return cmd_install()
    if args.command == "patch":
        return cmd_patch()
    if args.command == "sync-repl-table":
        return cmd_sync_repl_table()
    if args.command == "build-repl":
        if not args.tag:
            print("ERROR: build-repl requires a tag", file=sys.stderr)
            return 1
        return cmd_build_repl(args.tag, default=args.default)
    if args.command == "test":
        return cmd_test()
    return 0


if __name__ == "__main__":
    sys.exit(main())
