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
    python scripts/lean/setup_native_lean4_import.py build-repl v4.30.0-rc2
    python scripts/lean/setup_native_lean4_import.py --check

Probe evidence (2026-06, sensitivity_lean): ``import Sensitivity`` +
``#check huang_degree_theorem`` in a lean4-wsl kernel render the real signature,
``#print axioms`` -> [propext, Classical.choice, Quot.sound] (0 sorry). See
docs/reference/wsl-kernels-detail.md.
"""

import argparse
import re
import shutil
import subprocess
import sys
from pathlib import Path

WSL_DISTRO = "Ubuntu"
# Canonical matched-REPL install paths (one per toolchain tag).
REPL_TOOLCHAIN_TAGS = {
    "v4.30.0-rc2": "repl-4.30.0-rc2",
    "v4.31.0-rc1": "repl-4.31.0-rc1",
    "v4.32.0": "repl-4.32.0",
    "v4.32.1": "repl-4.32.1",
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
    """Run a command inside WSL, return CompletedProcess."""
    full = ["wsl.exe", "-d", WSL_DISTRO, "--", "bash", "-lc", cmd]
    # encoding explicite : la sortie WSL porte de l'unicode Lean (forall, mapsto).
    # text=True seul decode via la locale -> crash sur hote cp1252 (#12811).
    return subprocess.run(full, capture_output=True, text=True, timeout=timeout,
                          encoding="utf-8", errors="replace")


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
    return 0


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
    _wsl(
        f"export PATH=$HOME/.elan/bin:/usr/local/bin:/usr/bin:/bin; "
        f"mkdir -p ~/repl-build && cd ~/repl-build && "
        f"if [ ! -d repl ]; then git clone https://github.com/leanprover-community/repl.git; fi && "
        f"cd repl && git fetch --tags --force origin 2>&1 | tail -1; "
        f"git checkout {src_tag} 2>&1 | tail -1",
        timeout=300)
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
    print("test: 6/6 PASS (_reorder_lean_path_drvfs_first)")
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("command", nargs="?", choices=["install", "status", "patch", "build-repl", "test"],
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
