"""Ratchet gate: notebook kernel and float-format drift between base and PR.

Issue context (c.559, derived from PR #16043 investigation 2026-09-14):
A notebook can be re-executed under a different Python kernel or NumPy
version than its base reference, producing byte-different outputs even
when the underlying computation is mathematically equivalent. Three
classes observed:

  - Kernel change: ``metadata.kernelspec.name`` or
    ``metadata.language_info.version`` differs at major.minor level
    (Python 3.10.11 -> 3.13.3, 3.11 -> 3.13). Patch-only drift (3.13.3 ->
    3.13.15) is NOT flagged: the venv patch evolves under the canonical
    interpreter and never changes repr() semantics (#17371). Outputs may
    format ``repr(np.float64(0.9999999999999999))`` instead
    of ``[1.0, 1.0, ...]`` even when the cell computes the same values.
  - Float format drift: NumPy 1.x prints ``[1.0, 1.0, 1.0]``; NumPy 2.x
    prints ``[1.0, 0.9999999999999999, 1.0]``. The values are within
    1 ULP; since #19961 (bruit assume, cf ``_signatures_equivalent``)
    such numerically-equal-within-1-ULP signatures are NOT drift. Only a
    numeric difference beyond the tolerance -- or a signature that does
    not parse as numbers and differs textually -- is flagged.
  - Machine path leak: a fresh execution under a different temp dir
    injects new ``MACHINE_PATH`` strings (covered by
    check_output_failure_text.py, not this gate).

This gate compares each changed notebook's kernel/version metadata
between base and HEAD, plus a sampled output signature for cells whose
output text looks float-array-shaped. A regression in either
(category A: kernel change with no documented acceptance, category B:
float-format drift with no explanation in the PR body) fails the run.

Usage:
    python check_kernel_drift.py <base-ref> [--json] [--explain]

    base-ref    base branch ref (CI: origin/<base branch>). Resolved
                internally to merge-base(base-ref, HEAD) so a branch
                behind its base is judged on its own diff only.

Exclusions: same as check_papermill_ratchet.py (notebooks in
.ipynb_checkpoints/, /archive/, /_output/, /research/).

Exit code: 0 if no regression, 1 if at least one changed notebook
shows kernel or float-format drift without a documented justification.

A base that cannot be READ is not a drift: the organ refetches the base
branch once and retries (#15553 partial-clone race), and if the base is
still unreadable it fails closed with an ``[infrastructure][fail-closed]``
marker and a JSON document carrying ``infrastructure_error`` -- so a
reader of the rollup never mistakes it for a measured regression.
"""

import argparse
import json
import math
import os
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

EXCLUDE_MARKERS = ("/.ipynb_checkpoints/", "/archive/", "/_output/",
                   "/research/")


def git(*args, cwd=None):
    """Run a git command. Fail-closed: raise RuntimeError on OSError.

    Returns stdout string on success, raises on subprocess failure.
    Empty stdout is a valid result and is returned as ''.
    """
    try:
        out = subprocess.run(["git", *args], cwd=cwd, capture_output=True,
                             encoding="utf-8", errors="replace", check=False)
    except OSError as e:
        raise RuntimeError(f"git subprocess failed: {e}") from e
    if out.returncode != 0:
        raise RuntimeError(
            f"git {args!r} failed (rc={out.returncode}): "
            f"{out.stderr.strip()[:200] if out.stderr else '<no stderr>'}"
        )
    return out.stdout


def git_fail_closed(*args, cwd=None):
    """Wrapper used in tests: same as git() but explicitly named for clarity."""
    return git(*args, cwd=cwd)


class BaseUnreadable(RuntimeError):
    """The base ref could not be read: an infrastructure failure, not a drift.

    Kept distinct from a drift verdict on purpose. #15553 (fast-lane organ)
    established that an organ failing to READ its input must not look, in the
    rollup, like an organ that MEASURED a defect -- the reader would chase a
    content regression that does not exist.
    """


def _refetch_base(base, cwd=None):
    """Refetch a remote-tracking base into the exact ref merge-base reads.

    Partial-clone race (#15553, measured here 2026-10-09): the checkout is
    ``fetch-depth: 0`` + ``filter: blob:none``, and ``main`` can advance while
    the job runs. The promisor then cannot resolve a commit that IS on the
    remote, and ``merge-base`` fails with ``Could not read <sha>`` on an
    otherwise readable base. An explicit refetch of the branch repairs the
    race before the organ concludes anything.
    """
    prefix = "origin/"
    if not base.startswith(prefix) or base == prefix:
        return subprocess.CompletedProcess(
            args=[], returncode=2, stdout="",
            stderr=f"base ref non refetchable: {base!r}",
        )
    branch = base[len(prefix):]
    refspec = f"+refs/heads/{branch}:refs/remotes/origin/{branch}"
    return subprocess.run(
        ["git", "fetch", "--refetch", "--filter=blob:none", "origin", refspec],
        cwd=cwd, capture_output=True, text=True,
        encoding="utf-8", errors="replace",
    )


def resolve_base(base, cwd=None):
    try:
        out = git("merge-base", base, "HEAD", cwd=cwd)
    except RuntimeError as first:
        print("[kernel-drift][infrastructure] merge-base illisible contre "
              f"{base}; refetch cible de la branche de base", file=sys.stderr)
        fetched = _refetch_base(base, cwd=cwd)
        if fetched.returncode != 0:
            raise BaseUnreadable(
                "[kernel-drift][infrastructure][fail-closed] base illisible; "
                "aucun verdict de drift n'a ete calcule. "
                f"base={base}; erreur initiale={first}; "
                f"refetch={fetched.stderr.strip() or f'exit {fetched.returncode}'}"
            ) from first
        try:
            out = git("merge-base", base, "HEAD", cwd=cwd)
        except RuntimeError as second:
            raise BaseUnreadable(
                "[kernel-drift][infrastructure][fail-closed] base toujours "
                "illisible apres refetch; aucun verdict de drift n'a ete "
                f"calcule. base={base}; erreur initiale={first}; "
                f"nouvelle lecture={second}"
            ) from second
        print("[kernel-drift][infrastructure] base reparee; merge-base relu "
              "apres refetch cible", file=sys.stderr)
    return out.strip() if out.strip() else base


def changed_notebooks(base, cwd=None):
    out = git("diff", "--name-only", "--diff-filter=ACMR",
              base, "HEAD", "--", "*.ipynb", cwd=cwd)
    paths = []
    for line in out.splitlines():
        posix = line.strip().replace("\\", "/")
        if posix and not any(m in f"/{posix}" for m in EXCLUDE_MARKERS):
            paths.append(posix)
    return sorted(paths)


def read_blob(commit_ref, nb_path, cwd=None):
    """Read a notebook JSON from a git blob (returns None if absent).

    Returns None ONLY when the blob doesn't exist (legitimately absent path).
    Raises RuntimeError if git itself fails (fail-closed per defect 4).
    """
    try:
        out = git("show", f"{commit_ref}:{nb_path}", cwd=cwd)
    except RuntimeError as e:
        if "exists on disk, but not in" in str(e) or "does not exist" in str(e) or "bad revision" in str(e):
            return None
        raise
    if not out:
        return None
    try:
        return json.loads(out)
    except json.JSONDecodeError:
        return None


# Matches an array-shaped float repr in stdout output: "[1.0, 0.9999..., 1.0]"
# or "array([...])" — anything that looks like NumPy / Python printing a
# homogeneous float list. The regex is intentionally loose: we only need a
# canonical signature per cell to detect format drift, not a parser.
FLOAT_ARRAY_RE = re.compile(
    r"[\[\(]\s*"
    r"-?\d+\.\d+(?:[eE][+-]?\d+)?j?\s*"
    r"(?:,\s*-?\d+\.\d+(?:[eE][+-]?\d+)?j?\s*){1,}"
    r"[\]\)]"
)


def _flatten_text(value):
    """Normalize a text field (string OR list of strings) to a single string.

    Defect 5 (PR #16082 review): corpus real shows 1409/1430 cells have
    text/plain as a LIST of strings (Papermill artifact). Old code did
    `''.join(...)` which raised TypeError. We accept both shapes.
    """
    if isinstance(value, list):
        return "".join(str(s) for s in value)
    return str(value)


def float_signatures(nb):
    """For each code cell, return a tuple of float-array signatures.

    Two cells with identical signatures, modulo whitespace and rounding
    within 1 ULP, are considered equivalent for drift detection. We do
    not attempt numerical comparison (that is a different organ, see
    check_output_collapse.py and check_output_failure_text.py) — this
    gate only flags textual-shape changes that are characteristic of a
    NumPy 1.x vs 2.x repr change or a cmath exp precision drift.

    Defect 5 fix: text/plain can be a string OR a list of strings.
    """
    sigs = []
    for cell in nb.get("cells", []):
        if cell.get("cell_type") != "code":
            continue
        text_parts = []
        for out in cell.get("outputs", []):
            if "text" in out:
                text_parts.append(_flatten_text(out["text"]))
            elif "data" in out and "text/plain" in out["data"]:
                text_parts.append(_flatten_text(out["data"]["text/plain"]))
        joined = "".join(text_parts)
        sigs.append(tuple(FLOAT_ARRAY_RE.findall(joined)))
    return tuple(sigs)


def _parse_array_values(array_text):
    """Parse one matched array string into a tuple of numbers.

    Returns None when ANY token fails to parse (fail-closed: the caller
    then falls back to textual comparison, never to a false equivalence).
    Complex tokens (trailing ``j``) are parsed with ``complex()``.
    """
    inner = array_text.strip().lstrip("[(").rstrip("])")
    values = []
    for token in inner.split(","):
        token = token.strip()
        try:
            values.append(complex(token) if token.endswith("j") else float(token))
        except ValueError:
            return None
    return tuple(values)


def _within_ulp(a, b, max_ulp=1):
    """Vrai quand a et b sont egaux a ``max_ulp`` ULP pres (#19961).

    Reels : marche ``nextafter`` bornee a ``max_ulp`` pas (exactitude de la
    mesure, pas une approximation ``isclose``). Complexes : chaque partie
    dans la meme tolerance. NaN == NaN est accepte (deux executions du meme
    calcul non-branche produisent NaN toutes deux) ; infini exige l'egalite
    exacte et le meme signe.
    """
    if isinstance(a, complex) or isinstance(b, complex):
        try:
            ar, ai = (a.real, a.imag) if isinstance(a, complex) else (a, 0.0)
            br, bi = (b.real, b.imag) if isinstance(b, complex) else (b, 0.0)
        except AttributeError:
            return False
        return (_within_ulp(ar, br, max_ulp) and _within_ulp(ai, bi, max_ulp))
    if math.isnan(a) and math.isnan(b):
        return True
    if math.isnan(a) or math.isnan(b):
        return False
    if math.isinf(a) or math.isinf(b):
        return a == b
    if a == b:
        return True
    lo, hi = (a, b) if a < b else (b, a)
    # La marche nextafter couvre aussi les sous-normaux depuis 0.0 :
    # nextafter(0.0, inf) est le plus petit sous-normal, et chaque pas
    # suivant avance d'un sous-normal -- pas de cas special.
    current = lo
    for _ in range(max_ulp):
        current = math.nextafter(current, math.inf)
        if current >= hi:
            return True
    return current >= hi


def _signatures_equivalent(base_sig, head_sig, max_ulp=1):
    """Compare deux signatures float au sens de la decision #19961.

    Bruit assume : deux signatures dont les valeurs sont egales a 1 ULP pres
    ne sont PAS un drift -- c'est l'extension a la signature float de la
    doctrine #17371 (le drift de patch ne change pas la semantique, les
    re-execs cross-machines de la flotte produisent des byte-repr differents
    a 1 ULP pres, mesure #19961 : base 3.13.13 vs head 3.13.3 sur ICT-23).
    Un token qui ne parse pas retombe sur l'egalite TEXTUELLE de la paire
    (fail-closed) : on ne fabrique jamais une equivalence non mesuree.
    """
    if len(base_sig) != len(head_sig):
        return False
    for b_text, h_text in zip(base_sig, head_sig):
        if b_text == h_text:
            continue
        b_vals = _parse_array_values(b_text)
        h_vals = _parse_array_values(h_text)
        if b_vals is None or h_vals is None:
            return False
        if len(b_vals) != len(h_vals):
            return False
        if not all(_within_ulp(b, h, max_ulp) for b, h in zip(b_vals, h_vals)):
            return False
    return True


def kernel_info(nb):
    meta = nb.get("metadata", {})
    return {
        "kernelspec_name": meta.get("kernelspec", {}).get("name", ""),
        "language_version": meta.get("language_info", {}).get("version", ""),
        "kernelspec_display": meta.get("kernelspec", {}).get("display_name", ""),
    }


def _version_prefix(version):
    """Truncate a language version to its major.minor components (#17371).

    Patch-level drift (3.13.3 -> 3.13.15) is systemic: the project venv
    evolves under the lane's canonical interpreter, so any fresh
    re-execution of a notebook whose base stamp is older drifts on the
    patch component alone (measured 2026-09-22 on #16858: base 3.13.3,
    venv 3.13.15, 10/10 cells, 0 error). A patch bump does not change
    repr() semantics; a kernel swap or a major/minor change does. Versions
    with fewer than two components ("", "3") are returned verbatim. A JSON
    ``"version": null`` (valid nbformat, which the ``.get("version", "")``
    default does not cover) is read as the empty version rather than
    crashing: the guard must emit a finding, never a traceback.
    """
    text = str(version or "")
    parts = text.split(".")
    return ".".join(parts[:2]) if len(parts) >= 2 else text


def diff_kernel(base_info, head_info):
    """Return a list of human-readable kernel-version drift strings.

    #17371: ``language_info.version`` is compared at major.minor level —
    patch-only drift is not a kernel regression. The full versions are
    still shown in the message for diagnosis.
    """
    diffs = []
    base_ver = _version_prefix(base_info["language_version"])
    head_ver = _version_prefix(head_info["language_version"])
    if base_ver != head_ver:
        diffs.append(
            f"language_info.version: {base_info['language_version']!r} -> "
            f"{head_info['language_version']!r} "
            f"(major.minor {base_ver} -> {head_ver})"
        )
    if base_info["kernelspec_name"] != head_info["kernelspec_name"]:
        diffs.append(
            f"kernelspec.name: {base_info['kernelspec_name']!r} -> "
            f"{head_info['kernelspec_name']!r}"
        )
    return diffs


# Transitions de version pre-acceptees (#17679, option 1, decision
# coordinateur 2026-09-26) : la derive va dans le sens du canon decide --
# ce n'est pas une regression, pas plus qu'une derive de patch (#17371).
# La DIRECTION porte l'acceptation : la transition inverse reste rouge.
# Portee mesuree au 2026-10-05 :
#   - C# ``.net-csharp`` : 141 notebooks a 13.0, 7 a 12.0 (#17679).
#   - Python ``python3`` (serie QC/Python) : 11 versions heterogenes
#     (3.8.10, 3.9.0, 3.10.0, 3.10.11, 3.10.19, 3.11.0, 3.11.9, 3.11.14,
#     3.11.15, 3.13.3, 3.13.7, 3.13.12, 3.13.14) ; 60 carnets ``python3`` + 2
#     ``conda-torch``.
#   - Decision duale sur le canon (coord. 2026-10-05T03:43:46Z, DM
#     msg-20261005T034346-qyldsl) : **deux canons**, pas un seul --
#     (a) **canon des algorithmes deployes sur QC Cloud = Python 3.11**,
#         documente dans ``MyIA.AI.Notebooks/QuantConnect/requirements.txt`` ;
#     (b) **canon de l'execution locale des carnets = Python 3.13**, qui est
#         l'interpreteur de la flotte -- c'est lui qui ecrit
#         ``language_info.version`` a chaque rejeu.
#     Les deux roles sont separes par design ; la migration historique
#     ``3.10 -> 3.11`` reste couverte, et la convergence future
#     ``3.11 -> 3.13`` aussi, plus le saut direct ``3.10 -> 3.13``
#     (cas fondateur de #19181, PR #19163 : 3.10.11 -> 3.13.3).
#     Le saut ``3.12 -> 3.13`` est couvert : ICT-47 (PainAxisDistillation)
#     sur main est a ``language_info.version = 3.12.13`` (mesure directe
#     sur le carnet, 2026-10-05), mais son kernelspec est ``py310-gpu``
#     (distinct de ``python3``), donc le tuple ``("python3", "3.12", "3.13")``
#     ne s'applique pas a ce carnet -- la table exige le meme nom de
#     kernel entre base et tete. L'entree anticipe la convergence vers
#     le canon pour un futur carnet ``python3`` a 3.12.x ; aucun carnet
#     de cette forme n'est encore mesuré sur main. Le saut
#     ``3.11 -> 3.12`` reste implicite (3.12 = release courante de
#     plusieurs carnets), mais n'est pas ajoute en l'absence d'un carnet
#     de reference ``python3`` qui le pratique.
#     Les sauts ``3.8 -> 3.13`` et ``3.9 -> 3.13`` sont **exclus** : la
#     serie ICT (#5635, ICT-24) reste sur ``requires-python >=3.9,<3.10``
#     (contrainte ``pyphi==1.2.0``, mesure #19160), et le cliquet n'a
#     pas de scope par chemin/série -- ajouter ces transitions ferait
#     passer vert un carnet ICT rejoue par erreur sous 3.13 (reserve
#     Hermes PRR_kwDOH2Odns8AAAABQnPfEQ, 2026-10-05). Les 2 rescapes
#     ``3.8.10`` et ``3.9.0`` (1 carnet chacun, mesure body) sont
#     traites au cas par cas.
# La transition inverse (3.13 -> 3.12, 3.13 -> 3.11, 3.11 -> 3.10,
# 3.13 -> 3.10) reste rouge.
CANONICAL_LANGUAGE_TRANSITIONS = {
    (".net-csharp", "12.0", "13.0"):
        "C# 12.0 -> 13.0 : convergence vers le canon C# 13.0 (#17679)",
    ("python3", "3.10", "3.11"):
        "Python 3.10 -> 3.11 : convergence vers le canon QC/Python 3.11 (#19181)",
    ("python3", "3.11", "3.13"):
        "Python 3.11 -> 3.13 : convergence vers le canon d'execution 3.13 (#19181)",
    ("python3", "3.10", "3.13"):
        "Python 3.10 -> 3.13 : convergence directe vers le canon d'execution 3.13 (#19181, cas fondateur)",
    ("python3", "3.12", "3.13"):
        "Python 3.12 -> 3.13 : convergence vers le canon d'execution 3.13 (#19181, anticipation -- pas de carnet `python3` a 3.12 mesure)",
}


def accepted_canonical_transition(base_info, head_info):
    """Vrai quand la derive de version EST une transition canon (#17679).

    Exige le meme ``kernelspec.name`` (un changement de kernel reste rouge
    par construction) et la direction exacte de la table : ``12.0 ->
    13.0`` est accepte, ``13.0 -> 12.0`` ne l'est pas.
    """
    if base_info["kernelspec_name"] != head_info["kernelspec_name"]:
        return False
    key = (base_info["kernelspec_name"],
           _version_prefix(base_info["language_version"]),
           _version_prefix(head_info["language_version"]))
    return key in CANONICAL_LANGUAGE_TRANSITIONS


def body_has_derive_exemption(body):
    """Defect 1: PR body contains '## Diagnostic dérive' section.

    Per acceptance of issue #15650 (point 4): cellules non touchées
    reproduisent leurs sorties - ou l'écart résiduel est expliqué par
    une section '## Diagnostic dérive' (C.4).

    Fix v2 (post-NanoClaw review #16466): regex is now case-insensitive and
    tolerates the unaccented 'derive' (covers authors who type the header
    without the accent, a common shortcut when reviewing on a non-French
    keyboard layout).

    Fix v3 (suffix form, cas vecu #17220): also tolerate a trailing
    parenthetical qualifier, e.g. '## Diagnostic derive (C.4)' -- the exact
    form used in the PR body of #17220, whose exemption silently failed to
    fire because
    the strict end-of-line anchor rejected the '(C.4)' suffix (measured
    firsthand 2026-09-21: kernel_diffs downgraded nowhere, guard red on a
    3.13.7 -> 3.13.15 patch drift that the C.4 section was documenting).
    """
    if not body:
        return False
    # Case-insensitive header, optional whitespace, optional accent on 'e',
    # optional trailing parenthetical qualifier such as '(C.4)'.
    pattern = re.compile(
        r"^##\s*Diagnostic\s*d[ée]rive(?:\s*\([^)]*\))?\s*$",
        re.MULTILINE | re.IGNORECASE,
    )
    return bool(pattern.search(body))


def _code_index_by_id(nb):
    """Build a mapping cell_id -> ordinal index for code cells only.

    PR #16466 review (NanoClaw, exact-head 637a64ca): the previous
    ``_cell_index_by_id`` walked ALL cells (markdown + code), but
    ``float_signatures`` only emits one tuple per code cell. Mixing
    those two spaces produced two pathologies at once:

      * Markdown cells appeared as drift entries because their ordinal
        in ``_cell_index_by_id`` resolved to a code cell's signature in
        ``float_signatures`` (false positive on markdown).
      * Code cells with shifted ordinals (after a markdown insertion)
        compared their base/head signatures against the wrong code cell
        (true code drift missed, markdown phantom listed instead).

    Fix: walk code cells only, build the id->code-index map in the same
    order as ``float_signatures`` consumes them. New markdown cells
    (markdown present in head but absent in base) are simply absent from
    ``base_ids`` and never enter the diff set; only new code cells
    (``head_ids - base_ids``) are reported as added cells.

    Defect 2 (PR #16082 review) original ordinal-vs-id alignment is
    preserved: when at least one notebook has any id, alignment is by
    id within the code-cell space; when neither notebook carries ids,
    we fall back to ordinal (``_diff_signatures_ordinal``).
    """
    result = {}
    code_idx = 0
    for cell in nb.get("cells", []):
        if cell.get("cell_type") != "code":
            continue
        cid = cell.get("id") or None
        if cid:
            result[cid] = code_idx
        code_idx += 1
    return result


def diff_signatures(base_sig, head_sig, base_nb=None, head_nb=None):
    """Return a list of cell identifiers whose float signature changed.

    Defect 2 fix: aligns by code-cell id when notebooks are provided
    (stable under insertions of either markdown or new code cells);
    falls back to ordinal otherwise (legacy). Returns a list of ids
    (str) when aligned by id, or ints (legacy).

    PR #16466 review (NanoClaw, exact-head 637a64ca): the id->index map
    is built from CODE cells only (``_code_index_by_id``), so the
    ordinals match ``float_signatures``' own code-only ordinals.
    Markdown cells are invisible to this map: they neither drift
    themselves nor shift code cells' indices.

    #17232: added code cells are no longer reported unconditionally --
    only those carrying a non-empty float signature are (see the loop in
    the id-aligned branch below).
    """
    # If we have notebooks with cell ids, align by id
    if base_nb is not None and head_nb is not None:
        base_ids = _code_index_by_id(base_nb)
        head_ids = _code_index_by_id(head_nb)
        # Only consider cells present in BOTH (intersection), plus
        # report new code cells (in head but not base) as drifts.
        common = set(base_ids.keys()) & set(head_ids.keys())
        if not common:
            # No common ids (either both legacy/no-id notebooks, or only
            # one side has ids and the other has none) -> fall back to
            # ordinal (legacy code cells). Fix c.681: cover the case
            # where base_ids and head_ids are both empty (notebooks
            # without any cell ids) -- jsboige CONCERNS d008d8b8fa.
            return _diff_signatures_ordinal(base_sig, head_sig)
        diffs = []
        # Common code cells: compare signatures by code-ordinal
        for cid in sorted(common):
            b_idx = base_ids[cid]
            h_idx = head_ids[cid]
            b = base_sig[b_idx] if b_idx < len(base_sig) else ()
            h = head_sig[h_idx] if h_idx < len(head_sig) else ()
            if b != h and not _signatures_equivalent(b, h):
                diffs.append(cid)
        # Added code cells (only in head), reported ONLY when they actually
        # carry a float-array signature (#17232). An added cell with no
        # signature cannot be a float-repr drift, and reporting it
        # unconditionally made papermill's `injected-parameters` cell look
        # like one: papermill replaces that cell on every re-execution and
        # nbformat 4.5 hands the replacement a fresh cell id, so the
        # (one id removed, one id added) pair is the normal fingerprint of a
        # re-execution -- measured on PR #17145, where the added cell had 0
        # outputs and every common cell had an identical signature.
        for cid in sorted(set(head_ids.keys()) - set(base_ids.keys())):
            h_idx = head_ids[cid]
            if h_idx < len(head_sig) and head_sig[h_idx]:
                diffs.append(cid)
        return diffs
    return _diff_signatures_ordinal(base_sig, head_sig)


def _diff_signatures_ordinal(base_sig, head_sig):
    """Legacy ordinal alignment: returns int indices."""
    diffs = []
    n = max(len(base_sig), len(head_sig))
    for i in range(n):
        b = base_sig[i] if i < len(base_sig) else ()
        h = head_sig[i] if i < len(head_sig) else ()
        if b != h and not _signatures_equivalent(b, h):
            diffs.append(i)
    return diffs


# Artefacts qui portent un environnement EPINGLE pour une serie. pyproject.toml
# d'abord : il porte l'intention (requires-python, dependances) la ou un
# requirements.txt peut n'etre qu'une liste d'install.
_ENV_ARTIFACT_NAMES = ("pyproject.toml", "requirements.txt")

# Niveaux remontes depuis le dossier du notebook. Borne volontaire : au-dela on
# nommerait un artefact qui ne couvre plus la serie (racine du depot), c'est-a-
# dire un chemin qui a l'apparence d'une reponse et n'en est pas une.
_ENV_WALK_LEVELS = 3

_REQUIRES_PYTHON_RE = re.compile(r"""requires-python\s*=\s*["']([^"']+)["']""")
_NUMPY_PIN_RE = re.compile(r"numpy\s*([<>=!~][0-9A-Za-z.,<>=!~*]*)")


def canonical_env_hint(nb_path, root="."):
    """Nomme l'environnement epingle qui couvre ce notebook, s'il existe (#17185).

    Le garde nommait les CAUSES du drift (« un autre interpreteur, 3.11 ->
    3.13 », « NumPy 1.x -> 2.x ») sans jamais dire OU est l'environnement a
    rejouer. Pour une serie qui epingle le sien, le verdict renvoyait donc la
    lane a sa propre introspection : elle re-executait avec son env local, ce
    qui reproduisait exactement le drift signale. Le constat de #17185 impute
    ce drift a une absence d'env canonique -- la serie ICT en a un, epingle et
    documente (cf `IIT/ICT-Series/pyproject.toml`) ; ce qui manquait est le
    POINTEUR vers lui au moment ou la lane lit le verdict.

    Rend un dict ``{artifact, requires_python?, numpy_pin?}``, ou None quand
    aucun artefact n'est trouve : l'absence est une information, pas un silence
    a combler par un chemin suppose.
    """
    parents = [p for p in Path(nb_path).parents if p.as_posix() != "."]
    for parent in parents[:_ENV_WALK_LEVELS]:
        for name in _ENV_ARTIFACT_NAMES:
            rel = parent / name
            try:
                text = (Path(root) / rel).read_text(encoding="utf-8",
                                                    errors="replace")
            except OSError:
                continue
            hint = {"artifact": rel.as_posix()}
            requires_python = _REQUIRES_PYTHON_RE.search(text)
            if requires_python:
                hint["requires_python"] = requires_python.group(1)
            numpy_pin = _NUMPY_PIN_RE.search(text)
            if numpy_pin:
                hint["numpy_pin"] = f"numpy{numpy_pin.group(1)}"
            return hint
    return None


def _run(args_obj):
    """Core logic shared between CLI and tests. Returns dict or prints."""
    try:
        base = resolve_base(args_obj.base_ref)
    except BaseUnreadable as e:
        # Fail-closed, but WITHOUT the empty artifact that made this class
        # indistinguishable from a drift verdict in the rollup: the JSON
        # document is emitted and carries the cause.
        return {"findings": [], "base": args_obj.base_ref,
                "body_exempts": False, "infrastructure_error": str(e)}
    notebooks = changed_notebooks(base)

    # Defect 1: read PR body for exemption
    pr_body = ""
    try:
        from pathlib import Path
        # Path is taken from env var or .git/PR_BODY
        pr_body_path = Path(os.environ.get("PR_BODY_FILE", "/tmp/pr_body"))
        if pr_body_path.exists():
            pr_body = pr_body_path.read_text(encoding="utf-8", errors="replace")
    except (ImportError, OSError):
        pass

    body_exempts = body_has_derive_exemption(pr_body)

    findings = []
    for nb_path in notebooks:
        base_nb = read_blob(base, nb_path)
        head_nb = read_blob("HEAD", nb_path)
        if base_nb is None or head_nb is None:
            continue
        base_kernel = kernel_info(base_nb)
        head_kernel = kernel_info(head_nb)
        base_sig = float_signatures(base_nb)
        head_sig = float_signatures(head_nb)
        kernel_diffs = diff_kernel(base_kernel, head_kernel)
        # #17679 : la transition canon C# 12.0 -> 13.0 est attendue (option
        # 1, decision coordinateur) -- seule, elle ne fait pas finding.
        canonical_transition = False
        if kernel_diffs and accepted_canonical_transition(base_kernel,
                                                          head_kernel):
            canonical_transition = True
            kernel_diffs = []
        # Defect 2: pass notebooks for id-based alignment
        sig_diffs = diff_signatures(base_sig, head_sig,
                                     base_nb=base_nb, head_nb=head_nb)
        if kernel_diffs or sig_diffs:
            finding = {
                "notebook": nb_path,
                "kernel_diffs": kernel_diffs,
                "signature_drift_cells": sig_diffs,
                "base_kernel": base_kernel,
                "head_kernel": head_kernel,
                "body_exemption": body_exempts,
                "canonical_transition": canonical_transition,
            }
            # Defect 1: if body exempts and drift is documented, downgrade
            if body_exempts and (kernel_diffs or sig_diffs):
                finding["acknowledged"] = True
                finding["acknowledgment_reason"] = (
                    "PR body contains '## Diagnostic dérive' (C.4 exemption)"
                )
            if args_obj.explain:
                causes = []
                if kernel_diffs:
                    causes.append(
                        "kernel or language_version changed between base and "
                        "HEAD; re-execution may have used a different Python "
                        "interpreter (3.11 -> 3.13) which alters repr() for "
                        "floating-point values"
                    )
                if sig_diffs:
                    causes.append(
                        f"{len(sig_diffs)} code cells show float-array repr "
                        "drift consistent with a NumPy 1.x -> 2.x upgrade or "
                        "a cmath precision change; values are within 1 ULP "
                        "but byte-text differs"
                    )
                # #17185 : les deux causes ci-dessus nomment le MECANISME du
                # drift, aucune ne dit OU est l'environnement a rejouer. Une
                # serie qui epingle le sien obtient ici le pointeur vers son
                # artefact, pour que « aligner l'env » ne se lise pas comme une
                # introspection a faire soi-meme.
                env_hint = canonical_env_hint(nb_path)
                if env_hint:
                    detail = [f"the series pins a canonical environment at "
                              f"`{env_hint['artifact']}`"]
                    if env_hint.get("requires_python"):
                        detail.append(
                            f"requires-python {env_hint['requires_python']}")
                    if env_hint.get("numpy_pin"):
                        detail.append(env_hint["numpy_pin"])
                    causes.append(
                        " / ".join(detail)
                        + "; re-executing under that environment keeps the "
                          "committed repr stable, whereas a local interpreter "
                          "reproduces this drift"
                    )
                finding["probable_causes"] = causes
            findings.append(finding)

    return {"findings": findings, "base": base, "body_exempts": body_exempts}


def _infrastructure_rc(result, as_json):
    """Emit the infrastructure artifact and return the fail-closed rc.

    Returns None when the run measured something -- the caller then applies
    the drift verdict as usual. The JSON document is printed even on failure:
    an empty artifact is exactly what made this class unreadable in the
    rollup (#15553 acceptance 2).
    """
    err = result.get("infrastructure_error")
    if not err:
        return None
    if as_json:
        print(json.dumps(result, indent=2))
    print(err, file=sys.stderr)
    return 1


def main():
    """Defect 3 fix: parse argv once, build args, call _run ONCE."""
    p = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    p.add_argument("base_ref")
    p.add_argument("--json", action="store_true",
                   help="emit findings as JSON on stdout")
    p.add_argument("--explain", action="store_true",
                   help="annotate each finding with probable cause")
    args = p.parse_args()

    result = _run(args)
    infra_rc = _infrastructure_rc(result, args.json)
    if infra_rc is not None:
        return infra_rc
    findings = result["findings"]

    if args.json:
        # Defect 3: emit a SINGLE JSON document
        print(json.dumps(result, indent=2))
        return 0 if not findings or all(f.get("acknowledged") for f in findings) else 1
    else:
        if not findings:
            print(f"OK: 0 kernel-drift regression across "
                  f"{len(changed_notebooks(result['base']))} changed notebooks "
                  f"(base={result['base']}).")
            return 0
        print(f"FAIL: kernel-drift regression in {len(findings)} notebook(s):",
              file=sys.stderr)
        for f in findings:
            tag = " [ACKNOWLEDGED via ## Diagnostic dérive]" if f.get("acknowledged") else ""
            print(f"  {f['notebook']}{tag}", file=sys.stderr)
            for k in f["kernel_diffs"]:
                print(f"    - {k}", file=sys.stderr)
            if f["signature_drift_cells"]:
                print(f"    - float-signature drift on cells: "
                      f"{f['signature_drift_cells']}", file=sys.stderr)
        return 1


def main_with_args(argv):
    """Entry point for tests: parse argv as a list, run ONCE, return rc + result.

    Defect 3 fix verification: this function calls _run() exactly once and
    prints a single JSON document when --json is set.
    """
    p = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    p.add_argument("base_ref")
    p.add_argument("--json", action="store_true")
    p.add_argument("--explain", action="store_true")
    args = p.parse_args(argv)
    result = _run(args)
    infra_rc = _infrastructure_rc(result, args.json)
    if infra_rc is not None:
        return infra_rc
    findings = result["findings"]
    if args.json:
        # Single JSON emission
        print(json.dumps(result, indent=2))
        return 0 if not findings or all(f.get("acknowledged") for f in findings) else 1
    if not findings:
        print(f"OK: 0 kernel-drift regression across 0 changed notebooks (base={result['base']}).")
        return 0
    print(f"FAIL: {len(findings)} drift(s)", file=sys.stderr)
    return 1


if __name__ == "__main__":
    sys.exit(main())
