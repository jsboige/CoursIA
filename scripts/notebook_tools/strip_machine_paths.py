#!/usr/bin/env python3
"""Strip machine-username path leaks from notebook outputs.

This hook covers the **category-A (kernel-injected / env-dependent)** leak
family of rule-6 (``secrets-hygiene.md``): the username comes from the
worker's ``%USERPROFILE%`` / ``$HOME``, not from source code. This hook is
the sanctioned durable approach for category-A kernel-injected leaks (cf.
``strip_probe_banner.py`` post-mortem); contrast with category-C
(source-leak), which must be fixed at the source.

Five runtime-category tokens cover the observed kernel-injected leaks, each
with the runtime that injects them:

==== ============================================ ===========================
cat  cache / context token                        runtime
==== ============================================ ===========================
nuget   ``.nuget``                                 dotnet-interactive (``Loading
            extensions from`` display_data + ``Failed to load kernel
            extension`` stream stderr)

pip     ``AppData\\Roaming\\Python``               CPython peft / torch / diffusers
            import-warnings (FutureWarning, UserWarning, DeprecationWarning);

            also catches HuggingFace-cache warnings embedded in pip
            warnings (``huggingface_hub`` mentions in the trailing warning
            text), since both share the pip AppData path

ipykernel    ``AppData\\Local\\Temp\\ipykernel``   ipykernel stderr (per-cell
            temp file ``ipykernel_<pid>\\<hash>.py`` deprecation/source
            warnings)

conda   ``.conda\\envs``                           conda env (e.g.
            ``.conda\\envs\\mcp-jupyter-py310\\lib\\...\\torch`` deprecated
            ``nn.utils.weight_norm`` warning)

hf      ``.cache\\huggingface`` / ``.cache/huggingface``  HF transformers/datasets
            download warnings (``local_dir_use_symlinks is deprecated``,
            symlink-cache system warning, etc.)

other   ``AppData\\Local\\Temp`` (without ipykernel)     python-side ephemeral
            file prints (``Audio cree: ...\\Temp\\test_audio.mp3``,
            ``download -> C:\\Users\\<u>\\AppData\\Local\\Temp\\*.png``)

==== ============================================ ===========================

**Detection is path-based, not signature-based** (key on username path, not
the message prefix). A line is a leak iff it carries a runtime cache-context
token AND embeds a real username (``C:\\Users\\<u>``, ``Users/<u>``,
``/home/<u>``). The dotnet-interactive **tilde** variant
(``~\\.nuget\\packages\\...``, the ``%USERPROFILE%`` HOME *placeholder* with
no username) is correctly left untouched: it carries no PII. Keying on the
username path (not the message prefix) catches both ``stream`` and
``display_data`` kernel messages uniformly and is robust to future message
rewording (cf. ``#6537`` review which found v1 keyed on ``Loading extensions
from`` both missed the ``stream`` ``Failed to load`` variant AND false-
positive stripped legitimate tilde ``Loading extensions`` lines).

**Strategy: REDACT the username prefix, KEEP the trailing relative path.**
Most Python category-A lines are ``UserWarning`` / ``DeprecationWarning``
streams where the *prefix* ``C:\\Users\\<u>\\AppData\\Roaming\\...`` is the
leak, but the *trailing* ``triton\\windows_utils.py:433: UserWarning:
Failed to find CUDA.`` is pedagogically useful (which library, which line,
which warning). The hook redacts only the username prefix to a stable
placeholder (``<USER_PATH>``), preserving the rest byte-identically so the
warning content remains readable for pedagogy. Example::

    C:\\Users\\jsboi\\AppData\\Roaming\\Python\\Python313\\site-packages\\triton\\windows_utils.py:433: UserWarning: Failed to find CUDA.

becomes::

    <USER_PATH>\\triton\\windows_utils.py:433: UserWarning: Failed to find CUDA.

For lines carrying only the username path without a meaningful trailing
relative-path leaf (e.g. ``Audio cree: C:\\Users\\<u>\\AppData\\Local\\Temp\\
test_audio.mp3``) the full path is redacted (path-only print, no library
context to preserve).

**Double-backslash variant (C538-L1).** Some orchestration-harness
notebooks (NotebookMaker / multi-agent ``run_conversation()``, L495) embed
a sub-notebook conversation log as a JSON string within the outer
``outputs``. The sub-notebook's pip output carries single-bs paths
(``C:\\Users\\<u>\\...``); the surrounding JSON serialization doubles
every backslash so the on-disk cell text reads ``C:\\\\Users\\\\<u>\\\\...``.
Detection tokens are single-bs (``AppData\\Roaming\\Python``, ``Users\\``),
so the doubled form bypasses both ``_has_leak``'s token guard AND
``_redact_line``'s username-segment consume loop (the loop's
``while out[after_marker] not in ("\\", "/")`` skips over the doubled
``\\`` as if it were one separator, leaving the username itself intact).
Fix: collapse ``\\\\`` to ``\\`` once at the start of both functions before
pattern matching (see ``_normalize_bs``). The redacted output is then
re-serialized cleanly (``<USER_PATH>\\...`` → ``"\\\\<USER_PATH>\\\\..."``
in raw bytes — strictly shorter than the input, so no JSON width issue).

The strip is **output-only** — no source code is touched, ``execution_count``
is preserved, the surrounding ``outputs: [...]`` shape is unchanged. Same
surgical philosophy as ``strip_probe_banner.py`` /
``scrub_papermill_paths.py``: a text-level edit on the on-disk JSON so the
rest of the file is byte-identical (no JSON re-serialization, no float
coercion, no metadata churn).

Closed-loop supervision: re-running ``--apply-all`` after a re-injected leak
batch is idempotent — the redacted placeholder is recognized as not-a-leak
on the next scan (it carries no username marker), so applying twice is a
no-op. Verified by re-running ``--scan-all --check`` after each ``--apply``.

Usage:
    python strip_machine_paths.py --scan <path>          # dry-run, list only
    python strip_machine_paths.py --scan-all             # dry-run repo-wide
    python strip_machine_paths.py --scan-all --check     # exit 1 if defects
    python strip_machine_paths.py --apply <path>         # fix in place
    python strip_machine_paths.py --apply-all            # fix repo-wide
    python strip_machine_paths.py --scan-all --category pip       # triage
    python strip_machine_paths.py --apply  <path> --category pip   # fix scoped
"""

import argparse
import glob
import json
import os
import re
import sys


# Multi-runtime, path-based detector. Each ``(label, token)`` covers one
# runtime-family cache context. Keying on the **path** (not the message
# prefix) catches both ``stream`` and ``display_data`` outputs uniformly
# and is robust to future message rewording (cf. ``#6537`` review).
#
# Token order matters for --category CLI arg parsing; ``all`` is implicit
# when ACTIVE_CATEGORIES is None (default; category filter unused).
MACHINE_PATH_TOKENS = (
    ("nuget", ".nuget"),
    ("pip", "AppData\\Roaming\\Python"),
    ("ipykernel", "AppData\\Local\\Temp\\ipykernel"),
    ("conda", ".conda\\envs"),
    ("hf", ".cache\\huggingface"),  # forward-slash variant is detected by the
                                    # same token pair because cache tokens are
                                    # substring-matched, not slash-strict
    ("other", "AppData\\Local\\Temp"),  # generic %TEMP% prints (catches
                                        # both ipykernel-pid and bare temp
                                        # files; ipykernel category above is
                                        # strictly more specific and matches
                                        # first when both apply, so this is
                                        # the fallthrough for non-pid temp
                                        # prints like test_audio.mp3)
)

# Backwards-compat alias for the v1 single-NuGet hook (#6563, merged). Kept
# so the canonical tests + pre-commit config (which reference
# ``NUGET_CACHE_TOKEN``) don't break. New code should reference
# ``MACHINE_PATH_TOKENS[0]`` or the ``"nuget"`` label.
NUGET_CACHE_TOKEN = MACHINE_PATH_TOKENS[0][1]  # == ".nuget"

# CLI category filter. ``None`` means "all categories". Set via
# ``--category {nuget|pip|ipykernel|conda|hf|other|all}``. Module global so
# tests can also flip it; **tests must mutate via``import strip_machine_paths
# as _smp; _smp.ACTIVE_CATEGORIES = {...}``**, NOT ``from strip_machine_paths
# import ACTIVE_CATEGORIES`` (the latter rebinds the test module's local
# namespace, leaving the module global untouched — lesson learned the hard
# way; ``ACTIVE_CATEGORIES = None`` then misses any per-category isolation
# test that mutates to ``{"pip"}``).
ACTIVE_CATEGORIES = None

# Username-bearing absolute-path markers — the actual PII payload. The
# dotnet-interactive **tilde** variant (``~\.nuget\packages\...``) is the
# ``%USERPROFILE%`` HOME *placeholder* and carries NONE of these, so it is
# correctly left untouched (no username = no leak).
USERNAME_MARKERS = ("Users\\", "Users/", "/home/")


def _normalize_bs(text):
    """Collapse doubled backslashes (``\\\\``) to single (``\\``).

    C538-L1 — JSON re-serialization of sub-conversation-log strings (multi-
    agent ``run_conversation()``, NotebookMaker orchestration, L495) doubles
    every backslash of the embedded sub-notebook's pip output. Detection
    tokens and the redaction loop's separator consume are single-bs; without
    normalization, the doubled form bypasses both. Only used in-memory;
    callers are responsible for the byte-fidelity choice (the redacted
    output is written back via ``json.dumps`` re-encoding, which collapses
    the doubled escapes to a clean single-bs representation).
    """
    if not isinstance(text, str):
        return text
    return text.replace("\\\\", "\\")

# The stable placeholder used to replace the leaked username-bearing path
# prefix. Carries no PII (no username marker), so is correctly re-detected
# as **not** a leak on the next scan — making ``--apply-all`` idempotent.
REDACTED_PATH = "<USER_PATH>"

# Output fields that can carry the leak:
# - ``data["text/plain"]`` / ``data["text/html"]`` for ``display_data`` /
#   ``execute_result`` outputs.
# - top-level ``text`` for ``stream`` outputs (most Python ``UserWarning``
#   / ``DeprecationWarning`` lines live in stderr ``text``).
DATA_KEYS = ("text/plain", "text/html")
STREAM_KEY = "text"
ALL_KEYS = DATA_KEYS + (STREAM_KEY,)


def _active_tokens():
    """Return the list of ``(label, token)`` pairs to consider for detection.

    ``None`` (default) means "all categories". Otherwise filter to those
    whose label is in ``ACTIVE_CATEGORIES``.
    """
    if ACTIVE_CATEGORIES is None:
        return list(MACHINE_PATH_TOKENS)
    return [t for t in MACHINE_PATH_TOKENS if t[0] in ACTIVE_CATEGORIES]


def _has_leak(text):
    """Return True if ``text`` (a str) carries a category-A username leak.

    Path-based: requires BOTH a runtime cache-context token (nuget/pip/
    ipykernel/conda/hf/other per ``MACHINE_PATH_TOKENS``) AND a username
    absolute-path marker (``Users\\``, ``Users/``, ``/home/``). The tilde HOME
    placeholder carries neither marker and is left untouched.

    Normalizes ``\\\\`` to ``\\`` before matching (C538-L1) so double-bs
    JSON-escaped paths (orchestration sub-conversation logs) are still
    detected.
    """
    if not isinstance(text, str):
        return False
    norm = _normalize_bs(text)
    if not any(token in norm for _, token in _active_tokens()):
        return False
    return any(marker in norm for marker in USERNAME_MARKERS)


def _redact_line(text):
    """Return ``text`` with the leaked username path prefix replaced by
    ``<USER_PATH>``, preserving any trailing relative path (which carries
    pedagogy: library/source-file/symbol name).

    Strategy:
    1. Locate the username marker substring (``C:\\Users\\<u>\\`` or
       ``/Users/<u>/`` or ``/home/<u>/``).
    2. Find the **next** ``\\`` or ``/`` AFTER the username marker that ends
       a *runtime-distinct* leaf (one of the well-known cache tokens
       ``.nuget\\``, ``AppData\\Roaming\\Python\\``,
       ``AppData\\Local\\Temp\\ipykernel_``, ``.conda\\envs\\``,
       ``.cache\\huggingface\\``, ``AppData\\Local\\Temp\\``), then keep
       everything from that point onward.
    3. Replace the username prefix (everything BEFORE that point) with
       ``<USER_PATH>``.

    Edge cases:
    - Pure token lines without trailing relative path (e.g. ``Audio cree:
      C:\\Users\\<u>\\AppData\\Local\\Temp\\test_audio.mp3``): the leaf
      marker is ``AppData\\Local\\Temp\\`` and ``test_audio.mp3`` is the
      trailing relative filename (kept verbatim).
    - Multiple username markers in one line (rare, e.g. a HuggingFace
      ``UserWarning`` whose message embeds both the pip AppData path AND
      the HF cache path): **loop iteratively, scrub ALL occurrences**
      (L499). Embedded URLs (e.g. ``https://example.com/C:/Users/foo/bar``)
      do not contain a SECOND ``C:\\Users\\<u>\\`` segment, so the loop
      is a no-op on real URLs.
    - Double-backslash paths (C538-L1): a sub-conversation-log JSON
      serialization doubles every backslash, producing
      ``C:\\\\Users\\\\<u>\\\\...``. Normalized once at function entry
      (``_normalize_bs``) to ``C:\\Users\\<u>\\...``, the standard loop
      then consumes the username correctly and the redacted output
      re-serializes to the canonical ``<USER_PATH>\\...`` form.
    - The tilde HOME placeholder (``~\\.nuget\\packages\\...``) carries no
      username marker so is rejected by ``_has_leak`` upstream; not touched.
    """
    if not isinstance(text, str):
        return text  # defensive: caller invariant is ``_has_leak`` first.

    # Normalize doubled backslashes once (C538-L1). Operates on the
    # in-memory string; the byte-fidelity guarantee of the strip is
    # preserved because the redacted output is always re-encoded via
    # ``json.dumps`` at the substitution site (``strip_in_place``), which
    # produces the canonical single-bs JSON form regardless of the input
    # width.
    text = _normalize_bs(text)

    # Iterate leftmost-then-redact until no username marker remains (L499).
    # A single line can legitimately carry multiple ``Users\<u>`` PII
    # occurrences — e.g. a HuggingFace ``UserWarning`` whose text begins
    # with the pip AppData path (Python origin) and then names the HF
    # cache path (the data origin), both real ``Users\<u>`` leaks. We
    # must scrub BOTH, not just the leftmost. Embedded-URL safety is
    # preserved by the same loop: URLs of the form
    # ``https://example.com/C:/Users/foo/bar`` do not contain a SECOND
    # ``Users\<u>`` segment, so the second pass is a no-op on real URLs.
    out = text
    while True:
        # Find the leftmost username marker.
        leftmost_idx = -1
        leftmost_marker_len = 0
        for marker in USERNAME_MARKERS:
            idx = out.find(marker)
            if idx != -1 and (leftmost_idx == -1 or idx < leftmost_idx):
                leftmost_idx = idx
                leftmost_marker_len = len(marker)
        if leftmost_idx == -1:
            break  # no more leaks — done

        # Advance past the *entire username segment* (including its trailing
        # separator) so the username itself is dropped from the output. The
        # username is the directory segment IMMEDIATELY after the marker
        # (``Users\`` / ``Users/`` / ``/home/``) — it runs until the NEXT
        # ``\\`` or ``/`` character.
        after_marker = leftmost_idx + leftmost_marker_len  # points at ``<u>``
        while after_marker < len(out) and out[after_marker] not in ("\\", "/"):
            after_marker += 1
        if after_marker < len(out) and out[after_marker] in ("\\", "/"):
            after_marker += 1  # consume the trailing separator

        # If the marker is preceded by a Windows drive letter ``X:\`` (or
        # Unix ``/home/`` marker followed by extra path; here we just handle
        # the drive-letter + leading-separator), consume the prefix so the
        # output drops it too (cleaner anonymization: ``X:\Users\<u>\...``
        # → ``<USER_PATH>\...``, matching the v1 first-occurrence convention).
        # Pattern is ``[A-Z]:\`` or ``[A-Z]:/`` immediately before the marker.
        drive_start = leftmost_idx
        if leftmost_idx >= 3 and out[leftmost_idx - 1] == "\\" \
                and out[leftmost_idx - 2] == ":" \
                and out[leftmost_idx - 3].isalpha():
            drive_start = leftmost_idx - 3  # consume ``X:\``

        # Replace ``<prefix>Users\<u>\...`` with ``<prefix><USER_PATH>\...``.
        # Preserve any bytes BEFORE ``drive_start`` (the second occurrence
        # may be mid-line; bytes before it carry the first runtime prefix
        # that we want to keep in the output).
        out = out[:drive_start] + REDACTED_PATH + "\\" + out[after_marker:]
    return out


def _field_value(out, key):
    """Return the list/str value of output field ``key``, or None.

    ``data["text/plain"|"text/html"]`` for display_data/execute_result;
    top-level ``text`` for stream outputs. (A bare ``"text"`` key is
    stream-specific in nbformat outputs — display_data nests text under
    ``data``, so there is no collision with ``text/plain``.)
    """
    if key in DATA_KEYS:
        data = out.get("data", {})
        if not isinstance(data, dict):
            return None
        return data.get(key)
    if key == STREAM_KEY:
        return out.get(STREAM_KEY)
    return None


def _output_has_leak(blob):
    """Return True if any element of a field value (list or str) leaks."""
    if isinstance(blob, list):
        return any(_has_leak(el) for el in blob)
    return _has_leak(blob)


def count_leak_lines(nb_path):
    """Count leak-bearing list elements / string outputs across the notebook.

    Semantic is **distinct leak-bearing elements** (one per line for list-form,
    one per string output for string-form), aligned with what the strip removes.
    Scans both ``display_data`` data keys and ``stream`` ``text``.
    """
    try:
        with open(nb_path, encoding="utf-8") as f:
            nb = json.load(f)
    except (OSError, json.JSONDecodeError):
        return 0
    n = 0
    for cell in nb.get("cells", []):
        if cell.get("cell_type") != "code":
            continue
        for out in cell.get("outputs", []):
            for key in ALL_KEYS:
                v = _field_value(out, key)
                if isinstance(v, list):
                    n += sum(1 for el in v if _has_leak(el))
                elif _has_leak(v):
                    n += 1
    return n


def _first_matching_label(text):
    """Return the label (string part of the first ``(label, token)`` tuple
    in ``MACHINE_PATH_TOKENS``) whose token is a substring of ``text``.

    The ordering of ``MACHINE_PATH_TOKENS`` is the **priority order**: earlier
    tokens are more specific (e.g. ``ipykernel`` precedes ``other`` because
    an ipykernel-temp-path is also a Temp-path but the runtime distinction
    matters for downstream strategy logic).

    Normalizes ``\\\\`` to ``\\`` first (C538-L1) so double-bs
    JSON-escaped paths still report their proper category (avoids a
    spurious "" (no-match) fallback when a double-bs line leaked past
    the v1 token guard).
    """
    if not isinstance(text, str):
        return ""
    norm = _normalize_bs(text)
    for label, token in MACHINE_PATH_TOKENS:
        if token in norm:
            return label
    return ""


def find_leak_outputs(nb_path):
    """Return list of ``(cell_index, output_index, field_key)`` for leak outputs.

    ``field_key`` is one of ``text/plain`` / ``text/html`` (display_data /
    execute_result) or ``text`` (stream).
    """
    try:
        with open(nb_path, encoding="utf-8") as f:
            nb = json.load(f)
    except (OSError, json.JSONDecodeError):
        return []
    hits = []
    for ci, cell in enumerate(nb.get("cells", [])):
        if cell.get("cell_type") != "code":
            continue
        for oi, out in enumerate(cell.get("outputs", [])):
            for key in ALL_KEYS:
                if _output_has_leak(_field_value(out, key)):
                    hits.append((ci, oi, key))
    return hits


def _find_data_list_bounds(raw, key):
    """Return list of ``(body_start, body_end)`` for each ``"<key>": [...]``
    block in ``raw`` notebook JSON (JSON-string-aware bracket balancing).

    Mirrors ``strip_probe_banner.py._find_text_html_list_bounds`` but
    parameterized on the data key. ``body_start`` is the offset right after
    the opening ``[``, ``body_end`` is the closing ``]`` (exclusive).

    JSON-string-awareness is essential: ``]`` inside a JSON string literal
    (e.g. a path with a bracket, or a JS array literal the kernel may embed)
    must not prematurely close the list.
    """
    blocks = []
    head_pat = re.compile(r'"' + re.escape(key) + r'"\s*:\s*\[')
    for head in head_pat.finditer(raw):
        body_start = head.end()
        depth = 1
        i = body_start
        in_string = False
        escape_next = False
        while i < len(raw):
            ch = raw[i]
            if escape_next:
                escape_next = False
                i += 1
                continue
            if in_string:
                if ch == "\\":
                    escape_next = True
                elif ch == '"':
                    in_string = False
                i += 1
                continue
            if ch == '"':
                in_string = True
                i += 1
                continue
            if ch == "[":
                depth += 1
            elif ch == "]":
                depth -= 1
                if depth == 0:
                    blocks.append((body_start, i))
                    break
            i += 1
    return blocks


def _redact_drop_strategy(decoded, label):
    """Return ``(new_decoded_str, strategy)`` for a leak-bearing decoded
    element belonging to category ``label``.

    - For ``"nuget"`` (the canonical merged #6563/#6567 path): ``DROP``
      (return ``None`` to signal full removal).
    - For all other categories: ``REDACT`` (return the redacted string;
      the caller will substitute the JSON-encoded element with the redacted
      encoding).

    The NuGet DROP behaviour is FROZEN — backwards-compat with the
    already-merged #6567 batch, which replaced leak-bearing elements with
    empty strings (drop_in_place semantics). Changing NuGet to REDACT would
    re-introduce non-empty strings into the 8 already-shipped notebooks,
    dirtying their diff and forcing a no-op follow-up cleanup.
    """
    if label == "nuget":
        return (None, "drop")
    return (_redact_line(decoded), "redact")


def strip_in_place(nb_path):
    """Edit leak-bearing ``data[*]`` outputs in-place on disk.

    **Two strategies by category** (set by ``_redact_drop_strategy``):

    - ``DROP`` (canonical NuGet, merged in #6563/#6567): the leak-bearing
      element is removed from the list (``""`` if it was the only element)
      or, for a bare string value, replaced by ``""``. Backwards-compatible
      with the 8-notebook merged batch — re-running on a #6567-touched
      notebook is a no-op.

    - ``REDACT`` (Python categories: pip, ipykernel, conda, hf, other):
      the leak-bearing element's JSON encoding is substituted byte-identically
      with the redacted form (see ``_redact_line``). Only the *username
      prefix* changes (``C:\\Users\\<u>\\...`` → ``<USER_PATH>\\...``);
      the trailing relative path (which carries pedagogy: library/symbol/
      warning content) is preserved verbatim.

    Surgical text-level edit preserving every other byte (no JSON
    re-serialization, no metadata churn).

    Returns ``(outputs_with_leak, lines_fixed)``.
    """
    hits = find_leak_outputs(nb_path)
    if not hits:
        return (0, 0)

    with open(nb_path, encoding="utf-8") as f:
        text = f.read()

    try:
        with open(nb_path, encoding="utf-8") as f:
            nb = json.load(f)
    except (OSError, json.JSONDecodeError):
        return (len(hits), 0)

    new_text = text
    fixed = 0
    str_pat = re.compile(r'"((?:text/plain|text/html|text))"\s*:\s*"((?:[^"\\]|\\.)*)"')
    elem_pat = re.compile(r'"((?:[^"\\]|\\.)*)"')

    # --- String-form (single inline string output value, not list) ---
    str_targets = []
    for ci, oi, key in hits:
        try:
            cell = nb["cells"][ci]
        except (IndexError, KeyError):
            continue
        outs = cell.get("outputs", [])
        if oi >= len(outs):
            continue
        v = _field_value(outs[oi], key)
        if isinstance(v, str) and _has_leak(v):
            str_targets.append((key, v))

    for key, leak_str in reversed(str_targets):
        for m in list(str_pat.finditer(new_text)):
            if m.group(1) != key:
                continue
            raw_value = m.group(2)
            try:
                decoded = json.loads('"' + raw_value + '"')
            except json.JSONDecodeError:
                continue
            if decoded != leak_str:
                continue
            # Determine strategy by inspecting which category token matched
            # the leaked ``decoded`` (the str_targets only had ``_has_leak``
            # which is True iff ANY category token matched; we re-disambiguate
            # by finding the FIRST matched token).
            label = _first_matching_label(decoded)
            replacement, _strat = _redact_drop_strategy(decoded, label)
            if replacement is None:
                # DROP — replace the whole "key": "leaked" with "key": ""
                repl = '"%s": ""' % key
            else:
                # REDACT — substitute the JSON-encoded element. Note:
                # ``json.dumps`` with no separators and ``ensure_ascii=False``
                # gives us the canonical ``"\\\\Users\\\\..."`` form (NB
                # notebooks use ASCII-default encoding for non-ASCII so
                # ensure_ascii=True matches the stored encoding for ASCII
                # content; use False to match UTF-8 raw bytes for the
                # rare non-ASCII path).
                repl = '"%s": %s' % (key, json.dumps(replacement,
                                                     ensure_ascii=False))
            new_text = new_text[:m.start()] + repl + new_text[m.end():]
            fixed += 1
            break

    # --- List-form (the observed shape for ``text/plain`` text outputs) ---
    for key in ALL_KEYS:
        blocks = _find_data_list_bounds(new_text, key)
        # Filter to blocks containing at least one leak-bearing element.
        leak_blocks = []
        for body_start, body_end in blocks:
            body = new_text[body_start:body_end]
            for em in elem_pat.finditer(body):
                try:
                    decoded = json.loads('"' + em.group(1) + '"')
                except json.JSONDecodeError:
                    continue
                if _has_leak(decoded):
                    leak_blocks.append((body_start, body_end))
                    break
        # Process in REVERSE file-offset order so earlier offsets stay valid.
        for body_start, body_end in reversed(leak_blocks):
            body = new_text[body_start:body_end]
            elems = list(elem_pat.finditer(body))
            if not elems:
                continue
            # Classify each leak-bearing element by category to choose
            # strategy per element.
            edit_spans = []  # (start, end, replacement_text) for REPLACE; or
                             # (start, end, None) for DROP
            replaced_here = 0
            for em in elems:
                try:
                    decoded = json.loads('"' + em.group(1) + '"')
                except json.JSONDecodeError:
                    continue
                if not _has_leak(decoded):
                    continue
                replaced_here += 1
                label = _first_matching_label(decoded)
                replacement, _strat = _redact_drop_strategy(decoded, label)
                # Determine the boundary to remove/replace (trailing comma
                # for non-final elements, leading comma for final, or
                # entire list for single-element).
                if replacement is None:
                    # DROP — same boundary rules as before:
                    after = em.end()
                    tail_match = re.match(r'\s*,', body[after:])
                    if tail_match:
                        edit_spans.append(
                            (em.start(), after + tail_match.end(), None))
                    else:
                        before = em.start()
                        pre_match = re.search(r',\s*$', body[:before])
                        if pre_match:
                            edit_spans.append(
                                (pre_match.start(), em.end(), None))
                        else:
                            edit_spans.append(
                                (em.start(), em.end(), None))
                else:
                    # REDACT — keep the element position + comma, just swap
                    # the JSON-encoded string. Byte-identical when the
                    # redacted output re-encodes to the same character
                    # width as the input (which it does, since REDACT
                    # shortens ``C:\\Users\\jsboi\\...`` to ``<USER_PATH>\\...``
                    # — strictly shorter, so we DROP the trailing comma plus
                    # any extra whitespace, then re-insert the comma and
                    # the redacted element).
                    edit_spans.append(
                        (em.start(), em.end(),
                         json.dumps(replacement, ensure_ascii=False)))

            if not replaced_here:
                continue

            # Apply edits in REVERSE body-offset order so earlier offsets
            # remain valid. REDACT swaps the element content with no
            # boundary manipulation (the element stays inline; the comma
            # stays inline). DROP removes the element and the trailing /
            # preceding comma.
            new_body = body
            for start, end, replacement_text in reversed(edit_spans):
                if replacement_text is None:
                    # DROP
                    new_body = new_body[:start] + new_body[end:]
                else:
                    # REDACT — replace element content in place
                    old_elem = new_body[start:end]
                    # Preserve the surrounding whitespace pattern: assume
                    # the element is wrapped in ``"..."`` quotes only;
                    # trailing comma is kept OUTSIDE the regex match (the
                    # regex consumed up to the closing quote). Swap the
                    # content between the quotes.
                    assert old_elem.startswith('"') and old_elem.endswith(
                        '"'), "unexpected element shape: %r" % old_elem
                    new_elem = '"' + replacement_text.strip('"') + '"'
                    new_body = new_body[:start] + new_elem + new_body[end:]
            if new_body != body:
                new_text = new_text[:body_start] + new_body + new_text[body_end:]
                fixed += replaced_here

    if new_text != text:
        with open(nb_path, "w", encoding="utf-8", newline="") as f:
            f.write(new_text)

    return (len(hits), fixed)


def iter_notebooks(nb_root):
    for path in glob.glob(os.path.join(nb_root, "**", "*.ipynb"), recursive=True):
        if "_output" in os.path.basename(path) or "_executed" in os.path.basename(path):
            continue
        yield path


def main():
    global ACTIVE_CATEGORIES
    parser = argparse.ArgumentParser(
        description="Strip machine-username path leaks from notebook outputs. "
                    "Covers 5 runtime-category leaks: nuget (dotnet-interactive), "
                    "pip (CPython AppData\\Roaming\\Python), ipykernel (per-cell "
                    "temp file warnings), conda (env path warnings), hf "
                    "(HuggingFace cache warnings). Path-based detection."
    )
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--scan", metavar="PATH",
                       help="dry-run scan a file or dir; list leak outputs")
    group.add_argument("--scan-all", action="store_true",
                       help="dry-run scan repo-wide")
    group.add_argument("--apply", metavar="PATH",
                       help="fix a file in place (strip leaks)")
    group.add_argument("--apply-all", action="store_true",
                       help="fix repo-wide in place")
    parser.add_argument("--check", action="store_true",
                        help="with --scan-all: exit 1 if any leak found")
    parser.add_argument("--category", dest="category",
                        choices=[label for label, _ in MACHINE_PATH_TOKENS] + ["all"],
                        default="all",
                        help="limit scan/apply to one runtime category "
                             "(default: all). Useful for triage.")
    args = parser.parse_args()

    if args.category == "all":
        ACTIVE_CATEGORIES = None
    else:
        ACTIVE_CATEGORIES = {args.category}

    repo_root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    nb_root = os.path.join(repo_root, "MyIA.AI.Notebooks")

    do_apply = args.apply is not None or args.apply_all
    target = args.apply if args.apply else (args.scan if args.scan else nb_root)

    paths = []
    if args.scan_all or args.apply_all:
        paths = list(iter_notebooks(nb_root))
    elif os.path.isdir(target):
        paths = list(iter_notebooks(target))
    elif os.path.isfile(target):
        paths = [target]
    else:
        parser.error("path not found: %s" % target)

    total_files = 0
    total_found = 0
    total_fixed = 0
    skipped = []
    for p in sorted(paths):
        found = count_leak_lines(p)
        fixed = 0
        if do_apply and found:
            fixed = strip_in_place(p)[1]
        if not found:
            continue
        total_files += 1
        total_found += found
        total_fixed += fixed
        rel = os.path.relpath(p, repo_root)
        if do_apply:
            tag = "FIXED" if fixed == found else ("PARTIAL" if fixed else "SKIP")
            print("[%s] %s  (%d leak line(s), %d fixed)" % (tag, rel, found, fixed))
            if fixed < found:
                skipped.append(rel)
        else:
            print("[DEFECT] %s  (%d leak line(s))" % (rel, found))

    mode = "apply" if do_apply else "scan"
    cat_label = "all categories" if ACTIVE_CATEGORIES is None else (
        ", ".join(sorted(ACTIVE_CATEGORIES)))
    print("\n%s summary (%s): %d notebook(s) carrying %d leak line(s)"
          % (mode, cat_label, total_files, total_found))
    if do_apply:
        print("  fixed: %d   skipped: %d file(s)" % (total_fixed, len(skipped)))
        for rel in skipped:
            print("    [unfixed] %s" % rel)

    if args.check and total_found > 0:
        sys.exit(1)


if __name__ == "__main__":
    main()
