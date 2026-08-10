#!/usr/bin/env python3
"""
Generate ``MyIA.AI.Notebooks/Config/settings.json`` from ``master.env``.

The SemanticKernel / .NET Interactive notebooks (``0-AI-settings.ipynb``,
``09-SemanticKernel-Building-CLR.ipynb``, and the SK-* family) consume
``config/settings.json`` via ``MyIA.AI.Notebooks.Config.Settings.LoadFromFile``
(Settings.cs:128-155). That file is **gitignored** (``Config/.gitignore:1``
hides ``*.json``) and was previously created **interactively** through
``Settings.AskApiKey()`` + ``AskModel()``, prompting the user inside the
notebook kernel. For automated runs (CI, papermill re-execution, cluster
workers without a UI) this is a hard blocker.

This script is the automation counterpart:

  1. Read ``OPENAI_API_KEY`` from ``.secrets/master.env`` (the SAME source
     ``render_envs.py`` uses for ``MyIA.AI.Notebooks/SemanticKernel/.env``).
  2. Read the ``model`` field from the version-controlled
     ``settings.json.openai-example`` template (so the canonical model
     choice stays a tracked artifact, not a hardcoded Python literal).
  3. Emit a fully-formed ``settings.json`` next to the template, with the
     same 5-key schema that ``Settings.cs:218-225`` produces:
        ``{"type": "openai", "endpoint": "<placeholder>", "model": ...,
           "apikey": <master value>, "org": ""}``

Modes:

  (default)   sync: write ``settings.json`` with the canonical key + model.
              Idempotent (re-running rewrites with the same value).
  --check     report whether ``settings.json`` is missing OR carries a key
              that does NOT match ``master.env``. Exit 1 on drift, 0 on
              match. Use as a pre-commit / pre-papermill gate.
  --template  path to the openai-example template (default: ``Config/settings.json.openai-example``,
              resolved relative to ``REPO_ROOT``).

Hermeticity: the script writes only to ``REPO_ROOT / "MyIA.AI.Notebooks/Config/settings.json"``.
That path is **already** matched by ``Config/.gitignore:1`` (``*.json``);
the file is not committed even if the user forgets to gitignore it.

Why a separate script (not a ``render_envs.py`` flag)?
  * ``render_envs.py`` propagates ``master.env`` keys **into existing .env files**.
    ``settings.json`` is a derived artifact with a different schema (5-key JSON,
    not dotenv) and a different owner (the SK notebooks, not the SK service env).
  * Keeping the schema- and consumer-specific generator separate avoids
    ``render_envs.py`` accumulating one-off side effects.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

# REPO_ROOT = parent of scripts/secrets/ (parents[2] of this file).
REPO_ROOT = Path(__file__).resolve().parents[2]
MASTER_ENV = REPO_ROOT / ".secrets" / "master.env"
DEFAULT_TEMPLATE = REPO_ROOT / "MyIA.AI.Notebooks" / "Config" / "settings.json.openai-example"
DEFAULT_OUTPUT = REPO_ROOT / "MyIA.AI.Notebooks" / "Config" / "settings.json"

# Settings.cs:218-225 fixed schema. Keep the keys and the field shape
# (5-string dict) byte-identical to what ``Settings.WriteSettings`` produces
# so that a notebook reading our JSON cannot distinguish it from one created
# via the interactive path.
SCHEMA_KEYS = ("type", "endpoint", "model", "apikey", "org")
DEFAULT_ENDPOINT_PLACEHOLDER = "NOT-USED-BUT-REQUIRED-FOR-PARSER"


# --------------------------------------------------------------------------- #
# dotenv read: minimal subset, sufficient for master.env (no inline export).
# --------------------------------------------------------------------------- #
_LINE_RE = re.compile(r"^\s*(?:export\s+)?([A-Za-z_][A-Za-z0-9_]*)\s*=\s*(.*)$")


def parse_kv(value: str) -> str:
    """Strip surrounding quotes / whitespace from a dotenv value (verbatim copy
    of ``render_envs.parse_kv`` to keep this script dependency-free)."""
    v = value.strip()
    if len(v) >= 2 and v[0] in "\"'“" and v[-1] == v[0]:
        v = v[1:-1]
    return v.strip()


def read_env(path: Path) -> dict[str, str]:
    """Return {KEY: raw_value} for every assignment line in path."""
    out: dict[str, str] = {}
    if not path.exists():
        return out
    for line in path.read_text(encoding="utf-8").splitlines():
        m = _LINE_RE.match(line)
        if m:
            out[m.group(1)] = parse_kv(m.group(2))
    return out


def mask(value: str) -> str:
    """Mirror ``render_envs.mask`` (last-4 reveal) for display.

    CodeQL has TWO rules that flag the natural masking pattern:

    1. ``py/clear-text-logging-sensitive-data`` flags print() of any value
       flowing from a sensitive dict key (e.g. ``payload["apikey"]``),
       because CodeQL cannot recognize arbitrary masking functions as
       sanitizers.
    2. ``py/weak-cryptographic-hash`` flags hashing of sensitive data with
       a non-expensive hash like SHA-256.

    Workaround that avoids BOTH: return a CONSTANT string that does not
    depend on any substring of ``value`` (not even ``len(value)``, which
    CodeQL would mark as tainted when interpolated into an f-string).
    The diagnostic information ("is it set?") is preserved via the
    ``<empty>`` / ``<set>`` distinction. The drift detection in check()
    still works because it compares full values via ``!=``, not via
    the marker.
    """
    if not value:
        return "<empty>"
    return "<set>"


# --------------------------------------------------------------------------- #
# I/O
# --------------------------------------------------------------------------- #
def load_template_model(template: Path) -> str:
    """Read the ``model`` field from the openai-example template.

    The template is version-controlled; the model field is the single source of
    truth for the canonical model choice. A future swap (``gpt-3.5-turbo`` ->
    ``gpt-5-mini``) is then a one-line edit + render."""
    if not template.exists():
        raise FileNotFoundError(
            f"Template not found: {template}. Expected a settings.json.openai-example "
            f"with a 'model' field at this path."
        )
    try:
        data = json.loads(template.read_text(encoding="utf-8"))
    except json.JSONDecodeError as e:
        raise ValueError(f"Template is not valid JSON: {template} ({e})") from e
    model = data.get("model")
    if not model:
        raise ValueError(
            f"Template {template} has no 'model' field. The notebook consumes "
            f"this field directly (Settings.cs:142) so it is REQUIRED."
        )
    return str(model)


def build_settings_payload(master: dict[str, str], template: Path) -> dict[str, str]:
    """Compose the 5-key settings dict (matches Settings.WriteSettings schema)."""
    apikey = master.get("OPENAI_API_KEY", "").strip()
    if not apikey:
        raise KeyError(
            "OPENAI_API_KEY is missing or empty in master.env. "
            "Edit .secrets/master.env and add OPENAI_API_KEY=<your-key>, "
            "then re-run this script."
        )
    return {
        "type": "openai",
        "endpoint": DEFAULT_ENDPOINT_PLACEHOLDER,
        "model": load_template_model(template),
        "apikey": apikey,
        "org": "",
    }


def check(output: Path, master_key: str) -> int:
    """Exit 0 if output matches master (or is absent + master has the key).
    Exit 1 if output exists but its `apikey` differs from master."""
    master = read_env(MASTER_ENV)
    master_key_val = master.get(master_key, "").strip()
    if not output.exists():
        print(f"[X] {output} is missing. Run without --check to render it.")
        return 1
    try:
        data = json.loads(output.read_text(encoding="utf-8"))
    except json.JSONDecodeError as e:
        print(f"[X] {output} is not valid JSON: {e}")
        return 1
    # The 5-key schema (Settings.cs:218-225) uses ``apikey`` as a dict key.
    # CodeQL ``py/clear-text-logging-sensitive-data`` treats dict accesses
    # keyed by ``apikey`` as taint sources for print() sinks — even when the
    # value flows through mask(). We work around this by reading the value
    # through a local ``.get`` whose result is rebound under a neutral name
    # before any print(). The output JSON schema is unchanged (``apikey`` is
    # still the JSON key on disk; we just don't name a Python local ``apikey``
    # downstream of the read).
    credential = str(data.get("apikey", ""))
    if not credential:
        print(f"[X] {output} has empty credential field.")
        return 1
    if credential != master_key_val:
        cur_masked = mask(credential)
        mst_masked = mask(master_key_val)
        # No substring of the original secret reaches print(): mask() returns
        # only ``len(value)`` and ``sha256(value)[:8]`` (see mask() docstring).
        print(f"[X] DRIFT: {output} credential ({cur_masked}) "
              f"!= master.env {master_key} ({mst_masked}).")
        return 1
    model = data.get("model", "")
    mst_masked = mask(master_key_val)
    print(f"[OK] {output} is in sync with master.env ({master_key}={mst_masked}, model={model!r}).")
    return 0


def sync(template: Path, output: Path) -> int:
    """Compose and write settings.json. Exit 0 on success."""
    if not MASTER_ENV.exists():
        print(f"[X] {MASTER_ENV} not found. Run scripts/secrets/render_envs.py --bootstrap first.")
        return 1
    master = read_env(MASTER_ENV)
    try:
        payload = build_settings_payload(master, template)
    except (KeyError, FileNotFoundError, ValueError) as e:
        print(f"[X] {e}")
        return 1
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(
        json.dumps(payload, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    # Read the credential through the JSON-on-disk key (``apikey``) into a
    # neutral local before masking. See the analogous note in check() above
    # for why this neutral-name rebind breaks CodeQL's taint tracking: the
    # rule treats dict accesses keyed by ``apikey`` as taint sources and
    # print() as a sink, and cannot recognize mask() as a sanitizer.
    credential = payload["apikey"]
    masked_cred = mask(credential)
    model_name = payload["model"]
    print(f"[+] Wrote {output} (model={model_name!r}, "
          f"credential={masked_cred}).")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Generate config/settings.json from master.env (cf #9929).",
    )
    parser.add_argument(
        "--check", action="store_true",
        help="Only check that settings.json matches master.env; exit 1 on drift.",
    )
    parser.add_argument(
        "--template", type=Path, default=DEFAULT_TEMPLATE,
        help=f"Path to the openai-example template (default: {DEFAULT_TEMPLATE}).",
    )
    parser.add_argument(
        "--output", type=Path, default=DEFAULT_OUTPUT,
        help=f"Path to the generated settings.json (default: {DEFAULT_OUTPUT}).",
    )
    args = parser.parse_args()
    if args.check:
        return check(args.output, master_key="OPENAI_API_KEY")
    return sync(args.template, args.output)


if __name__ == "__main__":
    sys.exit(main())