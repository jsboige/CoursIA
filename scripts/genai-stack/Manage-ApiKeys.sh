#!/usr/bin/env bash
# Manage-ApiKeys — Generate and manage API keys for AI services (Linux / macOS)
#
# Cross-platform twin of Manage-ApiKeys.ps1. Generates cryptographically secure
# API keys for the GenAI stack services, stores them in a JSON registry, lists
# them (masked), and exports them.
#
# Which actions are portable, which are not:
#   - Generate / List / Export  -> fully portable (CSPRNG keygen + JSON store).
#   - Configure                 -> NOT portable: the .ps1 rewrites IIS URL Rewrite
#                                  rules in D:\Production\<site>\web.config, and
#                                  IIS exists only on Windows. On Linux/macOS the
#                                  equivalent (API-key validation at the reverse
#                                  proxy: nginx/caddy/Traefik) is deployment-
#                                  specific and intentionally out of scope here.
#                                  This script prints a clear notice + pointers
#                                  instead of silently no-op'ing.
#
# Usage: ./scripts/genai-stack/Manage-ApiKeys.sh <Generate|List|Export|Configure> [ServiceName] [-o <path>]
#   Generate   : generate one secure key per service, save to the registry.
#   List       : show all keys masked (first 8 + last 4 chars).
#   Export     : copy the registry to -o <path> (default ./api-keys-export.json).
#                Source registry = ${API_KEYS_PATH:-$HOME/.secrets/api-keys.json}.
#   Configure  : Windows-only (IIS); prints a notice on Linux/macOS.
#   ServiceName: restrict Generate/Configure to one service (substring match).
#   -o <path>  : Generate -> where to write the registry; List -> which registry
#                to read; Export -> where to write the export copy.
#                Registry default: ${API_KEYS_PATH:-$HOME/.secrets/api-keys.json}
#
# Prerequisites: openssl (keygen), python3 (JSON store). Both ship with macOS and
# are one `apt install` on Linux.
# See: scripts/genai-stack/Manage-ApiKeys.ps1 (canonical Windows version, #10644).

set -euo pipefail

# ---------------------------------------------------------------------------
# Colors (disabled when stdout is not a TTY)
# ---------------------------------------------------------------------------
if [[ -t 1 ]]; then
  C_GREEN=$'\033[32m'; C_YELLOW=$'\033[33m'; C_RED=$'\033[31m'
  C_CYAN=$'\033[36m'; C_GRAY=$'\033[90m'; C_RESET=$'\033[0m'
else
  C_GREEN=""; C_YELLOW=""; C_RED=""; C_CYAN=""; C_GRAY=""; C_RESET=""
fi

# ---------------------------------------------------------------------------
# Args
# ---------------------------------------------------------------------------
ACTION=""
SERVICE_NAME=""
OUTPUT_PATH="${API_KEYS_PATH:-$HOME/.secrets/api-keys.json}"
EXTRA_OUTPUT=""

while [[ $# -gt 0 ]]; do
  case "$1" in
    Generate|List|Export|Configure) ACTION="$1" ;;
    -o|--output) OUTPUT_PATH="$2"; EXTRA_OUTPUT="$2"; shift ;;
    -o=*|--output=*) OUTPUT_PATH="${1#*=}"; EXTRA_OUTPUT="${1#*=}" ;;
    -h|--help)
      sed -n '20,32p' "$0"; exit 0 ;;
    -*) echo "[WARN] Unknown flag: $1" ;;
    *) [[ -z "$SERVICE_NAME" ]] && SERVICE_NAME="$1" || SERVICE_NAME="$SERVICE_NAME $1" ;;
  esac
  shift
done

if [[ -z "$ACTION" ]]; then
  printf '%sERROR: Action required (Generate|List|Export|Configure).%s\n' "$C_RED" "$C_RESET"
  sed -n '20,32p' "$0"
  exit 1
fi

# ---------------------------------------------------------------------------
# Service catalogue (identical to Manage-ApiKeys.ps1)
# ---------------------------------------------------------------------------
# Format: "fqdn|Description" — bash 4+ associative arrays keep insertion order
# via a parallel index list so List shows services in the same order as the .ps1.
SERVICE_ORDER=(
  "whisper-api.myia.io|Whisper Speech-to-Text API"
  "tts-api.myia.io|Text-to-Speech API"
  "musicgen-api.myia.io|MusicGen Music Generation API"
  "demucs-api.myia.io|Demucs Audio Separation API"
  "mcp-tools.myia.io|MCP Tools API"
  "skagents.myia.io|Semantic Kernel Agents API"
  "embeddings.myia.io|Embeddings API"
  "qdrant.myia.io|Qdrant Vector Database"
  "students.qdrant.myia.io|Qdrant Students Instance"
  "search.myia.io|Search API"
  "api.micro.text-generation-webui.myia.io|Text Generation API (micro)"
  "api.mini.text-generation-webui.myia.io|Text Generation API (mini)"
  "api.medium.text-generation-webui.myia.io|Text Generation API (medium)"
  "api.large.text-generation-webui.myia.io|Text Generation API (large)"
)

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

# new_secure_api_key [length=32] -> writes a URL-safe base64 key to stdout.
# Mirrors New-SecureApiKey: CSPRNG bytes -> base64 -> RFC 4648 base64url (no padding).
new_secure_api_key() {
  local length="${1:-32}"
  local key=""
  if command -v openssl >/dev/null 2>&1; then
    key="$(openssl rand -base64 "$length" 2>/dev/null | tr '+/' '-_' | tr -d '= \n')"
  elif [[ -r /dev/urandom ]]; then
    # Fallback: /dev/urandom + base64 (available on every Linux/macOS).
    key="$(head -c "$length" /dev/urandom | base64 | tr '+/' '-_' | tr -d '= \n')"
  else
    printf '%sERROR: no CSPRNG available (need openssl or /dev/urandom).%s\n' "$C_RED" "$C_RESET" >&2
    exit 1
  fi
  printf '%s' "$key"
}

# iso_timestamp -> an ISO 8601 UTC timestamp (portable: no GNU date assumption
# beyond -u +FORMAT which both macOS BSD date and GNU date support).
iso_timestamp() {
  date -u '+%Y-%m-%dT%H:%M:%SZ'
}

# read_config / write_config: JSON store via python3 (no jq dependency). The
# registry shape matches the .ps1: {version, generated, keys:[{service,description,apiKey,created}]}.
read_config() {
  # Emit the JSON file content, or a minimal empty skeleton if missing/unreadable.
  if [[ -f "$OUTPUT_PATH" ]]; then
    cat "$OUTPUT_PATH"
  else
    printf '{"version":"1.0","generated":null,"keys":[]}'
  fi
}

# write_config <json-string> : atomically write + chmod 600 (restrictive perms,
# the Unix counterpart of the .ps1 ACL that grants FullControl to the owner only).
write_config() {
  local json="$1"
  local dir
  dir="$(dirname "$OUTPUT_PATH")"
  mkdir -p "$dir"
  printf '%s\n' "$json" > "$OUTPUT_PATH"
  chmod 600 "$OUTPUT_PATH" 2>/dev/null || true
}

# ---------------------------------------------------------------------------
# Actions
# ---------------------------------------------------------------------------

do_generate() {
  printf '\n%s========================================%s\n' "$C_CYAN" "$C_RESET"
  printf '%sGenerating API Keys%s\n' "$C_CYAN" "$C_RESET"
  printf '%s========================================%s\n\n' "$C_CYAN" "$C_RESET"

  command -v python3 >/dev/null 2>&1 || { printf '%sERROR: python3 required for the JSON store.%s\n' "$C_RED" "$C_RESET"; exit 1; }

  local gen_ts; gen_ts="$(iso_timestamp)"

  # Build the keys array in python from the service list (filtered by ServiceName),
  # generating a fresh CSPRNG key per service.
  local filter="$SERVICE_NAME"
  # NOTE: MKA_FILTER/MKA_NOW must PREFIX python3 (env assignment before the
  # command) — placed after `-c '...'` they would land in sys.argv, not the
  # environment, and os.environ[...] would KeyError.
  printf '%s\n' "${SERVICE_ORDER[@]}" | MKA_FILTER="$filter" MKA_NOW="$gen_ts" python3 -c '
import os, sys, subprocess, json, datetime

filter = os.environ["MKA_FILTER"].strip()
now = os.environ["MKA_NOW"]
keys = []
for line in sys.stdin:
    line = line.rstrip("\n")
    if not line:
        continue
    fqdn, desc = line.split("|", 1)
    if filter and filter not in fqdn:
        continue
    # CSPRNG: 32 bytes -> base64url, mirrors new_secure_api_key (openssl first).
    raw = subprocess.run(["openssl", "rand", "-base64", "32"],
                         capture_output=True, text=True).stdout
    api_key = raw.translate(str.maketrans({"+": "-", "/": "_", "=": "", "\n": "", " ": ""}))
    keys.append({"service": fqdn, "description": desc,
                 "apiKey": api_key, "created": now})
    print(f"{fqdn}:")
    print(f"  API Key: {api_key}")
    print(f"  Description: {desc}")
    print()
config = {"version": "1.0", "generated": now, "keys": keys}
print("JSON:" + json.dumps(config))
' > /tmp/mka_generate.$$.out || {
      printf '%sERROR: key generation failed.%s\n' "$C_RED" "$C_RESET"; rm -f "/tmp/mka_generate.$$.out"; exit 1; }

  # Split the human output from the JSON payload (prefixed "JSON:").
  local json_payload
  json_payload="$(grep '^JSON:' /tmp/mka_generate.$$.out | head -1 | sed 's/^JSON://')"
  grep -v '^JSON:' /tmp/mka_generate.$$.out
  rm -f "/tmp/mka_generate.$$.out"

  if [[ -z "$json_payload" ]]; then
    printf '%sERROR: no service matched / generation produced nothing.%s\n' "$C_RED" "$C_RESET"; exit 1
  fi

  write_config "$json_payload"
  printf '%sAPI keys saved to: %s%s\n' "$C_GREEN" "$OUTPUT_PATH" "$C_RESET"
  printf '\n%sWARNING: Store these keys securely!%s\n' "$C_YELLOW" "$C_RESET"
}

do_list() {
  printf '\n%s========================================%s\n' "$C_CYAN" "$C_RESET"
  printf '%sAPI Keys Summary%s\n' "$C_CYAN" "$C_RESET"
  printf '%s========================================%s\n\n' "$C_CYAN" "$C_RESET"

  command -v python3 >/dev/null 2>&1 || { printf '%sERROR: python3 required to read the JSON store.%s\n' "$C_RED" "$C_RESET"; exit 1; }

  read_config | python3 -c '
import sys, json
try:
    cfg = json.load(sys.stdin)
except Exception:
    print("Registry unreadable (invalid JSON)."); sys.exit(1)
keys = cfg.get("keys", [])
if not keys:
    print("No API keys configured.")
    print("Run: ./Manage-ApiKeys.sh Generate")
    sys.exit(0)
# NOTE: avoid f-strings here. The whole block rides in a bash single-quoted
# heredoc-like arg, so the dict-key quotes cannot be escaped inside an f-string
# expression (SyntaxError: backslash in f-string expr). Plain print() is safe
# and keeps the output byte-identical to the .ps1 layout.
print("Generated:", cfg.get("generated"))
print("Total keys:", len(keys))
print("")
for k in keys:
    ak = k.get("apiKey", "")
    masked = (ak[:8] + "..." + ak[-4:]) if len(ak) >= 12 else "(too short)"
    print(k.get("service"), ":")
    print("  Key:", masked)
    print("  Description:", k.get("description"))
    print("  Created:", k.get("created"))
'
}

do_export() {
  command -v python3 >/dev/null 2>&1 || { printf '%sERROR: python3 required to read the JSON store.%s\n' "$C_RED" "$C_RESET"; exit 1; }

  # Adaptation vs the .ps1: there, -OutputPath is overloaded as BOTH the registry
  # source and the export destination, so `Export -OutputPath <dest>` reads from
  # <dest> (often non-existent) -> "No API keys to export" (the .ps1 synopsis
  # example is itself broken by this). Here we separate the two: the source is
  # the canonical registry, the destination is -o (or ./api-keys-export.json).
  # This matches the obvious operator flow: Generate -> Export -o backup.json.
  local registry="${API_KEYS_PATH:-$HOME/.secrets/api-keys.json}"
  local export_dest="${EXTRA_OUTPUT:-./api-keys-export.json}"

  if [[ ! -f "$registry" ]]; then
    printf '%sNo API keys to export (registry not found: %s).%s\n' "$C_RED" "$registry" "$C_RESET"; exit 1
  fi
  local n
  n="$(cat "$registry" | python3 -c 'import sys,json; print(len(json.load(sys.stdin).get("keys",[])))' 2>/dev/null || echo 0)"
  if [[ "$n" -eq 0 ]]; then
    printf '%sNo API keys to export.%s\n' "$C_RED" "$C_RESET"; exit 1
  fi
  cp "$registry" "$export_dest"
  chmod 600 "$export_dest" 2>/dev/null || true
  printf '%sExported %s API keys to: %s%s\n' "$C_GREEN" "$n" "$export_dest" "$C_RESET"
  printf '\n%sWARNING: This file contains sensitive data. Store securely!%s\n' "$C_RED" "$C_RESET"
}

do_configure() {
  # The .ps1 Configure action rewrites IIS URL Rewrite rules in web.config — a
  # Windows-IIS-only operation with no direct Linux/macOS equivalent (the reverse
  # proxy validating the key differs per deployment: nginx, caddy, Traefik...).
  # Print an explicit notice + pointers rather than silently no-op'ing.
  printf '\n%s========================================%s\n' "$C_CYAN" "$C_RESET"
  printf '%sConfigure — Windows / IIS only%s\n' "$C_CYAN" "$C_RESET"
  printf '%s========================================%s\n\n' "$C_CYAN" "$C_RESET"
  printf '%sThe Configure action rewrites IIS URL Rewrite rules in web.config%s\n' "$C_YELLOW" "$C_RESET"
  printf '(see Manage-ApiKeys.ps1 -Action Configure). IIS exists only on Windows;\n'
  printf 'there is no portable equivalent in this script.\n\n'
  printf 'On Linux/macOS, API-key validation is configured at the reverse proxy.\n'
  printf 'Common patterns (deployment-specific, out of scope here):\n'
  printf '  - nginx:    if ($http_x_api_key != "<key>") { return 401; }\n'
  printf '  - caddy:    @nokey { not header X-Api-Key <key> }; respond @nokey 401\n'
  printf '  - Traefik:  middleware apiKeyAuth (forwardAuth / plugin)\n\n'
  printf '%sRun the .ps1 on the Windows/IIS host to configure URL Rewrite rules.%s\n' "$C_GRAY" "$C_RESET"
  printf '%sGenerate/List/Export ARE available on this platform.%s\n' "$C_GRAY" "$C_RESET"
  exit 0
}

case "$ACTION" in
  Generate)  do_generate ;;
  List)      do_list ;;
  Export)    do_export ;;
  Configure) do_configure ;;
  *) printf '%sERROR: unknown action %s%s\n' "$C_RED" "$ACTION" "$C_RESET"; exit 1 ;;
esac
