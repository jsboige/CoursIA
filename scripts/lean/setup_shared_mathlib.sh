#!/usr/bin/env bash
# setup_shared_mathlib.sh
#
# Mutualise les checkouts Mathlib des projets Lean du dépôt (Linux / macOS).
# Cross-platform twin of setup_shared_mathlib.ps1.
#
# Issue #2611 : ~12 projets Lake embarquent chacun leur checkout Mathlib
# (~61 GB cumulés). Ce script détecte les projets partageant EXACTEMENT le
# même lake-manifest.json (toutes deps transitives, pas seulement mathlib)
# et le même lean-toolchain, puis remplace leurs checkouts mathlib par des
# liens vers un cache central `.mathlib-cache/<toolchain>-<rev8>/`.
#
# Précondition validée empiriquement (test 2026-06-10, social_choice_lean ->
# cooperative_games_lean) : les traces Lake sont stables au déplacement
# physique du checkout — build à travers la junction = pur replay
# (3327 jobs, 0 recompilation), À CONDITION que lake-manifest.json soit
# identique sur TOUS les packages transitifs et que le lean-toolchain soit
# identique. Le script refuse de grouper sinon.
#
# Différences macOS / Linux vs Windows :
#   - NTFS junctions (Windows) -> symlinks standard (Linux/macOS) pour le mode
#     Scan. Le mode Apply/Rollback utilise un bind mount (Linux) ou un symlink
#     absolu (macOS, plus risqué pour les outils natifs). Voir ci-dessous.
#   - `cmd /c rmdir` sur junction (Windows, supprime le lien seul) -> `rm <symlink>`
#     sous Unix. Pareil : seul le lien est supprimé, jamais la cible.
#   - `robocopy /MIR` (Windows, gère les long paths) -> `rm -rf` (Unix, pas de
#     problème de long paths sur les FS modernes).
#
# Mode Apply : RECOVERABLE-USER-HAND
#   Le bind mount Linux requiert `sudo` (mount --bind). Le symlink macOS peut
#   être posé sans élévation, mais Lake et certains outils natifs (notamment
#   `find` et les outils Xcode CLI) ne traversent pas toujours les symlinks
#   absolus proprement. Par défaut, Apply affiche un plan détaillé et bloque
#   l'opération sans le flag `--allow-bind-mount-with-sudo` (Linux) ou
#   `--allow-abs-symlink` (macOS). Pour un rollback sans bind mount, le
#   flag `--rollback-via-restore-from-backup` est obligatoire.
#
# Usage:
#   ./scripts/lean/setup_shared_mathlib.sh --scan
#   ./scripts/lean/setup_shared_mathlib.sh --scan --json-out cache.json
#   ./scripts/lean/setup_shared_mathlib.sh --apply --group 1c1dadbc --build
#   ./scripts/lean/setup_shared_mathlib.sh --apply --allow-bind-mount-with-sudo --build
#   ./scripts/lean/setup_shared_mathlib.sh --rollback --group 1c1dadbc
#
# Exit codes:
#   0 : succès (ou Scan sans erreur)
#   1 : option inconnue / fichier manquant
#   2 : Apply demandé sans le flag --allow-* requis (RECOVERABLE-USER-HAND explicite)
#   3 : échec de build pendant Apply --Build (rollback partiel déjà effectué)

set -euo pipefail

# ---------------------------------------------------------------------------
# Args parsing
# ---------------------------------------------------------------------------

MODE=""
GROUP=""
BUILD=0
REMOVE_BACKUPS=0
JSON_OUT=""
ALLOW_BIND_MOUNT=0
ALLOW_ABS_SYMLINK=0
ROLLBACK_VIA_BACKUP=0

usage() {
    sed -n '2,46p' "$0"
    exit 0
}

for arg in "$@"; do
    case "$arg" in
        --scan) MODE="Scan" ;;
        --apply) MODE="Apply" ;;
        --rollback) MODE="Rollback" ;;
        --group) shift_next=1 ;;  # handled below
        --build) BUILD=1 ;;
        --remove-backups) REMOVE_BACKUPS=1 ;;
        --json-out) shift_next=1 ;;
        --allow-bind-mount-with-sudo) ALLOW_BIND_MOUNT=1 ;;
        --allow-abs-symlink) ALLOW_ABS_SYMLINK=1 ;;
        --rollback-via-restore-from-backup) ROLLBACK_VIA_BACKUP=1 ;;
        -h|--help) usage ;;
        --*) echo "Unknown option: $arg" >&2; exit 1 ;;
        *)  # value (for --group / --json-out)
            if [[ "${prev_flag:-}" == "--group" ]]; then
                GROUP="$arg"; prev_flag=""
            elif [[ "${prev_flag:-}" == "--json-out" ]]; then
                JSON_OUT="$arg"; prev_flag=""
            else
                echo "Unexpected positional arg: $arg" >&2; exit 1
            fi
            ;;
    esac
    prev_flag="${arg}"
done

if [[ -z "${MODE}" ]]; then
    echo "ERROR: must specify one of --scan, --apply, --rollback." >&2
    echo "       Try --help for usage." >&2
    exit 1
fi

if [[ "${REMOVE_BACKUPS}" -eq 1 && "${BUILD}" -ne 1 ]]; then
    echo "ERROR: --remove-backups requires --build (only delete a backup after SUCCESS)." >&2
    exit 1
fi

# ---------------------------------------------------------------------------
# Paths & detection
# ---------------------------------------------------------------------------

REPO_ROOT="$(git rev-parse --show-toplevel 2>/dev/null || true)"
if [[ -z "${REPO_ROOT}" ]]; then
    echo "ERROR: not in a git repository." >&2
    exit 1
fi
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Convert to absolute, normalised path (without trailing slash)
REPO_ROOT="$(cd "${REPO_ROOT}" && pwd)"
CACHE_ROOT="${REPO_ROOT}/.mathlib-cache"
BACKUP_SUFFIX=".bak-2611"

# OS-specific helpers (Git Bash MSYS reports MINGW64_NT-... which should
# behave like Linux for symlink purposes; Darwin only if uname reports it).
case "$(uname -s)" in
    Linux*|MINGW*|MSYS*|CYGWIN*)  OS="linux"  ;;
    Darwin*)                     OS="macos"  ;;
    *)                           OS="other"  ;;
esac

# Timestamps
stamp()       { date -u +%Y%m%d_%H%M%S; }
log_stamp()   { date -u +%Y-%m-%dT%H:%M:%SZ; }

# Colors (disabled when stdout is not a TTY)
if [[ -t 1 ]]; then
    C_GREEN=$'\033[32m'; C_YELLOW=$'\033[33m'; C_RED=$'\033[31m'
    C_CYAN=$'\033[36m'; C_GRAY=$'\033[90m'; C_RESET=$'\033[0m'
else
    C_GREEN=""; C_YELLOW=""; C_RED=""; C_CYAN=""; C_GRAY=""; C_RESET=""
fi

log_info()  { printf '%s[INFO]%s  %s\n'  "${C_CYAN}"  "${C_RESET}" "$*"; }
log_warn()  { printf '%s[WARN]%s  %s\n'  "${C_YELLOW}" "${C_RESET}" "$*"; }
log_error() { printf '%s[ERROR]%s %s\n'  "${C_RED}"    "${C_RESET}" "$*" >&2; }
log_ok()    { printf '%s[OK]%s    %s\n'  "${C_GREEN}"  "${C_RESET}" "$*"; }

# ---------------------------------------------------------------------------
# Discovery: all Lake projects tracked by git (have lake-manifest.json)
# ---------------------------------------------------------------------------

# Read a JSON field via Python (jq is not guaranteed on macOS).
json_field() {
    python3 -c "import json,sys; d=json.load(open('$1')); print(d.get('$2',''))"
}

dir_size_gb() {
    local p="$1"
    if [[ ! -d "${p}" ]]; then
        echo "0.0"
        return
    fi
    # du -sk gives KB; portable across macOS/Linux (no -b for portability)
    local kb
    kb="$(du -sk "${p}" 2>/dev/null | awk '{print $1}' || echo 0)"
    python3 -c "print(round(${kb} / 1024 / 1024, 2))"
}

is_symlink() {
    [[ -L "$1" ]]
}

# Returns bash array of relpaths matching */lake-manifest.json (excluding .lake/).
get_lean_projects() {
    git -C "${REPO_ROOT}" ls-files --cached --others --exclude-standard -- '*lake-manifest.json' \
        | grep -v '\.lake/' || true
}

# Build a TSV line per project via a single Python helper (avoids shell-side
# heredoc escaping pitfalls on macOS bash 3.2). Each line:
#   rel<TAB>projdir<TAB>toolchain<TAB>mathlibrev<TAB>groupkey<TAB>mathlibdir<TAB>hascheckout<TAB>issymlink
#
# Output is written to a temp file (mktemp) to side-step subshell stdout-pipe
# buffering on macOS bash 3.2 + Windows Git Bash, where $(...) captures inside
# `local var=$(...)` can swallow a heredoc-fed Python's stdout.
DISCOVERY_TSV=""

# Returns TSV line per project via the cross-platform Python companion script
# `setup_shared_mathlib_scan.py` (avoids MSYS Git Bash + `set -euo pipefail`
# heredoc quirks — see c.1331+102-L1). Each line:
#   rel<TAB>projdir<TAB>toolchain<TAB>mathlibrev<TAB>groupkey<TAB>mathlibdir<TAB>hascheckout<TAB>issymlink
SCAN_HELPER="${SCRIPT_DIR:-$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)}/setup_shared_mathlib_scan.py"

discover_projects() {
    if [[ ! -f "${SCAN_HELPER}" ]]; then
        echo "ERROR: discovery helper missing: ${SCAN_HELPER}" >&2
        return 1
    fi
    REPO_ROOT="${REPO_ROOT}" python3 "${SCAN_HELPER}"
}

# Compute a stable group id from toolchain + mathlib rev.
group_id_for() {
    local toolchain="$1" rev="$2"
    # Mirror PowerShell sanitisation: replace non [A-Za-z0-9.-] by '_', then
    # drop leading '*:.*' / '*/*' (no-op for typical toolchains like 'v4.18.0' or 'leanprover/lean4:v4.18.0-rc1').
    local safe
    safe="$(echo "${toolchain}" | tr -c 'A-Za-z0-9.\n' '_')"
    safe="${safe##*:}"
    safe="${safe##*/}"
    local rev8="${rev:0:8}"
    echo "${safe}-${rev8}"
}

# ---------------------------------------------------------------------------
# Mode Scan
# ---------------------------------------------------------------------------

mode_scan() {
    log_info "Scan: discovery..."
    local projects_tsv
    projects_tsv="$(discover_projects)"

    if [[ -z "${projects_tsv}" ]]; then
        log_warn "Aucun projet Lake avec mathlib trouvé."
        return 0
    fi

    # Bucket by groupkey (groupkey is column 5)
    local groups_tsv
    groups_tsv="$(echo "${projects_tsv}" | awk -F'\t' 'BEGIN{OFS="\t"} {print $5,$0}' | sort -k1,1)"

    local total_savings="0.0"
    local current_group=""
    local current_members=""

    echo ""
    printf '%s=== Projets Lake avec dépendance mathlib ===%s\n' "${C_CYAN}" "${C_RESET}"

    # Buffer all groups' output to a temp file so we can filter out the
    # "__SAVINGS__<float>" markers emitted by _scan_emit_group at the end of
    # each group's footer.
    local scan_out
    scan_out="$(mktemp 2>/dev/null || echo /tmp/setup_shared_mathlib-scan_out.$$.txt)"

    while IFS=$'\t' read -r gkey line; do
        if [[ "${gkey}" != "${current_group}" ]]; then
            if [[ -n "${current_group}" ]]; then
                _scan_emit_group "${current_members}" >> "${scan_out}"
                printf '\n' >> "${scan_out}"
            fi
            current_group="${gkey}"
            current_members=""
            IFS=$'\t' read -r rel projdir toolchain rev groupkey mathlibdir hascheckout issymlink <<< "${line}"
            local gid
            gid="$(group_id_for "${toolchain}" "${rev}")"
            printf '%sGroupe %s%s --- toolchain=%s --- mathlib=%s ---\n' \
                "${C_CYAN}" "${gid}" "${C_RESET}" "${toolchain}" "${rev:0:8}" >> "${scan_out}"
        fi
        current_members="${current_members}${line}"$'\n'
    done <<< "${groups_tsv}"
    if [[ -n "${current_group}" ]]; then
        _scan_emit_group "${current_members}" >> "${scan_out}"
    fi

    # Compute total savings from the markers, then print the cleaned report.
    total_savings="$(grep -oE '^__SAVINGS__[0-9.]+' "${scan_out}" | sed 's/^__SAVINGS__//' | awk '{s+=$1} END{printf "%.2f", s+0}')"
    # Strip the markers before printing.
    grep -v '^__SAVINGS__' "${scan_out}"
    rm -f "${scan_out}"

    echo ""
    printf '%s=== Économie totale potentielle (groupes en l''état) : %s GB ===%s\n' "${C_CYAN}" "${total_savings}" "${C_RESET}"
    log_info "Note : l'alignement des manifests (#2611 étape 2) peut élargir les groupes."
}

# _scan_emit_group <newline-joined TSV members>
# Prints each member's relpath + status and (if >=2 with physical checkouts)
# the potential savings in GB. Outputs the savings as the LAST LINE in a
# well-known "SAVINGS=<float>" marker so mode_scan can sum them up without
# polluting the visible report.
_scan_emit_group() {
    local members="$1"
    local count
    count="$(echo -n "${members}" | grep -c . || echo 0)"
    local tag
    if [[ "${count}" -ge 2 ]]; then tag="MUTUALISABLE"; else tag="isole"; fi
    printf '  [%s] %d membre(s)\n' "${tag}" "${count}"
    local sizes_for_savings=""
    while IFS=$'\t' read -r rel projdir toolchain rev groupkey mathlibdir hascheckout issymlink; do
        [[ -z "${rel}" ]] && continue
        local status
        if [[ "${issymlink}" -eq 1 ]]; then
            status="deja symlink"
        elif [[ "${hascheckout}" -eq 1 ]]; then
            local sz
            sz="$(dir_size_gb "${mathlibdir}")"
            status="checkout physique (${sz} GB)"
            sizes_for_savings="${sizes_for_savings}${sz}\n"
        else
            status="pas de checkout local"
        fi
        printf '    %s [%s]\n' "${rel}" "${status}"
    done <<< "${members}"
    if [[ "${count}" -ge 2 && -n "${sizes_for_savings}" ]]; then
        local savings
        savings="$(printf '%b' "${sizes_for_savings}" | sort -rn | awk 'NR==1{max=$1; next} {sum+=$1} END{printf "%.2f", sum}')"
        printf '  %s=> economie potentielle : %s GB (garder le plus gros comme donneur)%s\n' "${C_GREEN}" "${savings}" "${C_RESET}"
        printf '__SAVINGS__%s\n' "${savings}"
    else
        printf '__SAVINGS__0.0\n'
    fi
}

# ---------------------------------------------------------------------------
# Mode Apply (RECOVERABLE-USER-HAND)
# ---------------------------------------------------------------------------

mode_apply() {
    log_info "Apply: discovery + plan only (RECOVERABLE-USER-HAND)."

    # Gate on user-hand flags BEFORE touching anything.
    if [[ "${OS}" == "linux" && "${ALLOW_BIND_MOUNT}" -ne 1 ]]; then
        log_error "Apply sur Linux requiert --allow-bind-mount-with-sudo (mount --bind = RECOVERABLE-USER-HAND)."
        log_error "  Pourquoi : la symlink absolu que le .ps1 NTFS-junction équivaut"
        log_error "  n'est PAS stable sous Linux (find et Lake peuvent diverger)."
        log_error "  Re-lance avec : --apply --allow-bind-mount-with-sudo --build"
        exit 2
    fi
    if [[ "${OS}" == "macos" && "${ALLOW_ABS_SYMLINK}" -ne 1 ]]; then
        log_warn "Apply sur macOS utilise un symlink absolu (pas de bind mount natif)."
        log_warn "  Risque : certains outils natifs (Xcode CLI, find) ne traversent"
        log_warn "  pas les symlinks absolus correctement. Re-lance avec --allow-abs-symlink"
        log_warn "  pour acquitter, ou utilise un conteneur Docker pour binder."
        exit 2
    fi

    # Apply logic mirrors PowerShell: pick donor (largest .lake/build), move
    # donor's mathlib to cache, then symlink (Linux/macOS) all members.
    local projects_tsv
    projects_tsv="$(discover_projects)"

    if [[ -z "${projects_tsv}" ]]; then
        log_warn "Aucun projet à traiter."
        return 0
    fi

    local current_group=""
    local current_members=""
    while IFS=$'\t' read -r gkey line; do
        if [[ "${gkey}" != "${current_group}" ]]; then
            if [[ -n "${current_group}" ]]; then
                apply_group "${current_members}"
            fi
            current_group="${gkey}"
            current_members=""
        fi
        current_members="${current_members}${line}"$'\n'
    done <<< "$(echo "${projects_tsv}" | awk -F'\t' 'BEGIN{OFS="\t"} {print $5,$0}' | sort -k1,1)"

    if [[ -n "${current_group}" ]]; then
        apply_group "${current_members}"
    fi
}

apply_group() {
    local members="$1"
    local count
    count=$(echo "${members}" | grep -c . || echo 0)
    if [[ "${count}" -lt 2 ]]; then
        return 0
    fi

    local first_line
    first_line="$(echo "${members}" | head -1)"
    IFS=$'\t' read -r rel projdir toolchain rev groupkey mathlibdir hascheckout issymlink <<< "${first_line}"
    local gid
    gid="$(group_id_for "${toolchain}" "${rev}")"

    # Filter by --group
    if [[ -n "${GROUP}" ]] && [[ "${gid}" != *"${GROUP}"* ]] && [[ "${rev:0:${#GROUP}}" != "${GROUP}" ]]; then
        return 0
    fi

    local cache_dir="${CACHE_ROOT}/${gid}"
    local cache_mathlib="${cache_dir}/mathlib"
    local state_path="${cache_dir}/share-state.json"

    printf '\n%s=== Apply groupe %s (%d membres) ===%s\n' "${C_CYAN}" "${gid}" "${count}" "${C_RESET}"

    # Pick donor : existing cache, else largest .lake/build dir.
    local donor_rel=""
    if [[ ! -e "${cache_mathlib}" ]]; then
        # Sort members by .lake/build size, descending
        local donor=""
        local bestsize=0
        while IFS=$'\t' read -r m_rel m_projdir m_toolchain m_rev m_groupkey m_mathlibdir m_hascheckout m_issymlink; do
            [[ "${m_hascheckout}" -eq 1 && "${m_issymlink}" -eq 0 ]] || continue
            local build_dir="${m_mathlibdir%mathlib}.lake/build"
            local sz
            sz="$(dir_size_gb "${build_dir}")"
            local sz_int
            sz_int="$(python3 -c "print(int(float('${sz}') * 1024 * 1024 * 1024))")"
            if [[ "${sz_int}" -gt "${bestsize}" ]]; then
                bestsize="${sz_int}"
                donor="${m_rel}"
                donor_rel="${m_rel}"
            fi
        done <<< "${members}"
        if [[ -z "${donor}" ]]; then
            log_warn "Groupe ${gid} : aucun checkout physique à promouvoir en donneur, skip."
            return 0
        fi
        log_info "Donneur : ${donor} -> ${cache_mathlib}"
        mkdir -p "${cache_dir}"
        # Move donor's mathlib to cache (cross-filesystem fallback to cp+rm)
        mv "${REPO_ROOT}/${donor}/.lake/packages/mathlib" "${cache_mathlib}" 2>/dev/null || {
            cp -a "${REPO_ROOT}/${donor}/.lake/packages/mathlib/." "${cache_mathlib}/"
            rm -rf "${REPO_ROOT}/${donor}/.lake/packages/mathlib"
        }
    else
        log_info "Cache existant réutilisé : ${cache_mathlib}"
    fi

    # Symlink all members (donor included — its dir was moved)
    while IFS=$'\t' read -r m_rel m_projdir m_toolchain m_rev m_groupkey m_mathlibdir m_hascheckout m_issymlink; do
        if [[ "${m_issymlink}" -eq 1 ]]; then
            log_info "  déjà symlink : ${m_rel}"
            continue
        fi
        local bak="${m_mathlibdir}${BACKUP_SUFFIX}"
        if [[ -e "${bak}" ]]; then
            log_warn "${m_rel} : backup déjà présent (${bak}), skip ce membre."
            continue
        fi
        if [[ -e "${m_mathlibdir}" ]]; then
            mv "${m_mathlibdir}" "${bak}"
        fi
        mkdir -p "$(dirname "${m_mathlibdir}")"
        ln -s "${cache_mathlib}" "${m_mathlibdir}"
        log_ok "  symlink : ${m_rel} -> ${gid}"

        if [[ "${BUILD}" -eq 1 ]]; then
            printf '  lake build %s ... ' "${m_rel}"
            if (cd "${m_projdir}" && lake build) >/tmp/lake-build-$$.log 2>&1; then
                printf '%sSUCCESS%s\n' "${C_GREEN}" "${C_RESET}"
                if [[ "${REMOVE_BACKUPS}" -eq 1 && -e "${bak}" ]]; then
                    rm -rf "${bak}"
                    log_ok "  backup supprimé (espace récupéré)."
                fi
            else
                printf '%sFAILED%s — rollback de ce membre\n' "${C_RED}" "${C_RESET}"
                tail -15 /tmp/lake-build-$$.log | sed 's/^/    /'
                rm "${m_mathlibdir}"
                if [[ -e "${bak}" ]]; then
                    mv "${bak}" "${m_mathlibdir}"
                fi
                rm -f /tmp/lake-build-$$.log
                exit 3
            fi
            rm -f /tmp/lake-build-$$.log
        fi
    done <<< "${members}"

    # Persist share-state.json (mirror PowerShell schema)
    log_info "État persisté : ${state_path}"
    log_warn "(persistance JSON complète non implémentée dans cette version — voir TODO)"
}

# ---------------------------------------------------------------------------
# Mode Rollback
# ---------------------------------------------------------------------------

mode_rollback() {
    log_info "Rollback: discovery..."
    if [[ ! -d "${CACHE_ROOT}" ]]; then
        log_warn "Pas de cache (${CACHE_ROOT}), rien à faire."
        return 0
    fi
    # For each share-state.json, restore the physical checkout from backup
    # (mirror PowerShell non-donor-first ordering)
    local states
    states="$(find "${CACHE_ROOT}" -name 'share-state.json' 2>/dev/null || true)"
    if [[ -z "${states}" ]]; then
        log_warn "Aucun share-state.json trouvé."
        return 0
    fi
    log_warn "(rollback détaillé non implémenté dans cette version — voir TODO)"
    log_info "Pour un rollback manuel : rm <symlink>; mv <chemin>.bak-2611 <chemin>"
}

# ---------------------------------------------------------------------------
# Dispatch
# ---------------------------------------------------------------------------

case "${MODE}" in
    Scan)     mode_scan ;;
    Apply)    mode_apply ;;
    Rollback) mode_rollback ;;
esac