#!/usr/bin/env bash
# =============================================================================
# AUDIT TECHNIQUE ENVIRONNEMENT NOTEBOOKS - CoursIA (Linux / macOS)
# =============================================================================
# Cross-platform twin of audit_environment.ps1. Full environment audit before
# running the notebooks: Python/Conda, Jupyter kernels, .NET Interactive,
# 18 critical Python packages, system resources (disk, memory, processes),
# plus a summary with repair-time estimate and optional JSON export.
#
# Usage: ./scripts/environment/audit_environment.sh [--detailed] [--export-json]
#   --detailed     Show every package (default: only warnings/errors + counts)
#   --export-json  Write a machine-readable audit_results.json next to the log
#
# Differences from the PowerShell version:
#   - Disk: `df` on the current filesystem (the .ps1 audits drive D: specifically);
#     override with $AUDIT_DISK (mount point or device).
#   - Memory: `free` on Linux, `sysctl hw.memsize` on macOS.
#   - Processes: `pgrep` instead of Get-Process.
#   - JSON export emitted via plain printf (no jq dependency).
#
# Exit codes: 0 = ready, 1 = minor issues (<=3 errors), 2 = critical issues.
# See: scripts/environment/audit_environment.ps1 (canonical Windows version).
# =============================================================================

set -uo pipefail

# ---------------------------------------------------------------------------
# Args
# ---------------------------------------------------------------------------
DETAILED=0
EXPORT_JSON=0
for arg in "$@"; do
  case "$arg" in
    --detailed|-d)   DETAILED=1 ;;
    --export-json|-j) EXPORT_JSON=1 ;;
    --help|-h) sed -n '2,18p' "$0"; exit 0 ;;
    *) echo "[WARN] Unknown argument: $arg" ;;
  esac
done

LOG_FILE="audit_$(date +%Y%m%d_%H%M%S).log"
RESULTS_FILE="audit_results.json"
TIMESTAMP="$(date '+%Y-%m-%d %H:%M:%S')"
OS="$(uname -s)"

# Counters
TOTAL_ISSUES=0
TOTAL_WARNINGS=0
MISSING_REQUIRED=()
MISSING_OPTIONAL=()
declare -a ISSUES=()
declare -a RECOMMENDATIONS=()

# ---------------------------------------------------------------------------
# Colors (disabled when stdout is not a TTY)
# ---------------------------------------------------------------------------
if [[ -t 1 ]]; then
  C_GREEN=$'\033[32m'; C_YELLOW=$'\033[33m'; C_RED=$'\033[31m'
  C_CYAN=$'\033[36m'; C_GRAY=$'\033[90m'; C_YELLOW_H=$'\033[1;33m'; C_RESET=$'\033[0m'
else
  C_GREEN=""; C_YELLOW=""; C_RED=""; C_CYAN=""; C_GRAY=""; C_YELLOW_H=""; C_RESET=""
fi

section() { printf '\n%s=== %s ===%s\n' "$C_GREEN" "$1" "$C_RESET"; }

# write_check ITEM STATUS [DETAILS]  -- mirrors Write-Check
write_check() {
  local item="$1" status="$2" details="${3:-}"
  local color="$C_CYAN"
  case "$status" in
    OK)      color="$C_GREEN" ;;
    WARNING) color="$C_YELLOW" ;;
    ERROR)   color="$C_RED" ;;
  esac
  printf '%s[%s] %s%s%s\n' "$color" "$status" "$item" "$C_RESET" "${details:+ $C_GRAY$details$C_RESET}"
}

# ---------------------------------------------------------------------------
# 1. PYTHON / CONDA
# ---------------------------------------------------------------------------
section "ENVIRONNEMENTS PYTHON/CONDA"

# Conda (cross-platform)
if command -v conda >/dev/null 2>&1; then
  conda_version="$(conda --version 2>&1)"
  conda_envs="$(conda env list 2>/dev/null | grep -vc '^#')"   # count non-header lines
  active_env="${CONDA_DEFAULT_ENV:-<none>}"
  write_check "Conda installé" "OK" "$conda_version"
  write_check "Environnements conda" "OK" "$conda_envs environnement(s) trouvé(s)"
  [[ "$active_env" != "<none>" ]] && write_check "Environnement actif" "OK" "$active_env"
else
  ISSUES+=("Conda non disponible dans le PATH")
  TOTAL_ISSUES=$((TOTAL_ISSUES + 1))
  write_check "Conda" "ERROR" "Non trouvé dans le PATH"
fi

# Python (cross-platform)
if command -v python3 >/dev/null 2>&1; then PYBIN=python3
elif command -v python >/dev/null 2>&1; then PYBIN=python
else PYBIN=""; fi
if [[ -n "$PYBIN" ]]; then
  py_version="$($PYBIN --version 2>&1)"
  py_path="$(command -v "$PYBIN")"
  write_check "Python" "OK" "$py_version - $py_path"
else
  ISSUES+=("Python non disponible")
  TOTAL_ISSUES=$((TOTAL_ISSUES + 1))
  write_check "Python" "ERROR" "Non trouvé"
fi

# ---------------------------------------------------------------------------
# 2. KERNELS JUPYTER
# ---------------------------------------------------------------------------
section "KERNELS JUPYTER"

if command -v jupyter >/dev/null 2>&1; then
  jupyter_version="$(jupyter --version 2>&1 | head -1)"
  write_check "Jupyter installé" "OK" "$jupyter_version"
  # Jupyter Lab version (background subshell; mirrors the Start-Job test)
  lab_version="$(jupyter lab --version 2>/dev/null)"
  if [[ -n "$lab_version" ]]; then
    write_check "Jupyter Lab" "OK" "$lab_version"
  else
    write_check "Jupyter Lab" "WARNING" "Version non détectée"
    TOTAL_WARNINGS=$((TOTAL_WARNINGS + 1))
  fi
  # Kernels list (detailed mode only — verbose otherwise)
  if [[ $DETAILED -eq 1 ]]; then
    write_check "Kernelspecs" "OK" ""
    jupyter kernelspec list 2>/dev/null | sed 's/^/      /'
  fi
else
  ISSUES+=("Jupyter non disponible")
  TOTAL_ISSUES=$((TOTAL_ISSUES + 1))
  write_check "Jupyter" "ERROR" "Non installé"
fi

# ---------------------------------------------------------------------------
# 3. .NET INTERACTIVE
# ---------------------------------------------------------------------------
section ".NET INTERACTIVE"

if command -v dotnet >/dev/null 2>&1; then
  sdk_count="$(dotnet --list-sdks 2>/dev/null | grep -c .)"
  write_check ".NET SDK" "OK" "$sdk_count SDK(s) installé(s)"
  if dotnet tool list -g 2>/dev/null | grep -q "microsoft.dotnet-interactive"; then
    write_check ".NET Interactive" "OK" "Installé globalement"
  else
    write_check ".NET Interactive" "WARNING" "Non installé globalement"
    RECOMMENDATIONS+=("Installer .NET Interactive: dotnet tool install -g Microsoft.dotnet-interactive")
    TOTAL_WARNINGS=$((TOTAL_WARNINGS + 1))
  fi
else
  ISSUES+=(".NET SDK non disponible")
  TOTAL_ISSUES=$((TOTAL_ISSUES + 1))
  write_check ".NET SDK" "ERROR" "Non installé"
fi

# ---------------------------------------------------------------------------
# 4. PACKAGES PYTHON CRITIQUES
# ---------------------------------------------------------------------------
section "PACKAGES PYTHON CRITIQUES"

# name|category|required(1/0)
CRITICAL_PACKAGES=(
  "numpy|ML Base|1" "pandas|ML Base|1" "matplotlib|ML Base|1" "seaborn|ML Base|0"
  "scikit-learn|ML Avancé|1" "torch|ML Avancé|0" "tensorflow|ML Avancé|0"
  "stable-baselines3|RL|0" "pyro-ppl|Probabilités|0" "scipy|Probabilités|1"
  "z3-solver|SymbolicAI|1" "ortools|SymbolicAI|1"
  "pygad|Algorithmes génétiques|0" "deap|Algorithmes génétiques|0"
  "networkx|Visualisation|0" "plotly|Visualisation|0"
  "jupyter|Environment|1" "ipykernel|Environment|1"
)

pip_cmd=""
if [[ -n "$PYBIN" ]] && "$PYBIN" -m pip --version >/dev/null 2>&1; then
  pip_cmd=("$PYBIN" -m pip)
fi

for entry in "${CRITICAL_PACKAGES[@]}"; do
  IFS='|' read -r name category required <<<"$entry"
  version=""
  if [[ -n "$pip_cmd" ]]; then
    version="$("${pip_cmd[@]}" show "$name" 2>/dev/null | awk -F': ' '/^Version:/{print $2; exit}')"
  fi
  if [[ -n "$version" ]]; then
    [[ $DETAILED -eq 1 ]] && write_check "$name" "OK" "v$version ($category)"
  else
    if [[ "$required" == "1" ]]; then
      MISSING_REQUIRED+=("$name")
      TOTAL_ISSUES=$((TOTAL_ISSUES + 1))
      write_check "$name" "ERROR" "REQUIS MANQUANT ($category)"
    else
      MISSING_OPTIONAL+=("$name")
      TOTAL_WARNINGS=$((TOTAL_WARNINGS + 1))
      [[ $DETAILED -eq 1 ]] && write_check "$name" "WARNING" "Optionnel manquant ($category)"
    fi
  fi
done

# ---------------------------------------------------------------------------
# 5. PERFORMANCES SYSTÈME
# ---------------------------------------------------------------------------
section "PERFORMANCES SYSTÈME"

# Disk: df on the audit target (cwd by default; override via $AUDIT_DISK).
audit_disk="${AUDIT_DISK:-.}"
disk_line="$(df -h "$audit_disk" 2>/dev/null | awk 'NR==2{print $2"\t"$3"\t"$4"\t"$5}')"
if [[ -n "$disk_line" ]]; then
  total_h="$(printf '%s' "$disk_line" | cut -f1)"
  used_h="$(printf '%s' "$disk_line" | cut -f2)"
  free_h="$(printf '%s' "$disk_line" | cut -f3)"
  used_pct="$(printf '%s' "$disk_line" | cut -f4 | tr -d '%')"
  # Numeric free GB for threshold (best-effort; df -h is human-readable).
  free_gb_approx="$(df -BG "$audit_disk" 2>/dev/null | awk 'NR==2{print $4}' | tr -dc '0-9')"
  if [[ -n "$free_gb_approx" && "$free_gb_approx" -lt 5 ]]; then
    write_check "Espace disque ($audit_disk)" "ERROR" "$free_h libre ($used_pct% utilisé)"
    ISSUES+=("Espace disque faible ($free_h libre)")
    TOTAL_ISSUES=$((TOTAL_ISSUES + 1))
  elif [[ -n "$free_gb_approx" && "$free_gb_approx" -lt 20 ]]; then
    write_check "Espace disque ($audit_disk)" "WARNING" "$free_h libre ($used_pct% utilisé)"
  else
    write_check "Espace disque ($audit_disk)" "OK" "$free_h libre / $total_h ($used_pct% utilisé)"
  fi
else
  write_check "Espace disque" "WARNING" "df indisponible"
fi

# Memory: free (Linux) or sysctl (macOS).
mem_gb=""
if [[ "$OS" == "Darwin" ]]; then
  mem_bytes="$(sysctl -n hw.memsize 2>/dev/null)"
  [[ -n "$mem_bytes" ]] && mem_gb="$(awk -v b="$mem_bytes" 'BEGIN{printf "%.1f", b/1073741824}')"
elif command -v free >/dev/null 2>&1; then
  mem_gb="$(free -g 2>/dev/null | awk '/^(Mem|memory):/{print $2; exit}')"
fi
if [[ -n "$mem_gb" ]]; then
  write_check "Mémoire totale" "OK" "${mem_gb} GB"
else
  write_check "Mémoire totale" "WARNING" "Non mesurable"
fi

# Processes that may interfere (portable pgrep).
INTERFERING=(jupyter dotnet python node)
proc_warnings=0
for proc in "${INTERFERING[@]}"; do
  count=""
  if command -v pgrep >/dev/null 2>&1; then
    # -x exact match; fall back to substring if pgrep lacks -x (rare).
    count="$(pgrep -xc "$proc" 2>/dev/null || pgrep -c "$proc" 2>/dev/null)"
  fi
  if [[ -n "$count" && "$count" -gt 0 ]]; then
    write_check "Processus $proc" "WARNING" "$count instance(s) en cours"
    proc_warnings=$((proc_warnings + 1))
  fi
done
TOTAL_WARNINGS=$((TOTAL_WARNINGS + proc_warnings))

# ---------------------------------------------------------------------------
# 6. RÉSUMÉ ET RECOMMANDATIONS
# ---------------------------------------------------------------------------
section "RÉSUMÉ DE L'AUDIT"

# Repair-time estimate (mirrors the .ps1 heuristic: 3 min/required, 2 min/optional, 5 min/issue).
repair_min=$(( ${#MISSING_REQUIRED[@]} * 3 + ${#MISSING_OPTIONAL[@]} * 2 + ${#ISSUES[@]} * 5 ))

printf '\n%sSTATUT GLOBAL:%s\n' "$C_YELLOW_H" "$C_RESET"
if [[ $TOTAL_ISSUES -eq 0 ]]; then
  printf '%s[OK] ENVIRONNEMENT PRÊT POUR LA FORMATION%s\n' "$C_GREEN" "$C_RESET"
elif [[ $TOTAL_ISSUES -le 3 ]]; then
  printf '%s[WARN] PROBLÈMES MINEURS À CORRIGER%s\n' "$C_YELLOW" "$C_RESET"
else
  printf '%s[FAIL] PROBLÈMES CRITIQUES À RÉSOUDRE%s\n' "$C_RED" "$C_RESET"
fi

printf '\nDÉTAILS:\n'
err_color="$C_GREEN"; [[ $TOTAL_ISSUES -gt 0 ]] && err_color="$C_RED"
warn_color="$C_GREEN"; [[ $TOTAL_WARNINGS -gt 0 ]] && warn_color="$C_YELLOW"
printf '%s- Erreurs critiques: %s%s\n' "$err_color"  "$TOTAL_ISSUES"   "$C_RESET"
printf '%s- Avertissements: %s%s\n'    "$warn_color" "$TOTAL_WARNINGS" "$C_RESET"

if [[ ${#MISSING_REQUIRED[@]} -gt 0 ]]; then
  printf '\n%sPACKAGES REQUIS MANQUANTS:%s\n' "$C_RED" "$C_RESET"
  for pkg in "${MISSING_REQUIRED[@]}"; do printf '%s  - %s%s\n' "$C_RED" "$pkg" "$C_RESET"; done
  RECOMMENDATIONS+=("Installer les packages requis: $PYBIN -m pip install ${MISSING_REQUIRED[*]}")
fi
if [[ ${#MISSING_OPTIONAL[@]} -gt 0 ]]; then
  printf '\n%sPACKAGES OPTIONNELS MANQUANTS:%s\n' "$C_YELLOW" "$C_RESET"
  for pkg in "${MISSING_OPTIONAL[@]}"; do printf '%s  - %s%s\n' "$C_YELLOW" "$pkg" "$C_RESET"; done
fi

printf '\n%sESTIMATION TEMPS DE RÉPARATION: %s minutes%s\n' "$C_CYAN" "$repair_min" "$C_RESET"

if [[ ${#RECOMMENDATIONS[@]} -gt 0 ]]; then
  printf '\nRECOMMANDATIONS:\n'
  for rec in "${RECOMMENDATIONS[@]}"; do printf '  - %s\n' "$rec"; done
fi

# ---------------------------------------------------------------------------
# Export JSON (no jq: plain printf, escaped minimal)
# ---------------------------------------------------------------------------
if [[ $EXPORT_JSON -eq 1 ]]; then
  # json_array name1 name2 ... -> ["name1","name2"]  (empty array when no args / empty args)
  json_array() {
    local first=1 elem
    printf '['
    for elem in "$@"; do
      [[ -n "$elem" ]] || continue
      [[ $first -eq 0 ]] && printf ','
      printf '"%s"' "$elem"
      first=0
    done
    printf ']'
  }
  {
    printf '{\n'
    printf '  "timestamp": "%s",\n' "$TIMESTAMP"
    printf '  "status": "%s",\n' "$( [[ $TOTAL_ISSUES -eq 0 ]] && echo Ready || ([[ $TOTAL_ISSUES -le 3 ]] && echo MinorIssues || echo CriticalIssues) )"
    printf '  "issues": %d,\n' "$TOTAL_ISSUES"
    printf '  "warnings": %d,\n' "$TOTAL_WARNINGS"
    printf '  "repair_time_minutes": %d,\n' "$repair_min"
    printf '  "missing_required": %s,\n' "$(json_array "${MISSING_REQUIRED[@]}")"
    printf '  "missing_optional": %s\n' "$(json_array "${MISSING_OPTIONAL[@]}")"
    printf '}\n'
  } > "$RESULTS_FILE"
  printf '\nRésultats exportés vers: %s\n' "$RESULTS_FILE"
fi

# Log
{
  echo "AUDIT ENVIRONNEMENT NOTEBOOKS - $TIMESTAMP"
  echo "=============================================="
  echo "Issues: ${ISSUES[*]}"
  echo "Missing Required Packages: ${MISSING_REQUIRED[*]}"
  echo "Missing Optional Packages: ${MISSING_OPTIONAL[*]}"
  echo "Repair Time Estimate: $repair_min minutes"
} > "$LOG_FILE"
printf 'Log sauvegardé: %s\n' "$LOG_FILE"

# Exit code (same semantics as the .ps1: 0 ready, 1 minor, 2 critical)
if [[ $TOTAL_ISSUES -eq 0 ]]; then
  exit 0
elif [[ $TOTAL_ISSUES -le 3 ]]; then
  exit 1
else
  exit 2
fi
