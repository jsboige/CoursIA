#!/usr/bin/env bash
# =============================================================================
# SETUP ENVIRONNEMENT NOTEBOOKS - CoursIA (Linux / macOS)
# =============================================================================
# Cross-platform twin of setup_environment.ps1. Installs the Python packages,
# .NET tooling and Jupyter kernels the CoursIA notebooks rely on, with a
# checkpoint/resume mechanism so an interrupted run can pick up where it left.
#
# Usage: ./scripts/environment/setup_environment.sh [--auto-fix] [--install-optional] [--force] [--resume]
#   --auto-fix          Configure NuGet / .NET Interactive / Jupyter kernels (default: only check)
#   --install-optional  Also install the optional ML packages (torch, tensorflow, ...)
#   --force             Reinstall even already-installed packages
#   --resume            Reload checkpoints from a previous (interrupted) run
#
# Differences from the PowerShell version:
#   - Detects python3 first, falls back to python (macOS often only has python3).
#   - No APPDATA: the Jupyter kernels dir is resolved via `jupyter --data-dir`.
#   - No Windows admin check; on Unix root is *discouraged* for pip (warning).
#   - Checkpoints stored as a plain text file (one name per line), no JSON dep.
#
# Exit codes: 0 = clean, 1 = warnings (<=2 required failures), 2 = failed.
# See: scripts/environment/setup_environment.ps1 (canonical Windows version).
# =============================================================================

set -uo pipefail   # NB: no -e — like the .ps1, we collect per-step failures and report at the end.

# ---------------------------------------------------------------------------
# Args
# ---------------------------------------------------------------------------
AUTO_FIX=0
INSTALL_OPTIONAL=0
FORCE=0
RESUME=0
for arg in "$@"; do
  case "$arg" in
    --auto-fix|-a)      AUTO_FIX=1 ;;
    --install-optional) INSTALL_OPTIONAL=1 ;;
    --force|-f)         FORCE=1 ;;
    --resume|-r)        RESUME=1 ;;
    --help|-h)
      sed -n '2,20p' "$0"
      exit 0 ;;
    *) echo "[WARN] Unknown argument: $arg" ;;
  esac
done

# ---------------------------------------------------------------------------
# Config
# ---------------------------------------------------------------------------
CHECKPOINT_FILE="setup_checkpoint.txt"
LOG_FILE="setup_$(date +%Y%m%d_%H%M%S).log"

REQUIRED=(numpy pandas matplotlib scikit-learn scipy z3-solver ortools jupyter ipykernel)
OPTIONAL=(seaborn torch stable-baselines3 pyro-ppl pygad deap networkx plotly tensorflow)

BASIC=(numpy pandas matplotlib scipy)
ML=(scikit-learn jupyter ipykernel)
ADVANCED=(z3-solver ortools)
TEST_PKGS=(numpy pandas matplotlib sklearn scipy z3 ortools)

FAILED_REQUIRED=()
SUCCESS_COUNT=0
OPTIONAL_SUCCESS=0

# ---------------------------------------------------------------------------
# Color helpers (disabled when stdout is not a TTY)
# ---------------------------------------------------------------------------
if [[ -t 1 ]]; then
  C_GREEN=$'\033[32m'; C_YELLOW=$'\033[33m'; C_RED=$'\033[31m'
  C_CYAN=$'\033[36m';  C_YELLOW_H=$'\033[1;33m'; C_RESET=$'\033[0m'
else
  C_GREEN=""; C_YELLOW=""; C_RED=""; C_CYAN=""; C_YELLOW_H=""; C_RESET=""
fi

section() { printf '\n%s=== %s ===%s\n' "$C_GREEN" "$1" "$C_RESET"; }

action() {  # action MSG [STATUS]
  local msg="$1" status="${2:-INFO}"
  case "$status" in
    SUCCESS) printf '%s[%s] %s%s\n' "$C_GREEN"  "$status" "$msg" "$C_RESET" ;;
    WARNING) printf '%s[%s] %s%s\n' "$C_YELLOW" "$status" "$msg" "$C_RESET" ;;
    ERROR)   printf '%s[%s] %s%s\n' "$C_RED"    "$status" "$msg" "$C_RESET" ;;
    *)       printf '%s[%s] %s%s\n' "$C_CYAN"   "$status" "$msg" "$C_RESET" ;;
  esac
}

# ---------------------------------------------------------------------------
# Python / pip detection
# ---------------------------------------------------------------------------
if command -v python3 >/dev/null 2>&1; then
  PYTHON=python3
elif command -v python >/dev/null 2>&1; then
  PYTHON=python
else
  action "Python non disponible — installez Python 3.10+ (python.org / apt / brew)." "ERROR"
  exit 1
fi
PIP=( "$PYTHON" -m pip )

# ---------------------------------------------------------------------------
# Checkpoints (plain text, one name per line)
# ---------------------------------------------------------------------------
is_done() { [[ -f "$CHECKPOINT_FILE" ]] && grep -qx "$1" "$CHECKPOINT_FILE"; }
save_checkpoint() { printf '%s\n' "$1" >> "$CHECKPOINT_FILE"; action "Checkpoint: $1" "SUCCESS"; }
skip_if_done() {  # skip_if_done CHECKPOINT DESCRIPTION -> 0 if should skip
  if is_done "$1" && [[ $FORCE -eq 0 ]]; then
    action "Étape déjà terminée: $2" "INFO"
    return 0
  fi
  return 1
}

# ---------------------------------------------------------------------------
# Pip install helpers
# ---------------------------------------------------------------------------
pip_installed() {  # pip_installed PKG -> 0 if installed
  "${PIP[@]}" show "$1" >/dev/null 2>&1
}

install_pip_package() {  # install_pip_package PKG [OPTIONAL]
  local pkg="$1" optional="${2:-0}"
  action "Installation de $pkg via $PYTHON -m pip..." "INFO"
  if "${PIP[@]}" install "$pkg" >/dev/null 2>&1; then
    action "$pkg installé avec succès" "SUCCESS"
    return 0
  fi
  if [[ $optional -eq 1 ]]; then
    action "Échec de l'installation de $pkg" "WARNING"
  else
    action "Échec de l'installation de $pkg" "ERROR"
  fi
  return 1
}

# ---------------------------------------------------------------------------
# .NET helpers
# ---------------------------------------------------------------------------
setup_dotnet_nuget() {
  if skip_if_done "dotnet_nuget_config" "Configuration NuGet"; then return 0; fi
  if ! command -v dotnet >/dev/null 2>&1; then
    action ".NET SDK non disponible — configuration NuGet ignorée (https://dotnet.microsoft.com/download)" "WARNING"
    return 1
  fi
  if dotnet nuget list source 2>/dev/null | grep -q "nuget.org"; then
    action "Source NuGet déjà configurée" "SUCCESS"
    save_checkpoint "dotnet_nuget_config"
    return 0
  fi
  if dotnet nuget add source https://api.nuget.org/v3/index.json -n nuget.org >/dev/null 2>&1; then
    action "Source NuGet ajoutée avec succès" "SUCCESS"
    save_checkpoint "dotnet_nuget_config"
    return 0
  fi
  action "Échec de la configuration NuGet" "ERROR"
  return 1
}

install_dotnet_interactive() {
  if skip_if_done "dotnet_interactive_install" ".NET Interactive"; then return 0; fi
  if ! command -v dotnet >/dev/null 2>&1; then
    action ".NET SDK non disponible — installez-le (https://dotnet.microsoft.com/download)" "WARNING"
    return 1
  fi
  action ".NET SDK détecté : $(dotnet --version)" "SUCCESS"
  if dotnet tool list -g 2>/dev/null | grep -q "microsoft.dotnet-interactive"; then
    action ".NET Interactive déjà installé" "SUCCESS"
    save_checkpoint "dotnet_interactive_install"
    return 0
  fi
  action "Installation de .NET Interactive..." "INFO"
  if dotnet tool install -g Microsoft.dotnet-interactive >/dev/null 2>&1; then
    action ".NET Interactive installé avec succès" "SUCCESS"
    save_checkpoint "dotnet_interactive_install"
    # `dotnet tool install -g` places binaries in ~/.dotnet/tools; surface it if missing.
    case ":$PATH:" in
      *":$HOME/.dotnet/tools:"*) ;;
      *) action "Ajoutez ~/.dotnet/tools à votre PATH pour utiliser dotnet-interactive" "WARNING" ;;
    esac
    return 0
  fi
  action "Échec de l'installation .NET Interactive" "ERROR"
  return 1
}

setup_jupyter_directory() {
  if skip_if_done "jupyter_directory_setup" "Répertoire Jupyter"; then return 0; fi
  if ! command -v jupyter >/dev/null 2>&1; then
    action "Jupyter non disponible — répertoire kernels ignoré" "WARNING"; return 1
  fi
  local kernels_path
  kernels_path="$(jupyter --data-dir 2>/dev/null)/kernels"
  mkdir -p "$kernels_path"
  action "Répertoire kernels Jupyter: $kernels_path" "SUCCESS"
  save_checkpoint "jupyter_directory_setup"
}

install_python_kernel() {
  if skip_if_done "python_kernel_install" "Kernel Python"; then return 0; fi
  action "Installation du kernel Python..." "INFO"
  if "$PYTHON" -m ipykernel install --user >/dev/null 2>&1; then
    action "Kernel Python installé avec succès" "SUCCESS"
    save_checkpoint "python_kernel_install"
  else
    action "Échec de l'installation du kernel Python" "ERROR"
  fi
}

install_dotnet_kernels() {
  if skip_if_done "dotnet_kernel_install" "Kernels .NET"; then return 0; fi
  if ! command -v dotnet-interactive >/dev/null 2>&1 && ! command -v dotnet >/dev/null 2>&1; then
    action "dotnet-interactive non disponible — installation des kernels .NET ignorée" "WARNING"; return 1
  fi
  action "Installation des kernels .NET Interactive..." "INFO"
  if dotnet interactive jupyter install >/dev/null 2>&1; then
    action "Kernels .NET installés avec succès" "SUCCESS"
    save_checkpoint "dotnet_kernel_install"
  else
    action "Échec de l'installation des kernels .NET" "ERROR"
  fi
}

# =============================================================================
# INITIALISATION
# =============================================================================
section "INITIALISATION"
if [[ $RESUME -eq 1 ]]; then
  if [[ -f "$CHECKPOINT_FILE" ]]; then
    action "Mode reprise activé — checkpoints chargés depuis $CHECKPOINT_FILE" "INFO"
  else
    action "Aucun checkpoint trouvé, démarrage complet" "INFO"
  fi
else
  rm -f "$CHECKPOINT_FILE"
fi

# =============================================================================
# VÉRIFICATIONS PRÉLIMINAIRES
# =============================================================================
section "VÉRIFICATIONS PRÉLIMINAIRES"

if skip_if_done "preliminaries" "Vérifications préliminaires"; then
  : # already done in a previous resumed run
else
  # Root check — on Unix, running pip as root is discouraged (unlike Windows admin).
  if [[ "$(id -u)" -eq 0 ]]; then
    action "Script exécuté en tant que root — pip préfère un env utilisateur (venv ou --user)" "WARNING"
  fi
  if py_ver="$("$PYTHON" --version 2>&1)"; then
    action "Python détecté : $py_ver" "SUCCESS"
  else
    action "Python non disponible" "ERROR"; exit 1
  fi
  save_checkpoint "preliminaries"
fi

# =============================================================================
# INSTALLATION PACKAGES REQUIS (3 phases)
# =============================================================================
section "INSTALLATION PACKAGES REQUIS"

install_phase() {  # install_phase CHECKPOINT DESCRIPTION PHASE_NAME PACKAGES...
  local checkpoint="$1" description="$2" phase_name="$3"; shift 3
  local pkgs=("$@") phase_success=0
  if skip_if_done "$checkpoint" "$description"; then
    SUCCESS_COUNT=$((SUCCESS_COUNT + ${#pkgs[@]}))
    return 0
  fi
  action "$phase_name" "INFO"
  for pkg in "${pkgs[@]}"; do
    if pip_installed "$pkg" && [[ $FORCE -eq 0 ]]; then
      action "$pkg déjà installé" "SUCCESS"
      phase_success=$((phase_success + 1))
    elif install_pip_package "$pkg" 0; then
      phase_success=$((phase_success + 1))
    else
      FAILED_REQUIRED+=("$pkg")
    fi
  done
  if [[ $phase_success -eq ${#pkgs[@]} ]]; then
    save_checkpoint "$checkpoint"
  fi
  SUCCESS_COUNT=$((SUCCESS_COUNT + phase_success))
}

install_phase "python_packages_basic"    "Packages Python de base"     "Phase 1/3: Packages de base - numpy, pandas, matplotlib, scipy"    "${BASIC[@]}"
install_phase "python_packages_ml"       "Packages ML et Jupyter"      "Phase 2/3: Packages ML et Jupyter - scikit-learn, jupyter, ipykernel" "${ML[@]}"
install_phase "python_packages_advanced" "Packages Python avancés"     "Phase 3/3: Packages avancés - z3-solver, ortools"                 "${ADVANCED[@]}"

action "Packages requis installés : $SUCCESS_COUNT/${#REQUIRED[@]}" "INFO"

# =============================================================================
# INSTALLATION PACKAGES OPTIONNELS
# =============================================================================
if [[ $INSTALL_OPTIONAL -eq 1 ]]; then
  if ! skip_if_done "python_packages_optional" "Packages Python optionnels"; then
    section "INSTALLATION PACKAGES OPTIONNELS"
    for pkg in "${OPTIONAL[@]}"; do
      if pip_installed "$pkg" && [[ $FORCE -eq 0 ]]; then
        action "$pkg déjà installé" "SUCCESS"
        OPTIONAL_SUCCESS=$((OPTIONAL_SUCCESS + 1))
      elif install_pip_package "$pkg" 1; then
        OPTIONAL_SUCCESS=$((OPTIONAL_SUCCESS + 1))
      fi
    done
    save_checkpoint "python_packages_optional"
    action "Packages optionnels installés : $OPTIONAL_SUCCESS/${#OPTIONAL[@]}" "INFO"
  fi
fi

# =============================================================================
# CONFIGURATION .NET ET NUGET
# =============================================================================
section "CONFIGURATION .NET ET NUGET"
[[ $AUTO_FIX -eq 1 ]] && setup_dotnet_nuget || action " (--auto-fix requis pour configurer NuGet)" "INFO"

# =============================================================================
# CONFIGURATION .NET INTERACTIVE
# =============================================================================
section "CONFIGURATION .NET INTERACTIVE"
[[ $AUTO_FIX -eq 1 ]] && install_dotnet_interactive || action " (--auto-fix requis pour installer .NET Interactive)" "INFO"

# =============================================================================
# CONFIGURATION JUPYTER ET KERNELS
# =============================================================================
section "CONFIGURATION JUPYTER ET KERNELS"
if command -v jupyter >/dev/null 2>&1; then
  action "Jupyter détecté : $(jupyter --version 2>&1 | head -1)" "SUCCESS"
  if [[ $AUTO_FIX -eq 1 ]]; then
    setup_jupyter_directory
    install_python_kernel
    install_dotnet_kernels
    action "Kernels Jupyter disponibles :" "INFO"
    jupyter kernelspec list 2>/dev/null | sed 's/^/    /'
  fi
else
  action "Jupyter non disponible (sera installé par la phase Packages ML)" "ERROR"
fi

# =============================================================================
# TESTS DE L'ENVIRONNEMENT
# =============================================================================
section "TESTS DE L'ENVIRONNEMENT"

declare -a TEST_RESULTS=()
import_name_for() {  # map distribution name -> import name
  case "$1" in
    z3-solver) echo "z3" ;;
    scikit-learn) echo "sklearn" ;;
    *) echo "$1" ;;
  esac
}

action "Tests d'import des packages installés..." "INFO"
for pkg in "${TEST_PKGS[@]}"; do
  imp="$(import_name_for "$pkg")"
  if "$PYTHON" -c "import $imp" >/dev/null 2>&1; then
    action "Test import $pkg" "SUCCESS"
    TEST_RESULTS+=("OK")
  else
    action "Test import $pkg" "WARNING"
    TEST_RESULTS+=("FAILED")
  fi
done
PASSED_TESTS=0
for r in "${TEST_RESULTS[@]}"; do [[ "$r" == "OK" ]] && PASSED_TESTS=$((PASSED_TESTS + 1)); done

# =============================================================================
# RAPPORT FINAL
# =============================================================================
section "RAPPORT FINAL"

TOTAL_REQUIRED=${#REQUIRED[@]}
INSTALLED_REQUIRED=$((TOTAL_REQUIRED - ${#FAILED_REQUIRED[@]}))
SUCCESS_RATE=$(awk -v i="$INSTALLED_REQUIRED" -v t="$TOTAL_REQUIRED" 'BEGIN { printf "%.1f", (i/t)*100 }')
# Integer "rate < 90%" check (bash has no float compare): installed*10 < total*9
if (( INSTALLED_REQUIRED * 10 < TOTAL_REQUIRED * 9 )); then RATE_LOW=1; else RATE_LOW=0; fi

printf "\n%sRÉSULTATS DE L'INSTALLATION:%s\n" "$C_YELLOW_H" "$C_RESET"
rate_color="$C_GREEN"; [[ $RATE_LOW -eq 1 ]] && rate_color="$C_RED"
printf '%s- Packages requis : %s/%s (%s%%)%s\n' "$rate_color" "$INSTALLED_REQUIRED" "$TOTAL_REQUIRED" "$SUCCESS_RATE" "$C_RESET"

if [[ $INSTALL_OPTIONAL -eq 1 ]]; then
  opt_color="$C_GREEN"; [[ $OPTIONAL_SUCCESS -lt 5 ]] && opt_color="$C_YELLOW"
  printf '%s- Packages optionnels : %s/%s%s\n' "$opt_color" "$OPTIONAL_SUCCESS" "${#OPTIONAL[@]}" "$C_RESET"
fi

test_color="$C_GREEN"; [[ $PASSED_TESTS -ne ${#TEST_PKGS[@]} ]] && test_color="$C_YELLOW"
printf "%s- Tests d'import : %s/%s%s\n" "$test_color" "$PASSED_TESTS" "${#TEST_PKGS[@]}" "$C_RESET"

if [[ ${#FAILED_REQUIRED[@]} -gt 0 ]]; then
  printf '\n%sPACKAGES REQUIS ÉCHOUÉS:%s\n' "$C_RED" "$C_RESET"
  for pkg in "${FAILED_REQUIRED[@]}"; do printf '%s  - %s%s\n' "$C_RED" "$pkg" "$C_RESET"; done
  printf '\n%sCOMMANDE DE RÉCUPÉRATION:%s\n' "$C_YELLOW" "$C_RESET"
  printf '  %s -m pip install %s\n' "$PYTHON" "${FAILED_REQUIRED[*]}"
fi

printf '\n%sRECOMMANDATIONS:%s\n' "$C_CYAN" "$C_RESET"
[[ $RATE_LOW -eq 1 ]] && \
  printf '  1. Réexécuter: ./scripts/environment/setup_environment.sh --auto-fix --force\n'
printf "  2. Tester l'environnement: ./scripts/environment/audit_environment.sh\n"
printf '  3. Pour les packages optionnels: ./scripts/environment/setup_environment.sh --install-optional\n'

# Log final
{
  echo "SETUP ENVIRONNEMENT - $(date)"
  echo "================================"
  echo "Packages requis installés: $INSTALLED_REQUIRED/$TOTAL_REQUIRED ($SUCCESS_RATE%)"
  echo "Packages échoués: ${FAILED_REQUIRED[*]}"
  echo "Tests d'import réussis: $PASSED_TESTS/${#TEST_PKGS[@]}"
} > "$LOG_FILE"
printf '\nLog sauvegardé: %s\n' "$LOG_FILE"

# Exit code (same semantics as the .ps1)
if [[ ${#FAILED_REQUIRED[@]} -eq 0 && $PASSED_TESTS -eq ${#TEST_PKGS[@]} ]]; then
  printf '\n%s[OK] SETUP TERMINÉ AVEC SUCCÈS%s\n' "$C_GREEN" "$C_RESET"
  exit 0
elif [[ ${#FAILED_REQUIRED[@]} -le 2 ]]; then
  printf '\n%s[WARN] SETUP TERMINÉ AVEC AVERTISSEMENTS%s\n' "$C_YELLOW" "$C_RESET"
  exit 1
else
  printf '\n%s[FAIL] SETUP ÉCHOUÉ%s\n' "$C_RED" "$C_RESET"
  exit 2
fi
