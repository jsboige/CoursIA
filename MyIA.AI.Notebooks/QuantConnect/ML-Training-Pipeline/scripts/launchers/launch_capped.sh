#!/usr/bin/env bash
# Adaptateur POSIX du lanceur commun scripts/ci/run_guarded.py.
# La garde reste l'unique implementation des plafonds RSS, RAM libre et N=1.

set -euo pipefail

usage() {
    cat <<'EOF'
Usage : launch_capped.sh --log-path FICHIER --err-path FICHIER --pid-path FICHIER
                         [--memory-cap-gib N] [--reserve-gib N]
                         [--max-commit-charge-pct N] [--lock-path FICHIER]
                         [--python-exe FICHIER] -- COMMANDE [ARGUMENT...]

Lance la commande au premier plan sous la garde POSIX de run_guarded.py.
Le superviseur mesure le RSS cumule et la RAM libre, tient un verrou N=1,
ecrit le PID et transmet le code de sortie de la commande.
EOF
}

memory_cap_gib=48
reserve_gib=4
max_commit_charge_pct=90
lock_path="${XDG_RUNTIME_DIR:-${TMPDIR:-/tmp}}/coursia-train-ai01.lock"
python_exe="${PYTHON:-python3}"
log_path=""
err_path=""
pid_path=""
command=()

while (($#)); do
    case "$1" in
        --help|-h)
            usage
            exit 0
            ;;
        --memory-cap-gib)
            (($# >= 2)) || { echo "Valeur manquante pour $1" >&2; exit 2; }
            memory_cap_gib=$2
            shift 2
            ;;
        --reserve-gib)
            (($# >= 2)) || { echo "Valeur manquante pour $1" >&2; exit 2; }
            reserve_gib=$2
            shift 2
            ;;
        --max-commit-charge-pct)
            (($# >= 2)) || { echo "Valeur manquante pour $1" >&2; exit 2; }
            max_commit_charge_pct=$2
            shift 2
            ;;
        --log-path)
            (($# >= 2)) || { echo "Valeur manquante pour $1" >&2; exit 2; }
            log_path=$2
            shift 2
            ;;
        --err-path)
            (($# >= 2)) || { echo "Valeur manquante pour $1" >&2; exit 2; }
            err_path=$2
            shift 2
            ;;
        --pid-path)
            (($# >= 2)) || { echo "Valeur manquante pour $1" >&2; exit 2; }
            pid_path=$2
            shift 2
            ;;
        --lock-path)
            (($# >= 2)) || { echo "Valeur manquante pour $1" >&2; exit 2; }
            lock_path=$2
            shift 2
            ;;
        --python-exe)
            (($# >= 2)) || { echo "Valeur manquante pour $1" >&2; exit 2; }
            python_exe=$2
            shift 2
            ;;
        --)
            shift
            command=("$@")
            break
            ;;
        *)
            echo "Option inconnue : $1" >&2
            usage >&2
            exit 2
            ;;
    esac
done

for required in log_path err_path pid_path; do
    if [[ -z "${!required}" ]]; then
        echo "Option obligatoire absente : --${required//_/-}" >&2
        usage >&2
        exit 2
    fi
done
if ((${#command[@]} == 0)); then
    echo "Commande absente : fournir -- COMMANDE [ARGUMENT...]" >&2
    usage >&2
    exit 2
fi

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd -- "${script_dir}/../../../../.." && pwd)"
guarded="${repo_root}/scripts/ci/run_guarded.py"
if [[ ! -f "$guarded" ]]; then
    echo "Organe introuvable : $guarded" >&2
    exit 5
fi
if ! command -v "$python_exe" >/dev/null 2>&1 && [[ ! -x "$python_exe" ]]; then
    echo "Interpreteur Python introuvable : $python_exe" >&2
    exit 5
fi

exec "$python_exe" "$guarded" \
    --limit-gib "$memory_cap_gib" \
    --reserve-gib "$reserve_gib" \
    --max-commit-charge-pct "$max_commit_charge_pct" \
    --exclusive-lock "$lock_path" \
    --pid-file "$pid_path" \
    --log "$log_path" \
    --stderr-file "$err_path" \
    -- "${command[@]}"
