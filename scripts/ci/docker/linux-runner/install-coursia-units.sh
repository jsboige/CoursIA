#!/usr/bin/env bash
# install-coursia-units.sh -- installeur des unites systemd du superviseur CoursIA.
#
# Pourquoi ce fichier existe (#14846, A2 seconde moitie)
# ------------------------------------------------------
# L'installation des unites systemd du superviseur CoursIA n'etait codee
# nulle part dans le depot : les commandes ne vivaient qu'en prose commentee
# dans scripts/ci/docker/linux-runner/persist/README.md (vers l. 248-272 au
# moment de l'ecriture), et le deployement d'ai-01 rapporte par #14981 etait un
# `systemctl enable --now` tape a la main. Un operateur sur une machine neuve
# suivait la prose et tapait les commandes -- l'ecart etait muet.
#
# Ce script ferme cet ecart : il porte la totalite de la sequence dans un
# seul artefact executable, versionne et revisable en PR. Il est idempotent
# (un fichier byte-identique a la cible est laisse tel quel), il refuse un
# non-root (les unites vivent sous /etc/systemd/system/), il n'ecrase pas
# une cible differente sans le demander, et il termine par la verification
# A3 (`systemctl is-enabled` + `systemctl is-active`) qui etait jusqu'ici un
# geste manuel de la lane qui deploye.
#
# PERIMETRE (cf. persist/README.md, table l.13-32)
# -- ai-01  : coursia-runner (leg d'execution, label coursia-linux),
#             coursia-waiters (pool d'attente PR-gate, label coursia-waiter),
#             coursia-ci.slice (budget agrege) + daemon.json.
# -- po-2024: coursia-runner, coursia-lean (leg Lean, label coursia-lean).
#
# Ce script ne touche PAS a po-2026 (pas d'unite systemd ; voir
# persist/po-2026/README.md pour la chaine de cette machine).
#
# ACCEPTANCE (cf. #14846, commentaires 5988958968 et 6003441571)
# -- A2 premiere moitie : l'unite survit a un redemarrage, portee par
#    `Restart=always` + `WantedBy=multi-user.target` (livree par #14981 pour
#    ai-01, par ce script pour les clones frais).
# -- A2 seconde moitie  : installation portee par un script du depot. C'est
#    l'acceptance que ce fichier ferme.
# -- A3                 : `systemctl is-enabled` rend `enabled` pour chaque
#    unite installee ; `systemctl is-active` rend `active` apres demarrage.
#    Verifie par le script en fin de course ; un echec fait sortir en code 2.

set -uo pipefail

log() { printf '[install-coursia-units] %s\n' "$*" >&2; }
die() { printf '[install-coursia-units][ABANDON] %s\n' "$*" >&2; exit 1; }

usage() {
  cat <<'EOF'
Usage : install-coursia-units.sh [--machine ai-01|po-2024] [--dry-run]

Detection automatique de la machine via le hostname court (myia-ai-01,
myia-po-2024). Forcer via --machine si la machine est videe de son prefixe
myia- ou si elle n'est pas listee.

Variables d'environnement reconnues :
  COURSIA_INSTALL_MACHINE  : force la machine cible (meme valeurs que --machine).
  COURSIA_REPO_DIR          : chemin du depot sur la machine (defaut /mnt/d/CoursIA).
  COURSIA_NO_DOCKER_RESTART : si definie, ne PAS lancer `systemctl restart
                              docker.service` (la cible docker-ce porte peut-etre
                              des conteneurs en vol ; voir persist/README.md l.264-270).
  COURSIA_INSTALL_FORCE     : si definie et non nulle, ecrase une cible dont
                              la sha256 differe de la source (defaut : refuser).

Codes de retour :
  0  : succes, toutes les unites demandees sont `enabled` et `active`.
  1  : abandon (prereq, fichier source manquant, refu root, etc.).
  2  : installation reussie mais verification A3 en echec (voir log).
EOF
}

# --- detection machine ------------------------------------------------------
detect_machine() {
  case "${HOSTNAME:-$(hostname)}" in
    myia-ai-01|ai-01)            printf 'ai-01\n' ;;
    myia-po-2024|po-2024)        printf 'po-2024\n' ;;
    *)                           printf '\n' ;;
  esac
}

icc_MACHINE="${COURSIA_INSTALL_MACHINE:-}"
icc_DRY_RUN=0
while [ $# -gt 0 ]; do
  case "$1" in
    --machine) icc_MACHINE="$2"; shift 2 ;;
    --dry-run) icc_DRY_RUN=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) die "option inconnue : $1 (essayez --help)" ;;
  esac
done

[ -n "$icc_MACHINE" ] || icc_MACHINE="$(detect_machine)"
[ -n "$icc_MACHINE" ] || die "machine non detectee (hostname=${HOSTNAME:-inconnu}) ; passez --machine ai-01|po-2024"
case "$icc_MACHINE" in
  ai-01|po-2024) ;;
  *) die "machine non supportee par ce script : $icc_MACHINE (visees : ai-01, po-2024)" ;;
esac

# --- prereq -----------------------------------------------------------------
[ "$(id -u)" -eq 0 ] || die "root requis (installation sous /etc/systemd/system/ et /etc/docker/)"
command -v systemctl >/dev/null 2>&1 || die "systemctl absent (systemd requis sur la machine cible)"
command -v install    >/dev/null 2>&1 || die "install(1) absent (coreutils requis)"

icc_REPO_DIR="${COURSIA_REPO_DIR:-/mnt/d/CoursIA}"
[ -d "$icc_REPO_DIR" ] || die "depot introuvable : $icc_REPO_DIR"
icc_PERSIST_DIR="$icc_REPO_DIR/scripts/ci/docker/linux-runner/persist"
[ -d "$icc_PERSIST_DIR" ] || die "persist/ introuvable : $icc_PERSIST_DIR"

# --- inventaire des unites selon machine ------------------------------------
# Format : "TARGET_PATH|SRC_REL_PATH|DESCRIPTION"
# (separateur '|' choisi pour eviter les collisions avec les espaces des chemins)
collect_units() {
  case "$icc_MACHINE" in
    ai-01)
      cat <<'LIST'
/etc/systemd/system/coursia-runner.service|persist/ai-01/coursia-runner.service|leg d'execution (label coursia-linux)
/usr/local/bin/coursia-runner-start.sh|persist/ai-01/coursia-runner-start.sh|wrapper de la leg d'execution
/etc/systemd/system/coursia-runner.service.d/10-sizing.conf|persist/ai-01/coursia-runner.service.d/10-sizing.conf|drop-in cgroup (CPU+memoire) de la leg d'execution
/etc/systemd/system/coursia-waiters.service|persist/ai-01/coursia-waiters.service|pool d'attente PR-gate (label coursia-waiter)
/usr/local/bin/coursia-waiters-start.sh|persist/coursia-waiters-start.sh|wrapper du pool d'attente
/etc/systemd/system/coursia-ci.slice|persist/coursia-ci.slice|budget agrege des conteneurs
/etc/docker/daemon.json|persist/daemon.json|cgroup-parent docker-ce + log-driver local
LIST
      ;;
    po-2024)
      cat <<'LIST'
/etc/systemd/system/coursia-runner.service|persist/coursia-runner.service|leg d'execution (label coursia-linux)
/usr/local/bin/coursia-runner-start.sh|persist/coursia-runner-start.sh|wrapper de la leg d'execution
/etc/systemd/system/coursia-lean.service|persist/coursia-lean.service|leg Lean (label coursia-lean)
/usr/local/bin/coursia-lean-start.sh|persist/coursia-lean-start.sh|wrapper de la leg Lean
LIST
      ;;
  esac
}

# --- install d'un fichier avec garde byte-identite --------------------------
# Usage : icc_install_unit <target> <src_rel> <desc>
icc_install_unit() {
  local target="$1" src_rel="$2" desc="$3"
  local src="$icc_PERSIST_DIR/$src_rel"

  [ -r "$src" ] || die "$src_rel introuvable dans le depot (machine=$icc_MACHINE)"

  local mode=0644
  case "$target" in
    /usr/local/bin/*|/usr/bin/*) mode=0755 ;;
  esac

  if [ ! -e "$target" ]; then
    log "INSTALL  $target  ($desc)"
    [ "$icc_DRY_RUN" -eq 1 ] || install -m "$mode" "$src" "$target"
    return 0
  fi

  local src_sha tgt_sha
  src_sha="$(sha256sum "$src" | awk '{print $1}')"
  tgt_sha="$(sha256sum "$target" | awk '{print $1}')"

  if [ "$src_sha" = "$tgt_sha" ]; then
    log "SKIP     $target  (byte-identique, sha256=${src_sha:0:12})"
    return 0
  fi

  log "DIFF     $target  ($desc)"
  log "  src    $src  sha256=${src_sha:0:12}"
  log "  cible  $target  sha256=${tgt_sha:0:12}"
  diff -u "$target" "$src" >&2 || true

  if [ "${COURSIA_INSTALL_FORCE:-0}" -ne 1 ]; then
    die "cible differente ; posez COURSIA_INSTALL_FORCE=1 pour ecraser, ou corrigez la divergence d'abord"
  fi

  log "OVERWRITE $target"
  [ "$icc_DRY_RUN" -eq 1 ] || install -m "$mode" "$src" "$target"
}

# --- routine principale -----------------------------------------------------
log "machine   = $icc_MACHINE"
log "depot     = $icc_REPO_DIR"
log "persist   = $icc_PERSIST_DIR"
[ "$icc_DRY_RUN" -eq 1 ] && log "mode      = DRY-RUN (aucune ecriture)"
log ""

icc_failed=0
while IFS='|' read -r icc_target icc_src_rel icc_desc; do
  [ -n "$icc_target" ] || continue
  if ! icc_install_unit "$icc_target" "$icc_src_rel" "$icc_desc"; then
    icc_failed=1
  fi
done < <(collect_units)

if [ "$icc_failed" -ne 0 ]; then
  die "au moins une installation a echoue"
fi

# --- daemon-reload ----------------------------------------------------------
# Necessaire apres tout ajout sous /etc/systemd/system/.
log ""
log "systemctl daemon-reload"
[ "$icc_DRY_RUN" -eq 1 ] || systemctl daemon-reload

# --- restart docker.service (gated) ----------------------------------------
# L'unite coursia-ci.slice est referencee en cgroup-parent par daemon.json ;
# un daemon qui porte des conteneurs en vol survit grace a live-restore, mais
# la survie n'est pas verifiee ici -- d'ou la garde COURSIA_NO_DOCKER_RESTART
# (cf. persist/README.md l.264-270).
if [ -z "${COURSIA_NO_DOCKER_RESTART:-}" ]; then
  log "systemctl restart docker.service  (gated : posez COURSIA_NO_DOCKER_RESTART=1 pour sauter)"
  [ "$icc_DRY_RUN" -eq 1 ] || systemctl restart docker.service
else
  log "systemctl restart docker.service  (SAUTE -- COURSIA_NO_DOCKER_RESTART pose)"
fi

# --- start coursia-ci.slice (ai-01 uniquement) ------------------------------
if [ "$icc_MACHINE" = "ai-01" ]; then
  log "systemctl start coursia-ci.slice"
  [ "$icc_DRY_RUN" -eq 1 ] || systemctl start coursia-ci.slice
fi

# --- enable + start les unites, idempotent ---------------------------------
log ""
log "enable + start des unites :"
while IFS='|' read -r icc_target _unused _desc; do
  [ -n "$icc_target" ] || continue
  case "$icc_target" in
    /etc/systemd/system/*.service|/etc/systemd/system/*.slice)
      icc_unit_name="$(basename "$icc_target")"
      log "  systemctl enable --now $icc_unit_name"
      [ "$icc_DRY_RUN" -eq 1 ] || systemctl enable --now "$icc_unit_name" || die "echec enable --now $icc_unit_name"
      ;;
  esac
done < <(collect_units)

# --- verification A3 ---------------------------------------------------------
log ""
log "verification A3 (is-enabled + is-active) :"
icc_verify_failed=0
while IFS='|' read -r icc_target _unused _desc; do
  [ -n "$icc_target" ] || continue
  case "$icc_target" in
    /etc/systemd/system/*.service|/etc/systemd/system/*.slice)
      icc_unit_name="$(basename "$icc_target")"
      icc_enabled_state="$(systemctl is-enabled "$icc_unit_name" 2>&1 || true)"
      icc_active_state="$(systemctl is-active "$icc_unit_name" 2>&1 || true)"
      log "  $icc_unit_name  is-enabled=$icc_enabled_state  is-active=$icc_active_state"
      if [ "$icc_enabled_state" != "enabled" ]; then
        log "  ECHEC A3 : $icc_unit_name is-enabled=$icc_enabled_state (attendu: enabled)"
        icc_verify_failed=1
      fi
      if [ "$icc_active_state" != "active" ]; then
        log "  ECHEC A3 : $icc_unit_name is-active=$icc_active_state (attendu: active)"
        icc_verify_failed=1
      fi
      ;;
  esac
done < <(collect_units)

if [ "$icc_verify_failed" -ne 0 ]; then
  die "verification A3 en echec (voir log ci-dessus) ; code de retour 2"
fi

log ""
log "OK -- machine=$icc_MACHINE : unites installees, activees, verifiees."
exit 0