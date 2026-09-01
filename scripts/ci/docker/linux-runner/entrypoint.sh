#!/bin/bash
# Enregistrement ephemere du runner conteneurise. Le token ne passe JAMAIS
# par argv (pattern manage_self_hosted_runner.py) : config.sh lit
# ACTIONS_RUNNER_INPUT_TOKEN. Requis a l'appel (docker run -e ...) :
#   ACTIONS_RUNNER_INPUT_TOKEN   token d'enregistrement (valable 1 h)
#   ACTIONS_RUNNER_INPUT_URL     https://github.com/jsboige/CoursIA
#   ACTIONS_RUNNER_INPUT_NAME    myia-po-2024-linux-docker
#   ACTIONS_RUNNER_INPUT_LABELS  self-hosted,coursia-ephemeral,coursia-linux
set -euo pipefail

: "${ACTIONS_RUNNER_INPUT_TOKEN:?RUNNER token manquant}"
: "${ACTIONS_RUNNER_INPUT_URL:?RUNNER url manquante}"
: "${ACTIONS_RUNNER_INPUT_NAME:?RUNNER name manquant}"
: "${ACTIONS_RUNNER_INPUT_LABELS:?RUNNER labels manquants}"

export ACTIONS_RUNNER_INPUT_EPHEMERAL=true
export ACTIONS_RUNNER_INPUT_REPLACE=true
export ACTIONS_RUNNER_INPUT_WORK=/home/runner/_work

cd /opt/runner
./config.sh --unattended --ephemeral --replace

# Teardown symetrique : --ephemeral desenregistre de lui-meme apres le job ;
# le trap couvre les sorties en erreur (config echoue, run.sh interrompu).
trap './config.sh remove --unattended || true' EXIT

exec ./run.sh
