#!/usr/bin/env bash
# Point d'entree du service tts-zonos3 : lance le serveur natif zonos3.cpp.
#
# Le serveur de l'amont lie 127.0.0.1 et tourne sur CPU par defaut sur Linux ;
# dans un conteneur les deux defaults rendent le port injoignable depuis
# l'hote et la synthese dix fois plus lente. Les deux sont forces ici.
set -euo pipefail

MODEL_DIR="${ZONOS3_MODEL_DIR:-/models}"
BACKBONE="${ZONOS3_BACKBONE:-${MODEL_DIR}/backbone-ptq.gguf}"
PORT="${ZONOS3_PORT:-1919}"

fail_missing() {
    echo "tts-zonos3: fichier de modele absent : $1 (voir README.md, section « Poids : jeu minimal »)" >&2
    exit 2
}

# Obligatoires : le backbone PTQ et le decodeur keep2 (auto-detector par le
# serveur a cote du backbone).
[ -f "${BACKBONE}" ] || fail_missing "${BACKBONE}"
[ -f "${MODEL_DIR}/zac-keep2.gguf" ] || fail_missing "${MODEL_DIR}/zac-keep2.gguf"

args=(--host 0.0.0.0 --port "${PORT}" --gpu)

# Largeur de traitement simultane (sessions de synthese en parallele). Le
# serveur annonce 8 par defaut ; une valeur plus basse reduit la memoire du
# cache et l'empreinte VRAM.
if [ -n "${ZONOS3_BATCH:-}" ]; then
    args+=(--batch "${ZONOS3_BATCH}")
fi

# Répertoire des voix livrées (identifiants de GET /v2/speakers) : optionnel.
if [ -d "${ZONOS3_VOICES_DIR:-${MODEL_DIR}/voices}" ]; then
    args+=(--tts-default-voices-dir "${ZONOS3_VOICES_DIR:-${MODEL_DIR}/voices}")
fi

echo "tts-zonos3: zonos3-server ${BACKBONE} ${args[*]}"
exec zonos3-server "${BACKBONE}" "${args[@]}"
