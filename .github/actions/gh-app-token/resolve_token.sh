#!/usr/bin/env bash
# Rends le jeton REST a utiliser, sur GITHUB_OUTPUT.
#
# Contrat (volet D de #26739) :
# - `APP_TOKEN` non vide -> jeton d'installation de l'App : seau de quota
#   distinct de celui de `GITHUB_TOKEN` ;
# - sinon, `FALLBACK_TOKEN` non vide -> repli sur le jeton du job
#   (`GITHUB_TOKEN`) : comportement d'aujourd'hui, mecanisme inerte ;
# - sinon -> ERREUR nommee : aucun jeton, aucune sortie silencieuse.
#
# Les deux lignes ecrites sont `token` puis `source`, dans cet ordre. Le test
# (`scripts/tests/test_gh_app_token_action.py`) les lit telles quelles : une
# reordering du contrat se voit donc dans les tests.
#
# Le journal porte une ligne `api-quota:` -- meme famille que celle du PR gate
# (`api-quota: N gh api call(s)`) -- pour qu'un balayage de journaux sache
# d'ou vient le jeton sans ouvrir le job.

set -u

APP_TOKEN="${APP_TOKEN:-}"
FALLBACK_TOKEN="${FALLBACK_TOKEN:-}"
OUTPUT="${GITHUB_OUTPUT:-}"

if [ -z "$OUTPUT" ]; then
  echo "resolve_token: GITHUB_OUTPUT absent : aucune destination pour le jeton" >&2
  exit 1
fi

if [ -n "$APP_TOKEN" ]; then
  printf 'token=%s\n' "$APP_TOKEN" >> "$OUTPUT"
  printf 'source=app\n' >> "$OUTPUT"
  echo "api-quota: source=app (seau de l'App, distinct de GITHUB_TOKEN)"
  exit 0
fi

if [ -n "$FALLBACK_TOKEN" ]; then
  printf 'token=%s\n' "$FALLBACK_TOKEN" >> "$OUTPUT"
  printf 'source=github-token\n' >> "$OUTPUT"
  echo "api-quota: source=github-token (repli, seau partage du depot)"
  exit 0
fi

echo "resolve_token: ni APP_TOKEN ni FALLBACK_TOKEN : aucun jeton disponible" >&2
exit 1
