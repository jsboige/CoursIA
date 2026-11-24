#!/usr/bin/env bash
# Soin de l'arbre chaud, avant le `actions/checkout` a sparse-checkout des
# workflows du pool persistant (#23287, extrait de 14 occurrences identiques).
#
# Le corps sous le marqueur est EXTRAIT, pas reecrit : il reste byte-identique a
# celui que portent encore les workflows (`19b2163f6cc3`). Ce qui change est
# l'endroit ou il vit, pas ce qu'il fait.
#
# Pourquoi un script et une action composite DISTANTE plutot qu'une action
# locale `uses: ./...` : cet appel tourne AVANT `actions/checkout`, donc
# `.github/actions/` n'est pas encore dans l'espace de travail -- absent sur un
# pool froid, porteur de l'arbre du job precedent sur un pool chaud. Une action
# locale est structurellement impossible ici.
# --- corps extrait : byte-identique au bloc des workflows (#23287) ---
set -u
if [ -d "$GITHUB_WORKSPACE/.git" ]; then
  if ! dirty=$(git -C "$GITHUB_WORKSPACE" -c safe.directory="$GITHUB_WORKSPACE" status --porcelain 2>/dev/null); then
    echo "::warning::[heal-worktree] probe git status muet -- etat de l'arbre inconnu, reset applique quand meme (#22722)"
    dirty=""
  fi
  untracked=$(printf '%s\n' "$dirty" | grep -c '^??' || true)
  first_dirty=$(printf '%s\n' "$dirty" | head -n 1)
  if ! git -C "$GITHUB_WORKSPACE" -c safe.directory="$GITHUB_WORKSPACE" reset --hard --quiet; then
    echo "::warning::[heal-worktree] reset --hard a echoue -- le retrecissement sparse peut refuser (#22722)"
  elif [ -n "$dirty" ]; then
    echo "::notice::[heal-worktree] reset --hard effectue -- le job precedent avait laisse un etat sale (${first_dirty}) -- ${untracked} entree(s) non suivie(s) laissee(s) en place -- le retrecissement sparse passe (#22722)"
  fi
fi
