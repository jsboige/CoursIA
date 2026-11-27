#!/usr/bin/env bash
# Compiler Gource 0.53 avec les correctifs de patches/ et installer le binaire sous un prefixe.
#
# Usage :
#   build-gource.sh [PREFIX]            PREFIX par defaut : $HOME/gource-0.53-labels
#   build-gource.sh --tarball FICHIER   archive source deja presente (sinon telechargement)
#
# Prerequis (Debian/Ubuntu) :
#   build-essential pkg-config libgl1-mesa-dev libglu1-mesa-dev libfreetype6-dev
#   libpcre2-dev libglew-dev libglm-dev libboost-filesystem-dev libboost-system-dev
#   libpng-dev libsdl2-dev libsdl2-image-dev
#
# Les options ajoutees par 0002-dir-name-labels.patch sont inactives par defaut : sans
# aucune d'elles, le binaire rend le meme flux PPM que Gource 0.53 d'origine.
set -euo pipefail

VERSION=0.53
ARCHIVE=gource-$VERSION.tar.gz
URL=https://github.com/acaudwell/Gource/releases/download/gource-$VERSION/$ARCHIVE
SHA256=3d5f64c1c6812f644c320cbc9a9858df97bc6036fc1e5f603ca46b15b8dd7237

here=$(dirname "$(readlink -f "$0")")
prefix=${HOME:-/tmp}/gource-$VERSION-labels
tarball=

while [ $# -gt 0 ]; do
  case "$1" in
    --tarball)
      [ $# -ge 2 ] || { echo "--tarball attend un chemin" >&2; exit 2; }
      tarball=$2
      shift 2
      ;;
    -h|--help)
      sed -n '2,/^set -euo/p' "$0" | sed '$d'
      exit 0
      ;;
    *)
      prefix=$1
      shift
      ;;
  esac
done

build=$(mktemp -d)
trap 'rm -rf "$build"' EXIT

if [ -z "$tarball" ]; then
  tarball=$build/$ARCHIVE
  echo "telechargement de $URL"
  if command -v curl >/dev/null 2>&1; then
    curl -fsSL -o "$tarball" "$URL"
  else
    wget -q -O "$tarball" "$URL"
  fi
fi

echo "controle de l'archive"
echo "$SHA256  $tarball" | sha256sum -c -

mkdir -p "$build/src"
tar -xzf "$tarball" -C "$build/src" --strip-components=1

for patch_file in "$here"/patches/*.patch; do
  echo "application de $(basename "$patch_file")"
  patch -d "$build/src" -p1 < "$patch_file"
done

mkdir -p "$prefix"
(
  cd "$build/src"
  ./configure --prefix="$prefix"
  make -j"${JOBS:-$(nproc)}"
  make install
)

echo "--- binaire : $prefix/bin/gource"
echo "--- options ajoutees :"
"$prefix/bin/gource" -H | grep -- '--dir-name-\(time\|direct\|hubs\|hub-alpha\)'
