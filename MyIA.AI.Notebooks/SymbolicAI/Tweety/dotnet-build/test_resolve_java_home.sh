#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
# shellcheck source=resolve_java_home.sh
source "$SCRIPT_DIR/resolve_java_home.sh"

TEMP_ROOT=$(mktemp -d)
trap 'rm -rf "$TEMP_ROOT"' EXIT

make_jdk() {
    local root=$1
    mkdir -p "$root/bin"
    : > "$root/bin/java"
    : > "$root/bin/javac"
    chmod +x "$root/bin/java" "$root/bin/javac"
}

EXPECTED="$TEMP_ROOT/Java SDK/JDK 17"
make_jdk "$EXPECTED"
JAVA_HOME="$EXPECTED"
export JAVA_HOME
resolved=$(coursia_resolve_java_home)
[ "$resolved" = "$EXPECTED" ] || {
    printf 'FAIL: explicit JDK path with spaces resolved to %s\n' "$resolved" >&2
    exit 1
}

JAVA_HOME="$TEMP_ROOT/JDK link"
ln -s "$EXPECTED" "$JAVA_HOME"
export JAVA_HOME
resolved=$(coursia_resolve_java_home)
[ "$resolved" = "$EXPECTED" ] || {
    printf 'FAIL: symlinked JAVA_HOME resolved to %s\n' "$resolved" >&2
    exit 1
}

# An unset JAVA_HOME discovers javac through a symlink and returns the physical JDK.
unset JAVA_HOME
mkdir -p "$TEMP_ROOT/bin"
ln -s "$EXPECTED/bin/javac" "$TEMP_ROOT/bin/javac"
PATH="$TEMP_ROOT/bin:/usr/bin:/bin"
export PATH
resolved=$(coursia_resolve_java_home)
[ "$resolved" = "$EXPECTED" ] || {
    printf 'FAIL: PATH symlink resolved to %s\n' "$resolved" >&2
    exit 1
}

# An explicitly invalid JDK must fail even when a valid javac exists on PATH.
mkdir -p "$TEMP_ROOT/JRE/bin"
: > "$TEMP_ROOT/JRE/bin/java"
chmod +x "$TEMP_ROOT/JRE/bin/java"
JAVA_HOME="$TEMP_ROOT/JRE"
export JAVA_HOME
if coursia_resolve_java_home >/dev/null 2>&1; then
    printf 'FAIL: JRE-only JAVA_HOME was accepted\n' >&2
    exit 1
fi

# The implicit PATH route also rejects a JRE without javac.
unset JAVA_HOME
PATH="$TEMP_ROOT/jre-bin:/usr/bin:/bin"
mkdir -p "$TEMP_ROOT/jre-bin"
ln -s "$TEMP_ROOT/JRE/bin/java" "$TEMP_ROOT/jre-bin/java"
export PATH
if coursia_resolve_java_home >/dev/null 2>&1; then
    printf 'FAIL: absent javac was accepted\n' >&2
    exit 1
fi

printf 'OK: paths with spaces, JDK symlinks, PATH discovery, and JDK/JRE rejection\n'
