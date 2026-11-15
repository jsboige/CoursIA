#!/usr/bin/env bash
# Shared JDK locator for the Tweety rebuild recipes in this directory.

_coursia_physical_executable() {
    local path=$1
    local directory target

    while [ -L "$path" ]; do
        directory=$(cd -P "$(dirname "$path")" && pwd) || return 1
        target=$(readlink "$path") || return 1
        case "$target" in
            /*) path=$target ;;
            *) path=$directory/$target ;;
        esac
    done

    directory=$(cd -P "$(dirname "$path")" && pwd) || return 1
    printf '%s/%s\n' "$directory" "$(basename "$path")"
}

_coursia_jdk_home_from_executable() {
    local executable=$1
    local name

    for name in javac javac.exe; do
        if [ "$(basename "$executable")" = "$name" ]; then
            executable=$(_coursia_physical_executable "$executable") || return 1
            local java_home
            java_home=$(cd -P "$(dirname "$(dirname "$executable")")" && pwd) || return 1
            if [ -x "$java_home/bin/java" ] || [ -x "$java_home/bin/java.exe" ]; then
                printf '%s\n' "$java_home"
                return 0
            fi
            printf 'JDK invalide : javac trouve sans java compagnon dans %s\n' "$java_home" >&2
            return 1
        fi
    done

    printf 'JDK invalide : executable attendu javac ou javac.exe, recu %s\n' "$executable" >&2
    return 1
}

coursia_resolve_java_home() {
    local configured=${JAVA_HOME+x}
    local javac_path java_home

    if [ "$configured" = x ]; then
        if [ -z "$JAVA_HOME" ]; then
            printf 'JAVA_HOME est defini mais vide ; renseignez la racine d’un JDK.\n' >&2
            return 1
        fi
        java_home=$(cd -P "$JAVA_HOME" 2>/dev/null && pwd) || {
            printf 'JAVA_HOME invalide ou inaccessible : %s\n' "$JAVA_HOME" >&2
            return 1
        }
        for javac_path in "$java_home/bin/javac" "$java_home/bin/javac.exe"; do
            if [ -x "$javac_path" ]; then
                _coursia_jdk_home_from_executable "$javac_path"
                return $?
            fi
        done
        printf 'JAVA_HOME ne pointe pas vers un JDK (javac absent) : %s\n' "$java_home" >&2
        return 1
    fi

    javac_path=$(command -v javac 2>/dev/null) || javac_path=$(command -v javac.exe 2>/dev/null) || {
        printf 'Aucun JDK configure : definissez JAVA_HOME ou placez javac sur PATH.\n' >&2
        return 1
    }
    _coursia_jdk_home_from_executable "$javac_path"
}
