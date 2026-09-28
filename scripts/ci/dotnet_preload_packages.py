#!/usr/bin/env python3
"""Helper de prechargement NuGet -> assemblies locales (#17361).

POURQUOI CE SCRIPT EXISTE
-------------------------
Sur dotnet-interactive 1.0.617701 (pin cluster), le 2e `#r "nuget:"` d'une
session kernel leve par intermittence

    System.ArgumentException: Must provide errors when succeeded is false

dans `PackageRestoreResult..ctor` (mesure c.760 : repro 3 fois sur 3 le
2026-09-22, puis NON reproduit sur les 2 re-tentatives du 2026-09-23, a cache
chaud comme a cache froid). Le bug est donc **non deterministe** et sa cause
racine est interne a `Microsoft.DotNet.Interactive.PackageManagement`.

Quand l'exception tombe, elle tue la cellule sans contournement runtime : le
seul chemin defensif est de ne plus appeler `#r "nuget:"` du tout, et de
precharger chaque package en assembly locale referencee par chemin.

    #r "nuget: QuikGraph, 2.5.0"   ->   #r "./_deps/QuikGraph.dll"

Le `#r` est resolu au PARSE-TIME et n'accepte ni variable ni interpolation :
le chemin doit etre un LITTERAL relatif au dossier du notebook (forme mesuree
c.790/c.803). D'ou ce helper : il resout le cache NuGet, copie les DLL a plat
dans `_deps/` et emet un manifest donnant les lignes `#r` pretes a coller.

Contexte et mesures : `docs/reference/dotnet-restore-rfc-17361.md` (livrable 2).

PORTEE -- ce que ce helper ne fait PAS
--------------------------------------
- **Pas de dependances transitives.** Un package qui en declare d'autres (IKVM
  par exemple) doit les lister lui-meme dans la ligne de commande. Ce choix est
  delibere : copier l'arbre de dependances entier noierait `_deps/` et
  masquerait ce qui est reellement reference.
- **Pas de devinette de TFM.** Seuls les dossiers `lib/<tfm>/` sont lus ; un
  package sans `lib` (meta-package, `ref-only`) est signale comme tel, pas
  approxime.
- **`dotnet restore` seulement en dernier recours** : il n'est invoque que si
  le package est absent du cache global NuGet. Un cache deja peuple se lit hors
  ligne, sans SDK installe.

USAGE
-----
    python scripts/ci/dotnet_preload_packages.py QuikGraph==2.5.0 CsvHelper==33.0.1
    python scripts/ci/dotnet_preload_packages.py IKVM --dest _deps --json

Code de sortie : 0 si TOUS les packages ont ete resolus, 1 sinon (le detail par
package est dans le manifest et sur stdout).
"""
from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

# Version du format de manifest -- incrementee si les cles changent.
SCHEMA = 1

# Ordre de preference des Target Frameworks : le premier trouve dans le package
# gagne. .NET 9 est le TFM du cluster (CLAUDE.md section E) ; les `netstandard`
# couvrent les packages anciens qui n'ont pas de build moderne.
TFM_PREFERENCE = (
    "net9.0",
    "net8.0",
    "net7.0",
    "net6.0",
    "netstandard2.1",
    "netstandard2.0",
)

# TFM du projet jetable utilise par `dotnet restore`. Sans importance pour le
# telechargement (le projet ne compile pas), mais NuGet exige un TFM valide.
RESTORE_TFM = "net9.0"

# `Name`, `Name==1.2.3` ou `Name@1.2.3`. Noms et versions NuGet s'ecrivent en
# [A-Za-z0-9_.-] ; le `+` des metadonnees de build est volontairement exclu
# (ambigu avec une future syntaxe de selection).
_SPEC_RE = re.compile(
    r"^(?P<name>[A-Za-z0-9_.-]+)(?:(?:==|@)(?P<version>[A-Za-z0-9_.-]+))?$"
)


def parse_spec(spec: str) -> tuple[str, str | None]:
    """`Name[==version|@version]` -> `(nom, version ou None)`.

    Leve `ValueError` si la specification est vide ou mal formee -- l'appelant
    transforme cela en entree d'erreur du manifest, jamais en crash.
    """
    match = _SPEC_RE.match(spec.strip())
    if match is None:
        raise ValueError(
            f"specification invalide {spec!r} : attendu `Nom` ou `Nom==1.2.3`"
        )
    return match.group("name"), match.group("version")


def nuget_root() -> Path:
    """Racine du cache global NuGet (`NUGET_PACKAGES` sinon `~/.nuget/packages`)."""
    override = os.environ.get("NUGET_PACKAGES")
    if override:
        return Path(override)
    return Path.home() / ".nuget" / "packages"


def _version_key(version: str) -> tuple[tuple[int, ...], int, str]:
    """Cle de tri SemVer approximative, suffisante pour choisir le plus recent.

    Deux pieges que le tri lexicographique rate :
      - `2.10.0` doit trier AU-DESSUS de `2.9.0` (comparaison numerique) ;
      - `1.0.0-rc1` doit trier SOUS `1.0.0` (une prerelease precede sa release).
    """
    core, _, pre = version.partition("-")
    parts: list[int] = []
    for chunk in core.split("."):
        parts.append(int(chunk) if chunk.isdigit() else 0)
    while len(parts) < 4:
        parts.append(0)
    # 0 = prerelease, 1 = release : la release gagne a coeur egal.
    return (tuple(parts), 0 if pre else 1, pre)


def resolve_version(root: Path, package: str, requested: str | None) -> Path | None:
    """Dossier de version dans le cache, ou `None` si le package n'y est pas.

    NuGet ecrit ses dossiers en minuscules : la recherche l'est aussi. Si
    `requested` est fourni, la correspondance est EXACTE (pas de repli
    silencieux sur une autre version -- un pin non satisfait doit se voir).
    """
    package_dir = root / package.lower()
    if not package_dir.is_dir():
        return None
    if requested is not None:
        candidate = package_dir / requested.lower()
        return candidate if candidate.is_dir() else None
    versions = [child for child in package_dir.iterdir() if child.is_dir()]
    if not versions:
        return None
    return max(versions, key=lambda child: _version_key(child.name))


def pick_assemblies(version_dir: Path) -> list[Path]:
    """DLL du meilleur TFM disponible dans `<version_dir>/lib/`, sinon `[]`.

    Repli sur le premier dossier `lib/*` en ordre alphabetique quand aucun TFM
    prefere n'est present : mieux qu'un echec, et le manifest dit lequel a ete
    pris (le chemin des assemblies copiees).
    """
    lib_dir = version_dir / "lib"
    if not lib_dir.is_dir():
        return []
    by_tfm = {child.name.lower(): child for child in lib_dir.iterdir() if child.is_dir()}
    for tfm in TFM_PREFERENCE:
        if tfm in by_tfm:
            return sorted(by_tfm[tfm].glob("*.dll"))
    if by_tfm:
        return sorted(by_tfm[sorted(by_tfm)[0]].glob("*.dll"))
    return []


def restore_via_dotnet(
    package: str, version: str | None, timeout: int = 300
) -> tuple[bool, str]:
    """Peuple le cache global NuGet par un `dotnet restore` de projet jetable.

    Le projet utilise `PackageDownload` et non `PackageReference` : c'est
    l'item NuGet prevu pour *telecharger* un package sans contrainte de
    compatibilite de framework. Un `PackageReference` echouerait en NU1202 sur
    tout package qui ne cible pas le TFM du projet -- ce qui n'a aucun sens ici,
    puisque rien ne sera compile.

    Rend `(ok, message)`. Aucune exception ne remonte : un `dotnet` absent ou un
    reseau coupe sont des echecs ORDINAIRES du helper, pas un crash -- le helper
    reste utilisable hors ligne sur un cache deja peuple.
    """
    if version is None:
        return False, (
            f"{package} absent du cache et aucune version epinglee : "
            "`dotnet restore` exige `Nom==x.y.z`"
        )

    dotnet = shutil.which("dotnet")
    if dotnet is None:
        return False, "dotnet introuvable dans le PATH"

    project = (
        '<Project Sdk="Microsoft.NET.Sdk">\n'
        "  <PropertyGroup>\n"
        f"    <TargetFramework>{RESTORE_TFM}</TargetFramework>\n"
        "    <EnableDefaultCompileItems>false</EnableDefaultCompileItems>\n"
        "  </PropertyGroup>\n"
        "  <ItemGroup>\n"
        f'    <PackageDownload Include="{package}" Version="[{version}]" />\n'
        "  </ItemGroup>\n"
        "</Project>\n"
    )

    try:
        with tempfile.TemporaryDirectory(prefix="dotnet-preload-") as tmp:
            project_path = Path(tmp) / "preload.csproj"
            project_path.write_text(project, encoding="utf-8", newline="\n")
            proc = subprocess.run(
                [dotnet, "restore", str(project_path), "--nologo", "-v", "quiet"],
                capture_output=True,
                text=True,
                # `dotnet` ecrit ses erreurs en francais accentue ("Aucun package
                # associe...") : sans encoding explicite, un hote cp1252 leve
                # UnicodeDecodeError sur ce payload UTF-8 (#13140 / #12811).
                encoding="utf-8",
                errors="replace",
                timeout=timeout,
            )
    except subprocess.TimeoutExpired:
        return False, f"dotnet restore timeout apres {timeout}s"
    except OSError as exc:  # binaire present mais non executable
        return False, f"dotnet restore impossible a lancer : {exc}"

    if proc.returncode != 0:
        # `dotnet restore` ecrit ses erreurs sur STDOUT en mode quiet (mesure
        # 2026-09-25 : un package inexistant rend stderr vide) -- lire les deux
        # flux, sinon le diagnostic se reduit a "(stderr vide)".
        raw = (proc.stdout or "") + "\n" + (proc.stderr or "")
        lines = [line.strip() for line in raw.splitlines() if line.strip()]
        tail = " | ".join(lines[-3:]) if lines else "(aucune sortie)"
        return False, f"dotnet restore rc={proc.returncode} : {tail}"
    return True, f"dotnet restore rc=0 ({package} {version})"


def _reference_line(dest: Path, dll_name: str) -> str:
    """Ligne `#r` a coller dans le notebook, forme relative mesuree c.790.

    Un chemin relatif est prefixe de `./` (la forme litterale verifiee) ; un
    chemin absolu est rendu tel quel, faute de pouvoir etre relatif au notebook.
    """
    if dest.is_absolute():
        return f'#r "{dest.as_posix()}/{dll_name}"'
    return f'#r "./{dest.as_posix()}/{dll_name}"'


def main(argv: list[str] | None = None, restorer=restore_via_dotnet) -> int:
    """Point d'entree. `restorer` est injectable pour les tests (pas de reseau)."""
    parser = argparse.ArgumentParser(
        prog="dotnet_preload_packages",
        description="Precharge des packages NuGet en assemblies locales (#17361).",
    )
    parser.add_argument(
        "packages",
        nargs="+",
        help="packages a precharger : `Nom` ou `Nom==1.2.3`",
    )
    parser.add_argument(
        "--dest",
        default="_deps",
        help="dossier de destination des DLL (defaut : _deps, gitignore)",
    )
    parser.add_argument(
        "--manifest",
        default=None,
        help="chemin du manifest (defaut : <dest>/.NET-packages.json)",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="ecrire le manifest complet sur stdout au lieu du resume",
    )
    args = parser.parse_args(argv)

    root = nuget_root()
    dest = Path(args.dest)
    dest.mkdir(parents=True, exist_ok=True)
    manifest_path = Path(args.manifest) if args.manifest else dest / ".NET-packages.json"

    entries: list[dict] = []
    for spec in args.packages:
        entry: dict = {"spec": spec}
        try:
            name, requested = parse_spec(spec)
        except ValueError as exc:
            entries.append({**entry, "error": str(exc)})
            continue

        entry.update({"package": name, "requested_version": requested})
        version_dir = resolve_version(root, name, requested)

        if version_dir is None:
            ok, message = restorer(name, requested)
            entry["restore"] = message
            if not ok:
                entries.append({**entry, "error": message})
                continue
            version_dir = resolve_version(root, name, requested)
            if version_dir is None:
                entries.append(
                    {
                        **entry,
                        "error": "restore annonce rc=0 mais le package reste "
                        "introuvable dans le cache",
                    }
                )
                continue

        entry["version"] = version_dir.name
        dlls = pick_assemblies(version_dir)
        if not dlls:
            entries.append(
                {
                    **entry,
                    "error": f"aucune assembly dans {(version_dir / 'lib').as_posix()} "
                    "(meta-package ou ref-only ?)",
                }
            )
            continue

        copied: list[str] = []
        for dll in dlls:
            target = dest / dll.name
            shutil.copy2(dll, target)
            copied.append(target.as_posix())
        entry["assemblies"] = copied
        entry["reference"] = [_reference_line(dest, Path(path).name) for path in copied]
        entries.append(entry)

    payload = {
        "schema": SCHEMA,
        "issue": 17361,
        "dest": dest.as_posix(),
        "nuget_root": root.as_posix(),
        "packages": entries,
    }
    manifest_path.parent.mkdir(parents=True, exist_ok=True)
    manifest_path.write_text(
        json.dumps(payload, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
        newline="\n",
    )

    failed = [entry for entry in entries if "error" in entry]
    if args.json:
        print(json.dumps(payload, indent=2, ensure_ascii=False))
    else:
        for entry in entries:
            if "error" in entry:
                print(f"[KO] {entry['spec']} : {entry['error']}")
                continue
            print(f"[OK] {entry['spec']} -> {entry['version']} "
                  f"({len(entry['assemblies'])} assembly(ies))")
            for line in entry["reference"]:
                print(f"     {line}")
        print(f"manifest : {manifest_path.as_posix()}")

    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
