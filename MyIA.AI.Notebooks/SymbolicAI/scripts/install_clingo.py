#!/usr/bin/env python3
"""
Script d'installation automatique de Clingo pour TweetyProject ASP

Clingo est un solveur ASP (Answer Set Programming) de la suite Potassco.
Ce script télécharge et installe automatiquement clingo.exe pour Windows.

Note: Dans les versions modernes de Clingo (5.0+), gringo a été fusionné
dans clingo. GringoGrounder de TweetyProject ne fonctionnera donc pas
directement, mais ClingoSolver fonctionne parfaitement.

Usage:
    python install_clingo.py [--target-dir ext_tools/clingo] [--force]
"""

import sys
import os
import pathlib
import urllib.request
import zipfile
import shutil
import platform


def download_file(url, dest_path, desc=""):
    """Télécharge un fichier avec barre de progression"""
    print(f"Téléchargement de {desc or url}...")

    def reporthook(blocknum, blocksize, totalsize):
        readsofar = blocknum * blocksize
        if totalsize > 0:
            percent = readsofar * 100 / totalsize
            s = f"\r{percent:5.1f}% {readsofar // 1024:,}KB / {totalsize // 1024:,}KB"
            sys.stderr.write(s)
            if readsofar >= totalsize:
                sys.stderr.write("\n")
        else:
            sys.stderr.write(f"\r{readsofar // 1024:,}KB téléchargés")

    urllib.request.urlretrieve(url, dest_path, reporthook)
    print(f"✓ Téléchargement terminé: {dest_path}")


def install_clingo_windows(target_dir, force=False):
    """
    Installe Clingo pour Windows

    Télécharge depuis GitHub releases de Potassco/clingo
    Version: 5.7.1 (dernière version stable avec binaires Windows)
    """
    target_path = pathlib.Path(target_dir)
    clingo_exe = target_path / "clingo.exe"

    # Vérifier si déjà installé
    if clingo_exe.exists() and not force:
        print(f"✓ Clingo déjà installé: {clingo_exe}")
        return str(target_path)

    # Créer le répertoire cible
    target_path.mkdir(parents=True, exist_ok=True)

    # URL de téléchargement Clingo 5.7.1 Windows 64-bit
    # Note: Clingo 5.6+ fusionne gringo en interne
    clingo_version = "5.7.1"
    clingo_url = f"https://github.com/potassco/clingo/releases/download/v{clingo_version}/clingo-{clingo_version}-win64.zip"

    # Télécharger l'archive
    zip_path = target_path / f"clingo-{clingo_version}-win64.zip"

    try:
        download_file(clingo_url, str(zip_path), f"Clingo {clingo_version} Windows")

        # Extraire clingo.exe
        print("Extraction de clingo.exe...")
        with zipfile.ZipFile(zip_path, 'r') as zip_ref:
            # L'archive contient clingo.exe directement ou dans un sous-dossier
            for file_info in zip_ref.namelist():
                if file_info.endswith('clingo.exe'):
                    # Extraire uniquement clingo.exe
                    zip_ref.extract(file_info, target_path)
                    extracted_path = target_path / file_info

                    # Déplacer vers la racine du target_dir si dans un sous-dossier
                    if extracted_path != clingo_exe:
                        shutil.move(str(extracted_path), str(clingo_exe))

                    print(f"✓ clingo.exe extrait: {clingo_exe}")
                    break

        # Nettoyer l'archive
        zip_path.unlink()

        # Nettoyer les dossiers vides
        for item in target_path.iterdir():
            if item.is_dir():
                try:
                    item.rmdir()  # Supprime seulement si vide
                except OSError:
                    pass

        print(f"\n{'='*60}")
        print(f"✓ Installation de Clingo {clingo_version} réussie!")
        print(f"  Emplacement: {target_path}")
        print(f"  Exécutable : {clingo_exe}")
        print(f"{'='*60}\n")

        return str(target_path)

    except Exception as e:
        print(f"❌ Erreur lors de l'installation de Clingo: {e}")
        # Nettoyer en cas d'erreur
        if zip_path.exists():
            zip_path.unlink()
        raise


def install_clingo_unix(target_dir, force=False):
    """
    Instructions pour installer Clingo sur Linux/macOS

    Sur Unix, il est préférable d'utiliser le gestionnaire de paquets
    """
    print("Installation de Clingo sur Linux/macOS:")
    print("")
    print("Option 1 - Conda (recommandé):")
    print("  conda install -c conda-forge clingo")
    print("")
    print("Option 2 - pip:")
    print("  pip install clingo")
    print("")
    print("Option 3 - Gestionnaire de paquets système:")
    print("  Ubuntu/Debian: sudo apt-get install gringo")
    print("  Fedora:        sudo dnf install clingo")
    print("  macOS:         brew install clingo")
    print("")
    print("Une fois installé, clingo devrait être disponible dans le PATH système.")

    return None


def main():
    import argparse

    parser = argparse.ArgumentParser(description="Installation automatique de Clingo pour ASP")
    parser.add_argument("--target-dir", default="ext_tools/clingo",
                        help="Répertoire d'installation (défaut: ext_tools/clingo)")
    parser.add_argument("--force", action="store_true",
                        help="Forcer la réinstallation même si déjà présent")

    args = parser.parse_args()

    print("="*60)
    print("Installation de Clingo (Potassco ASP Solver)")
    print("="*60)
    print(f"Plateforme: {platform.system()} {platform.machine()}")
    print(f"Répertoire cible: {args.target_dir}")
    print("")

    system = platform.system()

    try:
        if system == "Windows":
            result = install_clingo_windows(args.target_dir, args.force)
            if result:
                print("\n✓ Clingo est prêt à être utilisé avec TweetyProject!")
                print(f"  Configurez EXTERNAL_TOOLS['CLINGO'] = '{result}'")
        else:
            install_clingo_unix(args.target_dir, args.force)

        return 0

    except Exception as e:
        print(f"\n❌ Échec de l'installation: {e}")
        return 1


if __name__ == "__main__":
    sys.exit(main())
