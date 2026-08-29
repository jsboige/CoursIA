#!/usr/bin/env python3
"""
Script d'installation automatique d'un JDK portable pour SymbolicAI Argument Analysis
Télécharge et installe automatiquement OpenJDK 17 si aucun JDK n'est disponible
"""

import os
import platform
import pathlib
import subprocess
import zipfile
import urllib.request
import logging
import sys

# Configuration JDK
JDK_VERSION = "17.0.11"
JDK_BUILD = "zulu17.50.19-ca-jdk17.0.11"
JDK_PORTABLE_DIR = pathlib.Path(__file__).parent / "jdk-17-portable"

# URLs par plateforme
JDK_URLS = {
    "Windows": f"https://cdn.azul.com/zulu/bin/{JDK_BUILD}-win_x64.zip",
    "Linux": f"https://cdn.azul.com/zulu/bin/{JDK_BUILD}-linux_x64.tar.gz",
    "Darwin": f"https://cdn.azul.com/zulu/bin/{JDK_BUILD}-macosx_x64.tar.gz"
}

def setup_logging():
    """Configure le logging pour le script."""
    logging.basicConfig(
        level=logging.INFO,
        format='%(asctime)s [%(levelname)s] %(message)s',
        datefmt='%H:%M:%S'
    )
    return logging.getLogger("JDKPortable")

def detect_system_jdk() -> bool:
    """Détecte si un JDK système est disponible."""
    logger = logging.getLogger("JDKPortable")
    
    try:
        # Test java command
        result = subprocess.run(["java", "-version"], 
                              capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=10)
        if result.returncode == 0:
            version_info = result.stderr.split('\n')[0] if result.stderr else 'Version inconnue'
            logger.info(f"✅ JDK système détecté: {version_info}")
            return True
    except (FileNotFoundError, subprocess.TimeoutExpired):
        pass
    
    # Test JAVA_HOME
    java_home = os.getenv("JAVA_HOME")
    if java_home and pathlib.Path(java_home).exists():
        java_exe = pathlib.Path(java_home) / "bin" / ("java.exe" if platform.system() == "Windows" else "java")
        if java_exe.exists():
            logger.info(f"✅ JDK via JAVA_HOME détecté: {java_home}")
            return True
    
    logger.info("❌ Aucun JDK système détecté")
    return False

def detect_portable_jdk() -> pathlib.Path:
    """Détecte si le JDK portable local existe et retourne son chemin."""
    logger = logging.getLogger("JDKPortable")
    
    if not JDK_PORTABLE_DIR.exists():
        return None
    
    # Chercher java.exe dans les sous-dossiers
    java_exe = "java.exe" if platform.system() == "Windows" else "java"
    for root, dirs, files in os.walk(JDK_PORTABLE_DIR):
        java_path = pathlib.Path(root) / "bin" / java_exe
        if java_path.exists():
            jdk_home = java_path.parent.parent
            logger.info(f"✅ JDK portable détecté: {jdk_home}")
            return jdk_home
    
    logger.info("❌ JDK portable non trouvé ou invalide")
    return None

def download_and_install_portable_jdk() -> pathlib.Path:
    """Télécharge et installe le JDK portable."""
    logger = logging.getLogger("JDKPortable")
    system = platform.system()
    
    if system not in JDK_URLS:
        logger.error(f"❌ Plateforme '{system}' non supportée pour JDK portable")
        return None
    
    jdk_url = JDK_URLS[system]
    archive_name = f"jdk-portable.{('zip' if system == 'Windows' else 'tar.gz')}"
    archive_path = pathlib.Path(archive_name)
    
    try:
        logger.info(f"📥 Téléchargement JDK {JDK_VERSION} depuis {jdk_url[:60]}...")
        
        # Téléchargement avec barre de progression
        def progress_hook(block_num, block_size, total_size):
            if total_size > 0 and block_num % 100 == 0:
                percent = min(100, (block_num * block_size * 100) // total_size)
                print(f"\r   📥 Téléchargement... {percent}%", end="", flush=True)
        
        urllib.request.urlretrieve(jdk_url, archive_path, progress_hook)
        print()  # Nouvelle ligne après la barre de progression
        logger.info(f"✅ Téléchargement terminé: {archive_path}")
        
        # Extraction
        logger.info(f"📦 Extraction vers {JDK_PORTABLE_DIR}...")
        JDK_PORTABLE_DIR.mkdir(exist_ok=True)
        
        if system == "Windows":
            with zipfile.ZipFile(archive_path, 'r') as zip_ref:
                zip_ref.extractall(JDK_PORTABLE_DIR)
        else:
            import tarfile
            with tarfile.open(archive_path, 'r:gz') as tar_ref:
                tar_ref.extractall(JDK_PORTABLE_DIR)
        
        logger.info("✅ Extraction terminée")
        
        # Nettoyage archive
        archive_path.unlink()
        logger.info("🧹 Archive nettoyée")
        
        # Vérification installation
        jdk_home = detect_portable_jdk()
        if jdk_home:
            logger.info("✅ Installation JDK portable réussie !")
            return jdk_home
        else:
            logger.error("❌ Vérification post-installation échouée")
            return None
            
    except Exception as e:
        logger.error(f"❌ Erreur installation JDK portable: {e}")
        # Nettoyage en cas d'erreur
        if archive_path.exists():
            archive_path.unlink()
        return None

def setup_java_environment(jdk_home: pathlib.Path) -> bool:
    """Configure l'environnement Java pour cette session."""
    logger = logging.getLogger("JDKPortable")
    
    # Configurer JAVA_HOME
    os.environ['JAVA_HOME'] = str(jdk_home)
    logger.info(f"🔧 JAVA_HOME configuré: {jdk_home}")
    
    # Ajouter au PATH pour cette session
    java_bin = jdk_home / "bin"
    current_path = os.environ.get('PATH', '')
    if str(java_bin) not in current_path:
        os.environ['PATH'] = f"{java_bin}{os.pathsep}{current_path}"
        logger.info(f"🔧 {java_bin} ajouté au PATH")
    
    # Test rapide
    java_exe = java_bin / ("java.exe" if platform.system() == "Windows" else "java")
    try:
        result = subprocess.run([str(java_exe), "-version"], 
                              capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=10)
        if result.returncode == 0:
            version_line = result.stderr.split('\n')[0] if result.stderr else "Version inconnue"
            logger.info(f"☕ JDK portable opérationnel: {version_line}")
            return True
        else:
            logger.warning(f"⚠️ Test JDK portable échoué: {result.stderr}")
    except subprocess.TimeoutExpired:
        logger.warning("⚠️ Test JDK portable: timeout")
    except Exception as e:
        logger.warning(f"⚠️ Test JDK portable échoué: {e}")
    
    return False

def main():
    """Fonction principale du script."""
    logger = setup_logging()
    logger.info("🔧 === INSTALLATION JDK PORTABLE POUR ARGUMENT ANALYSIS ===")
    
    # 1. Vérifier JDK système
    if detect_system_jdk():
        logger.info("✅ JDK système disponible, installation portable non nécessaire")
        return True
    
    # 2. Vérifier JDK portable existant
    jdk_home = detect_portable_jdk()
    if jdk_home:
        logger.info("✅ JDK portable existant trouvé")
        return setup_java_environment(jdk_home)
    
    # 3. Installer JDK portable
    logger.info("📋 Aucun JDK disponible. Installation automatique...")
    jdk_home = download_and_install_portable_jdk()
    
    if jdk_home:
        return setup_java_environment(jdk_home)
    else:
        logger.error("❌ ÉCHEC: Installation JDK portable échouée")
        logger.error("   Le PropositionalLogicAgent ne pourra pas fonctionner.")
        logger.error("   Veuillez installer manuellement un JDK >= 11.")
        return False

def get_java_home():
    """Retourne le JAVA_HOME configuré après installation."""
    return os.environ.get('JAVA_HOME')

if __name__ == "__main__":
    success = main()
    if success:
        print(f"\n🎉 SUCCÈS ! JAVA_HOME: {get_java_home()}")
        sys.exit(0)
    else:
        print("\n❌ ÉCHEC ! Voir les logs ci-dessus")
        sys.exit(1)