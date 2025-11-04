#!/usr/bin/env python3
"""
Script de resynchronisation complète des credentials ComfyUI
Génère un nouveau token brut + hash bcrypt et synchronise TOUS les fichiers
"""

import bcrypt
import secrets
import string
import subprocess
import os
from pathlib import Path
from datetime import datetime

class CredentialsResyncer:
    def __init__(self):
        self.project_root = Path("d:/Dev/CoursIA")
        self.new_token_raw = None
        self.new_token_hash = None
        self.timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        
    def generate_fresh_credentials(self):
        """Génère un nouveau token brut (32 chars) et son hash bcrypt"""
        print("🔑 Génération de nouveaux credentials...")
        
        # Générer token brut : 32 caractères alphanumériques + symboles
        chars = string.ascii_letters + string.digits + "@$^&*()_+-="
        self.new_token_raw = ''.join(secrets.choice(chars) for _ in range(32))
        
        # Générer hash bcrypt avec salt=12 (standard ComfyUI)
        self.new_token_hash = bcrypt.hashpw(
            self.new_token_raw.encode('utf-8'), 
            bcrypt.gensalt(rounds=12)
        ).decode('utf-8')
        
        print(f"✅ Token brut généré : {self.new_token_raw[:8]}...{self.new_token_raw[-4:]}")
        print(f"✅ Hash bcrypt généré : {self.new_token_hash[:20]}...{self.new_token_hash[-10:]}")
        
        # Vérification immédiate
        if bcrypt.checkpw(self.new_token_raw.encode('utf-8'), self.new_token_hash.encode('utf-8')):
            print("✅ Vérification bcrypt : OK")
        else:
            raise ValueError("❌ ERREUR : Hash bcrypt invalide !")
    
    def backup_existing_files(self):
        """Sauvegarde les fichiers existants avant modification"""
        print("\n📦 Sauvegarde des fichiers existants...")
        
        files_to_backup = [
            ".secrets/.env.generated",
            "docker-configurations/comfyui-qwen/.env"
        ]
        
        for file_path in files_to_backup:
            full_path = self.project_root / file_path
            if full_path.exists():
                backup_path = str(full_path) + f".backup_{self.timestamp}"
                import shutil
                shutil.copy2(full_path, backup_path)
                print(f"✅ Backup : {file_path} → {Path(backup_path).name}")
    
    def update_client_env_generated(self):
        """Met à jour .secrets/.env.generated avec le nouveau token brut"""
        print("\n📝 Mise à jour du fichier client (.secrets/.env.generated)...")
        
        file_path = self.project_root / ".secrets/.env.generated"
        file_path.parent.mkdir(parents=True, exist_ok=True)
        
        content = f"QWEN_API_USER_TOKEN={self.new_token_raw}\r\n"
        file_path.write_text(content, encoding='utf-8')
        
        print(f"✅ Fichier client mis à jour : {file_path}")
    
    def update_docker_env(self):
        """Met à jour docker-configurations/comfyui-qwen/.env avec le nouveau token"""
        print("\n📝 Mise à jour de la configuration Docker...")
        
        file_path = self.project_root / "docker-configurations/comfyui-qwen/.env"
        
        # Lire contenu existant
        content = file_path.read_text(encoding='utf-8')
        
        # Remplacer la ligne QWEN_API_TOKEN
        lines = content.split('\n')
        for i, line in enumerate(lines):
            if line.startswith('QWEN_API_TOKEN='):
                lines[i] = f'QWEN_API_TOKEN={self.new_token_raw}'
                break
        
        # Sauvegarder
        file_path.write_text('\n'.join(lines), encoding='utf-8')
        print(f"✅ Configuration Docker mise à jour : {file_path}")
    
    def update_server_token_file_wsl(self):
        """Met à jour le fichier serveur WSL avec le hash bcrypt"""
        print("\n📝 Mise à jour du fichier serveur WSL...")
        
        wsl_path = "/home/jesse/SD/workspace/comfyui-qwen/ComfyUI/.secrets/qwen-api-user.token"
        
        # Créer le répertoire si nécessaire
        subprocess.run(
            ["wsl", "mkdir", "-p", "/home/jesse/SD/workspace/comfyui-qwen/ComfyUI/.secrets"],
            check=True,
            capture_output=True
        )
        
        # Utiliser printf pour écrire sans newline
        cmd = f'printf "%s" "{self.new_token_hash}" > {wsl_path}'
        subprocess.run(
            ["wsl", "bash", "-c", cmd],
            check=True,
            capture_output=True
        )
        
        # Vérifier le contenu
        result = subprocess.run(
            ["wsl", "cat", wsl_path],
            capture_output=True,
            text=True,
            check=True
        )
        
        actual_content = result.stdout
        if actual_content == self.new_token_hash:
            print(f"✅ Fichier serveur WSL mis à jour : {wsl_path}")
            print(f"   Hash : {actual_content[:30]}...")
        else:
            print(f"⚠️  ATTENTION : Contenu différent")
            print(f"   Attendu ({len(self.new_token_hash)} chars) : {self.new_token_hash[:40]}...{self.new_token_hash[-20:]}")
            print(f"   Obtenu  ({len(actual_content)} chars) : {actual_content[:40]}...{actual_content[-20:]}")
            raise ValueError("❌ ERREUR : Contenu du fichier serveur ne correspond pas !")
    
    def generate_summary_report(self):
        """Génère un rapport de resynchronisation"""
        print("\n📊 Génération du rapport de resynchronisation...")
        
        report_path = self.project_root / f"rapports/rapport-resync-credentials-{self.timestamp}.md"
        
        report_content = f"""# Rapport de Resynchronisation des Credentials ComfyUI
**Date** : {datetime.now().strftime("%Y-%m-%d %H:%M:%S")}

## Nouveaux Credentials Générés

### Token Brut (Client)
```
{self.new_token_raw}
```

### Hash Bcrypt (Serveur)
```
{self.new_token_hash}
```

## Fichiers Synchronisés

| Fichier | Type | Valeur |
|---------|------|--------|
| `.secrets/.env.generated` | Token brut | `{self.new_token_raw[:10]}...` |
| `docker-configurations/comfyui-qwen/.env` | Token brut | `{self.new_token_raw[:10]}...` |
| `/home/jesse/SD/workspace/comfyui-qwen/ComfyUI/.secrets/qwen-api-user.token` (WSL) | Hash bcrypt | `{self.new_token_hash[:30]}...` |

## Étapes de Validation

### 1. Redémarrer le serveur Docker
```bash
wsl
cd /home/jesse/SD/workspace/comfyui-qwen
docker-compose restart
```

### 2. Tester l'authentification
```bash
curl -X GET \\
  -H "Authorization: Bearer {self.new_token_raw}" \\
  http://localhost:8188/system_stats
```

### 3. Relancer le script de génération
```bash
python docs/suivis/genai-image/phase-29-corrections-qwen-20251031-111200/transient-scripts/03-test-generation-images-20251031-230500.py
```

## Status
- ✅ Credentials générés
- ✅ Fichiers synchronisés
- ⏳ Tests à effectuer
"""
        
        report_path.parent.mkdir(parents=True, exist_ok=True)
        report_path.write_text(report_content, encoding='utf-8')
        
        print(f"✅ Rapport généré : {report_path}")
        return report_path
    
    def run_full_resync(self):
        """Exécute la resynchronisation complète"""
        print("=" * 80)
        print("🔄 RESYNCHRONISATION COMPLÈTE DES CREDENTIALS COMFYUI")
        print("=" * 80)
        
        try:
            # 1. Générer nouveaux credentials
            self.generate_fresh_credentials()
            
            # 2. Backup fichiers existants
            self.backup_existing_files()
            
            # 3. Mise à jour fichier client
            self.update_client_env_generated()
            
            # 4. Mise à jour configuration Docker
            self.update_docker_env()
            
            # 5. Mise à jour fichier serveur WSL
            self.update_server_token_file_wsl()
            
            # 6. Générer rapport
            report_path = self.generate_summary_report()
            
            print("\n" + "=" * 80)
            print("✅ RESYNCHRONISATION RÉUSSIE !")
            print("=" * 80)
            print(f"\n📋 Rapport complet : {report_path}")
            print("\n⚠️  PROCHAINES ÉTAPES OBLIGATOIRES :")
            print("   1. Redémarrer le serveur Docker : wsl docker-compose restart")
            print("   2. Tester avec curl (voir rapport)")
            print("   3. Relancer le script de génération d'image")
            
            return True
            
        except Exception as e:
            print(f"\n❌ ERREUR CRITIQUE : {str(e)}")
            import traceback
            traceback.print_exc()
            return False

if __name__ == "__main__":
    resyncer = CredentialsResyncer()
    success = resyncer.run_full_resync()
    
    exit(0 if success else 1)