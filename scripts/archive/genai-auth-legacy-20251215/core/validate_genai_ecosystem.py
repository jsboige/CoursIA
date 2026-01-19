#!/usr/bin/env python3
"""
validate_genai_ecosystem.py - Script de validation complète écosystème GenAI Images

Usage:
    python tests/validate_genai_ecosystem.py [--verbose] [--fix]

Options:
    --verbose    : Mode verbeux avec détails
    --fix        : Tente de corriger automatiquement les problèmes
    --report     : Génère rapport JSON détaillé
"""

import os
import sys
import json
import time
from pathlib import Path
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass, asdict
from datetime import datetime
import argparse

# Ajouter le répertoire racine au PYTHONPATH
sys.path.insert(0, str(Path(__file__).parent.parent))

@dataclass
class CheckResult:
    """Résultat d'un check"""
    name: str
    passed: bool
    message: str
    details: Optional[Dict] = None
    fix_available: bool = False
    fix_command: Optional[str] = None

@dataclass
class ValidationReport:
    """Rapport de validation complet"""
    timestamp: str
    total_checks: int
    passed_checks: int
    failed_checks: int
    warnings: int
    checks: List[CheckResult]
    summary: Dict
    
    def to_dict(self):
        return {
            'timestamp': self.timestamp,
            'total_checks': self.total_checks,
            'passed_checks': self.passed_checks,
            'failed_checks': self.failed_checks,
            'warnings': self.warnings,
            'checks': [asdict(c) for c in self.checks],
            'summary': self.summary
        }

class GenAIValidator:
    """Validateur écosystème GenAI Images"""
    
    def __init__(self, verbose: bool = False, fix: bool = False):
        self.verbose = verbose
        self.fix_mode = fix
        self.checks: List[CheckResult] = []
        self.warnings: List[str] = []
        
        # Chemins importants
        # scripts/genai-auth/core/validate_genai_ecosystem.py -> core -> genai-auth -> scripts -> ROOT
        self.root_dir = Path(__file__).parent.parent.parent.parent
        self.genai_dir = self.root_dir / "MyIA.AI.Notebooks" / "GenAI"
        self.docs_dir = self.root_dir / "docs"
        self.tests_dir = self.root_dir / "tests"
    
    def log(self, message: str, level: str = "INFO"):
        """Log message si verbose"""
        if self.verbose or level in ["ERROR", "WARNING"]:
            prefix = {
                "INFO": "ℹ️",
                "SUCCESS": "✅",
                "ERROR": "❌",
                "WARNING": "⚠️",
                "FIX": "🔧"
            }.get(level, "•")
            print(f"{prefix} {message}")
    
    def add_check(self, result: CheckResult):
        """Ajoute résultat check"""
        self.checks.append(result)
        
        if result.passed:
            self.log(f"{result.name}: PASS", "SUCCESS")
        else:
            self.log(f"{result.name}: FAIL - {result.message}", "ERROR")
            if result.fix_available and self.fix_mode:
                self.log(f"Tentative correction: {result.fix_command}", "FIX")
    
    # ============================================================
    # CHECKS STRUCTURE FICHIERS
    # ============================================================
    
    def check_directory_structure(self) -> CheckResult:
        """Vérifie structure répertoires GenAI"""
        self.log("Vérification structure répertoires...", "INFO")
        
        required_dirs = [
            "00-GenAI-Environment",
            "01-Images-Foundation",
            "02-Images-Advanced",
            "03-Images-Orchestration",
            "04-Images-Applications",
            "tutorials",
            "examples",
            "outputs"
        ]
        
        missing = []
        for dir_name in required_dirs:
            dir_path = self.genai_dir / dir_name
            if not dir_path.exists():
                missing.append(dir_name)
        
        if missing:
            return CheckResult(
                name="Structure Répertoires",
                passed=False,
                message=f"Répertoires manquants: {', '.join(missing)}",
                details={'missing': missing},
                fix_available=True,
                fix_command=f"mkdir -p {' '.join(str(self.genai_dir / d) for d in missing)}"
            )
        
        return CheckResult(
            name="Structure Répertoires",
            passed=True,
            message=f"Tous les répertoires requis existent ({len(required_dirs)})"
        )
    
    def check_notebooks_exist(self) -> CheckResult:
        """Vérifie présence notebooks essentiels"""
        self.log("Vérification notebooks essentiels...", "INFO")
        
        essential_notebooks = [
            "00-GenAI-Environment/00-1-Environment-Setup.ipynb",
            "00-GenAI-Environment/00-3-API-Endpoints-Configuration.ipynb",
            "00-GenAI-Environment/00-4-Environment-Validation.ipynb",
            "01-Images-Foundation/01-1-OpenAI-DALL-E-3.ipynb",
            "01-Images-Foundation/01-2-GPT-5-Image-Generation.ipynb",
            "01-Images-Foundation/01-3-Basic-Image-Operations.ipynb",
            "04-Images-Applications/04-1-Educational-Content-Generation.ipynb",
            "04-Images-Applications/04-2-Creative-Workflows.ipynb",
            "04-Images-Applications/04-3-Production-Integration.ipynb"
        ]
        
        missing = []
        for notebook in essential_notebooks:
            notebook_path = self.genai_dir / notebook
            if not notebook_path.exists():
                missing.append(notebook)
        
        if missing:
            return CheckResult(
                name="Notebooks Essentiels",
                passed=False,
                message=f"{len(missing)} notebook(s) manquant(s)",
                details={'missing': missing}
            )
        
        return CheckResult(
            name="Notebooks Essentiels",
            passed=True,
            message=f"Tous les notebooks essentiels présents ({len(essential_notebooks)})"
        )
    
    def check_documentation_complete(self) -> CheckResult:
        """Vérifie documentation complète"""
        self.log("Vérification documentation...", "INFO")
        
        required_docs = [
            "MyIA.AI.Notebooks/GenAI/README.md",
            "MyIA.AI.Notebooks/GenAI/INDEX.md",
            "MyIA.AI.Notebooks/GenAI/TROUBLESHOOTING.md",
            "MyIA.AI.Notebooks/GenAI/DEPLOYMENT.md",
            "docs/genai-images-mission-complete.md"
        ]
        
        missing = []
        for doc in required_docs:
            doc_path = self.root_dir / doc
            if not doc_path.exists():
                missing.append(doc)
        
        if missing:
            return CheckResult(
                name="Documentation Complète",
                passed=False,
                message=f"{len(missing)} document(s) manquant(s)",
                details={'missing': missing}
            )
        
        return CheckResult(
            name="Documentation Complète",
            passed=True,
            message=f"Toute la documentation requise présente ({len(required_docs)})"
        )
    
    def check_tutorials_exist(self) -> CheckResult:
        """Vérifie présence tutoriels"""
        self.log("Vérification tutoriels...", "INFO")
        
        required_tutorials = [
            "tutorials/dalle3-complete-guide.md",
            "tutorials/gpt5-image-analysis-guide.md",
            "tutorials/openrouter-ecosystem-guide.md",
            "tutorials/educational-workflows.md"
        ]
        
        missing = []
        for tutorial in required_tutorials:
            tutorial_path = self.genai_dir / tutorial
            if not tutorial_path.exists():
                missing.append(tutorial)
        
        if missing:
            return CheckResult(
                name="Tutoriels",
                passed=False,
                message=f"{len(missing)} tutoriel(s) manquant(s)",
                details={'missing': missing}
            )
        
        return CheckResult(
            name="Tutoriels",
            passed=True,
            message=f"Tous les tutoriels présents ({len(required_tutorials)})"
        )
    
    def check_examples_exist(self) -> CheckResult:
        """Vérifie présence exemples sectoriels"""
        self.log("Vérification exemples sectoriels...", "INFO")
        
        required_examples = [
            "examples/science-diagrams.ipynb",
            "examples/history-geography.ipynb",
            "examples/literature-visual.ipynb",
            "examples/mathematics-physics.ipynb"
        ]
        
        missing = []
        for example in required_examples:
            example_path = self.genai_dir / example
            if not example_path.exists():
                missing.append(example)
        
        if missing:
            return CheckResult(
                name="Exemples Sectoriels",
                passed=False,
                message=f"{len(missing)} exemple(s) manquant(s)",
                details={'missing': missing}
            )
        
        return CheckResult(
            name="Exemples Sectoriels",
            passed=True,
            message=f"Tous les exemples sectoriels présents ({len(required_examples)})"
        )
    
    # ============================================================
    # CHECKS CONFIGURATION
    # ============================================================
    
    def check_env_file(self) -> CheckResult:
        """Vérifie fichier .env"""
        self.log("Vérification .env...", "INFO")
        
        env_path = self.genai_dir / ".env"
        env_example_path = self.genai_dir / ".env.example"
        
        if not env_example_path.exists():
            return CheckResult(
                name="Fichier .env.example",
                passed=False,
                message=".env.example manquant (template requis)"
            )
        
        if not env_path.exists():
            return CheckResult(
                name="Fichier .env",
                passed=False,
                message=".env manquant (copier depuis .env.example)",
                fix_available=True,
                fix_command=f"cp {env_example_path} {env_path}"
            )
        
        return CheckResult(
            name="Fichier .env",
            passed=True,
            message=".env et .env.example présents"
        )
    
    def check_comfyui_web_auth(self) -> CheckResult:
        """Vérifie l'authentification sur l'interface web ComfyUI"""
        self.log("Vérification authentification web ComfyUI...", "INFO")
        
        try:
            import requests
            
            response = requests.get("http://localhost:8188/", timeout=10)
            
            if response.status_code == 401:
                return CheckResult(
                    name="Authentification Web ComfyUI",
                    passed=True,
                    message="Interface web PROTÉGÉE (401 Unauthorized)"
                )
            elif response.status_code == 200:
                if "login" in response.text.lower() or "auth" in response.text.lower():
                    return CheckResult(
                        name="Authentification Web ComfyUI",
                        passed=True,
                        message="Interface web PROTÉGÉE (page de login détectée)"
                    )
                else:
                    return CheckResult(
                        name="Authentification Web ComfyUI",
                        passed=False,
                        message="Interface web NON PROTÉGÉE (accès direct)"
                    )
            else:
                return CheckResult(
                    name="Authentification Web ComfyUI",
                    passed=False,
                    message=f"Réponse inattendue: {response.status_code}"
                )
               
        except Exception as e:
            return CheckResult(
                name="Authentification Web ComfyUI",
                passed=False,
                message=f"Erreur test web: {e}"
            )
    
    def check_comfyui_api_auth(self) -> CheckResult:
        """Vérifie l'authentification sur les endpoints API ComfyUI"""
        self.log("Vérification authentification API ComfyUI...", "INFO")
        
        try:
            import requests
            
            # Test de l'endpoint /prompt
            response = requests.post(
                "http://localhost:8188/prompt",
                json={"prompt": {}},
                headers={"Content-Type": "application/json"},
                timeout=10
            )
            
            if response.status_code == 401:
                return CheckResult(
                    name="Authentification API ComfyUI",
                    passed=True,
                    message="API PROTÉGÉE (401 Unauthorized)"
                )
            elif response.status_code == 200:
                return CheckResult(
                    name="Authentification API ComfyUI",
                    passed=False,
                    message="API NON PROTÉGÉE (accès direct)"
                )
            else:
                return CheckResult(
                    name="Authentification API ComfyUI",
                    passed=False,
                    message=f"Réponse API inattendue: {response.status_code}"
                )
               
        except Exception as e:
            return CheckResult(
                name="Authentification API ComfyUI",
                passed=False,
                message=f"Erreur test API: {e}"
            )

    def check_forge_connectivity(self) -> CheckResult:
        """Vérifie la connectivité et l'authentification de Forge SDXL Turbo"""
        self.log("Vérification connectivité Forge SDXL Turbo...", "INFO")
        
        try:
            import requests
            
            # Essayer d'abord IPv6 [::1] car Docker Windows mappe souvent dessus
            url = "http://[::1]:17861"
            try:
                # Ne pas suivre les redirections automatiquement pour détecter le 302 vers le portail
                response = requests.get(url, timeout=5, allow_redirects=False)
            except:
                # Fallback IPv4
                url = "http://localhost:17861"
                response = requests.get(url, timeout=5, allow_redirects=False)
            
            if response.status_code == 302 or response.status_code == 301:
                location = response.headers.get('Location', '')
                if "1111" in location or "login" in location:
                     return CheckResult(
                        name="Connectivité Forge SDXL Turbo",
                        passed=True,
                        message=f"Service accessible et PROTÉGÉ (Redirection vers Service Portal: {location})"
                    )
            
            if response.status_code == 401:
                return CheckResult(
                    name="Connectivité Forge SDXL Turbo",
                    passed=True,
                    message="Service accessible et PROTÉGÉ (401 Unauthorized)"
                )
            elif "login" in response.text.lower() or "service portal" in response.text.lower():
                return CheckResult(
                    name="Connectivité Forge SDXL Turbo",
                    passed=True,
                    message="Service accessible et PROTÉGÉ (Page de login détectée)"
                )
            elif response.status_code == 200:
                return CheckResult(
                    name="Connectivité Forge SDXL Turbo",
                    passed=False,
                    message="Service accessible mais NON PROTÉGÉ (200 OK sans login)"
                )
            else:
                return CheckResult(
                    name="Connectivité Forge SDXL Turbo",
                    passed=False,
                    message=f"Réponse inattendue: {response.status_code}"
                )
                
        except Exception as e:
            return CheckResult(
                name="Connectivité Forge SDXL Turbo",
                passed=False,
                message=f"Erreur connexion: {str(e)[:100]} (Vérifier si le conteneur forge-turbo est démarré)"
            )

    def check_api_keys_configured(self) -> CheckResult:
        """Vérifie configuration clés API"""
        self.log("Vérification clés API...", "INFO")
        
        from dotenv import load_dotenv
        
        # Charger .env
        env_path = self.genai_dir / ".env"
        if not env_path.exists():
            return CheckResult(
                name="Clés API Configurées",
                passed=False,
                message=".env manquant - impossible de vérifier clés"
            )
        
        load_dotenv(dotenv_path=env_path)
        
        required_keys = {
            'OPENAI_API_KEY': 'OpenAI (DALL-E 3)',
            'OPENROUTER_API_KEY': 'OpenRouter (GPT-5)'
        }
        
        missing = []
        configured = []
        
        for key, description in required_keys.items():
            value = os.getenv(key)
            if not value or value.startswith('sk-...') or len(value) < 20:
                missing.append(f"{key} ({description})")
            else:
                configured.append(description)
        
        if missing:
            return CheckResult(
                name="Clés API Configurées",
                passed=False,
                message=f"Clés manquantes ou invalides: {', '.join(missing)}",
                details={'missing': missing, 'configured': configured}
            )
        
        return CheckResult(
            name="Clés API Configurées",
            passed=True,
            message=f"Toutes les clés API configurées ({len(configured)})",
            details={'configured': configured}
        )
    
    def check_python_dependencies(self) -> CheckResult:
        """Vérifie dépendances Python"""
        self.log("Vérification dépendances Python...", "INFO")
        
        required_packages = {
            'openai': '1.3.0',
            'Pillow': '10.0.0',
            'requests': '2.31.0',
            'python-dotenv': '1.0.0',
            'jupyter': '1.0.0'
        }
        
        missing = []
        installed = []
        
        for package, min_version in required_packages.items():
            try:
                __import__(package.replace('-', '_'))
                installed.append(package)
            except ImportError:
                missing.append(f"{package}>={min_version}")
        
        if missing:
            return CheckResult(
                name="Dépendances Python",
                passed=False,
                message=f"{len(missing)} package(s) manquant(s)",
                details={'missing': missing, 'installed': installed},
                fix_available=True,
                fix_command=f"pip install {' '.join(missing)}"
            )
        
        return CheckResult(
            name="Dépendances Python",
            passed=True,
            message=f"Toutes les dépendances installées ({len(installed)})",
            details={'installed': installed}
        )
    
    # ============================================================
    # CHECKS APIS
    # ============================================================
    
    def check_openai_api_connectivity(self) -> CheckResult:
        """Teste connectivité OpenAI API"""
        self.log("Test connectivité OpenAI...", "INFO")
        
        try:
            from openai import OpenAI
            from dotenv import load_dotenv
            
            load_dotenv(dotenv_path=self.genai_dir / ".env")
            
            api_key = os.getenv("OPENAI_API_KEY")
            if not api_key or len(api_key) < 20:
                return CheckResult(
                    name="OpenAI API Connectivity",
                    passed=False,
                    message="OPENAI_API_KEY manquante ou invalide"
                )
            
            client = OpenAI(api_key=api_key)
            
            # Test simple
            start = time.time()
            models = client.models.list()
            latency = (time.time() - start) * 1000
            
            return CheckResult(
                name="OpenAI API Connectivity",
                passed=True,
                message=f"OpenAI API accessible (latence: {latency:.0f}ms)",
                details={'latency_ms': round(latency, 2), 'models_count': len(models.data)}
            )
            
        except Exception as e:
            return CheckResult(
                name="OpenAI API Connectivity",
                passed=False,
                message=f"Erreur connexion OpenAI: {str(e)[:100]}",
                details={'error': str(e)}
            )
    
    def check_openrouter_api_connectivity(self) -> CheckResult:
        """Teste connectivité OpenRouter API"""
        self.log("Test connectivité OpenRouter...", "INFO")
        
        try:
            from openai import OpenAI
            from dotenv import load_dotenv
            
            load_dotenv(dotenv_path=self.genai_dir / ".env")
            
            api_key = os.getenv("OPENROUTER_API_KEY")
            if not api_key or len(api_key) < 20:
                return CheckResult(
                    name="OpenRouter API Connectivity",
                    passed=False,
                    message="OPENROUTER_API_KEY manquante ou invalide"
                )
            
            client = OpenAI(
                api_key=api_key,
                base_url="https://openrouter.ai/api/v1"
            )
            
            # Test simple
            start = time.time()
            response = client.chat.completions.create(
                model="openai/gpt-4-turbo",
                messages=[{"role": "user", "content": "test"}],
                max_tokens=5
            )
            latency = (time.time() - start) * 1000
            
            return CheckResult(
                name="OpenRouter API Connectivity",
                passed=True,
                message=f"OpenRouter API accessible (latence: {latency:.0f}ms)",
                details={'latency_ms': round(latency, 2)}
            )
            
        except Exception as e:
            return CheckResult(
                name="OpenRouter API Connectivity",
                passed=False,
                message=f"Erreur connexion OpenRouter: {str(e)[:100]}",
                details={'error': str(e)}
            )
    
    # ============================================================
    # CHECKS QUALITÉ NOTEBOOKS
    # ============================================================
    
    def check_notebooks_bom(self) -> CheckResult:
        """Vérifie absence BOM UTF-8 dans notebooks"""
        self.log("Vérification BOM UTF-8 notebooks...", "INFO")
        
        notebooks_with_bom = []
        
        for notebook_path in self.genai_dir.rglob("*.ipynb"):
            with open(notebook_path, 'rb') as f:
                start = f.read(3)
                if start == b'\xef\xbb\xbf':
                    notebooks_with_bom.append(str(notebook_path.relative_to(self.genai_dir)))
        
        if notebooks_with_bom:
            return CheckResult(
                name="Notebooks sans BOM",
                passed=False,
                message=f"{len(notebooks_with_bom)} notebook(s) avec BOM UTF-8",
                details={'notebooks_with_bom': notebooks_with_bom},
                fix_available=True,
                fix_command="python scripts/37-fix-genai-bom-utf8-20251008.ps1"
            )
        
        return CheckResult(
            name="Notebooks sans BOM",
            passed=True,
            message="Aucun BOM UTF-8 détecté dans notebooks"
        )
    
    def check_notebooks_valid_json(self) -> CheckResult:
        """Vérifie validité JSON notebooks"""
        self.log("Vérification JSON notebooks...", "INFO")
        
        invalid_notebooks = []
        
        for notebook_path in self.genai_dir.rglob("*.ipynb"):
            try:
                with open(notebook_path, 'r', encoding='utf-8') as f:
                    json.load(f)
            except json.JSONDecodeError as e:
                invalid_notebooks.append({
                    'path': str(notebook_path.relative_to(self.genai_dir)),
                    'error': str(e)
                })
        
        if invalid_notebooks:
            return CheckResult(
                name="Notebooks JSON Valide",
                passed=False,
                message=f"{len(invalid_notebooks)} notebook(s) JSON invalide",
                details={'invalid': invalid_notebooks}
            )
        
        return CheckResult(
            name="Notebooks JSON Valide",
            passed=True,
            message="Tous les notebooks ont un JSON valide"
        )
    
    def check_token_unification(self) -> CheckResult:
        """Vérifie l'unification des tokens ComfyUI-Login"""
        self.log("Vérification unification tokens ComfyUI...", "INFO")
        
        try:
            # Importer le synchroniseur
            sys.path.append(str(self.root_dir / "scripts" / "genai-auth" / "utils"))
            from token_synchronizer import TokenSynchronizer
            
            # Créer le synchroniseur
            synchronizer = TokenSynchronizer(root_dir=self.root_dir)
            
            # Valider la cohérence
            is_consistent = synchronizer.validate_consistency()
            
            if is_consistent:
                return CheckResult(
                    name="Unification Tokens ComfyUI",
                    passed=True,
                    message="✅ Tous les tokens sont unifiés et cohérents"
                )
            else:
                return CheckResult(
                    name="Unification Tokens ComfyUI",
                    passed=False,
                    message="❌ Les tokens ne sont pas unifiés ou incohérents",
                    fix_available=True,
                    fix_command="python scripts/genai-auth/utils/token_synchronizer.py --unify"
                )
                
        except Exception as e:
            return CheckResult(
                name="Unification Tokens ComfyUI",
                passed=False,
                message=f"Erreur validation unification: {e}"
            )
    
    # ============================================================
    # EXÉCUTION VALIDATION
    # ============================================================
    
    def run_all_checks(self) -> ValidationReport:
        """Exécute tous les checks"""
        print("\n" + "=" * 60)
        print("🏥 VALIDATION ÉCOSYSTÈME GENAI IMAGES COURSIA")
        print("=" * 60 + "\n")
        
        # Checks structure
        print("📂 STRUCTURE FICHIERS")
        print("-" * 60)
        self.add_check(self.check_directory_structure())
        self.add_check(self.check_notebooks_exist())
        self.add_check(self.check_documentation_complete())
        self.add_check(self.check_tutorials_exist())
        self.add_check(self.check_examples_exist())
        
        # Checks configuration
        print("\n⚙️ CONFIGURATION")
        print("-" * 60)
        self.add_check(self.check_env_file())
        self.add_check(self.check_api_keys_configured())
        self.add_check(self.check_python_dependencies())
        
        # Checks APIs (optionnel si clés manquantes)
        print("\n🌐 CONNECTIVITÉ APIS")
        print("-" * 60)
        self.add_check(self.check_openai_api_connectivity())
        self.add_check(self.check_openrouter_api_connectivity())
        
        # Checks authentification ComfyUI
        print("\n🔐 AUTHENTIFICATION COMFYUI")
        print("-" * 60)
        self.add_check(self.check_comfyui_web_auth())
        self.add_check(self.check_comfyui_api_auth())
        self.add_check(self.check_token_unification())

        # Checks Forge
        print("\n🔨 AUTHENTIFICATION FORGE")
        print("-" * 60)
        self.add_check(self.check_forge_connectivity())
        
        # Checks qualité
        print("\n✨ QUALITÉ NOTEBOOKS")
        print("-" * 60)
        self.add_check(self.check_notebooks_bom())
        self.add_check(self.check_notebooks_valid_json())
        
        # Génération rapport
        passed = sum(1 for c in self.checks if c.passed)
        failed = sum(1 for c in self.checks if not c.passed)
        
        report = ValidationReport(
            timestamp=datetime.now().isoformat(),
            total_checks=len(self.checks),
            passed_checks=passed,
            failed_checks=failed,
            warnings=len(self.warnings),
            checks=self.checks,
            summary={
                'success_rate': round((passed / len(self.checks)) * 100, 1),
                'ready_for_production': failed == 0
            }
        )
        
        # Affichage résumé
        self.print_summary(report)
        
        return report
    
    def print_summary(self, report: ValidationReport):
        """Affiche résumé rapport"""
        print("\n" + "=" * 60)
        print("📊 RÉSUMÉ VALIDATION")
        print("=" * 60)
        
        success_rate = report.summary['success_rate']
        
        print(f"\n✅ Checks réussis: {report.passed_checks}/{report.total_checks} ({success_rate}%)")
        print(f"❌ Checks échoués: {report.failed_checks}/{report.total_checks}")
        
        if report.failed_checks > 0:
            print("\n⚠️ PROBLÈMES DÉTECTÉS:")
            for check in report.checks:
                if not check.passed:
                    print(f"  • {check.name}: {check.message}")
                    if check.fix_available:
                        print(f"    🔧 Fix: {check.fix_command}")
        
        print("\n" + "=" * 60)
        
        if report.summary['ready_for_production']:
            print("✅ SYSTÈME PRÊT POUR PRODUCTION")
        else:
            print("❌ CORRECTIONS NÉCESSAIRES AVANT PRODUCTION")
        
        print("=" * 60 + "\n")
    
    def save_report(self, report: ValidationReport, output_path: str):
        """Sauvegarde rapport JSON"""
        output_file = Path(output_path)
        output_file.parent.mkdir(parents=True, exist_ok=True)
        
        with open(output_file, 'w', encoding='utf-8') as f:
            json.dump(report.to_dict(), f, indent=2, ensure_ascii=False)
        
        print(f"📄 Rapport sauvegardé: {output_file}")


def main():
    """Point d'entrée principal"""
    parser = argparse.ArgumentParser(
        description="Validation complète écosystème GenAI Images CoursIA"
    )
    parser.add_argument(
        '--verbose', '-v',
        action='store_true',
        help="Mode verbeux avec détails"
    )
    parser.add_argument(
        '--fix', '-f',
        action='store_true',
        help="Tente de corriger automatiquement les problèmes"
    )
    parser.add_argument(
        '--report', '-r',
        type=str,
        help="Chemin fichier rapport JSON"
    )
    
    args = parser.parse_args()
    
    # Créer validateur
    validator = GenAIValidator(verbose=args.verbose, fix=args.fix)
    
    # Exécuter validation
    try:
        report = validator.run_all_checks()
        
        # Sauvegarder rapport si demandé
        if args.report:
            validator.save_report(report, args.report)
        
        # Code retour
        sys.exit(0 if report.failed_checks == 0 else 1)
        
    except Exception as e:
        print(f"\n❌ ERREUR FATALE: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(2)

if __name__ == '__main__':
    main()