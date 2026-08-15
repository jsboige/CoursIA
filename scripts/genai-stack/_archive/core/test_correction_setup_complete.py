#!/usr/bin/env python3
"""
Script de test pour valider la correction de la logique dans setup_complete_qwen.py

Ce script simule différents scénarios pour vérifier que :
1. Les vrais succès retournent True
2. Les échecs retournent maintenant False (correction)
3. Le logging détaillé fonctionne correctement

Auteur: Validation correction critique
Date: 2025-11-06
"""

import sys
import tempfile
import subprocess
from pathlib import Path
from unittest.mock import Mock, patch
import logging

# Configuration logging pour les tests
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)

# Importer la classe corrigée
sys.path.insert(0, str(Path(__file__).parent))
from setup_complete_qwen import QwenSetup

class MockArgs:
    """Mock pour les arguments de ligne de commande."""
    def __init__(self, skip_test=False):
        self.skip_test = skip_test
        self.skip_docker = True
        self.skip_models = True
        self.skip_auth = True
        self.report_dir = "test_reports"

def test_skip_test_returns_true():
    """Test 1: --skip-test doit retourner True."""
    print("\n" + "="*60)
    print("TEST 1: --skip-test doit retourner True")
    print("="*60)
    
    args = MockArgs(skip_test=True)
    setup = QwenSetup(args)
    
    result = setup.test_image_generation()
    
    if result is True:
        print("✅ TEST 1 RÉUSSI: --skip-test retourne True")
        return True
    else:
        print(f"❌ TEST 1 ÉCHOUÉ: --skip-test retourne {result} (attendu: True)")
        return False

def test_missing_script_returns_false():
    """Test 2: Script de test manquant doit retourner False."""
    print("\n" + "="*60)
    print("TEST 2: Script de test manquant doit retourner False")
    print("="*60)
    
    args = MockArgs(skip_test=False)
    setup = QwenSetup(args)
    
    # Simuler un script qui n'existe pas
    with patch('pathlib.Path.exists', return_value=False):
        result = setup.test_image_generation()
    
    if result is False:
        print("✅ TEST 2 RÉUSSI: Script manquant retourne False")
        return True
    else:
        print(f"❌ TEST 2 ÉCHOUÉ: Script manquant retourne {result} (attendu: False)")
        return False

def test_subprocess_failure_returns_false():
    """Test 3: Échec subprocess doit retourner False."""
    print("\n" + "="*60)
    print("TEST 3: Échec subprocess doit retourner False")
    print("="*60)
    
    args = MockArgs(skip_test=False)
    setup = QwenSetup(args)
    
    # Simuler un script qui existe mais échoue
    mock_result = Mock()
    mock_result.returncode = 1  # Échec
    mock_result.stdout = "Test output"
    mock_result.stderr = "Test error"
    
    with patch('pathlib.Path.exists', return_value=True), \
         patch('subprocess.run', return_value=mock_result):
        result = setup.test_image_generation()
    
    if result is False:
        print("✅ TEST 3 RÉUSSI: Échec subprocess retourne False")
        return True
    else:
        print(f"❌ TEST 3 ÉCHOUÉ: Échec subprocess retourne {result} (attendu: False)")
        return False

def test_subprocess_success_returns_true():
    """Test 4: Succès subprocess doit retourner True."""
    print("\n" + "="*60)
    print("TEST 4: Succès subprocess doit retourner True")
    print("="*60)
    
    args = MockArgs(skip_test=False)
    setup = QwenSetup(args)
    
    # Simuler un script qui réussit
    mock_result = Mock()
    mock_result.returncode = 0  # Succès
    mock_result.stdout = "Test successful"
    mock_result.stderr = ""
    
    with patch('pathlib.Path.exists', return_value=True), \
         patch('subprocess.run', return_value=mock_result):
        result = setup.test_image_generation()
    
    if result is True:
        print("✅ TEST 4 RÉUSSI: Succès subprocess retourne True")
        return True
    else:
        print(f"❌ TEST 4 ÉCHOUÉ: Succès subprocess retourne {result} (attendu: True)")
        return False

def test_timeout_returns_false():
    """Test 5: Timeout doit retourner False."""
    print("\n" + "="*60)
    print("TEST 5: Timeout doit retourner False")
    print("="*60)
    
    args = MockArgs(skip_test=False)
    setup = QwenSetup(args)
    
    # Simuler un timeout
    with patch('pathlib.Path.exists', return_value=True), \
         patch('subprocess.run', side_effect=subprocess.TimeoutExpired("test", 600)):
        result = setup.test_image_generation()
    
    if result is False:
        print("✅ TEST 5 RÉUSSI: Timeout retourne False")
        return True
    else:
        print(f"❌ TEST 5 ÉCHOUÉ: Timeout retourne {result} (attendu: False)")
        return False

def test_exception_returns_false():
    """Test 6: Exception doit retourner False."""
    print("\n" + "="*60)
    print("TEST 6: Exception doit retourner False")
    print("="*60)
    
    args = MockArgs(skip_test=False)
    setup = QwenSetup(args)
    
    # Simuler une exception
    with patch('pathlib.Path.exists', return_value=True), \
         patch('subprocess.run', side_effect=Exception("Test exception")):
        result = setup.test_image_generation()
    
    if result is False:
        print("✅ TEST 6 RÉUSSI: Exception retourne False")
        return True
    else:
        print(f"❌ TEST 6 ÉCHOUÉ: Exception retourne {result} (attendu: False)")
        return False

def main():
    """Exécute tous les tests de validation."""
    print("VALIDATION DE LA CORRECTION CRITIQUE setup_complete_qwen.py")
    print("="*60)
    print("Objectif: Vérifier que la logique de retour est maintenant correcte")
    print("Correction appliquée: Échec du test = échec de l'installation (return False)")
    
    tests = [
        test_skip_test_returns_true,
        test_missing_script_returns_false,
        test_subprocess_failure_returns_false,
        test_subprocess_success_returns_true,
        test_timeout_returns_false,
        test_exception_returns_false,
    ]
    
    results = []
    for test_func in tests:
        try:
            result = test_func()
            results.append(result)
        except Exception as e:
            print(f"❌ Exception dans {test_func.__name__}: {e}")
            results.append(False)
    
    # Résumé des tests
    print("\n" + "="*60)
    print("RÉSUMÉ DES TESTS DE VALIDATION")
    print("="*60)
    
    passed = sum(results)
    total = len(results)
    
    for i, (test_func, result) in enumerate(zip(tests, results), 1):
        status = "✅ RÉUSSI" if result else "❌ ÉCHOUÉ"
        print(f"Test {i}: {test_func.__name__} - {status}")
    
    print(f"\nTotal: {passed}/{total} tests passés")
    
    if passed == total:
        print("🎉 TOUS LES TESTS SONT PASSÉS - CORRECTION VALIDÉE")
        print("✅ La logique de retour est maintenant correcte")
        print("✅ Les faux positifs sont éliminés")
        print("✅ Les rapports d'installation seront fiables")
        return True
    else:
        print("❌ CERTAINS TESTS ONT ÉCHOUÉ - CORRECTION INCOMPLÈTE")
        print("❌ La logique nécessite des ajustements supplémentaires")
        return False

if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)