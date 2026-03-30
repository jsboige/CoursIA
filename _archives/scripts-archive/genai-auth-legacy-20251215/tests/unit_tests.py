#!/usr/bin/env python3
"""
unit_tests.py - Tests unitaires pour les modules consolidés GenAI-Auth

Vérifie l'intégrité des modules :
- auth_manager.py
- docker_manager.py
- comfyui_client.py
- validation_suite.py

Usage:
    python scripts/genai-auth/tests/unit_tests.py
"""

import sys
import unittest
from pathlib import Path

# Ajouter le répertoire parent au path
PROJECT_ROOT = Path(__file__).resolve().parent.parent.parent.parent
SCRIPTS_DIR = PROJECT_ROOT / "scripts" / "genai-auth"
sys.path.append(str(SCRIPTS_DIR))

try:
    from auth_manager import GenAIAuthManager
    from docker_manager import DockerManager
    from comfyui_client import ComfyUIClient, WorkflowManager
    from validation_suite import ValidationSuite
except ImportError as e:
    print(f"❌ Erreur d'importation : {e}")
    sys.exit(1)

class TestAuthManager(unittest.TestCase):
    def setUp(self):
        self.auth = GenAIAuthManager(PROJECT_ROOT)

    def test_token_generation(self):
        token = self.auth.generate_secure_token(32)
        self.assertEqual(len(token), 32)
        
    def test_bcrypt_hash(self):
        pwd = "test_password"
        hash_ = self.auth.generate_bcrypt_hash(pwd)
        self.assertTrue(hash_.startswith("$2b$"))
        self.assertTrue(self.auth.validate_bcrypt_pair(pwd, hash_))

class TestDockerManager(unittest.TestCase):
    def setUp(self):
        self.docker = DockerManager()

    def test_command_detection(self):
        self.assertEqual(self.docker.docker_cmd, "docker")

    def test_known_services(self):
        from docker_manager import KNOWN_SERVICES
        self.assertIn("comfyui-qwen", KNOWN_SERVICES)
        self.assertIn("forge-turbo", KNOWN_SERVICES)

class TestComfyUIClient(unittest.TestCase):
    def test_client_init(self):
        client = ComfyUIClient()
        self.assertEqual(client.config.host, "localhost")
        self.assertEqual(client.config.port, 8188)

    def test_workflow_validation(self):
        valid_workflow = {"nodes": [{"id": 1, "type": "Test"}]}
        is_valid, errors = WorkflowManager.validate(valid_workflow)
        self.assertTrue(is_valid)
        self.assertEqual(len(errors), 0)

        invalid_workflow = {"nodes": [{"type": "Test"}]} # Missing ID
        is_valid, errors = WorkflowManager.validate(invalid_workflow)
        self.assertFalse(is_valid)
        self.assertIn("Node #0 missing 'id'", errors)

if __name__ == '__main__':
    print(f"🔍 Exécution des tests unitaires depuis {SCRIPTS_DIR}...")
    unittest.main()