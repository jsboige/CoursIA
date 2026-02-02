import pytest
import subprocess
import os
import sys
import time
from contextlib import closing
import socket
from dotenv import load_dotenv

# Définir les chemins et constantes
# Le chemin vers l'exécutable Python est maintenant chargé depuis le .env
# via la fixture flask_server ci-dessous.
# VENV_PYTHON = os.getenv("VENV_PYTHON_PATH") # Ancienne approche
BASE_URL = "http://127.0.0.1:5000"

@pytest.fixture(scope="session")
def app_dir():
    """Une fixture qui retourne le chemin absolu vers la racine de l'application."""
    return os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))

def wait_for_server(url, timeout=60):
    """Attend que le serveur Flask soit prêt."""
    start_time = time.time()
    while time.time() - start_time < timeout:
        try:
            with closing(socket.socket(socket.AF_INET, socket.SOCK_STREAM)) as sock:
                if sock.connect_ex(('127.0.0.1', 5000)) == 0:
                    print("Serveur prêt.")
                    return
        except ConnectionRefusedError:
            pass
        time.sleep(0.5)
    raise TimeoutError("Le serveur Flask n'a pas démarré dans le temps imparti.")

@pytest.fixture(scope="session")
def flask_server(app_dir):
    """Fixture pour démarrer et arrêter le serveur Flask."""
    
    dotenv_path = os.path.join(app_dir, '.env')
    load_dotenv(dotenv_path=dotenv_path)
    print(f"Chargement des variables d'environnement depuis {dotenv_path}")

    server_process = subprocess.Popen(
        [os.getenv("VENV_PYTHON_PATH"), "main.py"],
        cwd=app_dir,
        text=True,
        env={**os.environ, "PYTHONPATH": app_dir}
    )
    print(f"Serveur Flask démarré avec PID: {server_process.pid}")
    
    try:
        wait_for_server(BASE_URL)
        yield BASE_URL
    finally:
        print(f"Arrêt du serveur Flask (PID: {server_process.pid})...")
        
        # Arrêt du processus serveur
        server_process.terminate()
        server_process.kill() # Forcer l'arrêt à la fin
            
        print("Serveur Flask arrêté.")