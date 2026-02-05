"""
Helpers pour les notebooks Claude CLI.

Ce module fournit des fonctions utilitaires pour executer Claude Code
en ligne de commande depuis des notebooks Jupyter.

Exemple d'utilisation:
    from helpers.claude_cli import run_claude, check_claude_status

    # Verifier l'installation
    if verify_installation():
        stdout, stderr, code = run_claude("Bonjour")
        print(stdout)
"""

import subprocess
import json
import shutil
from typing import Tuple, Dict, Any, Optional, List

# Mode simulation : si True, les appels a Claude sont simules
SIMULATION_MODE = False

# Reponses simulees pour le mode sans API
SIMULATED_RESPONSES = {
    "default": "Ceci est une reponse simulee. Activez une cle API pour des reponses reelles.",
    "bonjour": "Bonjour ! Je suis Claude, un assistant IA. Comment puis-je vous aider ?",
    "version": "Claude Code CLI v1.0.0",
    "status": '{"connected": true, "model": "simulation-mode", "baseUrl": "simulation"}',
}


def verify_installation() -> bool:
    """
    Verifie que Claude Code CLI est installe et accessible.

    Returns:
        bool: True si Claude est installe, False sinon.

    Example:
        >>> if verify_installation():
        ...     print("Claude CLI est pret")
        ... else:
        ...     print("Veuillez installer Claude CLI")
    """
    return shutil.which("claude") is not None


def run_claude(
    prompt: str,
    model: str = "sonnet",
    output_format: str = "text",
    timeout: int = 60,
    extra_args: Optional[List[str]] = None,
    working_dir: Optional[str] = None
) -> Tuple[str, str, int]:
    """
    Execute une commande Claude CLI et retourne le resultat.

    Args:
        prompt: Le prompt a envoyer a Claude.
        model: Le modele a utiliser (sonnet, opus, haiku).
        output_format: Format de sortie (text, json).
        timeout: Timeout en secondes.
        extra_args: Arguments supplementaires pour la commande.
        working_dir: Repertoire de travail pour l'execution.

    Returns:
        Tuple[str, str, int]: (stdout, stderr, return_code)

    Example:
        >>> stdout, stderr, code = run_claude("Explique Python en 2 phrases")
        >>> print(stdout)
    """
    if SIMULATION_MODE:
        # Mode simulation
        response = SIMULATED_RESPONSES.get(
            prompt.lower().split()[0] if prompt else "default",
            SIMULATED_RESPONSES["default"]
        )
        return response, "", 0

    if not verify_installation():
        return "", "Erreur: Claude CLI n'est pas installe", 1

    # Construction de la commande
    cmd = ["claude", "-p", prompt]

    if model and model != "sonnet":
        cmd.extend(["--model", model])

    if output_format == "json":
        cmd.extend(["--output-format", "json"])

    if extra_args:
        cmd.extend(extra_args)

    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout,
            cwd=working_dir
        )
        return result.stdout, result.stderr, result.returncode
    except subprocess.TimeoutExpired:
        return "", f"Erreur: Timeout apres {timeout} secondes", -1
    except FileNotFoundError:
        return "", "Erreur: Claude CLI n'est pas installe ou pas dans le PATH", 1
    except Exception as e:
        return "", f"Erreur inattendue: {str(e)}", -1


def run_claude_json(
    prompt: str,
    model: str = "sonnet",
    timeout: int = 60
) -> Dict[str, Any]:
    """
    Execute une commande Claude CLI et parse la reponse JSON.

    Args:
        prompt: Le prompt a envoyer a Claude.
        model: Le modele a utiliser.
        timeout: Timeout en secondes.

    Returns:
        Dict: La reponse parsee en JSON, ou un dict d'erreur.

    Example:
        >>> result = run_claude_json("Liste 3 langages en JSON")
        >>> print(result)
    """
    stdout, stderr, code = run_claude(
        prompt,
        model=model,
        output_format="json",
        timeout=timeout
    )

    if code != 0:
        return {"error": stderr or "Erreur inconnue", "code": code}

    try:
        return json.loads(stdout)
    except json.JSONDecodeError as e:
        return {
            "error": f"Erreur de parsing JSON: {str(e)}",
            "raw_output": stdout
        }


def check_claude_status() -> Dict[str, Any]:
    """
    Verifie le statut de connexion de Claude Code.

    Returns:
        Dict contenant:
            - connected (bool): True si connecte
            - model (str): Modele actif
            - base_url (str): URL de l'API
            - error (str, optional): Message d'erreur si echec

    Example:
        >>> status = check_claude_status()
        >>> if status["connected"]:
        ...     print(f"Connecte avec {status['model']}")
    """
    if SIMULATION_MODE:
        return {
            "connected": True,
            "model": "simulation-mode",
            "base_url": "simulation",
            "simulation": True
        }

    if not verify_installation():
        return {
            "connected": False,
            "error": "Claude CLI n'est pas installe"
        }

    try:
        result = subprocess.run(
            ["claude", "/status"],
            capture_output=True,
            text=True,
            timeout=10
        )

        if result.returncode == 0:
            # Parser la sortie de /status
            output = result.stdout.lower()
            connected = "connected" in output or "connecte" in output

            # Extraire le modele si possible
            model = "unknown"
            if "model:" in output:
                lines = output.split("\n")
                for line in lines:
                    if "model:" in line.lower():
                        model = line.split(":")[-1].strip()
                        break

            return {
                "connected": connected,
                "model": model,
                "base_url": "detected",
                "raw_output": result.stdout
            }
        else:
            return {
                "connected": False,
                "error": result.stderr or "Erreur de connexion"
            }

    except subprocess.TimeoutExpired:
        return {"connected": False, "error": "Timeout"}
    except Exception as e:
        return {"connected": False, "error": str(e)}


def format_code_block(code: str, language: str = "python") -> str:
    """
    Formate du code pour l'affichage dans un notebook.

    Args:
        code: Le code a formater.
        language: Le langage pour la coloration syntaxique.

    Returns:
        str: Le code formate avec backticks Markdown.
    """
    return f"```{language}\n{code}\n```"


def print_response(stdout: str, stderr: str, code: int) -> None:
    """
    Affiche proprement une reponse Claude dans un notebook.

    Args:
        stdout: Sortie standard.
        stderr: Sortie d'erreur.
        code: Code de retour.
    """
    if code == 0:
        print("=== Reponse Claude ===")
        print(stdout)
    else:
        print("=== Erreur ===")
        print(f"Code: {code}")
        if stderr:
            print(f"Message: {stderr}")


# Pour les tests
if __name__ == "__main__":
    print("Test du module claude_cli")
    print(f"Installation verifiee: {verify_installation()}")

    status = check_claude_status()
    print(f"Statut: {status}")

    if status.get("connected"):
        stdout, stderr, code = run_claude("Dis 'test reussi' en francais")
        print_response(stdout, stderr, code)
