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
import sys
from typing import Tuple, Dict, Any, Optional, List

# Mode simulation : si True, les appels a Claude sont simules
SIMULATION_MODE = False


def _resolve_claude_command() -> List[str]:
    """
    Resout la commande Claude utilisable par subprocess sur cette plateforme.

    Sous Windows, l'installation npm fournit un shim `claude.CMD` que
    CreateProcess refuse d'executer directement (FileNotFoundError) alors que
    shutil.which le trouve : il faut passer par cmd.exe /c. Une installation
    native (claude.exe, Linux/macOS) s'invoque telle quelle.
    """
    exe = shutil.which("claude")
    if exe is None:
        return []
    if sys.platform == "win32" and exe.lower().endswith((".cmd", ".bat")):
        return ["cmd.exe", "/c", exe]
    return [exe]


def installation_status() -> Dict[str, Any]:
    """
    Diagnostique l'installation de la CLI en distinguant les trois etats :
    introuvable, present mais non executable, executable.
    """
    resolved = shutil.which("claude")
    if resolved is None:
        return {"state": "introuvable", "message": "Claude CLI n'est pas installe (shutil.which ne le trouve pas)"}
    cmd = _resolve_claude_command()
    try:
        result = subprocess.run(
            cmd + ["--version"],
            capture_output=True,
            text=True,
            timeout=15
        )
        if result.returncode == 0:
            return {
                "state": "executable",
                "message": "Claude CLI installe et executable",
                "version": result.stdout.strip(),
                "resolved_path": resolved
            }
        return {
            "state": "non-executable",
            "message": f"Claude CLI trouve ({resolved_path}) mais 'claude --version' echoue (code {result.returncode})",
            "resolved_path": resolved
        }
    except (FileNotFoundError, subprocess.TimeoutExpired, OSError) as e:
        return {
            "state": "non-executable",
            "message": f"Claude CLI trouve ({resolved_path}) mais non executable: {e}",
            "resolved_path": resolved
        }

# Reponses simulees pour le mode sans API
SIMULATED_RESPONSES = {
    "default": "Ceci est une reponse simulee. Activez une cle API pour des reponses reelles.",
    "bonjour": "Bonjour ! Je suis Claude, un assistant IA. Comment puis-je vous aider ?",
    "version": "Claude Code CLI v1.0.0",
    "status": '{"connected": true, "model": "simulation-mode", "baseUrl": "simulation"}',
}


def verify_installation() -> bool:
    """
    Verifie que Claude Code CLI est installe ET reellement executable.

    Teste l'executabilite (un appel reel a 'claude --version'), pas seulement
    la presence sur le PATH : sous Windows, un shim npm .CMD est trouve par
    shutil.which mais refuse par CreateProcess — c'est l'ecart qui produisait
    un faux 'prete: True' suivi d'echecs d'invocation. Voir installation_status()
    pour le diagnostic detaille (introuvable / non-executable / executable).

    Returns:
        bool: True si la CLI s'execute, False sinon.

    Example:
        >>> if verify_installation():
        ...     print("Claude CLI est pret")
        ... else:
        ...     print("Veuillez installer Claude CLI")
    """
    return installation_status()["state"] == "executable"


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
        return "", f"Erreur: Claude CLI {installation_status()['state']} ({installation_status()['message']})", 1

    # Construction de la commande (resolver : shim Windows -> cmd.exe /c)
    cmd = _resolve_claude_command() + ["-p", prompt]

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


def check_claude_status(timeout: int = 60) -> Dict[str, Any]:
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

    # /status n'existe qu'en mode interactif (il repond "isn't available in
    # this environment" en one-shot) ; la sonde de vie canonique ici est un
    # mini-appel -p : il valide installation, authentification et routage.
    try:
        result = subprocess.run(
            _resolve_claude_command() + ["-p", "Reponds uniquement: OK"],
            capture_output=True,
            text=True,
            timeout=timeout
        )

        if result.returncode == 0 and result.stdout.strip():
            return {
                "connected": True,
                "model": "detected",
                "base_url": "detected",
                "raw_output": result.stdout.strip()
            }
        return {
            "connected": False,
            "error": result.stderr.strip() or f"Erreur de connexion (code {result.returncode})"
        }

    except subprocess.TimeoutExpired:
        return {"connected": False, "error": f"Timeout apres {timeout} secondes"}
    except Exception as e:
        return {"connected": False, "error": str(e)}


def get_claude_version() -> str:
    """
    Retourne la version de Claude CLI installee.

    Returns:
        str: Version de Claude CLI, ou message d'erreur/simulation.

    Example:
        >>> version = get_claude_version()
        >>> print(version)
    """
    if SIMULATION_MODE:
        return SIMULATED_RESPONSES["version"]

    if not verify_installation():
        return "Claude CLI n'est pas installe"

    try:
        result = subprocess.run(
            _resolve_claude_command() + ["--version"],
            capture_output=True,
            text=True,
            timeout=10
        )
        return result.stdout.strip() if result.returncode == 0 else f"Erreur: {result.stderr}"
    except subprocess.TimeoutExpired:
        return "Erreur: Timeout"
    except FileNotFoundError:
        return "Erreur: Claude CLI introuvable dans le PATH"
    except Exception as e:
        return f"Erreur: {str(e)}"


def run_claude_continue(
    prompt: str,
    timeout: int = 60,
    fork: bool = False
) -> Tuple[str, str, int]:
    """
    Continue la derniere conversation avec le flag -c.

    Args:
        prompt: Le message de suite a envoyer.
        timeout: Timeout en secondes.
        fork: Si True, cree un fork de session (--fork-session).

    Returns:
        Tuple[str, str, int]: (stdout, stderr, return_code)

    Example:
        >>> stdout, stderr, code = run_claude_continue("Et pour les tuples ?")
        >>> print(stdout)
    """
    if SIMULATION_MODE:
        response = SIMULATED_RESPONSES.get(
            prompt.lower().split()[0] if prompt else "default",
            SIMULATED_RESPONSES["default"]
        )
        suffix = " (fork)" if fork else " (suite)"
        return response + suffix, "", 0

    if not verify_installation():
        return "", "Erreur: Claude CLI n'est pas installe", 1

    cmd = _resolve_claude_command() + ["-c"]
    if fork:
        cmd.append("--fork-session")
    cmd.append(prompt)

    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout
        )
        return result.stdout, result.stderr, result.returncode
    except subprocess.TimeoutExpired:
        return "", f"Erreur: Timeout apres {timeout} secondes", -1
    except FileNotFoundError:
        return "", "Erreur: Claude CLI introuvable dans le PATH", 1
    except Exception as e:
        return "", f"Erreur inattendue: {str(e)}", -1


def run_claude_command(
    command: str,
    timeout: int = 30
) -> Tuple[str, str, int]:
    """
    Execute une commande slash Claude (ex: /sessions, /status).

    Args:
        command: La commande a executer (avec ou sans /).
        timeout: Timeout en secondes.

    Returns:
        Tuple[str, str, int]: (stdout, stderr, return_code)

    Example:
        >>> stdout, stderr, code = run_claude_command("/sessions")
        >>> print(stdout)
    """
    if not command.startswith("/"):
        command = f"/{command}"

    if SIMULATION_MODE:
        if "session" in command.lower():
            return "Sessions simulees:\n  session-001 (2 messages)\n  session-002 (5 messages)", "", 0
        elif "status" in command.lower():
            return SIMULATED_RESPONSES["status"], "", 0
        return f"Commande {command} simulee", "", 0

    if not verify_installation():
        return "", "Erreur: Claude CLI n'est pas installe", 1

    try:
        result = subprocess.run(
            _resolve_claude_command() + [command],
            capture_output=True,
            text=True,
            timeout=timeout
        )
        return result.stdout, result.stderr, result.returncode
    except subprocess.TimeoutExpired:
        return "", f"Erreur: Timeout apres {timeout} secondes", -1
    except FileNotFoundError:
        return "", "Erreur: Claude CLI introuvable dans le PATH", 1
    except Exception as e:
        return "", f"Erreur inattendue: {str(e)}", -1


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
