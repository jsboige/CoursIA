#!/usr/bin/env python3
"""Prevol Colab des trois parcours GenAI (vibe-coding, Semantic Kernel, fine-tuning).

Ce module repond a une seule question, celle que pose un eleve au debut d'un TP
sous Colab : *est-ce que mon environnement est pret, et si non, que dois-je
faire ?* Il ne fait aucun appel de modele, ne lit aucun secret et n'ecrit rien :
il **observe** et il **nomme** un etat par element.

Les trois etats par element (contrat unique, repris tel quel par le rendu) :

- ``OK`` -- l'element est present et exploitable ;
- ``ACTION`` -- l'element manque ou est mal configure, et le remede est nomme
  (une commande ou une manipulation d'environnement) ;
- ``INFO`` -- l'element n'est pas necessaire pour ce parcours, ou son etat
  n'est pas mesurable ici.

Trois garanties, verifiees par ``tests/test_colab_preflight.py`` :

1. **Aucune valeur de secret n'est rendue.** Seule la *presence* d'une cle et sa
   *source* (environnement / Secret Colab / absente) sont rapportees. La
   resolution de la cle est delegatee a ``genai_helpers`` -- l'organe partage
   livre par #23264 -- pour ne pas dupliquer la configuration partagee.
2. **Aucun appel de modele.** Le module ne declenche ni CLI ni SDK : il mesure
   l'environnement et l'etat de configuration.
3. **Un etat nomme par element.** Aucun message de repli : un element qui n'a
   pas ete verifie est dit tel quel.

Usage (sous Colab) :

    !wget -q https://raw.githubusercontent.com/jsboige/CoursIA/main/MyIA.AI.Notebooks/GenAI/shared/helpers/genai_helpers.py
    !wget -q https://raw.githubusercontent.com/jsboige/CoursIA/main/MyIA.AI.Notebooks/GenAI/shared/helpers/colab_preflight.py
    !python colab_preflight.py all

En local :

    python colab_preflight.py sk --json
"""

from __future__ import annotations

import argparse
import json
import os
import platform
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional

__all__ = [
    "runtime_facts",
    "check_claude_cli",
    "check_semantic_kernel",
    "check_finetuning",
    "preflight",
    "render",
    "OK",
    "ACTION",
    "INFO",
]

OK = "OK"
ACTION = "ACTION"
INFO = "INFO"

# Emplacement mesure du binaire installe par `npm i -g @anthropic-ai/claude-code`
# sous Colab (runtime 2026-11-25 : code retour 0 en 11,5 s, binaire dans
# /tools/node/bin). Fait mesure sur ce runtime : `/tools/node/bin` etait deja
# dans le PATH du kernel -- l'installation seule ne suffit donc pas a expliquer
# un echec, et le cas "installe mais hors du PATH" reste un cas **defensif**
# (il s'est produit sur d'autres runtimes), pas le fait general.
COLAB_NPM_BIN_DIR = "/tools/node/bin"

# Modele du carnet FT-01 (fine-tuning) : 124 M parametres.
FT_MODEL_NAME = "openai-community/gpt2"

# Les trois parcours du tableau de prevol (#23276).
PARCOURS = ("claude-cli", "sk", "finetune")


# ---------------------------------------------------------------------------
# Utilitaires internes
# ---------------------------------------------------------------------------
def _import_genai_helpers():
    """Importe l'organe partage de resolution de la cle, ou None.

    L'organe vit dans le meme dossier que ce module. Sous Colab, l'eleve
    telecharge les deux fichiers dans le meme repertoire ; en local, le module
    est importe depuis le depot. L'absence de l'organe n'est pas une erreur
    fatale : les controles qui ne dependentent pas de la cle restent valides,
    et le controle de cle est alors signale ``ACTION`` avec son remede.
    """
    try:
        import genai_helpers  # type: ignore
    except Exception:
        dossier = str(Path(__file__).resolve().parent)
        if dossier not in sys.path:
            sys.path.insert(0, dossier)
        try:
            import genai_helpers  # type: ignore
        except Exception:
            return None
    return genai_helpers


def _element(nom: str, etat: str, detail: str, remede: Optional[str] = None) -> Dict[str, Any]:
    """Construit un element de rapport (etat + detail + remede)."""
    return {"element": nom, "etat": etat, "detail": detail, "remede": remede}


def _version_commande(cmd: List[str]) -> Optional[str]:
    """Execute une commande de version et rend sa premiere ligne, ou None."""
    try:
        resultat = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=20,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    if resultat.returncode != 0:
        return None
    premiere = (resultat.stdout or resultat.stderr or "").strip().splitlines()
    return premiere[0] if premiere else None


# ---------------------------------------------------------------------------
# Faits de runtime
# ---------------------------------------------------------------------------
def runtime_facts() -> Dict[str, Any]:
    """Relève les faits du runtime courant (OS, Python, Node, Colab ou non)."""
    return {
        "os": platform.platform(),
        "python": platform.python_version(),
        "colab": _is_colab(),
        "node": _version_commande(["node", "--version"]),
        "npm": _version_commande(["npm", "--version"]),
        "cwd": os.getcwd(),
    }


def _is_colab() -> bool:
    """Vrai si le code tourne dans un notebook Google Colab."""
    try:
        import google.colab  # noqa: F401
    except Exception:
        return False
    return True


# ---------------------------------------------------------------------------
# Parcours 1 -- vibe-coding / Claude Code CLI
# ---------------------------------------------------------------------------
def check_claude_cli() -> List[Dict[str, Any]]:
    """Verifie la CLI Claude Code : presente, executable, et dans le PATH.

    Deux causes distinctes de ``shutil.which("claude") is None`` sous Colab :
    le binaire n'est pas installe du tout, ou il est installe (par npm, dans
    ``/tools/node/bin``) mais ce repertoire n'est pas dans le PATH du kernel.
    Sur le runtime mesure le 2026-11-25, ``/tools/node/bin`` etait deja dans le
    PATH : la seconde cause est donc un cas **defensif**, pas le fait general.
    Le controle distingue les deux et nomme le remede exact.
    """
    elements: List[Dict[str, Any]] = []

    which = shutil.which("claude")
    binaire_colab = Path(COLAB_NPM_BIN_DIR) / "claude"

    if which:
        elements.append(_element(
            "claude-cli / binaire",
            OK,
            "trouve dans le PATH : %s" % which,
        ))
    elif binaire_colab.exists():
        elements.append(_element(
            "claude-cli / binaire",
            ACTION,
            "installe mais hors du PATH du kernel : %s" % binaire_colab,
            "os.environ['PATH'] = '%s:' + os.environ['PATH']  "
            "# puis relancer la cellule ; un '!export' ne survit pas a son sous-shell"
            % COLAB_NPM_BIN_DIR,
        ))
    else:
        elements.append(_element(
            "claude-cli / binaire",
            ACTION,
            "absent (ni dans le PATH, ni dans %s)" % COLAB_NPM_BIN_DIR,
            "!npm install -g @anthropic-ai/claude-code   # voie mesuree sous Colab : rc 0 en 11,5 s",
        ))

    if which:
        version = _version_commande([which, "--version"])
        if version:
            elements.append(_element("claude-cli / version", OK, version))
        else:
            elements.append(_element(
                "claude-cli / version",
                ACTION,
                "'claude --version' ne repond pas (binaire trouve mais non executable)",
                "verifier les droits d'execution du binaire, puis relancer",
            ))

    elements.append(_element(
        "claude-cli / authentification",
        INFO,
        "non verifiable sans appeler la CLI : l'appel avec une cle valide est "
        "facture ; le parcours se verifie apres le premier 'claude -p' borne",
        "!claude -p 'Reponds uniquement: OK' --model haiku   # rc 1 et 'Not logged in' si la cle est absente",
    ))
    return elements


# ---------------------------------------------------------------------------
# Parcours 2 -- Semantic Kernel
# ---------------------------------------------------------------------------
def check_semantic_kernel() -> List[Dict[str, Any]]:
    """Verifie l'installation et le cablage du kernel Semantic Kernel.

    Le carnet ``SemanticKernel/01-SemanticKernel-Intro.ipynb`` suppose un
    environnement deja installe (sa cellule 1 ne fait qu'importer
    ``semantic_kernel``) : sous Colab, ou rien n'est preinstalle, l'import
    echoue. Ce controle nomme l'etat et le remede.
    """
    elements: List[Dict[str, Any]] = []

    try:
        import semantic_kernel  # type: ignore
        version = getattr(semantic_kernel, "__version__", "version inconnue")
        elements.append(_element("sk / installation", OK, "semantic-kernel %s" % version))
    except Exception as exc:
        elements.append(_element(
            "sk / installation",
            ACTION,
            "semantic_kernel non importable (%s)" % type(exc).__name__,
            "!pip install semantic-kernel   # carnet SK-01 : aucune cellule d'installation",
        ))
        return elements

    try:
        from semantic_kernel import Kernel  # type: ignore
        from semantic_kernel.connectors.ai.open_ai import OpenAIChatCompletion  # type: ignore

        kernel = Kernel()
        kernel.add_service(OpenAIChatCompletion(service_id="default"))
        elements.append(_element(
            "sk / cablage",
            OK,
            "Kernel() cree et service OpenAIChatCompletion enregistre",
        ))
    except Exception as exc:
        elements.append(_element(
            "sk / cablage",
            ACTION,
            "cableage impossible : %s: %s" % (type(exc).__name__, exc),
            "relire la version installee : !pip show semantic-kernel",
        ))

    elements.append(_element_cle("sk"))
    elements.append(_element(
        "sk / plugins",
        INFO,
        "le carnet SK-01 charge ./prompt_template_samples/FunPlugin -- depot "
        "obligatoire sous Colab (le dossier n'y est pas)",
        "!git clone --depth 1 https://github.com/jsboige/CoursIA.git CoursIA   # ou telecharger le dossier",
    ))
    return elements


# ---------------------------------------------------------------------------
# Parcours 3 -- fine-tuning / post-training
# ---------------------------------------------------------------------------
def check_finetuning() -> List[Dict[str, Any]]:
    """Verifie la chaine fine-tuning : torch, GPU, paquets, modele.

    Le parcours est le seul qui demande un GPU. Le controle ne promet rien : il
    dit ce que le runtime offre reellement, et signale explicitement quand le
    parcours n'est **pas** mesurable ici (pas de GPU).
    """
    elements: List[Dict[str, Any]] = []

    try:
        import torch  # type: ignore
    except Exception as exc:
        elements.append(_element(
            "ft / torch",
            ACTION,
            "torch non importable (%s)" % type(exc).__name__,
            "!pip install torch   # Colab preinstalle torch sur les runtimes GPU",
        ))
        return elements

    cuda = bool(torch.cuda.is_available())
    elements.append(_element("ft / torch", OK, "PyTorch %s" % torch.__version__))
    if cuda:
        nom = torch.cuda.get_device_name(0)
        vram = torch.cuda.get_device_properties(0).total_memory / 1e9
        elements.append(_element(
            "ft / gpu",
            OK,
            "%s, %.1f Go de VRAM" % (nom, vram),
        ))
        if vram < 10:
            elements.append(_element(
                "ft / taille",
                ACTION,
                "%.1f Go de VRAM : le run complet du carnet FT-01 (GPT-2 124 M + LoRA) "
                "a demande 17,2 Go sur la carte du carnet" % vram,
                "borner l'essai (lot reduit, sequence courte, 1 epoch) ou choisir un runtime plus grand",
            ))
    else:
        elements.append(_element(
            "ft / gpu",
            ACTION,
            "aucun GPU visible (torch.cuda.is_available() = False) : le parcours "
            "fine-tuning n'est **pas** mesurable sur ce runtime",
            "Runtime > Modifier le type d'execution > GPU (T4), puis relancer le runtime",
        ))

    manquants = []
    for paquet in ("transformers", "peft", "datasets"):
        try:
            __import__(paquet)
        except Exception:
            manquants.append(paquet)
    if manquants:
        elements.append(_element(
            "ft / paquets",
            ACTION,
            "absents : %s" % ", ".join(manquants),
            "!pip install %s" % " ".join(manquants),
        ))
    else:
        elements.append(_element("ft / paquets", OK, "transformers, peft et datasets importables"))

    elements.append(_element(
        "ft / modele",
        INFO,
        "%s (124 M) n'est pas telecharge par ce controle ; le carnet FT-01 le "
        "charge, avec ou sans jeton HF (debit limite sans jeton)" % FT_MODEL_NAME,
        None,
    ))
    return elements


# ---------------------------------------------------------------------------
# Cle -- deleguee a l'organe partage (#23264)
# ---------------------------------------------------------------------------
def _element_cle(prefixe: str) -> Dict[str, Any]:
    """Construit l'element de cle en s'appuyant sur l'organe partage.

    Aucune valeur de cle n'est rendue : ni la cle, ni un prefixe de celle-ci.
    """
    helpers = _import_genai_helpers()
    if helpers is None:
        return _element(
            "%s / cle" % prefixe,
            ACTION,
            "organe de resolution de la cle absent (genai_helpers.py introuvable)",
            "telecharger aussi genai_helpers.py dans le meme dossier "
            "(raw.githubusercontent.com/jsboige/CoursIA/main/MyIA.AI.Notebooks/GenAI/shared/helpers/genai_helpers.py)",
        )
    try:
        config = helpers.resolve_openai_config(required=False)
    except Exception as exc:
        return _element(
            "%s / cle" % prefixe,
            ACTION,
            "resolution de la cle impossible (%s)" % type(exc).__name__,
            "relire le contrat de cle : docs/reference/... ou l'organe genai_helpers.py",
        )
    if config is None:
        return _element(
            "%s / cle" % prefixe,
            ACTION,
            "aucune cle trouvee ni dans l'environnement ni dans les Secrets Colab",
            "sous Colab : ajouter le Secret OPENAI_API_KEY (ou OPENROUTER_API_KEY) et "
            "basculer 'Acces au notebook' sur ON ; en local : fichier .env",
        )
    return _element(
        "%s / cle" % prefixe,
        OK,
        "cle presente (source : %s, fournisseur : %s, modele : %s) -- valeur jamais affichee"
        % (config.key_source, config.provider, config.model),
    )


# ---------------------------------------------------------------------------
# Assemblage et rendu
# ---------------------------------------------------------------------------
def preflight(parcours: str = "all") -> Dict[str, Any]:
    """Execute le prevol demande et rend le rapport.

    Args:
        parcours: ``claude-cli``, ``sk``, ``finetune`` ou ``all``.

    Returns:
        Un rapport ``{"parcours": ..., "elements": [...]}``.
    """
    if parcours not in PARCOURS and parcours != "all":
        raise ValueError("parcours inconnu : %r (attendu : %s ou all)" % (parcours, ", ".join(PARCOURS)))

    elements: List[Dict[str, Any]] = []
    if parcours in ("all", "claude-cli"):
        elements += check_claude_cli()
    if parcours in ("all", "sk"):
        elements += check_semantic_kernel()
    if parcours in ("all", "finetune"):
        elements += check_finetuning()
    return {"parcours": parcours, "elements": elements}


def render(rapport: Dict[str, Any]) -> str:
    """Rend le rapport en texte lisible dans une cellule."""
    lignes: List[str] = ["=== Prevol Colab : %s ===" % rapport.get("parcours", "?")]
    for element in rapport.get("elements", []):
        lignes.append("[%s] %s -- %s" % (element["etat"], element["element"], element["detail"]))
        if element.get("remede"):
            lignes.append("      remede : %s" % element["remede"])
    compte = {OK: 0, ACTION: 0, INFO: 0}
    for element in rapport.get("elements", []):
        compte[element["etat"]] = compte.get(element["etat"], 0) + 1
    lignes.append(
        "--- %d OK, %d ACTION, %d INFO" % (compte[OK], compte[ACTION], compte[INFO])
    )
    return "\n".join(lignes)


def main(argv: Optional[List[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.strip().splitlines()[0])
    parser.add_argument(
        "parcours",
        nargs="?",
        default="all",
        choices=list(PARCOURS) + ["all"],
        help="Parcours a prevoler (defaut : all)",
    )
    parser.add_argument("--json", action="store_true", help="Rend le rapport en JSON")
    args = parser.parse_args(argv)

    rapport = preflight(args.parcours)
    if args.json:
        print(json.dumps(rapport, ensure_ascii=False, indent=2))
    else:
        print(render(rapport))
    return 0


if __name__ == "__main__":
    sys.exit(main())
