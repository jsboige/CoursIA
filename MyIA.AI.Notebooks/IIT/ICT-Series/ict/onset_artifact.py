"""Schema de l'artefact du runner onset — module pur, sans dependance lourde.

Le runner :mod:`ict.onset_runner` importe torch / trl / peft au chargement : un test
qui voudrait verifier la forme de l'artefact devrait donc payer l'import du stack
d'entrainement, et ne pourrait pas tourner sur une machine sans lui. Le schema vit
donc ici, sans dependance, et le runner le consomme.

**Pourquoi le budget de completion est dans l'artefact (#21998).** Un artefact de
mesure qui ne dit pas sous quel regime de troncature il a ete produit n'est pas
relisible : `ict25_arms.py` a servi pendant des semaines des comparaisons entre un
bras a cap 1024 et un bras a cap 80 sans que rien, dans les fichiers, ne permette
de le voir. Le defaut a ete corrige la-bas le 2026-10-23 ; ce module porte la meme
exigence pour les runs onset — `max_completion_length` y est ecrit au niveau de
l'artefact **et** dans chaque resultat de graine.
"""

from __future__ import annotations

from typing import Any

# 80 est le regime des artefacts baseline 0.5B (comparaison W/S @120 steps) : le
# garder par defaut maintient les runs comparables entre eux. Ce n'est PAS une
# calibration : la mesure EOS de #13596 montre qu'a 80 les completions sont
# systematiquement tronquees (min = max = 80 sur 40/40 steps). Le cap est donc un
# parametre du protocole, pas une propriete du modele — d'ou son enregistrement.
DEFAULT_MAX_COMPLETION_LENGTH = 80

SCRIPT_ID = "ict/onset_runner.py"


def artifact_payload(*, model: str, max_steps: int, lr: float, num_gen: int, seeds: list[int],
                     max_completion_length: int, results: dict[str, Any],
                     summary: dict[str, Any]) -> dict[str, Any]:
    """Assemble le JSON d'artefact d'un run onset. Fonction pure, sans effet de bord.

    Les cles ``script`` et ``max_completion_length`` ne sont pas decoratives : elles
    rendent l'artefact auto-suffisant pour un lecteur qui n'a pas le depot sous les
    yeux (regime de troncature et producteur).
    """
    return {
        "script": SCRIPT_ID,
        "model": model,
        "max_steps": max_steps,
        "lr": lr,
        "num_generations": num_gen,
        "max_completion_length": max_completion_length,
        "seeds": list(seeds),
        "results": results,
        "summary": summary,
    }
