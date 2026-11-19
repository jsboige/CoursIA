"""Driver ligne-de-commande du coeur TSP pour la cellule Kernel Gateway C#.

Pli 0 v2 (#27218) : le carnet MGS-07-TSP tourne sous kernel C# (.NET Interactive)
et consomme directement le sous-module MetaGeneticSharp. Le coeur d'optimisation
du service web est Python (`mgs_tsp_core`). La cellule d'endpoint `# POST /search/tsp`
du carnet invoque ce driver en sous-processus (stdin = corps JSON, stdout =
reponse du contrat) : un seul carnet porte cours + TP + service, sans jumeau
Python (veto Q168 respecte).

Usage : `echo '<corps JSON>' | python mgs_tsp_gateway_driver.py`
Sortie : une ligne JSON `{"status": "ok"|"invalid"|"error", ...}` — le meme
contrat que `mgs_tsp_service.py` (FastAPI) et que la cellule d'endpoint.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from mgs_tsp_core import TspInputError, TspRunError, run


def main() -> None:
    raw = sys.stdin.read()
    try:
        payload = json.loads(raw) if raw.strip() else None
        data = run(payload)
        print(json.dumps({"status": "ok", "data": data}, ensure_ascii=False))
    except (TspInputError, json.JSONDecodeError) as exc:
        print(json.dumps({"status": "invalid", "error": str(exc)}, ensure_ascii=False))
    except TspRunError:
        print(json.dumps({"status": "error", "error": "echec de l'optimisation TSP"}, ensure_ascii=False))
    except Exception:
        print(json.dumps({"status": "error", "error": "echec de l'optimisation TSP"}, ensure_ascii=False))


if __name__ == "__main__":
    main()
