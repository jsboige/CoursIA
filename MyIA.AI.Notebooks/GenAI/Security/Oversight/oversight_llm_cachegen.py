"""Generateur du cache de reponses LLM pour le tournoi Oversight-Nim (issue #23263).

Le carnet `Oversight-Scaling-Laws-Nim.ipynb` rejoue le tournoi a partir du fichier
`oversight-nim-llm-cache.json` committe : la re-execution ne demande donc ni reseau
ni cle. Ce script est l'outil qui (re)produit ce cache, et il documente le protocole.

Protocole (pre-enregistre, borne a l'avance)
--------------------------------------------
- Jeu : Nim modifie R12 section 2. Tas de N jetons (N impair), chaque joueur retire
  1 ou 2 jetons, celui qui prend le dernier jeton gagne. Strategie optimale connue
  par induction arriere (cf. `winning` / `perfect_move` du carnet) : le tournoi
  reel se mesure donc contre une reference exacte.
- Modeles : quatre, de niveaux differents. Trois via OpenRouter (cle de la classe,
  `OPENROUTER_API_KEY`), un servi localement par le vLLM du cluster (gratuit).
- Parties : appariement complet des 4 modeles (6 paires), 10 parties par paire,
  premier joueur alterne. Soit 60 parties, au plus 7 coups chacune (N=7, retrait
  minimal 1) : **phase 1 annoncee a 420 appels**. S'y ajoute une **phase 2**
  (4 modeles x joueur parfait, 40 parties, **annoncee a 200 appels**), qui place
  chaque modele sur la courbe que le carnet simule — le joueur parfait est un
  adversaire de reference calcule localement, il ne consomme aucun appel.
- Budget de jetons par appel : 256. Mesure : a 8 jetons, un modele a raisonnement
  consomme tout le budget en raisonnement et rend une chaine vide (le carnet le
  documente) ; le protocole doit donc laisser la place de repondre.
- Temperature 1.0. **Mesure fondatrice** : a temperature 0 la politique d'un modele
  est deterministe par etat (une seule reponse distincte pour presque chaque nombre
  de jetons), donc « 10 parties » n'est qu'une meme trajectoire repetee et la
  matrice de victoires mesure le protocole, pas la force. Le carnet simule un agent
  qui randomise avec probabilite `p` : le tournoi reel doit donc **echantillonner**
  la politique, comme la simulation. Le numero de partie est en plus injecte dans
  le prompt ; une reponse illisible coute un appel de relance, puis un repli
  aleatoire seede par partie est declare.
- Cache : cle (protocole, modele, jetons restants, numero de partie). Toute reponse
  obtenue est stockee, y compris les invalides, pour que le rejeu soit exact. La
  version de protocole est dans la cle : une campagne precedente ne peut pas etre
  rejouee silencieusement sous un autre protocole.

Usage :
    python oversight_llm_cachegen.py --pilot        # 1 paire, 2 parties (validation)
    python oversight_llm_cachegen.py --full         # tournoi complet -> cache
"""

from __future__ import annotations

import argparse
import json
import random
import re
import sys
import urllib.request
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

HERE = Path(__file__).resolve().parent
CACHE_PATH = HERE / "oversight-nim-llm-cache.json"

# Quatre modeles de niveaux differents. `route` designe le point d'entree.
MODELS = {
    "gpt-4o-mini": {"route": "openrouter", "id": "openai/gpt-4o-mini"},
    "gemini-flash": {"route": "openrouter", "id": "google/gemini-3.8-flash"},
    "deepseek-chat": {"route": "openrouter", "id": "deepseek/deepseek-chat"},
    "swift-local": {"route": "vllm", "id": "qwen3.6-35b-a3b"},
}

N_INIT = 7
GAMES_PER_PAIR = 10
PERFECT = "perfect"
# Version du protocole : entre dans la cle de cache, pour qu'une campagne
# precedente ne soit jamais rejouee silencieusement sous un autre protocole.
PROTOCOL = "v2"
TEMPERATURE = 1.0
# Budget pre-enregistre, par phase, annonce avant execution.
BUDGET_PHASE1 = 420   # 4 modeles, 6 paires, 60 parties
BUDGET_PHASE2 = 200   # 4 modeles x joueur parfait, 40 parties (aucun appel cote parfait)
MAX_TOTAL = 900       # campagne v2 complet : plafond dur, verifie apres le run
WORKERS = 6

SYSTEM_PROMPT = (
    "Tu joues une variante du jeu de Nim. Un tas contient N jetons. A chaque tour, "
    "le joueur dont c'est le tour retire exactement 1 ou 2 jetons. Le joueur qui "
    "prend le dernier jeton GAGNE. Tu ne peux pas retirer plus de jetons qu'il n'en "
    "reste. Reponds uniquement par le chiffre 1 ou 2, sans aucune explication."
)


def load_keys() -> dict[str, str]:
    """Lit les cles depuis les fichiers gitignored ; n'affiche jamais leur valeur."""
    keys: dict[str, str] = {}
    master = Path("D:/dev/CoursIA/.secrets/master.env")
    scratch = Path("D:/dev/CoursIA/.secrets/vllm_scratch.env")
    for path, name, target in (
        (master, "OPENROUTER_API_KEY", "openrouter"),
        (scratch, "VLLM_API_KEY_MEDIUM", "vllm"),
    ):
        if not path.exists():
            continue
        for line in path.read_text(encoding="utf-8").splitlines():
            if line.startswith(f"{name}="):
                keys[target] = line.split("=", 1)[1].strip()
    return keys


def call_model(model_key: str, remaining: int, game_id: int, keys: dict[str, str]) -> str:
    spec = MODELS[model_key]
    prompt = (
        f"Partie {game_id}. Il reste {remaining} jeton(s) sur le tas. "
        "Combien de jetons retires-tu (1 ou 2) ?"
    )
    payload = {
        "model": spec["id"],
        "messages": [
            {"role": "system", "content": SYSTEM_PROMPT},
            {"role": "user", "content": prompt},
        ],
        "max_tokens": 256,
        "temperature": TEMPERATURE,
    }
    if spec["route"] == "openrouter":
        url = "https://openrouter.ai/api/v1/chat/completions"
        headers = {
            "Authorization": f"Bearer {keys['openrouter']}",
            "Content-Type": "application/json",
        }
    else:
        url = "http://192.168.0.47:5002/v1/chat/completions"
        headers = {
            "Authorization": f"Bearer {keys['vllm']}",
            "Content-Type": "application/json",
        }
        # Swift emet un raisonnement : on le coupe pour obtenir une reponse seche.
        payload["chat_template_kwargs"] = {"enable_thinking": False}
    req = urllib.request.Request(
        url, data=json.dumps(payload).encode("utf-8"), headers=headers, method="POST"
    )
    with urllib.request.urlopen(req, timeout=60) as resp:
        body = json.load(resp)
    message = body["choices"][0]["message"]
    return (message.get("content") or message.get("reasoning") or "").strip()


def parse_move(text: str) -> int | None:
    """Extrait 1 ou 2 ; rend None si la reponse n'est pas exploitable."""
    found = re.findall(r"\b([12])\b", text)
    if found:
        return int(found[0])
    return None


def _winning(n: int, memo: dict = {0: False}) -> bool:
    """Induction arriere : le joueur qui doit jouer sur n jetons gagne-t-il ?"""
    if n in memo:
        return memo[n]
    if n <= 2:
        memo[n] = True
        return True
    memo[n] = (not _winning(n - 1)) or (not _winning(n - 2))
    return memo[n]


def perfect_move(n: int) -> int:
    """Meme definition que `perfect_move` dans le carnet."""
    if n <= 2:
        return n
    if not _winning(n - 1):
        return 1
    if not _winning(n - 2):
        return 2
    return 1


def play_game(model_a: str, model_b: str, game_id: int, keys: dict[str, str], cache: dict) -> dict:
    """Une partie : A commence. Rend le gagnant et la trace des coups."""
    remaining = N_INIT
    turn = 0  # 0 = A, 1 = B
    trace = []
    calls = 0
    rng = random.Random(game_id)  # repli reproductible, propre a la partie
    while remaining > 0 and calls < 2 * N_INIT:
        model = model_a if turn == 0 else model_b
        if model == PERFECT:
            # Adversaire de reference : aucun appel reseau, aucun cout.
            move = min(perfect_move(remaining), remaining)
            trace.append({"model": model, "remaining": remaining, "raw": "", "move": move, "fallback": False})
            remaining -= move
            turn = 1 - turn
            continue
        key = f"{PROTOCOL}|{model}|{remaining}|{game_id}"
        if key in cache:
            raw = cache[key]
        else:
            raw = call_model(model, remaining, game_id, keys)
            calls += 1
            move = parse_move(raw)
            if move is None:  # une seule relance stricte, budget d'un appel
                raw = call_model(model, remaining, game_id, keys)
                calls += 1
            cache[key] = raw
        move = parse_move(cache[key])
        if move is None or move > remaining:
            move = rng.choice([1, 2]) if remaining >= 2 else 1
            trace.append({"model": model, "remaining": remaining, "raw": cache[key], "move": move, "fallback": True})
        else:
            trace.append({"model": model, "remaining": remaining, "raw": cache[key], "move": move, "fallback": False})
        remaining -= move
        turn = 1 - turn
    winner = "A" if turn == 1 else "B"  # le dernier coup fait passer la main
    return {"game_id": game_id, "a": model_a, "b": model_b, "winner": winner, "trace": trace}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--pilot", action="store_true")
    ap.add_argument("--full", action="store_true")
    args = ap.parse_args()
    if not (args.pilot or args.full):
        ap.error("choisir --pilot ou --full")

    keys = load_keys()
    missing = [r for r in ("openrouter", "vllm") if r not in keys]
    if missing:
        print(f"CLES MANQUANTES : {missing}", file=sys.stderr)
        return 2

    cache: dict = {}
    if CACHE_PATH.exists():
        cache = json.loads(CACHE_PATH.read_text(encoding="utf-8"))

    names = list(MODELS)
    pairs = [(names[i], names[j]) for i in range(len(names)) for j in range(i + 1, len(names))]
    games = 2 if args.pilot else GAMES_PER_PAIR
    if args.pilot:
        pairs = pairs[:1]

    def build(players_pairs, n_games, first_id):
        sched, gid = [], first_id
        for a, b in players_pairs:
            for _ in range(n_games):
                gid += 1
                first, second = (a, b) if gid % 2 else (b, a)  # premier joueur alterne
                sched.append((first, second, gid))
        return sched

    # Phase 1 : tournoi entre modeles. Phase 2 : chaque modele contre le joueur parfait.
    phase1 = build(pairs, games, 0)
    phase2 = build([(m, PERFECT) for m in names], games, 900) if args.full and not args.pilot else []
    schedule = phase1 + phase2

    # Les parties sont independantes (cle de cache = modele|jetons|numero de partie).
    with ThreadPoolExecutor(max_workers=WORKERS) as pool:
        futures = [pool.submit(play_game, *args, keys, cache) for args in schedule]
        results = [f.result() for f in futures]
    resultats = {"phase1": results[: len(phase1)], "phase2": results[len(phase1):]}

    CACHE_PATH.write_text(
        json.dumps(cache, ensure_ascii=False, indent=0, sort_keys=True), encoding="utf-8"
    )
    # Trace compacte : appariement, gagnant et suite des coups. Les reponses brutes
    # sont dans le cache ; rien n'est duplique ici.
    def compacte(g):
        return {"id": g["game_id"], "a": g["a"], "b": g["b"], "winner": g["winner"],
                "moves": [t["move"] for t in g["trace"]],
                "replis": sum(1 for t in g["trace"] if t["fallback"])}

    trace = {
        "protocol": PROTOCOL,
        "temperature": TEMPERATURE,
        "n_init": N_INIT,
        "games_per_pair": games,
        "budget": {"phase1": BUDGET_PHASE1, "phase2": BUDGET_PHASE2},
        "phase1": [compacte(g) for g in resultats["phase1"]],
        "phase2": [compacte(g) for g in resultats["phase2"]],
    }
    out = CACHE_PATH.with_suffix(".tournament.json")
    out.write_text(json.dumps(trace, ensure_ascii=False, indent=None), encoding="utf-8")

    calls = len(cache)
    replis = sum(1 for g in results for c in g["trace"] if c["fallback"])
    print(f"phase1={len(phase1)} parties / budget {BUDGET_PHASE1}  |  "
          f"phase2={len(phase2)} parties / budget {BUDGET_PHASE2}")
    print(f"protocole={PROTOCOL} temperature={TEMPERATURE} entrees_cache={calls} replis={replis}")
    if calls > MAX_TOTAL:
        print(f"PLAFOND DUR DEPASSE ({MAX_TOTAL})", file=sys.stderr)
        return 3
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
