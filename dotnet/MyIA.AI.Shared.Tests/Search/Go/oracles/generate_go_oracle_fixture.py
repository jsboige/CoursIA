#!/usr/bin/env python3
"""Generateur de la fixture de validation croisee des regles du Go.

EPIC #7265 (pepite B3), tranche 2b. Le moteur `GoGame` (MyIA.AI.Shared) porte
les semantiques du `GoBoard` de GoTraxx ; cette fixture le confronte a DEUX
oracles independants, sur des parties aleatoires seedees :

- **pyspiel** (OpenSpiel, C++ DeepMind) : verdict de legalite coup par coup et
  vainqueur en fin de partie. Le jeu `go` d'OpenSpiel normalise son payoff en
  {-1, +1} : il donne le VAINQUEUR, jamais le nombre de points.
- **gnugo 3.8** (mode GTP) : verdict d'acceptation coup par coup, plateau final
  et captures par couleur via `showboard`, score chiffre via `final_score`.
  gnugo tourne en `--simple-ko` (defaut), la meme regle de ko que le
  patrimoine.

Les trois moteurs doivent s'accorder sur : la legalite de chaque coup, le
plateau final pierre a pierre, les captures par couleur, et le signe du score.
Une divergence (typiquement un superko ou une detection de vie/morte propre a
gnugo) tronque la sequence au prefixe concordant et est comptee dans les
metadonnees -- jamais masquee.

Determinisme : seeds fixes, aucune date dans la sortie -- regenerer la fixture
avec les memes oracles produit le meme fichier.

Usage (depuis ce dossier) :
    python generate_go_oracle_fixture.py

Prerequis :
- `pyspiel` importable dans le python courant (`pip install open-spiel`)
- gnugo dans WSL : build local documente dans la PR (`$HOME/gnugo-install/bin/gnugo`)
"""
from __future__ import annotations

import json
import random
import re
import subprocess
import sys
from pathlib import Path

import pyspiel

GNUGO_WSL_PATH = "$HOME/gnugo-install/bin/gnugo"
GTP_LETTERS = "ABCDEFGHJKLMNOPQRSTUVWXYZ"  # le I est saute (convention GTP)

# (board_size, komi, nb_parties, seed de base)
CONFIGS = [
    (5, 0.0, 4, 101),
    (5, 2.5, 4, 202),
    (7, 0.5, 4, 303),
]
MAX_MOVES = 70
PASS_ACTION = lambda size: size * size  # noqa: E731 -- passe = dernier id d'action


class GnuGo:
    """Client GTP minimal : une session gnugo --mode gtp pilotee par stdin."""

    def __init__(self) -> None:
        self.proc = subprocess.Popen(
            ["wsl", "-e", "sh", "-c", f"{GNUGO_WSL_PATH} --mode gtp"],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            text=True,
            encoding="utf-8",
        )

    def cmd(self, line: str) -> str:
        assert self.proc.stdin and self.proc.stdout
        self.proc.stdin.write(line + "\n")
        self.proc.stdin.flush()
        out: list[str] = []
        # Reponse GTP : lignes jusqu'a une ligne vide.
        while True:
            resp = self.proc.stdout.readline()
            if resp == "" or resp.strip() == "":
                break
            out.append(resp.rstrip("\n"))
        return "\n".join(out)

    def accepted(self, response: str) -> bool:
        return response.startswith("=")

    def close(self) -> None:
        try:
            self.cmd("quit")
        finally:
            self.proc.kill()


def point_name(x: int, y: int) -> str:
    """Nom GTP du point -- la meme convention que GoPoint.ToString() en C#."""
    return f"{GTP_LETTERS[x]}{y + 1}"


def parse_showboard(show: str, size: int) -> tuple[list[str], int, int]:
    """Plateau + captures depuis `showboard`.

    Rend (board, white_captures, black_captures) ou board[y] est une chaine de
    `size` caracteres, 'X' noir, 'O' blanc, '.' vide. Les lignes affichees par
    gnugo sont numerotees depuis le bas : la ligne `r` porte les intersections
    d'ordonnee y = r - 1 (meme convention que point_name).
    """
    board = ["." * size for _ in range(size)]
    white_cap = black_cap = 0
    for line in show.splitlines():
        stripped = line.strip()
        if "has captured" in stripped:
            n = int(stripped.split("has captured")[1].split("stone")[0].strip())
            # La ligne commence par le numero de rangee : la couleur est ailleurs
            # dans la ligne ("3 . . X . 3     WHITE (O) has captured 2 stones").
            if "WHITE (O)" in stripped:
                white_cap = n
            elif "BLACK (X)" in stripped:
                black_cap = n
            # Retirer la mention pour parser les cellules de la meme ligne.
            stripped = re.split(r"\s{2,}", stripped)[0].strip()
        parts = stripped.split()
        # Forme attendue : "5 . . . . . 5" (numero, cells, numero)
        if len(parts) >= size + 1 and parts[0].isdigit():
            row = int(parts[0])
            cells = parts[1:1 + size]
            if len(cells) == size:
                board[row - 1] = "".join("." if c in ".+" else c for c in cells)
    return board, white_cap, black_cap


def parse_pyspiel_board(state: "pyspiel.State", size: int) -> list[str]:
    """Plateau depuis GoState.to_string() (lignes numerotees depuis le bas)."""
    board = ["." * size for _ in range(size)]
    for line in state.to_string().splitlines():
        parts = line.split()
        # OpenSpiel rend "  5 +++++" : numero puis chaine de cellules compacte.
        if len(parts) == 2 and parts[0].isdigit() and len(parts[1]) == size:
            row = int(parts[0])
            board[row - 1] = "".join(
                "X" if c == "X" else "O" if c == "O" else "." for c in parts[1]
            )
    return board


def illegal_probes(state: "pyspiel.State", size: int, rng: random.Random) -> list[tuple[int, int]]:
    """Quelques intersections non legales au trait, pour tester le refus."""
    legal = set(state.legal_actions())
    candidates = [a for a in range(size * size) if a not in legal]
    rng.shuffle(candidates)
    return [(a % size, a // size) for a in candidates[:3]]


def generate() -> dict:
    gnugo = GnuGo()
    sequences: list[dict] = []
    divergences = {"gnugo_refused_played_move": 0, "board_mismatch_at_end": 0}
    pyspiel_version = getattr(pyspiel, "__version__", "unknown")

    try:
        for size, komi, n_games, seed0 in CONFIGS:
            game = pyspiel.load_game("go", {"board_size": size, "komi": komi})
            for i in range(n_games):
                seed = seed0 + i
                rng = random.Random(seed)
                state = game.new_initial_state()
                moves: list[dict] = []
                probes: list[dict] = []

                gnugo.cmd(f"boardsize {size}")
                gnugo.cmd(f"komi {komi}")
                gnugo.cmd("clear_board")

                consecutive_passes = 0
                while len(moves) < MAX_MOVES and consecutive_passes < 2:
                    # Un etat terminal n'a plus de couleur au trait (pyspiel rend
                    # -4, l'id du joueur terminal) : sonder ici fabriquerait des
                    # sondes etiquetees "white" sur une partie finie. On sort.
                    if state.is_terminal():
                        break

                    for (px, py) in illegal_probes(state, size, rng):
                        probes.append({
                            "x": px, "y": py,
                            "after_moves": len(moves),
                            "color": "black" if state.current_player() == 0 else "white",
                            "pyspiel_legal": False,
                        })

                    actions = state.legal_actions()
                    if not actions:
                        break
                    stone_actions = [a for a in actions if a != PASS_ACTION(size)]
                    if stone_actions and rng.random() >= 0.06:
                        action = rng.choice(stone_actions)
                    else:
                        action = PASS_ACTION(size)
                    if action not in actions:
                        break
                    if action == PASS_ACTION(size):
                        color = "black" if state.current_player() == 0 else "white"
                        resp = gnugo.cmd(f"play {color} pass")
                        if not gnugo.accepted(resp):
                            divergences["gnugo_refused_played_move"] += 1
                            break
                        state.apply_action(action)
                        moves.append({"x": -1, "y": -1, "color": color,
                                      "pyspiel_legal": True, "gnugo_legal": True})
                        consecutive_passes += 1
                        continue

                    x, y = action % size, action // size
                    color = "black" if state.current_player() == 0 else "white"
                    resp = gnugo.cmd(f"play {color} {point_name(x, y)}")
                    if not gnugo.accepted(resp):
                        divergences["gnugo_refused_played_move"] += 1
                        break
                    state.apply_action(action)
                    moves.append({"x": x, "y": y, "color": color,
                                  "pyspiel_legal": True, "gnugo_legal": True})
                    consecutive_passes = 0

                board_pyspiel = parse_pyspiel_board(state, size)
                show = gnugo.cmd("showboard")
                board_gnugo, white_cap, black_cap = parse_showboard(show, size)
                if board_gnugo != board_pyspiel:
                    divergences["board_mismatch_at_end"] += 1

                final: dict = {
                    "terminal": state.is_terminal(),
                    "pyspiel_board": board_pyspiel,
                    "gnugo_board": board_gnugo,
                    "gnugo_white_captures": white_cap,
                    "gnugo_black_captures": black_cap,
                    "board_agree": board_gnugo == board_pyspiel,
                }
                if state.is_terminal():
                    returns = state.returns()
                    final["pyspiel_winner"] = "black" if returns[0] > 0 else "white"
                    score = gnugo.cmd("final_score")
                    final["gnugo_final_score"] = score.lstrip("= ").strip()

                sequences.append({
                    "board_size": size, "komi": komi, "seed": seed,
                    "moves": moves, "probes": probes, "final": final,
                })
    finally:
        gnugo.close()

    return {
        "meta": {
            "generator": "generate_go_oracle_fixture.py",
            "regenerate_command": "python generate_go_oracle_fixture.py",
            "oracles": {
                "pyspiel": pyspiel_version,
                "gnugo": "3.8 (GNU Go, build local -fcommon, --simple-ko par defaut)",
            },
            "params": [
                {"board_size": s, "komi": k, "games": n, "seed_base": sd}
                for (s, k, n, sd) in CONFIGS
            ],
            "divergences": divergences,
            "notes": [
                "pyspiel normalise son payoff en {-1,+1} : il donne le vainqueur, jamais le nombre de points.",
                "gnugo n'impose PAS l'alternance en GTP (il accepte deux noirs de suite) ; les sequences generees alternent neanmoins, le croisement reste valide.",
                "final_score de gnugo applique une detection de vie/morte : il n'est PAS asserte chiffre par chiffre, seul le signe l'est via le vainqueur pyspiel.",
            ],
        },
        "sequences": sequences,
    }


def main() -> int:
    out = Path(__file__).parent / "go_oracle_fixture.json"
    data = generate()
    out.write_text(json.dumps(data, indent=1, ensure_ascii=True) + "\n",
                   encoding="utf-8", newline="\n")
    total_moves = sum(len(s["moves"]) for s in data["sequences"])
    total_probes = sum(len(s["probes"]) for s in data["sequences"])
    print(f"{out.name}: {len(data['sequences'])} sequences, "
          f"{total_moves} coups joues, {total_probes} sondes de refus, "
          f"divergences={data['meta']['divergences']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
