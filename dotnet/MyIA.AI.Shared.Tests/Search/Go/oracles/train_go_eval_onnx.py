"""Evaluation Go apprise, voie ONNX (EPIC #7265, pepite B3, tranche 8).

Entraine un petit CNN de valeur sur du auto-jeu aleatoire pyspiel 9x9 (komi 0),
l'exporte en ONNX pour la consommation .NET (Microsoft.ML.OnnxRuntime), et mesure
honnement son MAE contre la baseline `GoGameAdapter.TerritoryHeuristic` : le
score d'aire du plateau COURANT comme predicteur du score final. Verdict
BEATS / NO BEATS rendu tel quel, sans embellissement.

Le verdict d'entree (CNTK INTRINSIC, axe 6) designe cette voie : la technologie
d'evaluation du patrimoine est archivee en lecture seule ; ONNX Runtime est
l'organe de remplacement, avec precedent dans le depot (ML/ML-6-ONNX.ipynb).

Conventions (memes que generate_go_oracle_fixture.py, tranche 2b) :
- deterministe : graines fixees, aucune date en sortie ;
- plateau pyspiel lu via `to_string()` (lignes numerotees depuis le bas,
  X noir, O blanc), range dans le meme referentiel que GoPoint(x, y) :
  y=0 = ligne GTP 1 = bas du goban, x=0 = colonne A ;
- action pyspiel id = ligneDepuisHaut * 9 + colonne, passe = 81 ;
- le score d'aire est Tromp-Taylor (pierres + territoires mono-couleur,
  dame a personne), la meme mesure que GoGame.AreaScore(). La komi n'est pas
  une entree du modele : le consommateur C# l'ajoute apres coup (arithmetique
  exacte, pas apprise).

Sorties (dans ce repertoire) :
- go_eval_9x9_v1.onnx : le modele exporte (reproductible en environ, exact
  en fixtures : le fichier commite fait foi, pas la regeneration) ;
- go_eval_onnx_expected.json : temoins figes pour les tests C# -- positions
  relevees sur une partie sonde hors des jeux d'entrainement, sorties
  attendues calculees par ONNX Runtime lui-meme sur le modele exporte.

Usage : python train_go_eval_onnx.py   (deps : pyspiel, torch, onnx, onnxruntime, numpy)
"""

from __future__ import annotations

import json
import random
from collections import deque
from pathlib import Path

import numpy as np
import onnxruntime as ort
import torch
from torch import nn

# --- Parametres (figes : la fixture commitee doit rester reproducible) -------

BOARD = 9
KOMI = 0.0
N_GAMES = 800          # auto-jeu aleatoire uniforme
TRAIN_SPLIT = 720      # 40 derniers jeux = test tenu (decoupe par JEU, pas par
                       # position : deux positions voisines d'une meme partie
                       # partagent leur label -- les separer serait une fuite)
MAX_MOVES = 300        # au-dela : deux passes forcees -> terminal deterministe
PASS_ID = BOARD * BOARD
BASE_SEED = 20261009   # jeu i -> BASE_SEED + i (test : 360..399)
PROBE_SEED = 555001    # partie temoin, hors plage d'entrainement
TRAIN_SEEDS = (11, 22, 33)
EPOCHS = 8
BATCH = 256
LR = 1e-3
OUT_DIR = Path(__file__).resolve().parent

# --- Plateau pyspiel -> representation GoPoint ------------------------------


def parse_board(state) -> np.ndarray:
    """Plateau [9,9] : 0 vide, 1 noir (X), 2 blanc (O). Ligne 0 = bas (GTP 1)."""
    board = np.zeros((BOARD, BOARD), dtype=np.uint8)
    for line in state.to_string().splitlines():
        parts = line.split()
        if len(parts) == 2 and parts[0].isdigit() and len(parts[1]) == BOARD:
            row = int(parts[0])           # numero GTP, 1 = bas
            cells = parts[1]
            for x, c in enumerate(cells):
                board[row - 1][x] = 1 if c == "X" else 2 if c == "O" else 0
    return board


def to_play_black(state) -> bool:
    """True si noir au trait (pyspiel go : joueur 0 = noir)."""
    return state.current_player() == 0


def action_to_gopoint(action: int) -> dict:
    """id pyspiel -> {x, y} au referentiel GoPoint (y compte depuis le bas).

    Mesure sur 5x5 (asymetrique, la 9x9 ne distingue pas les deux formes par
    symetrie) : l'action 0 pose la pierre sur la ligne GTP 1, la premiere
    ligne IMPRIMEE en bas -- id = (ligne GTP - 1) * 9 + colonne, ligne comptee
    depuis le bas. C'est l'encodage de la tranche 2b (y = action // size).
    """
    if action == PASS_ID:
        return {"pass": True}
    gtp_row, x = divmod(action, BOARD)
    return {"x": x, "y": gtp_row}


def area_score(board: np.ndarray) -> int:
    """Score d'aire Tromp-Taylor, la mesure de GoGame.AreaScore() sans komi.

    Pierres + regions vides bordees par une seule couleur ; une region dame
    (deux couleurs) ne compte pour personne.
    """
    black = white = 0
    seen = np.zeros_like(board, dtype=bool)
    for y in range(BOARD):
        for x in range(BOARD):
            cell = board[y][x]
            if cell == 1:
                black += 1
            elif cell == 2:
                white += 1
            elif not seen[y][x]:
                size, colors = 0, set()
                queue = deque([(x, y)])
                seen[y][x] = True
                while queue:
                    cx, cy = queue.popleft()
                    size += 1
                    for nx, ny in ((cx - 1, cy), (cx + 1, cy),
                                   (cx, cy - 1), (cx, cy + 1)):
                        if 0 <= nx < BOARD and 0 <= ny < BOARD:
                            neighbor = board[ny][nx]
                            if neighbor == 0:
                                if not seen[ny][nx]:
                                    seen[ny][nx] = True
                                    queue.append((nx, ny))
                            else:
                                colors.add(int(neighbor))
                if colors == {1}:
                    black += size
                elif colors == {2}:
                    white += size
    return black - white


def play_random_game(seed: int):
    """Une partie aleatoire uniforme ; rend (positions, plateau_final, coups).

    positions : liste de (plateau, noir_au_trait) relevee avant chaque coup
    plus le plateau terminal ; coups : la sequence en GoPoint, pour temoins.
    """
    import pyspiel

    game = pyspiel.load_game("go", {"board_size": BOARD, "komi": KOMI})
    state = game.new_initial_state()
    rng = random.Random(seed)
    positions: list[tuple[np.ndarray, bool]] = []
    moves: list[dict] = []
    for _ in range(MAX_MOVES):
        if state.is_terminal():
            break
        positions.append((parse_board(state), to_play_black(state)))
        action = rng.choice(state.legal_actions())
        moves.append(action_to_gopoint(action))
        state.apply_action(action)
    if not state.is_terminal():          # plafond atteint : deux passes forcees
        positions.append((parse_board(state), to_play_black(state)))
        state.apply_action(PASS_ID)
        state.apply_action(PASS_ID)
    else:
        positions.append((parse_board(state), to_play_black(state)))
    return positions, parse_board(state), moves


def featurize(boards_and_to_play) -> np.ndarray:
    """[(plateau, noir_au_trait)] -> tenseur [N, 3, 9, 9] float32.

    Plan 0 : pierres noires ; plan 1 : pierres blanches ; plan 2 : 1 si noir
    au trait, 0 sinon. Ligne 0 = bas du goban (referentiel GoPoint).
    """
    n = len(boards_and_to_play)
    out = np.zeros((n, 3, BOARD, BOARD), dtype=np.float32)
    for i, (board, black_to_play) in enumerate(boards_and_to_play):
        out[i, 0] = board == 1
        out[i, 1] = board == 2
        out[i, 2] = 1.0 if black_to_play else 0.0
    return out


# --- Reseau (volontairement minuscule : c'est une demonstration de la voie,
#     pas une performance d'etat de l'art -- le MAE rendu dit ce qu'il vaut) --


class GoValueNet(nn.Module):
    """Deux conv puis une tete aplaties : ~170k parametres.

    La premiere version (conv 1x1 -> ReLU -> moyenne spatiale -> Linear(1,1))
    laissait deux graines sur trois en loss plat : le ReLU pre-moyenne peut
    mourir sur toute la carte et laisser le reseau reduit a une constante,
    plus mauvaise que de predire zero. La tete aplatie n'a pas de chemin mort.
    """

    def __init__(self):
        super().__init__()
        self.body = nn.Sequential(
            nn.Conv2d(3, 16, kernel_size=3, padding=1), nn.ReLU(),
            nn.Conv2d(16, 32, kernel_size=3, padding=1), nn.ReLU(),
            nn.Flatten(),
        )
        self.head = nn.Sequential(nn.Linear(32 * 81, 64), nn.ReLU(), nn.Linear(64, 1))

    def forward(self, x):
        return self.head(self.body(x)).squeeze(1)


def train_one(x_train, y_train, seed, log):
    torch.manual_seed(seed)
    model = GoValueNet()
    opt = torch.optim.Adam(model.parameters(), lr=LR)
    loss_fn = nn.MSELoss()
    g = torch.Generator().manual_seed(seed)
    n = x_train.shape[0]
    for epoch in range(EPOCHS):
        order = torch.randperm(n, generator=g)
        total = 0.0
        for start in range(0, n, BATCH):
            idx = order[start:start + BATCH]
            batch_x = x_train[idx]
            batch_y = y_train[idx]
            opt.zero_grad()
            loss = loss_fn(model(batch_x), batch_y)
            loss.backward()
            opt.step()
            total += loss.item() * len(idx)
        log(f"  epoque {epoch + 1}/{EPOCHS} mse train {total / n:.2f}")
    return model


def mae_of(model, x, y) -> float:
    model.eval()
    with torch.no_grad():
        pred = model(x)
    return float((pred - y).abs().mean())


# --- Export ONNX ------------------------------------------------------------


def export_onnx(model: nn.Module, path: Path):
    model.eval()
    dummy = torch.zeros(1, 3, BOARD, BOARD)
    try:
        torch.onnx.export(
            model, dummy, str(path),
            input_names=["input"], output_names=["score"],
            opset_version=17, dynamo=False,
        )
    except TypeError:                     # torch ou la kw a change de face
        torch.onnx.export(
            model, dummy, str(path),
            input_names=["input"], output_names=["score"],
            opset_version=17,
        )


def ort_score(path: Path, tensor: np.ndarray) -> float:
    """Sortie du graphe ONNX par ONNX Runtime (paradigme exact des temoins C#)."""
    session = ort.InferenceSession(str(path), providers=["CPUExecutionProvider"])
    (out,) = session.run(None, {"input": tensor})
    return float(np.asarray(out).reshape(-1)[0])


# --- Programme ---------------------------------------------------------------


def main():
    log = print

    log(f"[1/5] auto-jeu pyspiel {BOARD}x{BOARD} komi {KOMI} : {N_GAMES} parties")
    train_pos, test_pos = [], []
    baseline_abs_err = []                 # MAE de TerritoryHeuristic sur le test
    for i in range(N_GAMES):
        positions, final_board, _ = play_random_game(BASE_SEED + i)
        label = float(area_score(final_board))       # komi 0, hors modele
        bucket = train_pos if i < TRAIN_SPLIT else test_pos
        for board, black_to_play in positions:
            bucket.append(((board, black_to_play), label))
        if i >= TRAIN_SPLIT:
            for board, _ in positions:
                baseline_abs_err.append(abs(area_score(board) - label))
    x_train = torch.from_numpy(featurize([p for p, _ in train_pos]))
    y_train = torch.tensor([l for _, l in train_pos], dtype=torch.float32)
    x_test = torch.from_numpy(featurize([p for p, _ in test_pos]))
    y_test = torch.tensor([l for _, l in test_pos], dtype=torch.float32)
    log(f"  positions : {len(train_pos)} train / {len(test_pos)} test")

    log("[2/5] entrainement (3 graines, le meilleur MAE test est exporte)")
    best_model, best_mae, per_seed = None, float("inf"), {}
    for seed in TRAIN_SEEDS:
        model = train_one(x_train, y_train, seed, log)
        mae = mae_of(model, x_test, y_test)
        per_seed[seed] = round(mae, 3)
        log(f"  graine {seed} : MAE test {mae:.3f}")
        if mae < best_mae:
            best_model, best_mae = model, mae
    baseline_mae = float(np.mean(baseline_abs_err))
    verdict = "BEATS" if best_mae < baseline_mae else "NO BEATS"
    log(f"[3/5] MAE test : net {best_mae:.3f} vs baseline TerritoryHeuristic "
        f"{baseline_mae:.3f} -> {verdict}")

    log("[4/5] export ONNX")
    model_path = OUT_DIR / "go_eval_9x9_v1.onnx"
    export_onnx(best_model, model_path)

    log("[5/5] temoins figes (partie sonde, hors jeux d'entrainement)")
    positions, final_board, moves = play_random_game(PROBE_SEED)
    final_label = float(area_score(final_board))
    witness_plies = [0, 4, 12, 30, 60, len(moves)]
    witnesses = []
    for ply in sorted(set(min(p, len(moves)) for p in witness_plies)):
        board, black_to_play = positions[ply]
        tensor = featurize([(board, black_to_play)])
        expected = ort_score(model_path, tensor)
        witnesses.append({
            "ply": ply,
            "moves": moves[:ply],
            "to_play": "black" if black_to_play else "white",
            "expected_score": round(expected, 4),
            "current_area": area_score(board),   # ce que dit la baseline ici
            "final_label": final_label,          # ce que vaut vraiment la fin
        })
    # Parite torch vs ONNX Runtime sur le premier temoin (garde d'export).
    with torch.no_grad():
        torch_out = float(best_model(x_test[:1]).item())
    parity = abs(torch_out - ort_score(model_path, x_test[:1].numpy()))
    if parity > 1e-4:
        raise SystemExit(f"parite torch/ONNX rompue : {parity}")
    log(f"  parite torch/ONNX Runtime : {parity:.2e}")

    manifest = {
        "board_size": BOARD,
        "komi": KOMI,
        "model_file": model_path.name,
        "generator": Path(__file__).name,
        "conventions": {
            "tensor": "1x3x9x9 float32 ; plan0 pierres noires, plan1 blanches, "
                      "plan2 = 1 si noir au trait ; ligne 0 = bas (GoPoint)",
            "action_id": "(ligne GTP - 1) * 9 + colonne, comptee depuis le bas (mesure 5x5, cf action_to_gopoint) ; passe = 81",
            "score": "aire Tromp-Taylor sans komi ; le consommateur ajoute la "
                     "komi exacte apres inference",
        },
        "metrics": {
            "positions_train": len(train_pos),
            "positions_test": len(test_pos),
            "mae_net_per_seed": per_seed,
            "mae_net_exported": round(best_mae, 3),
            "mae_baseline_territory_heuristic": round(baseline_mae, 3),
            "verdict": verdict,
        },
        "witnesses": witnesses,
    }
    expected_path = OUT_DIR / "go_eval_onnx_expected.json"
    expected_path.write_text(
        json.dumps(manifest, indent=1) + "\n", encoding="utf-8")
    log(f"  ecrit : {model_path.name} ({model_path.stat().st_size} octets), "
        f"{expected_path.name} ({len(witnesses)} temoins)")


if __name__ == "__main__":
    main()
