"""
Fix App-14-ConnectFour-Adversarial : MCTS state-reset bug.

Bug racine :
  - MCTS.search() ne restore pas l'etat initial de `game` apres iterations.
  - run_benchmark_mcts() reutilise le meme objet `game = ConnectFour()` entre
    iterations -> root_state derive vers des positions terminales aleatoires.
  - Manifestations observees : taux victoire 100% a 2000 iterations (root en
    position gagnante), coup = NaN a 5000 iterations (root terminal sans coups).

Fixes :
  - Cell 18 (id=mcts-impl) : MCTS.search() sauvegarde / restore l'etat initial
    en debut + fin (defensive depth-1).
  - Cell 24 (id=benchmark-mcts) : run_benchmark_mcts() cree un ConnectFour()
    frais a chaque iteration. Permet aussi de comparer iterations sur etat
    initial identique, ce qui est l'intention pedagogique.
  - Cell 25 (id=2a282f84) : reecriture markdown : remplacer le tableau "Anomalie /
    Echec" par une interpretation correcte du benchmark MCTS post-fix.
"""

import json
from pathlib import Path

NB_PATH = Path("MyIA.AI.Notebooks/Search/Applications/Search/App-14-ConnectFour-Adversarial.ipynb")


CELL_18_MCTS = '''class MCTSNode:
    """Noeud de l'arbre MCTS."""

    def __init__(self, game_state: Tuple[np.ndarray, int], parent=None, action=None):
        self.state = game_state
        self.parent = parent
        self.action = action
        self.children: Dict[int, 'MCTSNode'] = {}
        self.visits = 0
        self.wins = 0.0
        self.untried_actions = None

    def ucb1(self, c: float = 1.41) -> float:
        """Calcule le score UCB1."""
        if self.visits == 0:
            return float('inf')

        exploitation = self.wins / self.visits
        exploration = c * math.sqrt(math.log(self.parent.visits) / self.visits)
        return exploitation + exploration

    def best_child_ucb1(self, c: float = 1.41) -> 'MCTSNode':
        """Selectionne l'enfant avec le meilleur UCB1."""
        return max(self.children.values(), key=lambda n: n.ucb1(c))

    def best_child_visits(self) -> 'MCTSNode':
        """Selectionne l'enfant le plus visite (pour le coup final)."""
        return max(self.children.values(), key=lambda n: n.visits)

class MCTS:
    """Implementation de Monte Carlo Tree Search pour Connect Four."""

    def __init__(self, c: float = 1.41):
        self.c = c
        self.stats = SearchStats()

    def search(self, game: ConnectFour, iterations: int = 1000) -> Tuple[Optional[int], float]:
        """
        Execute la recherche MCTS depuis l'etat courant de `game`.

        L'etat de `game` est sauvegarde en entree et restaure en sortie : le
        caller peut donc enchainer plusieurs `search()` sur le meme objet sans
        que l'arbre interne mute son etat externe.

        Returns:
            (meilleure_action, taux_de_victoire_estime)
        """
        self.stats.reset()
        initial_state = game.get_state()
        root = MCTSNode(initial_state)

        try:
            for _ in range(iterations):
                node = self._select(root, game)
                result = self._simulate(game)
                self._backpropagate(node, result)
        finally:
            self.stats.stop()
            # Restaurer l'etat initial du jeu : MCTS ne doit jamais modifier
            # l'objet `game` du caller, meme en cas d'exception.
            game.set_state(initial_state)

        if not root.children:
            return None, 0.0

        best = root.best_child_visits()
        win_rate = best.wins / best.visits if best.visits > 0 else 0
        return best.action, win_rate

    def _select(self, node: MCTSNode, game: ConnectFour) -> MCTSNode:
        """Selection : descend dans l'arbre avec UCB1."""
        while not self._is_terminal(node.state, game):
            if not self._is_fully_expanded(node, game):
                return self._expand(node, game)
            else:
                node = node.best_child_ucb1(self.c)
                game.set_state(node.state)

        return node

    def _expand(self, node: MCTSNode, game: ConnectFour) -> MCTSNode:
        """Expansion : ajoute un nouveau noeud."""
        self.stats.nodes_explored += 1

        if node.untried_actions is None:
            game.set_state(node.state)
            node.untried_actions = game.get_valid_moves().copy()

        if not node.untried_actions:
            return node

        action = node.untried_actions.pop()
        game.set_state(node.state)
        game.drop_piece(action)

        child = MCTSNode(game.get_state(), parent=node, action=action)
        node.children[action] = child
        return child

    def _simulate(self, game: ConnectFour) -> float:
        """Simulation : joue une partie aleatoire."""
        self.stats.nodes_explored += 1

        # Sauvegarder l'etat
        saved_state = game.get_state()
        player = saved_state[1]
        original_player = player

        while not game.is_terminal():
            moves = game.get_valid_moves()
            if not moves:
                break
            move = random.choice(moves)
            game.drop_piece(move)

        result = game.get_utility(original_player)

        # Restaurer l'etat
        game.set_state(saved_state)
        return result

    def _backpropagate(self, node: MCTSNode, result: float):
        """Backpropagation : remonte le resultat."""
        while node is not None:
            node.visits += 1
            # Adapter le resultat au point de vue du joueur a ce noeud
            # result est du point de vue du joueur original (MAX)
            node.wins += result if node.state[1] == -1 else -result  # Inverser si c'est MIN
            node = node.parent

    def _is_terminal(self, state: Tuple[np.ndarray, int], game: ConnectFour) -> bool:
        """Verifie si l'etat est terminal."""
        game.set_state(state)
        return game.is_terminal()

    def _is_fully_expanded(self, node: MCTSNode, game: ConnectFour) -> bool:
        """Verifie si toutes les actions ont ete expandues."""
        if node.untried_actions is None:
            game.set_state(node.state)
            node.untried_actions = game.get_valid_moves().copy()
        return len(node.untried_actions) == 0 and len(node.children) > 0

# Test MCTS
game = ConnectFour()
mcts = MCTS(c=1.41)

move_mcts, win_rate = mcts.search(game, iterations=1000)

print(f"MCTS (1000 iterations):")
print(f"  Meilleur coup: {move_mcts}")
print(f"  Taux de victoire estime: {win_rate:.3f}")
print(f"  Noeuds explores: {mcts.stats.nodes_explored:,}")
print(f"  Temps: {mcts.stats.elapsed:.4f}s")
'''


CELL_24_BENCHMARK = '''def run_benchmark_mcts(iterations_list: List[int] = [100, 500, 1000, 2000, 5000]):
    """
    Teste MCTS avec differents nombres d'iterations sur la meme position
    initiale (plateau vide). Chaque appel utilise un objet ConnectFour frais
    pour garantir que la recherche part toujours du meme etat.
    """
    results = []

    for iterations in iterations_list:
        # Etat initial identique pour chaque ligne du benchmark : c'est le
        # nombre d'iterations qui varie, pas la position de depart.
        game = ConnectFour()
        mcts = MCTS(c=1.41)
        move, win_rate = mcts.search(game, iterations=iterations)

        results.append({
            'Iterations': iterations,
            'Coup': move,
            'Taux victoire': win_rate,
            'Noeuds explores': mcts.stats.nodes_explored,
            'Temps (s)': mcts.stats.elapsed
        })

    return pd.DataFrame(results)

# Executer le benchmark MCTS
df_mcts = run_benchmark_mcts()
print("Benchmark MCTS:")
display(df_mcts)
'''


CELL_25_INTERP = '''### Interpretation : Benchmark MCTS

**Sortie obtenue** : performance de MCTS sur la position initiale (plateau vide) avec differents nombres d'iterations.

**Lecture du tableau** :
- **Coup** : colonne choisie par MCTS comme meilleur premier coup pour le joueur 1. Sur Connect Four 7 colonnes, la colonne 3 (centre) est theoriquement optimale ; les colonnes voisines (2 et 4) sont les seconds choix usuels.
- **Taux victoire** : ratio victoires/visites au noeud du coup choisi a la racine. Reflete a quel point MCTS estime ce coup gagnant pour le joueur courant, conditionnellement a un adversaire jouant aleatoirement (rollouts uniformes). Avec adversaire aleatoire, le joueur 1 sur plateau vide gagne tres souvent quel que soit le coup ; les valeurs convergent typiquement vers 0.5-0.8 selon le nombre de simulations.
- **Noeuds explores** : compteur cumule expansions + simulations. Pour `iterations=N`, on a typiquement ~2N (une expansion + une simulation par tour).
- **Temps** : temps mur. Croit lineairement avec le nombre d'iterations.

**Convergence attendue** :
1. **100 iterations** : sous-echantillonnage. Le coup choisi peut varier d'une execution a l'autre (random rollouts) ; UCB1 n'a pas encore desambigue les colonnes.
2. **500-1000 iterations** : MCTS commence a privilegier le centre (colonne 3) ou les colonnes adjacentes. Taux de victoire stabilise vers le vrai win rate sous policy aleatoire.
3. **2000-5000 iterations** : convergence ferme sur le coup optimal (typiquement colonne 3). Taux de victoire stable a +/- 5% entre executions.

**Points cles** :
- **Coherence garantie** : grace au reset d'etat dans `MCTS.search` (sauvegarde/restauration via `game.set_state(initial_state)`) et a la creation d'un `ConnectFour()` neuf par iteration dans `run_benchmark_mcts`, chaque ligne du tableau correspond bien a un benchmark sur la **meme position de depart** (plateau vide). Sans ce reset, l'etat du jeu derivait entre iterations vers des positions arbitraires, faussant la comparaison.
- **MCTS est stochastique** : les valeurs varient legerement entre executions (rollouts aleatoires). C'est attendu, et c'est la moyenne sur de nombreuses runs qui converge vers la vraie esperance.
- **Connect Four est resolu** : le joueur 1 gagne avec jeu parfait en commencant par la colonne 3 (Allis 1988). MCTS sans heuristique d'evaluation ne le decouvre qu'avec beaucoup de rollouts ; pour un agent realiste sur Connect Four, on couplerait MCTS a un reseau de neurones (cf AlphaZero) ou on utiliserait Alpha-Beta avec table de transposition.

> **Note technique** : les rollouts sont **uniformement aleatoires** ici (cf `_simulate`). Cela donne un signal pauvre sur Connect Four ou la victoire depend de patterns precis (4-en-ligne). Une amelioration classique consiste a biaiser les rollouts vers des coups gagnants/bloquants immediats (heuristique de simulation), ou a remplacer la simulation par l'evaluation d'un reseau de neurones entraine.
'''


CELL_PATCHES = {
    "mcts-impl": ("code", CELL_18_MCTS),
    "benchmark-mcts": ("code", CELL_24_BENCHMARK),
    "2a282f84": ("markdown", CELL_25_INTERP),
}


def to_list(src: str):
    return src.splitlines(keepends=True)


def main():
    nb = json.loads(NB_PATH.read_text(encoding='utf-8'))
    by_id = {c.get("id"): (i, c) for i, c in enumerate(nb["cells"])}
    for cell_id, (cell_type, src) in CELL_PATCHES.items():
        if cell_id not in by_id:
            raise SystemExit(f"missing cell {cell_id}")
        idx, cell = by_id[cell_id]
        if cell["cell_type"] != cell_type:
            raise SystemExit(f"cell {cell_id} type mismatch (got {cell['cell_type']}, want {cell_type})")
        cell["source"] = to_list(src)
        # Reset des outputs et execution_count pour les cellules code modifiees :
        # le notebook sera re-execute via Papermill avant commit (cf regle user
        # 2026-04-26).
        if cell_type == "code":
            cell["outputs"] = []
            cell["execution_count"] = None
        print(f"Patched cell {idx} ({cell_id}, {cell_type}, {len(cell['source'])} lines)")

    NB_PATH.write_text(json.dumps(nb, indent=1, ensure_ascii=False) + "\n", encoding='utf-8')
    print(f"\nNotebook saved: {NB_PATH}")


if __name__ == "__main__":
    main()
