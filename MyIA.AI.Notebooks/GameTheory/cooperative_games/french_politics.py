"""
French Political Coalition Analysis - 2024 Legislative Elections
================================================================

This module models the French left coalition (Nouveau Front Populaire)
using cooperative game theory and Shapley value analysis.

Context (June-July 2024):
- Snap legislative elections called after EU elections
- Left parties formed "Nouveau Front Populaire" (NFP) coalition
- Main parties: LFI, PS, EELV, PCF
- NFP won the most seats but no absolute majority

Data sources:
- Ministry of Interior (official results)
- IFOP/Ipsos polling data
- INSEE demographic data

Key insight: Shapley value reveals each party's true marginal contribution,
which often differs from their perceived political weight and demands.
"""

from typing import Dict, List, Set, Tuple, Optional
from dataclasses import dataclass
import numpy as np
from .coalition_games import CoalitionGame, WeightedVotingGame
from .shapley import shapley_value_exact, shapley_value_monte_carlo, ShapleyCalculator


# ============================================================================
# 2024 Legislative Election Data
# ============================================================================

@dataclass
class PartyData:
    """Data for a political party in 2024 elections."""
    name: str
    short_name: str
    first_round_votes: int        # Premier tour (30 juin 2024)
    first_round_pct: float        # % des suffrages exprimes
    seats_won: int                # Sieges obtenus (second tour 7 juillet)
    estimated_alone_seats: int    # Sieges estimes si seul (sans desistements)


# Official results from Ministry of Interior
# Source: https://www.resultats-elections.interieur.gouv.fr/legislatives2024/
PARTIES_2024 = {
    'LFI': PartyData(
        name="La France Insoumise",
        short_name="LFI",
        first_round_votes=4_935_908,
        first_round_pct=9.89,
        seats_won=74,
        estimated_alone_seats=45,  # Estimation sans front republicain
    ),
    'PS': PartyData(
        name="Parti Socialiste",
        short_name="PS",
        first_round_votes=2_993_292,  # PS + divers gauche allies
        first_round_pct=5.99,
        seats_won=59,
        estimated_alone_seats=35,
    ),
    'EELV': PartyData(
        name="Europe Ecologie Les Verts",
        short_name="EELV",
        first_round_votes=1_625_481,
        first_round_pct=3.26,
        seats_won=33,
        estimated_alone_seats=15,
    ),
    'PCF': PartyData(
        name="Parti Communiste Francais",
        short_name="PCF",
        first_round_votes=1_154_236,
        first_round_pct=2.31,
        seats_won=9,
        estimated_alone_seats=5,
    ),
}

# NFP total results
NFP_TOTAL_SEATS = 182  # Total sieges NFP
NFP_FIRST_ROUND_VOTES = 10_709_917
NFP_FIRST_ROUND_PCT = 21.45

# Key thresholds
ABSOLUTE_MAJORITY = 289  # Majorite absolue a l'Assemblee
TOTAL_SEATS = 577


# ============================================================================
# Coalition Value Functions
# ============================================================================

def get_2024_legislative_data() -> Dict[str, PartyData]:
    """
    Get the official 2024 legislative election data.

    Returns:
        Dictionary mapping party codes to PartyData
    """
    return PARTIES_2024.copy()


def seats_coalition_value(coalition: Set[int], parties: List[str]) -> float:
    """
    Value function based on actual seats won in coalition.

    This models the "power" of a coalition as its number of seats.
    A coalition's value is NOT simply the sum of individual seats
    because desistements (withdrawals) affect second-round outcomes.

    Args:
        coalition: Set of party indices
        parties: List of party codes ['LFI', 'PS', 'EELV', 'PCF']

    Returns:
        Estimated seats for the coalition
    """
    if not coalition:
        return 0.0

    party_codes = [parties[i] for i in coalition]

    # Individual seats (if party runs alone)
    individual_seats = sum(PARTIES_2024[p].estimated_alone_seats for p in party_codes)

    # Coalition bonus from desistements and front republicain
    # This is a simplified model - real values are complex to estimate
    n_parties = len(coalition)

    if n_parties == 1:
        return individual_seats

    elif n_parties == 2:
        # Two-party alliance: moderate synergy
        synergy = 1.15
        return individual_seats * synergy

    elif n_parties == 3:
        # Three-party alliance: good synergy
        synergy = 1.35
        return individual_seats * synergy

    elif n_parties == 4:
        # Full NFP: maximum synergy from unified front
        # Actual NFP got 182 seats vs ~100 estimated individually
        return NFP_TOTAL_SEATS

    return individual_seats


def voting_power_value(coalition: Set[int], parties: List[str]) -> float:
    """
    Value function based on legislative voting power.

    A coalition's value is its probability of being pivotal in votes.
    This depends on the overall composition of the Assembly.

    Simplified model:
    - Value = seats / ABSOLUTE_MAJORITY (capped at 1)
    - Represents "blocking power" potential

    Args:
        coalition: Set of party indices
        parties: List of party codes

    Returns:
        Voting power score (0 to 1)
    """
    if not coalition:
        return 0.0

    seats = seats_coalition_value(coalition, parties)

    # Power is proportional to distance from majority
    # Below majority: linear increase
    # At/above majority: full power (1.0)
    if seats >= ABSOLUTE_MAJORITY:
        return 1.0
    else:
        return seats / ABSOLUTE_MAJORITY


def negotiation_value(coalition: Set[int], parties: List[str]) -> float:
    """
    Value function based on negotiation leverage.

    This models the coalition's ability to negotiate with other blocs.
    A larger, more unified coalition has more leverage.

    Includes:
    - Size effect (more seats = more leverage)
    - Unity effect (fewer parties = more coherent)
    - Ideological coherence penalty for large coalitions

    Args:
        coalition: Set of party indices
        parties: List of party codes

    Returns:
        Negotiation power score
    """
    if not coalition:
        return 0.0

    party_codes = [parties[i] for i in coalition]
    seats = seats_coalition_value(coalition, parties)

    # Base value from seats
    base_value = seats / TOTAL_SEATS

    # Unity bonus/penalty
    n_parties = len(coalition)
    if n_parties == 1:
        unity_factor = 1.0
    elif n_parties == 2:
        # Check ideological distance
        if set(party_codes) == {'LFI', 'PCF'}:
            unity_factor = 0.95  # Close ideologically
        elif set(party_codes) == {'PS', 'EELV'}:
            unity_factor = 0.95  # Close ideologically
        elif 'LFI' in party_codes and 'PS' in party_codes:
            unity_factor = 0.85  # Some tension
        else:
            unity_factor = 0.90
    elif n_parties == 3:
        unity_factor = 0.80  # Harder to coordinate
    else:
        unity_factor = 0.75  # Full coalition has internal tensions

    return base_value * unity_factor * 100  # Scale to 0-100


# ============================================================================
# French Left Coalition Game
# ============================================================================

class FrenchLeftCoalition2024(CoalitionGame):
    """
    Cooperative game model of the French left coalition (NFP) in 2024.

    This game models the formation of the Nouveau Front Populaire,
    analyzing each party's contribution to the coalition.

    Value functions available:
    - 'seats': Based on legislative seats won/estimated
    - 'voting_power': Based on Assembly voting power
    - 'negotiation': Based on negotiation leverage

    Example:
        >>> game = FrenchLeftCoalition2024(value_type='seats')
        >>> shapley = shapley_value_exact(game)
        >>> game.print_analysis(shapley)
    """

    PARTIES = ['LFI', 'PS', 'EELV', 'PCF']

    def __init__(self, value_type: str = 'seats'):
        """
        Initialize the French left coalition game.

        Args:
            value_type: 'seats', 'voting_power', or 'negotiation'
        """
        self.value_type = value_type
        self.party_data = get_2024_legislative_data()

        if value_type == 'seats':
            v_func = lambda S: seats_coalition_value(S, self.PARTIES)
        elif value_type == 'voting_power':
            v_func = lambda S: voting_power_value(S, self.PARTIES)
        elif value_type == 'negotiation':
            v_func = lambda S: negotiation_value(S, self.PARTIES)
        else:
            raise ValueError(f"Unknown value type: {value_type}")

        super().__init__(
            n_players=4,
            characteristic_function=v_func,
            player_names=[self.party_data[p].name for p in self.PARTIES]
        )

    def print_analysis(self, shapley_values: np.ndarray) -> str:
        """
        Print a detailed analysis of Shapley values.

        Args:
            shapley_values: Computed Shapley values

        Returns:
            Formatted analysis string
        """
        lines = [
            "=" * 70,
            "ANALYSE DES COALITIONS - NOUVEAU FRONT POPULAIRE 2024",
            "=" * 70,
            "",
            f"Fonction de valeur: {self.value_type}",
            f"Valeur coalition complete (NFP): {self.grand_coalition_value():.1f}",
            "",
            "RESULTATS LEGISLATIVES 2024 (1er tour, 30 juin):",
            "-" * 50,
        ]

        for code in self.PARTIES:
            p = self.party_data[code]
            lines.append(f"  {p.short_name:5} | {p.first_round_pct:5.2f}% | "
                        f"{p.seats_won:3} sieges")

        lines.extend([
            "",
            "VALEUR DE SHAPLEY (contribution marginale moyenne):",
            "-" * 50,
        ])

        total_shapley = shapley_values.sum()
        for i, code in enumerate(self.PARTIES):
            p = self.party_data[code]
            sv = shapley_values[i]
            pct = (sv / total_shapley * 100) if total_shapley > 0 else 0

            # Compare to perceived weight (first round %)
            perceived = p.first_round_pct
            ratio = sv / (perceived / 100 * total_shapley) if perceived > 0 else 0

            lines.append(f"  {p.short_name:5} | Shapley: {sv:6.1f} ({pct:5.1f}%) | "
                        f"Ratio percu: {ratio:.2f}x")

        lines.extend([
            "",
            "INTERPRETATION:",
            "-" * 50,
        ])

        # Find over/under-valued parties
        for i, code in enumerate(self.PARTIES):
            p = self.party_data[code]
            sv = shapley_values[i]
            pct_shapley = (sv / total_shapley * 100) if total_shapley > 0 else 0
            pct_perceived = p.first_round_pct / sum(
                self.party_data[c].first_round_pct for c in self.PARTIES
            ) * 100

            diff = pct_shapley - pct_perceived
            if abs(diff) > 2:
                direction = "SOUS-ESTIME" if diff > 0 else "SUR-ESTIME"
                lines.append(f"  {p.short_name}: {direction} dans le debat public "
                            f"(ecart: {diff:+.1f} points)")

        lines.extend([
            "",
            "POURQUOI SHAPLEY EST DIFFICILE A APPLIQUER EN POLITIQUE:",
            "-" * 50,
            "  1. Calcul non-intuitif (combinatoire complexe)",
            "  2. Chaque parti surestime sa contribution marginale",
            "  3. Narratif politique vs calcul mathematique",
            "  4. Asymetrie d'information (sondages vs terrain)",
            "  5. Enjeux de leadership (qui sera Premier ministre?)",
            "",
            "=" * 70,
        ])

        return "\n".join(lines)

    def marginal_contributions_table(self) -> str:
        """
        Generate a table of all marginal contributions.

        Shows how each party's contribution varies depending on
        which other parties are already in the coalition.
        """
        lines = [
            "CONTRIBUTIONS MARGINALES PAR COALITION:",
            "-" * 60,
            f"{'Coalition existante':<30} | {'Parti':<8} | {'MC':>10}",
            "-" * 60,
        ]

        for size in range(4):
            from itertools import combinations
            for existing in combinations(range(4), size):
                existing_set = set(existing)
                existing_names = "+".join(self.PARTIES[i] for i in existing) or "Vide"

                for i in range(4):
                    if i not in existing_set:
                        mc = self.marginal_contribution(i, existing_set)
                        lines.append(f"{existing_names:<30} | {self.PARTIES[i]:<8} | {mc:>10.1f}")

        return "\n".join(lines)


def analyze_coalition_dynamics(value_type: str = 'seats') -> Dict:
    """
    Perform a complete analysis of the French left coalition.

    Args:
        value_type: 'seats', 'voting_power', or 'negotiation'

    Returns:
        Dictionary with analysis results
    """
    game = FrenchLeftCoalition2024(value_type=value_type)

    # Compute Shapley values
    shapley = shapley_value_exact(game)

    # Check if Core is non-empty
    from .core import compute_core, is_in_core
    core_exists, core_point = compute_core(game, objective='equal')

    # Check convexity
    is_convex = game.is_convex()

    results = {
        "game": game,
        "shapley_values": shapley,
        "shapley_dict": {game.PARTIES[i]: shapley[i] for i in range(4)},
        "grand_coalition_value": game.grand_coalition_value(),
        "core_exists": core_exists,
        "core_point": core_point,
        "is_convex": is_convex,
        "analysis_text": game.print_analysis(shapley),
        "marginal_table": game.marginal_contributions_table(),
    }

    return results


# ============================================================================
# Additional Analysis Functions
# ============================================================================

def compare_value_functions() -> str:
    """
    Compare Shapley values across different value functions.

    Returns:
        Formatted comparison table
    """
    lines = [
        "COMPARAISON DES FONCTIONS DE VALEUR:",
        "=" * 70,
        "",
        f"{'Parti':<8} | {'Sieges':>12} | {'Pouvoir vote':>12} | {'Negociation':>12}",
        "-" * 70,
    ]

    shapley_by_type = {}
    for vtype in ['seats', 'voting_power', 'negotiation']:
        game = FrenchLeftCoalition2024(value_type=vtype)
        shapley_by_type[vtype] = shapley_value_exact(game)

    for i, code in enumerate(FrenchLeftCoalition2024.PARTIES):
        lines.append(
            f"{code:<8} | "
            f"{shapley_by_type['seats'][i]:>12.1f} | "
            f"{shapley_by_type['voting_power'][i]:>12.3f} | "
            f"{shapley_by_type['negotiation'][i]:>12.1f}"
        )

    lines.extend([
        "-" * 70,
        "",
        "Interpretation:",
        "  - 'Sieges': Contribution aux sieges de l'Assemblee",
        "  - 'Pouvoir vote': Probabilite d'etre pivot dans les votes",
        "  - 'Negociation': Levier dans les negociations inter-blocs",
    ])

    return "\n".join(lines)


def scenario_analysis() -> str:
    """
    Analyze different coalition scenarios.

    What if certain parties didn't join?
    """
    game = FrenchLeftCoalition2024(value_type='seats')

    lines = [
        "ANALYSE DE SCENARIOS - ET SI...?",
        "=" * 70,
        "",
    ]

    scenarios = [
        ("Sans LFI", {1, 2, 3}),
        ("Sans PS", {0, 2, 3}),
        ("Sans EELV", {0, 1, 3}),
        ("Sans PCF", {0, 1, 2}),
        ("LFI + PCF seulement", {0, 3}),
        ("PS + EELV seulement", {1, 2}),
        ("NFP complet", {0, 1, 2, 3}),
    ]

    for name, coalition in scenarios:
        value = game.value(coalition)
        parties = "+".join(game.PARTIES[i] for i in sorted(coalition))
        lines.append(f"{name:<25} ({parties}): {value:.0f} sieges estimes")

    lines.extend([
        "",
        "Note: Ces estimations sont des modeles simplifies.",
        "Les vraies valeurs dependent de nombreux facteurs locaux.",
    ])

    return "\n".join(lines)


def create_voting_game_assembly() -> Tuple[WeightedVotingGame, np.ndarray]:
    """
    Create a weighted voting game for Assembly votes.

    Models the NFP as a single bloc voting against other blocs.
    Returns the game and Banzhaf indices.
    """
    # Simplified Assembly composition (July 2024)
    blocs = {
        'NFP': 182,           # Nouveau Front Populaire
        'Ensemble': 168,      # Macron's coalition (Renaissance + MoDem + Horizons)
        'LR': 45,             # Les Republicains
        'RN': 143,            # Rassemblement National + allies
        'Autres': 39,         # Divers
    }

    weights = list(blocs.values())
    names = list(blocs.keys())

    # Quota = absolute majority
    game = WeightedVotingGame(weights, quota=ABSOLUTE_MAJORITY, player_names=names)

    return game, game.banzhaf_index()
