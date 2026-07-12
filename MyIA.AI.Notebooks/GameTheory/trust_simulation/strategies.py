# -*- coding: utf-8 -*-
"""
Strategies for Iterated Prisoner's Dilemma
==========================================

Implementation of classic IPD strategies from Axelrod's tournaments.
Inspired by Nicky Case's "Evolution of Trust" (https://ncase.me/trust/)

Strategies implemented:
- AlwaysCooperate (Dove): Always cooperates
- AlwaysDefect (Hawk): Always defects
- TitForTat (Copycat): Cooperates first, then copies opponent's last move
- Copykitten (TitForTwoTats): Defects only after two consecutive defections
- Grudger (GrimTrigger): Cooperates until betrayed, then always defects
- Random: Randomly cooperates or defects
- Pavlov (Win-Stay-Lose-Shift): Repeats last action if rewarded, switches otherwise
- TitForTwoTats: More forgiving version, requires two defections to retaliate
"""

from abc import ABC, abstractmethod
from typing import List, Literal, Optional
import random

# Action types (consistent with GameTheory-6-EvolutionTrust.ipynb)
Action = Literal["C", "D"]  # Cooperate or Defect

# Constants for compatibility with notebook 6
COOPERATE = "C"
DEFECT = "D"
C = COOPERATE
D = DEFECT


class Strategy(ABC):
    """Base class for IPD strategies."""

    name: str = "Strategy"
    description: str = "Base strategy class"

    def __init__(self):
        self.reset()

    def reset(self):
        """Reset strategy state for a new game."""
        self.my_history: List[Action] = []
        self.opponent_history: List[Action] = []

    @abstractmethod
    def choose(self) -> Action:
        """Choose an action based on the game history."""
        pass

    def record(self, my_action: Action, opponent_action: Action):
        """Record the actions taken this round."""
        self.my_history.append(my_action)
        self.opponent_history.append(opponent_action)

    def __repr__(self):
        return f"{self.name}"


class AlwaysCooperate(Strategy):
    """Always cooperates. Also known as 'Dove' or 'Sucker'."""

    name = "AlwaysCooperate"
    description = "Always cooperates, no matter what"

    def choose(self) -> Action:
        return "C"


class AlwaysDefect(Strategy):
    """Always defects. Also known as 'Hawk' or 'Cheater'."""

    name = "AlwaysDefect"
    description = "Always defects, no matter what"

    def choose(self) -> Action:
        return "D"


class TitForTat(Strategy):
    """
    Cooperates on first move, then copies opponent's last move.

    This is Anatol Rapoport's famous strategy that won Axelrod's first tournament.
    Also known as 'Copycat' in Nicky Case's "Evolution of Trust".

    Properties:
    - Nice: Never defects first
    - Retaliatory: Punishes defection immediately
    - Forgiving: Returns to cooperation after one retaliation
    - Clear: Easy to understand and predict
    """

    name = "TitForTat"
    description = "Cooperates first, then copies opponent's last move"

    def choose(self) -> Action:
        if not self.opponent_history:
            return "C"  # Cooperate on first move
        return self.opponent_history[-1]  # Copy opponent's last move


class Copykitten(Strategy):
    """
    Only defects after two consecutive defections from opponent.

    Also known as 'TitForTwoTats'. More forgiving than TitForTat,
    which helps in noisy environments.

    From "Evolution of Trust": "I'll start cooperating, and
    only betray if you betray me twice in a row."
    """

    name = "Copykitten"
    description = "Defects only after opponent defects twice in a row"

    def choose(self) -> Action:
        if len(self.opponent_history) < 2:
            return "C"
        # Defect only if opponent defected twice in a row
        if self.opponent_history[-1] == "D" and self.opponent_history[-2] == "D":
            return "D"
        return "C"


class TitForTwoTats(Copykitten):
    """Alias for Copykitten - defects after two consecutive betrayals."""
    name = "TitForTwoTats"


class Grudger(Strategy):
    """
    Cooperates until betrayed once, then always defects.

    Also known as 'Grim Trigger' or 'Spiteful'. Once the opponent
    defects, Grudger remembers forever and never cooperates again.

    From "Evolution of Trust": "I'll cooperate, until you betray me once.
    Then I'll defect forever."
    """

    name = "Grudger"
    description = "Cooperates until betrayed, then always defects"

    def __init__(self):
        super().__init__()
        self.grudge = False

    def reset(self):
        super().reset()
        self.grudge = False

    def choose(self) -> Action:
        if self.grudge:
            return "D"
        if self.opponent_history and self.opponent_history[-1] == "D":
            self.grudge = True
            return "D"
        return "C"


class Random(Strategy):
    """
    Randomly cooperates or defects with equal probability.

    This strategy is unpredictable and serves as a baseline.
    """

    name = "Random"
    description = "Randomly cooperates or defects (50/50)"

    def __init__(self, p_cooperate: float = 0.5):
        super().__init__()
        self.p_cooperate = p_cooperate

    def choose(self) -> Action:
        return "C" if random.random() < self.p_cooperate else "D"


class Pavlov(Strategy):
    """
    Win-Stay, Lose-Shift strategy.

    Cooperates on first move. Then:
    - If the last round was 'good' (CC or DC), repeat the last action
    - If the last round was 'bad' (CD or DD), switch action

    A 'good' outcome means getting the cooperation or temptation payoff (3 or 5).
    A 'bad' outcome means getting the sucker or punishment payoff (0 or 1).
    """

    name = "Pavlov"
    description = "Win-Stay, Lose-Shift: repeats action if rewarded, switches if punished"

    def choose(self) -> Action:
        if not self.my_history:
            return "C"

        # Check if last round was 'good' (both same action = mutual outcome)
        my_last = self.my_history[-1]
        opp_last = self.opponent_history[-1]

        # Good: CC (3,3) or DC (5,0) - I got 3 or 5
        # Bad: CD (0,5) or DD (1,1) - I got 0 or 1
        if my_last == opp_last:  # CC or DD
            if my_last == "C":  # CC is good (3), repeat
                return "C"
            else:  # DD is bad (1), switch
                return "C"
        else:  # CD or DC
            if my_last == "D":  # DC is good (5), repeat
                return "D"
            else:  # CD is bad (0), switch
                return "D"


class Detective(Strategy):
    """
    Probes the opponent then adapts.

    Plays C, D, C, C in the first four rounds to test the opponent:
    - If opponent ever retaliates, plays TitForTat
    - If opponent never retaliates, exploits with AlwaysDefect

    From "Evolution of Trust": "First, I'll test you with C, D, C, C.
    If you ever retaliate, I'll play Copycat. If you never retaliate,
    I'll exploit you."
    """

    name = "Detective"
    description = "Tests opponent, then adapts: TitForTat or exploit"

    def __init__(self):
        super().__init__()
        self.probe_sequence = ["C", "D", "C", "C"]
        self.retaliated = False

    def reset(self):
        super().reset()
        self.retaliated = False

    def choose(self) -> Action:
        round_num = len(self.my_history)

        # Probing phase (first 4 rounds)
        if round_num < 4:
            return self.probe_sequence[round_num]

        # Check if opponent retaliated during probe
        if round_num == 4:
            self.retaliated = "D" in self.opponent_history[:4]

        # Exploitation or TitForTat
        if self.retaliated:
            # Play TitForTat
            return self.opponent_history[-1]
        else:
            # Exploit the sucker
            return "D"


# Standard payoff matrix for Prisoner's Dilemma
# (row_payoff, col_payoff) for (row_action, col_action)
STANDARD_PAYOFFS = {
    ("C", "C"): (3, 3),  # Reward for mutual cooperation
    ("C", "D"): (0, 5),  # Sucker's payoff vs Temptation
    ("D", "C"): (5, 0),  # Temptation vs Sucker's payoff
    ("D", "D"): (1, 1),  # Punishment for mutual defection
}


def play_round(
    strategy1: Strategy,
    strategy2: Strategy,
    payoffs: dict = None
) -> tuple:
    """
    Play one round of the Prisoner's Dilemma.

    Returns:
        Tuple of (action1, action2, payoff1, payoff2)
    """
    if payoffs is None:
        payoffs = STANDARD_PAYOFFS

    action1 = strategy1.choose()
    action2 = strategy2.choose()

    p1, p2 = payoffs[(action1, action2)]

    strategy1.record(action1, action2)
    strategy2.record(action2, action1)

    return action1, action2, p1, p2


def play_match(
    strategy1: Strategy,
    strategy2: Strategy,
    rounds: int = 200,
    payoffs: dict = None
) -> dict:
    """
    Play a full match of iterated Prisoner's Dilemma.

    Args:
        strategy1: First player's strategy
        strategy2: Second player's strategy
        rounds: Number of rounds to play
        payoffs: Custom payoff matrix (optional)

    Returns:
        Dictionary with match results including total scores
    """
    strategy1.reset()
    strategy2.reset()

    history = []
    total1, total2 = 0, 0

    for _ in range(rounds):
        a1, a2, p1, p2 = play_round(strategy1, strategy2, payoffs)
        history.append((a1, a2, p1, p2))
        total1 += p1
        total2 += p2

    return {
        "strategy1": strategy1.name,
        "strategy2": strategy2.name,
        "rounds": rounds,
        "score1": total1,
        "score2": total2,
        "avg1": total1 / rounds,
        "avg2": total2 / rounds,
        "history": history,
    }


# List of all available strategies
ALL_STRATEGIES = [
    AlwaysCooperate,
    AlwaysDefect,
    TitForTat,
    Copykitten,
    Grudger,
    Random,
    Pavlov,
    Detective,
]
