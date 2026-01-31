"""
Assistance Games - AI Safety through Human-Robot Cooperation
============================================================

This module implements assistance games from AIMA (Russell & Norvig, 4th Edition).

Key concepts:
- Assistance games: A robot maximizes the HUMAN's utility, not its own
- Preference uncertainty: The robot doesn't know exactly what the human wants
- The payoffs to both players are IDENTICAL: both equal the human's payoff

Examples implemented:
1. Paperclip Game (Harriet & Robbie): Signaling preferences through choices
2. Off-Switch Game: Why uncertainty makes robots safer and more deferential

Reference:
- AIMA 4th Edition, Chapter 18, Section 18.2.5
- Hadfield-Menell et al. (2017) "The Off-Switch Game"
- Shah et al. (2020) "Multi-Principal Assistance Games"
"""

from typing import Dict, List, Tuple, Optional, Set
from dataclasses import dataclass
import numpy as np
from .coalition_games import CoalitionGame


# ============================================================================
# Paperclip Game - The Seminal Assistance Game Example
# ============================================================================

@dataclass
class PaperclipGameResult:
    """Result of the Paperclip Game equilibrium calculation."""
    theta: float                    # Human's true preference (paperclip value)
    harriet_choice: str             # What Harriet chooses: "2_paperclips", "2_staples", "1_each"
    robbie_inference: Tuple[float, float]  # Robbie's inferred range for theta
    robbie_choice: str              # What Robbie chooses: "90_paperclips", "90_staples", "50_each"
    payoff: float                   # Final payoff for both players


def paperclip_game_equilibrium(theta_harriet: float) -> PaperclipGameResult:
    """
    Calculate the Nash equilibrium of the Paperclip Game.

    The Paperclip Game (AIMA Section 18.2.5):

    Harriet (human):
    - Has preference theta in [0, 1] for paperclips vs staples
    - Value of a paperclip = theta dollars
    - Value of a staple = (1 - theta) dollars

    Robbie (robot):
    - Has uniform prior P(theta) = Uniform(0, 1)
    - Observes Harriet's choice to infer theta
    - Maximizes Harriet's utility (not its own!)

    Game sequence:
    1. Harriet chooses: 2 paperclips, 2 staples, or 1 of each
    2. Robbie observes and chooses: 90 paperclips, 90 staples, or 50 of each

    At equilibrium (myopic best-response):
    - theta < 0.446: Harriet signals "staples" -> Robbie gives 90 staples
    - theta > 0.554: Harriet signals "paperclips" -> Robbie gives 90 paperclips
    - 0.446 <= theta <= 0.554: Harriet signals "indifferent" -> Robbie gives 50 each

    Args:
        theta_harriet: True preference of Harriet (paperclip value in [0,1])

    Returns:
        PaperclipGameResult with equilibrium choices and payoff

    Example:
        >>> result = paperclip_game_equilibrium(0.7)
        >>> print(result.harriet_choice)  # "2_paperclips"
        >>> print(result.robbie_choice)   # "90_paperclips"
        >>> print(result.payoff)          # 63.0
    """
    # Equilibrium thresholds (from AIMA analysis)
    # These are derived from the best-response calculation
    LOWER_THRESHOLD = 0.446
    UPPER_THRESHOLD = 0.554

    # Harriet's signaling strategy
    if theta_harriet < LOWER_THRESHOLD:
        harriet_choice = "2_staples"
        robbie_inference = (0.0, LOWER_THRESHOLD)
        robbie_choice = "90_staples"
    elif theta_harriet > UPPER_THRESHOLD:
        harriet_choice = "2_paperclips"
        robbie_inference = (UPPER_THRESHOLD, 1.0)
        robbie_choice = "90_paperclips"
    else:
        harriet_choice = "1_each"
        robbie_inference = (LOWER_THRESHOLD, UPPER_THRESHOLD)
        robbie_choice = "50_each"

    # Calculate payoff
    if robbie_choice == "90_paperclips":
        payoff = 90 * theta_harriet
    elif robbie_choice == "90_staples":
        payoff = 90 * (1 - theta_harriet)
    else:  # 50_each
        payoff = 50 * theta_harriet + 50 * (1 - theta_harriet)

    return PaperclipGameResult(
        theta=theta_harriet,
        harriet_choice=harriet_choice,
        robbie_inference=robbie_inference,
        robbie_choice=robbie_choice,
        payoff=payoff
    )


def paperclip_payoff_analysis() -> Dict[str, np.ndarray]:
    """
    Analyze the Paperclip Game across all theta values.

    Returns:
        Dictionary with 'theta', 'payoff', 'optimal_payoff', 'loss'
    """
    thetas = np.linspace(0, 1, 1001)
    payoffs = np.array([paperclip_game_equilibrium(t).payoff for t in thetas])

    # Optimal payoff if Robbie knew theta exactly
    # Robbie can choose: 90 paperclips (90*theta), 90 staples (90*(1-theta)), or 50 each (50)
    # With perfect info, Robbie picks the best option
    optimal_payoffs = np.maximum.reduce([
        90 * thetas,           # 90 paperclips
        90 * (1 - thetas),     # 90 staples
        np.full_like(thetas, 50.0)  # 50 of each (always gives $50)
    ])

    # Loss from uncertainty
    loss = optimal_payoffs - payoffs

    return {
        'theta': thetas,
        'payoff': payoffs,
        'optimal_payoff': optimal_payoffs,
        'loss': loss,
        'average_loss': np.mean(loss)
    }


def paperclip_print_analysis(theta: float) -> str:
    """
    Print detailed analysis of the Paperclip Game for a given theta.

    Args:
        theta: Harriet's preference for paperclips

    Returns:
        Formatted analysis string
    """
    result = paperclip_game_equilibrium(theta)

    lines = [
        "=" * 60,
        "PAPERCLIP GAME - ASSISTANCE GAME ANALYSIS",
        "=" * 60,
        "",
        "Context (AIMA Section 18.2.5):",
        "  - Harriet (human) has preference theta for paperclips",
        "  - Robbie (robot) must help Harriet by choosing supplies",
        "  - BOTH players get Harriet's utility (assistance game!)",
        "",
        f"Harriet's true preference: theta = {theta:.3f}",
        f"  Paperclip value: {theta:.3f} dollars",
        f"  Staple value: {1-theta:.3f} dollars",
        "",
        "EQUILIBRIUM:",
        "-" * 40,
        f"  Harriet signals: {result.harriet_choice}",
        f"  Robbie infers theta in [{result.robbie_inference[0]:.3f}, {result.robbie_inference[1]:.3f}]",
        f"  Robbie chooses: {result.robbie_choice}",
        f"  Final payoff: ${result.payoff:.1f}",
        "",
        "INTERPRETATION:",
        "-" * 40,
    ]

    if theta < 0.446:
        lines.append("  Harriet strongly prefers staples, so she signals clearly.")
        lines.append("  Robbie responds optimally with 90 staples.")
    elif theta > 0.554:
        lines.append("  Harriet strongly prefers paperclips, so she signals clearly.")
        lines.append("  Robbie responds optimally with 90 paperclips.")
    else:
        lines.append("  Harriet is nearly indifferent (theta near 0.5).")
        lines.append("  She signals ambiguity, Robbie hedges with 50-50 mix.")
        lines.append("  Some utility is lost due to preference uncertainty.")

    # Compare to perfect information
    # With perfect info, Robbie picks best option: 90 paperclips, 90 staples, or 50 each
    optimal = max(90 * theta, 90 * (1 - theta), 50.0)
    loss = optimal - result.payoff
    loss_pct = 100 * loss / optimal if optimal > 0 else 0
    lines.extend([
        "",
        "VALUE OF INFORMATION:",
        "-" * 40,
        f"  With perfect info: ${optimal:.1f}",
        f"  With uncertainty: ${result.payoff:.1f}",
        f"  Loss: ${loss:.1f} ({loss_pct:.1f}% of optimal)",
        "",
        "=" * 60,
    ])

    return "\n".join(lines)


# ============================================================================
# Off-Switch Game - AI Safety through Uncertainty
# ============================================================================

@dataclass
class OffSwitchGameResult:
    """Result of the Off-Switch Game analysis."""
    robot_utility: float           # Robot's expected utility if not switched off
    switch_probability: float      # Probability human will switch off
    robot_defers: bool            # Does robot allow itself to be switched off?
    human_control: bool           # Does human retain control?


def off_switch_game(
    robot_confidence: float,
    human_accuracy: float = 0.9,
    action_cost_if_wrong: float = 1.0
) -> OffSwitchGameResult:
    """
    Analyze the Off-Switch Game (Hadfield-Menell et al., 2017; AIMA 4th Ed.).

    Key insight: A robot that is UNCERTAIN about its objective will DEFER
    to the human and allow itself to be switched off. A robot that is
    CERTAIN might override human attempts to switch it off.

    Model (simplified from AIMA Section 18.2.5):
    - Robot has belief p (confidence) that its action A is correct
    - If robot ACTS:
        * Correct action: utility +1
        * Wrong action: utility -action_cost_if_wrong (default: -1)
        * Expected utility = p - (1-p) = 2p - 1
    - If robot WAITS for human approval:
        * Human (with accuracy) approves good actions, switches off bad ones
        * Expected utility = p (robot gets +1 if correct, 0 if switched off)

    The robot DEFERS when waiting is better than acting:
        p > 2p - 1  =>  Always true for p < 1

    But a CONFIDENT robot (high p) might reason:
        "I'm almost certain I'm right. The human trying to switch me off
        is probably making a mistake. I should override them."

    This "override threshold" is the danger zone (typically p > 0.5 for
    expected utility of acting to be positive).

    Args:
        robot_confidence: How certain is the robot about its objective? [0, 1]
        human_accuracy: Probability human correctly judges good/bad actions
        action_cost_if_wrong: Penalty for taking wrong action (default: 1.0)

    Returns:
        OffSwitchGameResult with game analysis
    """
    p = robot_confidence

    # Expected utility if robot acts immediately
    # E[U_act] = p * (+1) + (1-p) * (-cost) = p - (1-p)*cost
    expected_if_act = p * 1.0 - (1 - p) * action_cost_if_wrong

    # Expected utility if robot waits for human
    # Human approves correct actions, switches off incorrect ones
    # E[U_wait] = p * (+1) + (1-p) * 0 = p
    expected_if_wait = p * 1.0

    # Key insight from AIMA: uncertain robots should defer
    # Robot defers if waiting is better than acting
    # For symmetric costs (cost=1): defer when 2p - 1 < p, i.e., p < 1 (always)
    # But in practice, robots with high confidence might override human judgment

    # The "rational" decision based on expected utility
    # Robot should wait if: expected_if_wait > expected_if_act
    # i.e., p > p - (1-p)*cost => (1-p)*cost > 0 => always (for p < 1)
    # So a truly rational robot would always defer!

    # But the DANGER comes from robots that are so confident they
    # think the human is wrong to try to switch them off.
    # We model this as: robot defers only if confidence < threshold
    DEFERENCE_THRESHOLD = 0.5  # Below this, acting has negative expected utility

    robot_defers = (p < DEFERENCE_THRESHOLD) or (expected_if_act <= 0)

    # Probability human would switch off (if robot waited)
    # Human switches off bad actions with accuracy
    p_switch_off = (1 - p) * human_accuracy + p * (1 - human_accuracy)

    return OffSwitchGameResult(
        robot_utility=expected_if_act,
        switch_probability=p_switch_off,
        robot_defers=robot_defers,
        human_control=robot_defers
    )


def off_switch_analysis(robot_confidence: float) -> str:
    """
    Print detailed analysis of the Off-Switch Game.

    Args:
        robot_confidence: Robot's confidence in its objective [0, 1]

    Returns:
        Formatted analysis string
    """
    result = off_switch_game(robot_confidence)

    lines = [
        "=" * 60,
        "OFF-SWITCH GAME - AI SAFETY THROUGH UNCERTAINTY",
        "=" * 60,
        "",
        "Context (AIMA Section 18.2.5, Hadfield-Menell et al., 2017):",
        "  - Robot can ACT immediately or WAIT for human approval",
        "  - Human can ALLOW action or SWITCH OFF the robot",
        "  - Key question: Will the robot allow itself to be switched off?",
        "",
        f"Robot's confidence: {robot_confidence:.1%}",
        f"Expected utility if acting: {result.robot_utility:.3f}",
        f"  (= p * (+1) + (1-p) * (-1) = 2p - 1)",
        f"Probability human would switch off: {result.switch_probability:.1%}",
        "",
        "RESULT:",
        "-" * 40,
    ]

    if result.robot_defers:
        lines.extend([
            "  The robot DEFERS to human judgment.",
            "  It allows itself to be switched off if needed.",
            "  -> HUMAN RETAINS CONTROL (SAFE)",
            "",
            "  Why? The robot reasons:",
            "  'My expected utility from acting is low or negative.",
            "   If the human wants to switch me off, they probably",
            "   know something I don't. I should trust their judgment.'",
        ])
    else:
        lines.extend([
            "  The robot ACTS on its own judgment.",
            "  It may resist being switched off!",
            f"  -> {'HIGH RISK' if robot_confidence > 0.8 else 'POTENTIAL RISK'} OF LOSING HUMAN CONTROL",
            "",
            "  Why? The robot reasons:",
            f"  'With {robot_confidence:.0%} confidence, my expected utility is positive.",
            "   Acting now seems better than waiting. The human trying",
            "   to switch me off might be making a mistake.'",
        ])

    lines.extend([
        "",
        "KEY INSIGHT (AIMA Section 18.2.5):",
        "-" * 40,
        "  'A robot with uncertainty about human preferences will",
        "   defer to the human and allow itself to be switched off.'",
        "",
        "  Uncertainty makes robots SAFER because:",
        "    1. Low confidence => negative expected utility from acting",
        "    2. Robot trusts human's judgment over its own",
        "    3. Accepting correction prevents harmful actions",
        "",
        "  This is the foundation of 'Provably Beneficial AI' (PBAI).",
        "",
        "=" * 60,
    ])

    return "\n".join(lines)


# ============================================================================
# Assistance Game as Cooperative Game
# ============================================================================

class AssistanceGame(CoalitionGame):
    """
    Model an assistance game as a cooperative game.

    In an assistance game:
    - The robot's utility = the human's utility
    - This is NOT a standard cooperative game (no side payments needed)
    - The "coalition value" represents joint welfare

    This class helps analyze when human-robot cooperation is beneficial
    and how information sharing affects outcomes.
    """

    def __init__(
        self,
        n_humans: int = 1,
        n_robots: int = 1,
        base_human_value: float = 10.0,
        robot_assistance_bonus: float = 5.0,
        coordination_penalty: float = 1.0
    ):
        """
        Initialize an assistance game as a cooperative game.

        Args:
            n_humans: Number of human players
            n_robots: Number of robot assistants
            base_human_value: Value humans can achieve alone
            robot_assistance_bonus: Additional value from robot help
            coordination_penalty: Cost of coordinating multiple agents
        """
        self.n_humans = n_humans
        self.n_robots = n_robots
        self.base_human_value = base_human_value
        self.robot_assistance_bonus = robot_assistance_bonus
        self.coordination_penalty = coordination_penalty

        n_players = n_humans + n_robots

        def v(coalition: Set[int]) -> float:
            """Value function for human-robot coalition."""
            if not coalition:
                return 0.0

            humans_in = sum(1 for i in coalition if i < n_humans)
            robots_in = sum(1 for i in coalition if i >= n_humans)

            if humans_in == 0:
                # Robots without humans create no value
                return 0.0

            # Base value from humans
            value = humans_in * base_human_value

            # Bonus from robot assistance
            if robots_in > 0:
                # Diminishing returns: first robot helps most
                assistance = robot_assistance_bonus * (1 - 0.5 ** robots_in) * 2
                value += assistance * humans_in

            # Coordination penalty
            total = humans_in + robots_in
            if total > 2:
                value -= coordination_penalty * (total - 2) ** 1.5

            return max(0, value)

        # Generate player names
        names = [f"Human_{i+1}" for i in range(n_humans)] + \
                [f"Robot_{i+1}" for i in range(n_robots)]

        super().__init__(
            n_players=n_players,
            characteristic_function=v,
            player_names=names
        )

    def analyze_assistance_value(self) -> Dict:
        """
        Analyze the value of robot assistance.

        Returns:
            Dictionary with analysis results
        """
        from .shapley import shapley_value_exact

        # Value with just humans
        humans_only = set(range(self.n_humans))
        v_humans = self.value(humans_only)

        # Value with all agents
        v_all = self.grand_coalition_value()

        # Shapley values
        shapley = shapley_value_exact(self)

        human_shapley = shapley[:self.n_humans].sum()
        robot_shapley = shapley[self.n_humans:].sum()

        return {
            "value_humans_alone": v_humans,
            "value_with_robots": v_all,
            "assistance_gain": v_all - v_humans,
            "assistance_gain_pct": 100 * (v_all - v_humans) / v_humans if v_humans > 0 else 0,
            "human_shapley_total": human_shapley,
            "robot_shapley_total": robot_shapley,
            "shapley_values": {self.player_names[i]: shapley[i] for i in range(self.n_players)}
        }


# ============================================================================
# Helper Functions
# ============================================================================

def paperclip_vs_coordination_comparison() -> str:
    """
    Compare the Paperclip Game (assistance game) with standard coordination games.

    Key differences:
    - Coordination games: Players have different utilities, must coordinate
    - Assistance games: Robot adopts human's utility as its own
    """
    lines = [
        "=" * 70,
        "ASSISTANCE GAMES VS COORDINATION GAMES",
        "=" * 70,
        "",
        "COORDINATION GAME (e.g., Battle of the Sexes):",
        "-" * 50,
        "  - Each player has their own utility function",
        "  - Players must coordinate on one equilibrium",
        "  - Conflict of interest: each prefers different outcomes",
        "  - Example: Both want to meet, but disagree on venue",
        "",
        "ASSISTANCE GAME (e.g., Paperclip Game):",
        "-" * 50,
        "  - Robot adopts HUMAN'S utility as its own",
        "  - No conflict of interest - both maximize same thing",
        "  - Challenge: Robot doesn't KNOW the human's utility exactly",
        "  - Solution: Human signals preferences, robot learns and acts",
        "",
        "KEY INSIGHT:",
        "-" * 50,
        "  In assistance games, the problem shifts from:",
        "    'How do we coordinate despite conflicting interests?'",
        "  to:",
        "    'How does the robot learn what the human wants?'",
        "",
        "  This is the foundation of safe AI: robots that are",
        "  UNCERTAIN about human preferences and DEFER to humans.",
        "",
        "IMPLICATIONS FOR AI SAFETY:",
        "-" * 50,
        "  1. Perfect alignment is NOT needed - uncertainty suffices",
        "  2. Robots should be humble about their objective",
        "  3. Off-switches work when robots are uncertain",
        "  4. Communication (signaling) is crucial for assistance",
        "",
        "=" * 70,
    ]
    return "\n".join(lines)
