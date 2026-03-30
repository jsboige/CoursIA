# -*- coding: utf-8 -*-
"""
Visualization Tools for Trust Simulation
=========================================

Plotting and animation functions for IPD tournaments and population dynamics.
"""

from typing import List, Dict, Optional
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.animation import FuncAnimation
import os

# Check if running in batch mode (no display)
BATCH_MODE = os.environ.get("BATCH_MODE", "").lower() in ("true", "1", "yes")


def plot_tournament_results(
    results,
    title: str = "Tournament Results",
    figsize: tuple = (10, 6),
    save_path: str = None
):
    """
    Plot tournament results as a bar chart.

    Args:
        results: TournamentResults object
        title: Plot title
        figsize: Figure size
        save_path: Optional path to save figure
    """
    fig, ax = plt.subplots(figsize=figsize)

    names = [r[0] for r in results.rankings]
    scores = [r[1] for r in results.rankings]

    colors = plt.cm.viridis(np.linspace(0.2, 0.8, len(names)))

    bars = ax.barh(range(len(names)), scores, color=colors)
    ax.set_yticks(range(len(names)))
    ax.set_yticklabels(names)
    ax.invert_yaxis()  # Best at top
    ax.set_xlabel("Total Score")
    ax.set_title(title)

    # Add score labels
    for i, (bar, score) in enumerate(zip(bars, scores)):
        ax.text(score + 10, i, f"{score:.0f}", va="center")

    plt.tight_layout()

    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches="tight")

    if not BATCH_MODE:
        plt.show()
    plt.close()


def plot_population_dynamics(
    history: List[Dict[str, int]],
    title: str = "Population Dynamics",
    figsize: tuple = (12, 6),
    save_path: str = None
):
    """
    Plot population changes over generations.

    Args:
        history: List of population dictionaries per generation
        title: Plot title
        figsize: Figure size
        save_path: Optional path to save figure
    """
    if not history:
        return

    strategies = list(history[0].keys())
    generations = len(history)

    fig, ax = plt.subplots(figsize=figsize)

    for strategy in strategies:
        pops = [h.get(strategy, 0) for h in history]
        ax.plot(range(generations), pops, label=strategy, linewidth=2)

    ax.set_xlabel("Generation")
    ax.set_ylabel("Population")
    ax.set_title(title)
    ax.legend(loc="upper right")
    ax.grid(True, alpha=0.3)

    plt.tight_layout()

    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches="tight")

    if not BATCH_MODE:
        plt.show()
    plt.close()


def plot_replicator_dynamics(
    history: np.ndarray,
    strategy_names: List[str],
    title: str = "Replicator Dynamics",
    figsize: tuple = (12, 6),
    save_path: str = None
):
    """
    Plot replicator dynamics trajectories.

    Args:
        history: Array of shape (timesteps, n_strategies)
        strategy_names: Names of strategies
        title: Plot title
        figsize: Figure size
        save_path: Optional path to save figure
    """
    fig, ax = plt.subplots(figsize=figsize)

    timesteps = history.shape[0]

    for i, name in enumerate(strategy_names):
        ax.plot(range(timesteps), history[:, i], label=name, linewidth=2)

    ax.set_xlabel("Time")
    ax.set_ylabel("Population Proportion")
    ax.set_title(title)
    ax.legend(loc="upper right")
    ax.grid(True, alpha=0.3)
    ax.set_ylim(0, 1)

    plt.tight_layout()

    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches="tight")

    if not BATCH_MODE:
        plt.show()
    plt.close()


def plot_match_history(
    history: List[tuple],
    player1_name: str = "Player 1",
    player2_name: str = "Player 2",
    figsize: tuple = (14, 4),
    save_path: str = None
):
    """
    Visualize the action history of a single match.

    Args:
        history: List of (action1, action2, payoff1, payoff2) tuples
        player1_name: Name of first player
        player2_name: Name of second player
        figsize: Figure size
        save_path: Optional path to save figure
    """
    fig, (ax1, ax2) = plt.subplots(2, 1, figsize=figsize, sharex=True)

    rounds = len(history)
    actions1 = [1 if h[0] == "C" else 0 for h in history]
    actions2 = [1 if h[1] == "C" else 0 for h in history]

    # Plot actions as step functions
    ax1.step(range(rounds), actions1, where="mid", linewidth=1.5, color="blue")
    ax1.fill_between(range(rounds), actions1, step="mid", alpha=0.3, color="blue")
    ax1.set_ylabel(player1_name)
    ax1.set_yticks([0, 1])
    ax1.set_yticklabels(["Defect", "Cooperate"])
    ax1.set_ylim(-0.1, 1.1)

    ax2.step(range(rounds), actions2, where="mid", linewidth=1.5, color="orange")
    ax2.fill_between(range(rounds), actions2, step="mid", alpha=0.3, color="orange")
    ax2.set_ylabel(player2_name)
    ax2.set_yticks([0, 1])
    ax2.set_yticklabels(["Defect", "Cooperate"])
    ax2.set_ylim(-0.1, 1.1)
    ax2.set_xlabel("Round")

    # Calculate cumulative scores
    cum_score1 = np.cumsum([h[2] for h in history])
    cum_score2 = np.cumsum([h[3] for h in history])

    fig.suptitle(f"Match: {player1_name} vs {player2_name}\n"
                 f"Final: {cum_score1[-1]:.0f} - {cum_score2[-1]:.0f}")

    plt.tight_layout()

    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches="tight")

    if not BATCH_MODE:
        plt.show()
    plt.close()


def animate_replicator_dynamics(
    history: np.ndarray,
    strategy_names: List[str],
    interval: int = 100,
    save_path: str = None
) -> Optional[FuncAnimation]:
    """
    Create an animation of replicator dynamics.

    Args:
        history: Array of shape (timesteps, n_strategies)
        strategy_names: Names of strategies
        interval: Milliseconds between frames
        save_path: Optional path to save as GIF

    Returns:
        FuncAnimation object (or None in batch mode)
    """
    if BATCH_MODE:
        # In batch mode, just save the final frame
        plot_replicator_dynamics(history, strategy_names, save_path=save_path)
        return None

    fig, ax = plt.subplots(figsize=(10, 6))

    n_strategies = len(strategy_names)
    lines = []
    colors = plt.cm.tab10(np.linspace(0, 1, n_strategies))

    for i, name in enumerate(strategy_names):
        line, = ax.plot([], [], label=name, linewidth=2, color=colors[i])
        lines.append(line)

    ax.set_xlim(0, len(history))
    ax.set_ylim(0, 1)
    ax.set_xlabel("Time")
    ax.set_ylabel("Population Proportion")
    ax.set_title("Replicator Dynamics")
    ax.legend(loc="upper right")
    ax.grid(True, alpha=0.3)

    def init():
        for line in lines:
            line.set_data([], [])
        return lines

    def animate(frame):
        for i, line in enumerate(lines):
            line.set_data(range(frame + 1), history[:frame + 1, i])
        return lines

    anim = FuncAnimation(
        fig, animate, init_func=init,
        frames=len(history), interval=interval,
        blit=True
    )

    if save_path:
        anim.save(save_path, writer="pillow", fps=10)

    return anim


def plot_payoff_matrix_heatmap(
    payoff_matrix: np.ndarray,
    strategy_names: List[str],
    title: str = "Payoff Matrix",
    figsize: tuple = (10, 8),
    save_path: str = None
):
    """
    Plot a heatmap of the payoff matrix.

    Args:
        payoff_matrix: n x n matrix where [i,j] is strategy i's score vs j
        strategy_names: Names of strategies
        title: Plot title
        figsize: Figure size
        save_path: Optional path to save figure
    """
    fig, ax = plt.subplots(figsize=figsize)

    im = ax.imshow(payoff_matrix, cmap="RdYlGn")

    # Set ticks
    ax.set_xticks(range(len(strategy_names)))
    ax.set_yticks(range(len(strategy_names)))
    ax.set_xticklabels(strategy_names, rotation=45, ha="right")
    ax.set_yticklabels(strategy_names)

    # Add colorbar
    cbar = plt.colorbar(im)
    cbar.set_label("Score")

    # Add text annotations
    for i in range(len(strategy_names)):
        for j in range(len(strategy_names)):
            text = ax.text(j, i, f"{payoff_matrix[i, j]:.0f}",
                          ha="center", va="center", color="black", fontsize=8)

    ax.set_xlabel("Opponent")
    ax.set_ylabel("Strategy")
    ax.set_title(title)

    plt.tight_layout()

    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches="tight")

    if not BATCH_MODE:
        plt.show()
    plt.close()
