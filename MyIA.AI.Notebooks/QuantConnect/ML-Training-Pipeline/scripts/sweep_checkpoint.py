"""
Generic sweep checkpoint-resume utility for ML training loops.

Tracks completed (seed, symbol, param_combo) combinations in a JSON state file.
On restart, automatically skips already-completed combos.

Usage in training scripts:
    from sweep_checkpoint import SweepCheckpoint

    sweep = SweepCheckpoint("checkpoints/lstm_sweep", seeds=[0,1,7,42], symbols=["SPY","ETH"])

    for combo in sweep.remaining():
        result = train_single(**combo)
        sweep.mark_done(combo, result["metrics"])

    sweep.finalize()

Cross-platform: works on Linux and Windows. No GPU dependency.
"""

from __future__ import annotations

import json
import os
import platform
import signal
import sys
import time
from pathlib import Path
from typing import Any, Generator


class SweepCheckpoint:
    """Portable checkpoint-resume for parameter sweep loops.

    State is stored in ``<output_dir>/sweep_state.json`` with:
    - ``completed``: list of combo dicts with their results
    - ``pending``: list of combo dicts not yet run
    - ``meta``: sweep metadata (start time, platform, etc.)

    Parameters
    ----------
    output_dir : str or Path
        Directory for the state file. Created if needed.
    seeds : list[int] or None
        Seeds to sweep. Combined with symbols/params.
    symbols : list[str] or None
        Symbols to sweep.
    extra_param_grid : dict or None
        Additional parameter grid. Keys are param names, values are lists.
        Example: ``{"hidden_size": [64, 128], "num_layers": [1, 2]}``
    resume : bool
        If True, load existing state and skip completed combos.
        If False, start fresh (overwrite existing state).
    """

    def __init__(
        self,
        output_dir: str | Path,
        seeds: list[int] | None = None,
        symbols: list[str] | None = None,
        extra_param_grid: dict[str, list] | None = None,
        resume: bool = True,
    ) -> None:
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)
        self.state_path = self.output_dir / "sweep_state.json"

        self.seeds = seeds or [0]
        self.symbols = symbols or ["default"]
        self.extra_param_grid = extra_param_grid or {}

        self._completed: list[dict] = []
        self._pending: list[dict] = []
        self._start_time = time.time()
        self._interrupted = False

        if resume and self.state_path.exists():
            self._load_state()
        else:
            self._build_combos()

        # Register graceful shutdown on SIGINT/SIGTERM
        if platform.system() != "Windows":
            signal.signal(signal.SIGTERM, self._handle_signal)
        signal.signal(signal.SIGINT, self._handle_signal)

    def _build_combos(self) -> None:
        """Generate all parameter combinations."""
        combos = []
        for seed in self.seeds:
            for symbol in self.symbols:
                base = {"seed": seed, "symbol": symbol}
                if not self.extra_param_grid:
                    combos.append(base)
                else:
                    keys = list(self.extra_param_grid.keys())
                    values = [self.extra_param_grid[k] for k in keys]
                    from itertools import product
                    for vals in product(*values):
                        combo = {**base}
                        for k, v in zip(keys, vals):
                            combo[k] = v
                        combos.append(combo)

        self._pending = combos
        self._completed = []
        self._save_state()

    def _combo_key(self, combo: dict) -> str:
        """Stable string key for a combo dict."""
        return json.dumps(combo, sort_keys=True)

    def _load_state(self) -> None:
        """Load existing state from disk."""
        with open(self.state_path, "r", encoding="utf-8") as f:
            state = json.load(f)
        self._completed = state.get("completed", [])
        self._pending = state.get("pending", [])

        done_keys = {self._combo_key(c) for c in self._completed}
        self._pending = [c for c in self._pending if self._combo_key(c) not in done_keys]

        print(f"SweepCheckpoint: resumed {len(self._completed)} done, "
              f"{len(self._pending)} remaining")

    def _save_state(self) -> None:
        """Persist current state to disk."""
        state = {
            "meta": {
                "platform": platform.system(),
                "python": platform.python_version(),
                "updated": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
                "elapsed_s": round(time.time() - self._start_time, 1),
            },
            "completed": self._completed,
            "pending": self._pending,
        }
        tmp_path = self.state_path.with_suffix(".tmp")
        with open(tmp_path, "w", encoding="utf-8") as f:
            json.dump(state, f, indent=2, default=str)
        tmp_path.replace(self.state_path)

    def _handle_signal(self, signum: int, frame: Any) -> None:
        """Save state on interrupt, then exit."""
        self._interrupted = True
        print(f"\nSweepCheckpoint: signal {signum} received, saving state...")
        self._save_state()
        print(f"  {len(self._completed)} completed, {len(self._pending)} remaining")
        sys.exit(130)

    def remaining(self) -> Generator[dict, None, None]:
        """Yield pending combos.

        Yields combo dicts. Call ``mark_done()`` after each successful run.
        If the sweep was previously interrupted, skips completed combos.
        """
        while self._pending:
            combo = self._pending.pop(0)
            self._save_state()
            yield combo

    def mark_done(self, combo: dict, metrics: dict | None = None) -> None:
        """Mark a combo as completed with optional metrics.

        Parameters
        ----------
        combo : dict
            The parameter combination that was run.
        metrics : dict or None
            Result metrics to store alongside the combo.
        """
        entry = {**combo}
        if metrics:
            entry["metrics"] = metrics
        entry["completed_at"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
        self._completed.append(entry)
        self._save_state()

        done = len(self._completed)
        total = done + len(self._pending)
        pct = done / total * 100 if total else 100
        print(f"  Sweep progress: {done}/{total} ({pct:.0f}%)")

    def finalize(self) -> dict:
        """Write final summary and return aggregated results.

        Returns dict with completed count, total, elapsed time, and results.
        """
        elapsed = time.time() - self._start_time
        total = len(self._completed) + len(self._pending)
        summary = {
            "total_combos": total,
            "completed": len(self._completed),
            "remaining": len(self._pending),
            "elapsed_s": round(elapsed, 1),
            "completed_combos": self._completed,
        }

        summary_path = self.output_dir / "sweep_summary.json"
        with open(summary_path, "w", encoding="utf-8") as f:
            json.dump(summary, f, indent=2, default=str)

        print(f"\nSweep complete: {len(self._completed)}/{total} combos "
              f"in {elapsed:.0f}s")
        return summary

    @property
    def progress(self) -> tuple[int, int]:
        """Return (completed, total) counts."""
        total = len(self._completed) + len(self._pending)
        return len(self._completed), total

    @property
    def results(self) -> list[dict]:
        """Return all completed combo results."""
        return list(self._completed)
