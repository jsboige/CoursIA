"""Vector-to-vector comparison for SOTA bridge tests.

Helpers
-------
- `vector_linf(a, b)`            : distance L∞ (max absolu) entre 2 vecteurs
- `vector_l2(a, b)`              : distance L2 (euclidienne) entre 2 vecteurs
- `vector_close(a, b, tol, ...)` : verdict booleen structure sur tolerance
- `compare_bridge(a, b, ...)`    : verdict machine (status + distance + indices)
                                  + resume lisible humain

Convention de tolerance
-----------------------
| Mode       | Critere                                             |
|------------|-----------------------------------------------------|
| 'absolute' | distance <= tol                                     |
| 'relative' | distance <= tol * max(|a|, |b|)                     |
| 'both'     | les 2 concourent ; True si l'un OU l'autre tient    |

Sortie `compare_bridge`
-----------------------
- `status`        : 'CONCORDANT' | 'DIVERGENT' | 'SHAPE_MISMATCH' | 'EMPTY'
- `distance`      : float (L∞ choisi par defaut)
- `max_index`     : index de la composante ou la distance est maximale (None si vide)
- `max_pair`      : (a_max, b_max) pour lecture humaine
- `tolerance`     : tolerance absolue declaree (echo)
- `mode`          : mode de tolerance applique
- `summary`       : ligne lisible humain, pour les cellules d'un notebook
"""
from __future__ import annotations

import math
from dataclasses import dataclass, asdict
from typing import Sequence, Tuple, Union, List, Optional

Number = Union[int, float]
Vector = Sequence[Number]


def _flatten(v: Vector) -> List[float]:
    """Coerce un iterable en list[float] et rejeter les elements non numeriques."""
    out: List[float] = []
    for i, x in enumerate(v):
        try:
            f = float(x)
        except (TypeError, ValueError) as e:
            raise TypeError(
                f"composante #{i} non numerique ({type(x).__name__}={x!r}): {e}"
            ) from e
        if math.isnan(f) or math.isinf(f):
            raise ValueError(f"composante #{i} NaN/Inf interdite ({f})")
        out.append(f)
    return out


def vector_linf(a: Vector, b: Vector) -> float:
    """Distance L∞ : max(|a_i - b_i|). 0 si identiques, +∞ si dimensions !=."""
    af, bf = _flatten(a), _flatten(b)
    if len(af) != len(bf):
        raise ValueError(
            f"dimensions differentes (L∞): {len(af)} vs {len(bf)}"
        )
    if not af:
        return 0.0
    return max(abs(ai - bi) for ai, bi in zip(af, bf))


def vector_l2(a: Vector, b: Vector) -> float:
    """Distance L2 (euclidienne) : sqrt(somme |a_i - b_i|^2). 0 si identiques."""
    af, bf = _flatten(a), _flatten(b)
    if len(af) != len(bf):
        raise ValueError(
            f"dimensions differentes (L2): {len(af)} vs {len(bf)}"
        )
    if not af:
        return 0.0
    return math.sqrt(sum((ai - bi) ** 2 for ai, bi in zip(af, bf)))


def _relative_pass(dist: float, scale: float, tol: float) -> bool:
    if scale == 0:
        return dist <= tol
    return dist <= tol * scale


def vector_close(
    a: Vector,
    b: Vector,
    tol: float,
    *,
    mode: str = "absolute",
    metric: str = "linf",
    scale: Optional[float] = None,
) -> bool:
    """Verdict booleen structure (True/False). Cf. docstring module pour modes.

    | Mode       | True si                                                |
    |------------|--------------------------------------------------------|
    | absolute   | distance <= tol                                        |
    | relative   | distance <= tol * scale (defaut = max |a_i|, |b_i|)    |
    | both       | absolute OR relative tient                             |

    `metric` : 'linf' (defaut) ou 'l2'.
    """
    if mode not in ("absolute", "relative", "both"):
        raise ValueError(f"mode inconnu: {mode!r}")

    af, bf = _flatten(a), _flatten(b)
    if len(af) != len(bf):
        return False

    if metric == "linf":
        dist = vector_linf(af, bf)
    elif metric == "l2":
        dist = vector_l2(af, bf)
    else:
        raise ValueError(f"metric inconnue: {metric!r}")

    if scale is None:
        if af or bf:
            scale = max(max(map(abs, af)), max(map(abs, bf))) if (af or bf) else 0.0
        else:
            scale = 0.0

    abs_ok = dist <= tol
    rel_ok = _relative_pass(dist, scale, tol)

    if mode == "absolute":
        return abs_ok
    if mode == "relative":
        return rel_ok
    return abs_ok or rel_ok


@dataclass(frozen=True)
class BridgeVerdict:
    status: str
    distance: float
    max_index: Optional[int]
    max_pair: Tuple[float, float]
    tolerance: float
    mode: str
    metric: str
    summary: str

    def as_dict(self):
        return asdict(self)


def compare_bridge(
    a: Vector,
    b: Vector,
    *,
    tol: float = 1e-6,
    mode: str = "absolute",
    metric: str = "linf",
    label: str = "",
) -> BridgeVerdict:
    """Verdict machine (BridgeVerdict) + resume lisible humain.

    Parameters
    ----------
    a, b : vecteurs (sequences numeriques)
    tol  : tolerance declaree (cf docstring module)
    mode : 'absolute' | 'relative' | 'both'
    metric : 'linf' | 'l2'
    label : nom court du comparanda (pour le resume)

    Returns
    -------
    BridgeVerdict avec `status` ∈ {'CONCORDANT', 'DIVERGENT', 'SHAPE_MISMATCH', 'EMPTY'}
    """
    af, bf = _flatten(a), _flatten(b)

    if not af and not bf:
        return BridgeVerdict(
            status="EMPTY",
            distance=0.0,
            max_index=None,
            max_pair=(0.0, 0.0),
            tolerance=tol,
            mode=mode,
            metric=metric,
            summary=f"{label}: vecteurs vides (rien a comparer)".strip(),
        )

    if len(af) != len(bf):
        return BridgeVerdict(
            status="SHAPE_MISMATCH",
            distance=float("inf"),
            max_index=None,
            max_pair=(float("nan"), float("nan")),
            tolerance=tol,
            mode=mode,
            metric=metric,
            summary=(
                f"{label}: dimensions incompatibles "
                f"({len(af)} vs {len(bf)})".strip()
            ),
        )

    if metric == "linf":
        diffs = [abs(ai - bi) for ai, bi in zip(af, bf)]
        dist = max(diffs)
        idx = diffs.index(dist)
    elif metric == "l2":
        # L2 = sqrt(somme (a_i - b_i)^2) ; on garde aussi la composante
        # maximale pour le rapport humain (idx, max_pair).
        diffs = [abs(ai - bi) for ai, bi in zip(af, bf)]
        dist = math.sqrt(sum(d ** 2 for d in diffs))
        idx = max(range(len(diffs)), key=lambda i: diffs[i])
    else:
        raise ValueError(f"metric inconnue: {metric!r}")

    a_max, b_max = af[idx], bf[idx]

    scale = max(max(map(abs, af)), max(map(abs, bf)))
    abs_ok = dist <= tol
    rel_ok = _relative_pass(dist, scale, tol)

    if mode == "absolute":
        passed = abs_ok
    elif mode == "relative":
        passed = rel_ok
    else:
        passed = abs_ok or rel_ok

    status = "CONCORDANT" if passed else "DIVERGENT"
    tag = f" [{label}]" if label else ""
    summary = (
        f"{tag} {metric}={dist:.6g} tol={tol:.1e} mode={mode} -> {status} "
        f"(idx={idx} a={a_max} b={b_max})".strip()
    )

    return BridgeVerdict(
        status=status,
        distance=dist,
        max_index=idx,
        max_pair=(a_max, b_max),
        tolerance=tol,
        mode=mode,
        metric=metric,
        summary=summary,
    )
