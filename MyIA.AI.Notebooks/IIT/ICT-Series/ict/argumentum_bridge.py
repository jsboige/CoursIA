"""Jonction Argumentum : l'organe EPITA ``argumentation_lib`` comme oracle.

La jonction Tweety (section 8sexies du carnet) valide l'instrument de la
serie contre TweetyProject brut, ponte directement. Celle-ci valide le
MEME instrument contre la pile que la serie Argument_Analysis consomme :
l'organe EPITA ``argumentation_lib`` (couche shim vendored, voir #4960) --
``TweetyInitializer`` + ``AFHandler`` + raisonneurs Tweety. L'organe
routant lui-meme vers Tweety par jpype, la parite mesuree ici est
**inter-organes** : l'instrument pur Python contre la pile EPITA, sur la
MEME JVM que la jonction Tweety (un processus, une seule JVM).

Prerequis double, tous deux fail-closed :

1. la JVM doit deja tourner -- c'est la jonction Tweety (8sexies) qui la
   demarre ; cette jonction n'en lance jamais une deuxieme ;
2. l'alias de routage ``tweety_initializer`` doit etre present dans
   l'arbre (PR #21657) -- sans lui la couche AF de l'organe est morte a
   l'import depuis le merge C186f, et la jonction se declare indisponible
   au lieu d'improviser un contournement.
"""
from __future__ import annotations

import sys
from pathlib import Path
from typing import Dict, Iterable, List, Tuple

from . import tweety_bridge


class ArgumentumUnavailable(RuntimeError):
    """L'organe EPITA n'est pas consommable dans cet environnement."""


def _argument_analysis_dir() -> Path:
    """Repertoire de l'organe dans l'arbre du depot (ICT-Series -> ...)."""
    # argumentum_bridge.py -> ict -> ICT-Series -> IIT -> MyIA.AI.Notebooks
    return Path(__file__).resolve().parents[3] / "SymbolicAI" / "Argument_Analysis"


def availability() -> Tuple[bool, str]:
    """Disponibilite de l'organe, fail-closed sur chaque prerequis."""
    try:
        import jpype
    except ImportError:
        return False, "jpype absent"
    if not jpype.isJVMStarted():
        return False, "JVM non demarree -- la jonction Tweety (8sexies) doit l'amener"

    arg = _argument_analysis_dir()
    if not (arg / "argumentation_lib" / "__init__.py").is_file():
        return False, "organe introuvable dans l'arbre (Argument_Analysis absent)"
    if str(arg) not in sys.path:
        sys.path.insert(0, str(arg))
    try:
        import argumentation_lib  # noqa: F401
    except Exception as exc:  # pragma: no cover - arbre casse
        return False, f"argumentation_lib non importable ({exc.__class__.__name__})"

    handler = _handler()
    if handler is None:
        return False, "couche AF morte a l'import -- alias tweety_initializer absent (PR #21657)"
    return True, "organe EPITA argumentation_lib, JVM deja demarree par la jonction Tweety"


_HANDLER = None


def _handler():
    """Singleton AFHandler ; None si la couche AF ne s'importe pas."""
    global _HANDLER
    if _HANDLER is not None:
        return _HANDLER
    try:
        import argumentation_lib
        initializer = argumentation_lib.get_tweety_initializer_symbol()()
        initializer.ensure_jvm_and_components_are_ready()
        handler_cls = argumentation_lib.get_af_handler_symbol()
        _HANDLER = handler_cls(initializer)
    except Exception:
        return None
    return _HANDLER


def organ_grounded(af) -> frozenset:
    """Extension grounded selon l'organe EPITA (AFHandler, semantique unique)."""
    handler = _handler()
    if handler is None:
        raise ArgumentumUnavailable("couche AF de l'organe non importable")
    names = [f"a{i}" for i in af.arguments]
    attacks = [[f"a{s}", f"a{t}"] for s, t in af.attacks]
    result = handler.analyze_dung_framework(names, attacks, semantics="grounded")
    extensions = result["extensions"]["grounded"]
    # La semantique grounded admet une extension unique ; un organe qui en
    # rendrait plusieurs serait un bug a faire remonter, pas a absorber.
    if len(extensions) != 1:
        raise ArgumentumUnavailable(
            f"organe : {len(extensions)} extensions grounded (attendu 1)"
        )
    return frozenset(int(name[1:]) for name in extensions[0])


def parity(cases: Iterable[Tuple[str, object]]) -> Dict[str, object]:
    """Parite organe EPITA vs instrument de la serie, cas par cas."""
    rows: List[Dict[str, object]] = []
    accord = 0
    for name, af in cases:
        organ = organ_grounded(af)
        instrument = tweety_bridge.instrument_grounded(af)
        ok = organ == instrument
        accord += int(ok)
        rows.append({
            "name": name,
            "accord": ok,
            "instrument": sorted(instrument),
            "organe": sorted(organ),
        })
    return {"n": len(rows), "accord": accord, "desaccord": len(rows) - accord, "rows": rows}
