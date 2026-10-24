"""Jonction vers l'organe natif d'argumentation (TweetyProject), optionnelle.

La serie ICT implemente la semantique grounded de Dung en pur Python
(:func:`ict.argumentation.grounded_labeling`). Les trajectoires de croyance du
carnet C3 reposent entierement sur cette implementation : tant qu'elle n'est
confrontee a aucun oracle exterieur, rien ne distingue une semantique correcte
d'une semantique seulement plausible.

Ce module branche l'**organe natif** -- TweetyProject 1.30 via ``jpype``, deja
outille par la serie ``SymbolicAI/Tweety`` (``Tweety-12``) -- dans les deux
sens :

* **validation** : :func:`native_grounded` calcule l'extension grounded avec
  ``SimpleGroundedReasoner`` et :func:`parity` mesure l'accord avec
  l'instrument de la serie sur un banc d'AF canoniques et aleatoires ;
* **lecture** : :func:`af_from_native` importe un ``DungTheory`` construit par
  l'organe dans la representation de la serie (:class:`DungAF`).

L'organe est **optionnel et hors depot** : ni les JARs ni le JDK portable ne
sont versionnes (mesure du 2026-10-20 : 0 fichier suivi sous ``Tweety/libs``
et ``Tweety/jdk-17-portable``). :func:`availability` rend donc ``(False,
raison)`` quand il manque, et les appelants doivent alors **nommer l'absence**
plutot que produire un chiffre par defaut. Aucun import de ``jpype`` au niveau
module ; les messages ne portent jamais de chemin absolu (les sorties de carnet
sont commitees -- un chemin machine y serait une fuite).
"""

from __future__ import annotations

import os
import random
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Tuple

from .argumentation import DungAF, grounded_labeling

TWEETY_HOME_ENV = "TWEETY_HOME"

_TWEETY_RELATIVE = Path("MyIA.AI.Notebooks") / "SymbolicAI" / "Tweety"

_jvm_started = False
_cached_availability: Optional[Tuple[bool, str]] = None


class TweetyUnavailable(RuntimeError):
    """L'organe natif n'est pas joignable sur cette machine (raison portee)."""


# --------------------------------------------------------------------------- #
#  Localisation de l'organe (hors depot)                                      #
# --------------------------------------------------------------------------- #


def tweety_home() -> Path:
    """Racine de l'organe : ``TWEETY_HOME`` sinon ``SymbolicAI/Tweety`` du depot.

    ``TWEETY_HOME`` sert les worktrees et les machines ou l'organe est installe
    ailleurs : JARs et JDK ne sont pas versionnes, donc un checkout neuf ne les
    porte pas.
    """
    override = os.environ.get(TWEETY_HOME_ENV)
    if override:
        return Path(override)
    repo_root = Path(__file__).resolve().parents[4]
    return repo_root / _TWEETY_RELATIVE


def _jars(home: Optional[Path] = None) -> List[Path]:
    libs = (home or tweety_home()) / "libs"
    return sorted(libs.glob("*.jar")) if libs.is_dir() else []


def _portable_jdk(home: Path) -> Optional[Path]:
    base = home / "jdk-17-portable"
    if not base.is_dir():
        return None
    for candidate in sorted(base.glob("zulu*")):
        if candidate.is_dir():
            return candidate
    return None


def _env_java_home() -> Optional[str]:
    value = os.environ.get("JAVA_HOME")
    return value if value and Path(value).is_dir() else None


def availability() -> Tuple[bool, str]:
    """L'organe est-il joignable ? ``(bool, raison)``, sans chemin absolu.

    Trois conditions, mesurees dans cet ordre : ``jpype`` importable, au moins
    un JAR Tweety, un JDK (portable ou ``JAVA_HOME``). La raison est courte et
    publiable dans une sortie de carnet.
    """
    global _cached_availability
    if _cached_availability is not None:
        return _cached_availability
    try:
        import jpype  # noqa: F401
    except Exception as exc:  # noqa: BLE001 - toute absence est une raison
        _cached_availability = (False, f"jpype1 absent ({type(exc).__name__})")
        return _cached_availability
    home = tweety_home()
    jars = _jars(home)
    if not jars:
        _cached_availability = (
            False,
            "aucun JAR Tweety (libs/ absent ou vide) : "
            "download_tweety_tools.py --lib-dir, ou TWEETY_HOME",
        )
        return _cached_availability
    if _portable_jdk(home) is None and _env_java_home() is None:
        _cached_availability = (
            False,
            "aucun JDK (jdk-17-portable absent et JAVA_HOME vide)",
        )
        return _cached_availability
    _cached_availability = (True, f"{len(jars)} JARs Tweety prets")
    return _cached_availability


def ensure_jvm() -> int:
    """Demarre la JVM une seule fois avec le classpath Tweety ; rend le nb de JARs.

    Leve :class:`TweetyUnavailable` si l'organe manque -- aucun demarrage
    partiel, aucune exception avalee.
    """
    global _jvm_started
    ok, reason = availability()
    if not ok:
        raise TweetyUnavailable(reason)

    import jpype
    import jpype.imports  # installe le hook d'import des paquets Java (org.*)

    jars = _jars()
    if jpype.isJVMStarted():
        _jvm_started = True
        return len(jars)

    jdk = _portable_jdk(tweety_home())
    if jdk is not None:
        os.environ["JAVA_HOME"] = str(jdk)
    classpath = os.pathsep.join(str(jar.resolve()) for jar in jars)
    jpype.startJVM(classpath=[classpath])
    _jvm_started = True
    return len(jars)


def _dung_syntax():
    from org.tweetyproject.arg.dung.syntax import (  # type: ignore[import]
        Argument,
        Attack,
        DungTheory,
    )

    return DungTheory, Argument, Attack


def _grounded_reasoner():
    from org.tweetyproject.arg.dung.reasoner import (  # type: ignore[import]
        SimpleGroundedReasoner,
    )

    return SimpleGroundedReasoner


# --------------------------------------------------------------------------- #
#  Les deux sens de la jonction                                               #
# --------------------------------------------------------------------------- #


def build_native_af(af: DungAF):
    """Construit un ``DungTheory`` TweetyProject a partir d'un :class:`DungAF`."""
    ensure_jvm()
    DungTheory, Argument, Attack = _dung_syntax()
    theory = DungTheory()
    nodes = {arg: Argument(str(arg)) for arg in af.arguments}
    for node in nodes.values():
        theory.add(node)
    for (src, tgt) in af.attacks:
        theory.add(Attack(nodes[src], nodes[tgt]))
    return theory


def native_grounded(af: DungAF) -> frozenset:
    """Extension grounded calculee par l'ORACLE Java, en identifiants entiers."""
    theory = build_native_af(af)
    SimpleGroundedReasoner = _grounded_reasoner()
    extension = SimpleGroundedReasoner().getModel(theory)
    return frozenset(int(str(arg.getName())) for arg in extension)


def instrument_grounded(af: DungAF) -> frozenset:
    """Extension grounded de l'INSTRUMENT de la serie (pur Python)."""
    label = grounded_labeling(af)
    return frozenset(arg for arg, value in label.items() if value == "in")


def af_from_native(theory) -> DungAF:
    """Lit un ``DungTheory`` construit par l'organe dans un :class:`DungAF`."""
    arguments = [int(str(node.getName())) for node in theory.getNodes()]
    attacks = [
        (
            int(str(attack.getAttacker().getName())),
            int(str(attack.getAttacked().getName())),
        )
        for attack in theory.getAttacks()
    ]
    return DungAF(arguments, attacks)


# --------------------------------------------------------------------------- #
#  Banc de mesure de la parite                                                #
# --------------------------------------------------------------------------- #


def canonical_cases() -> List[Tuple[str, DungAF]]:
    """12 AF canoniques : cycles, auto-attaque, defense, composantes, clique.

    Les cas couvrent les figures ou la semantique grounded n'est pas lisible
    d'un coup d'oeil (cycles pairs et impairs, auto-attaque, cycle + argument
    isole) et deux cas ou elle est deterministe (chaine, etoile) : un banc qui
    ne porterait que des cas triviaux ne distinguerait pas deux implementations
    fausses de la meme facon.
    """
    return [
        ("cycle 2 (Nixon)", DungAF([0, 1], [(0, 1), (1, 0)])),
        ("Tweety bird", DungAF([0, 1, 2], [(0, 1), (1, 0), (2, 1)])),
        ("chaine 5", DungAF(list(range(5)), [(0, 1), (1, 2), (2, 3), (3, 4)])),
        ("cycle 3", DungAF([0, 1, 2], [(0, 1), (1, 2), (2, 0)])),
        ("cycle 4", DungAF([0, 1, 2, 3], [(0, 1), (1, 2), (2, 3), (3, 0)])),
        ("auto-attaque", DungAF([0, 1], [(0, 0), (0, 1)])),
        ("etoile 0->1..4", DungAF(list(range(5)), [(0, i) for i in range(1, 5)])),
        ("deux composantes", DungAF([0, 1, 2, 3], [(0, 1), (2, 3), (3, 2)])),
        ("defense 0->1,1->2", DungAF([0, 1, 2], [(0, 1), (1, 2)])),
        ("aucune attaque", DungAF([0, 1, 2], [])),
        ("argument isole + cycle", DungAF([0, 1, 2], [(1, 2), (2, 1)])),
        (
            "clique 4 sans auto",
            DungAF([0, 1, 2, 3], [(a, b) for a in range(4) for b in range(4) if a != b]),
        ),
    ]


def random_cases(
    seed: int = 42,
    count: int = 200,
    n_min: int = 4,
    n_max: int = 6,
) -> List[Tuple[str, DungAF]]:
    """``count`` AF aleatoires reproductibles (auto-attaques incluses).

    Densite tiree parmi 0.15 / 0.30 / 0.50 : le banc couvre des graphes creux
    (beaucoup d'arguments ``in``) et denses (beaucoup de cycles, donc
    d'``undec``). Les auto-attaques ne sont pas filtrees : c'est un cas
    legitime de Dung, et il separe deux implementations qui divergeraient sur
    les cycles de longueur 1.
    """
    rng = random.Random(seed)
    cases: List[Tuple[str, DungAF]] = []
    for i in range(count):
        n = rng.randint(n_min, n_max)
        p = rng.choice([0.15, 0.3, 0.5])
        attacks = [(a, b) for a in range(n) for b in range(n) if rng.random() < p]
        cases.append((f"aleatoire-{i:03d} (n={n}, m={len(attacks)})", DungAF(list(range(n)), attacks)))
    return cases


def parity(cases: Iterable[Tuple[str, DungAF]]) -> Dict[str, object]:
    """Confronte instrument et oracle sur ``cases`` ; rend lignes et comptes.

    Un desaccord n'est jamais leve en exception : il est **compte** et porte
    ses deux ensembles, pour que le carnet puisse nommer les cas divergents au
    lieu d'un simple « echec ».
    """
    rows: List[Dict[str, object]] = []
    agree = 0
    disagree = 0
    for name, af in cases:
        instrument = instrument_grounded(af)
        native = native_grounded(af)
        same = instrument == native
        agree += int(same)
        disagree += int(not same)
        rows.append(
            {
                "name": name,
                "instrument": sorted(instrument),
                "natif": sorted(native),
                "accord": same,
            }
        )
    return {
        "rows": rows,
        "n": len(rows),
        "accord": agree,
        "desaccord": disagree,
    }