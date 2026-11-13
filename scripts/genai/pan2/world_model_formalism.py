#!/usr/bin/env python3
"""world_model_formalism.py — PAN 2 / GLP : la formalisation, vérifiable sans le modèle.

Encode la formalisation de l'architecture **GLP** (Generative Latent Prediction) et de son
instanciation **PAN**, distillées de :

- Xing, Deng, Hou — *Critique of World Model* (arXiv 2507.05169, juin 2026) ;
- la model card `IFM/PAN2` (Hugging Face) et la recette vLLM officielle.

CPU, sans dépendance (bibliothèque standard uniquement). L'outil **ne reproduit pas** le
modèle 29 B (qui se sert sur 4x B300 / 8x H200) : il rend la *formalisation* vérifiable —
les cinq dimensions de design, les trois niveaux du GLP, la distribution **dégénérée** de
JEPA (masse de Dirac, non probabiliste) opposée à une distribution générative propre, et la
factorisation  p_PAN(o' | o, a) = p_h . p_f . p_g  (le décodeur ``g`` absent de JEPA,
présent de GLP, est ce qui ferme la boucle).

Usage:
    python world_model_formalism.py            # affiche la formalisation
    python world_model_formalism.py --check    # auto-test, sortie 0/1/2

Sortie : 0 = tous les contrôles PASS · 1 = au moins un FAIL · 2 = erreur d'usage.
"""
from __future__ import annotations

import sys
from dataclasses import dataclass
from typing import Callable

# ---------------------------------------------------------------------------
# Les cinq dimensions de design (papier §4, p.2-3) + la position GLP sur chacune
# ---------------------------------------------------------------------------
DIMENSIONS: tuple[str, ...] = ("data", "representation", "architecture", "objective", "usage")

GLP_POSITION: dict[str, str] = {
    "data": "toutes les modalités d'expérience; densité d'information, pas seulement le volume",
    "representation": "mixte continu + discret, hiérarchique, multi-niveaux",
    "architecture": "GLP: bottleneck génératif + backbone LLM + prédicteur de next-embedding par diffusion",
    "objective": "perte générative ancrée dans les données d'observation (espace données, pas seulement latent)",
    "usage": "simuler l'expérience pour entraîner des agents par RL",
}

# ---------------------------------------------------------------------------
# Les trois niveaux du GLP (papier §4.3.3, p.14-15)
# ---------------------------------------------------------------------------
@dataclass(frozen=True)
class GLPLevel:
    name: str
    mechanism: str
    handles: str


GLP_LEVELS: tuple[GLPLevel, ...] = (
    GLPLevel("bas", "next-embedding (diffusion latente)",
             "perceptuel continu fin-grain: pixels, audio, proprioception"),
    GLPLevel("intermédiaire", "next-token (Transformer autoregressif, tokens type VQ-VAE)",
             "structure symbolique et compositionnelle"),
    GLPLevel("haut", "LLM en 'thought space' (tokens langue)",
             "planification long-horizon, simulation mentale, contre-factuel"),
)

# ---------------------------------------------------------------------------
# Distributions : dégénérée (JEPA) vs générative propre (GLP)
# ---------------------------------------------------------------------------
@dataclass(frozen=True)
class DiracDelta:
    """Distribution dégénérée : masse ponctuelle centrée sur une prédiction déterministe."""

    center: float

    def support_size(self) -> int:
        return 1  # un seul point

    def is_probabilistic(self) -> bool:
        # Ne modélise pas l'incertitude (pas d'échantillonnage sur une distribution).
        return False


@dataclass(frozen=True)
class GenerativeDistribution:
    """Distribution générative propre : support étendu, modélise l'incertitude."""

    def support_size(self) -> int:
        return 2  # au moins deux points (non ponctuel)

    def is_probabilistic(self) -> bool:
        return True


# ---------------------------------------------------------------------------
# Factorisation d'un modèle du monde : encodeur / monde / [décodeur]
# ---------------------------------------------------------------------------
@dataclass
class WorldModelFactorization:
    encoder: str = "p_h(s_hat|o)"               # observation -> état latent
    world_model: str = "p_f(s_hat'|s_hat,a)"    # état + action -> état suivant
    decoder: str | None = "p_g(o'|s_hat')"      # état latent -> observation (None = absent)

    def is_closed_loop(self) -> bool:
        """Boucle fermée = présence du décodeur (validation contre l'observation)."""
        return self.decoder is not None

    def factors(self) -> list[str]:
        fs = [self.encoder, self.world_model]
        if self.decoder is not None:
            fs.append(self.decoder)
        return fs


JEPA = WorldModelFactorization(decoder=None)  # boucle ouverte, décodeur absent
GLP = WorldModelFactorization(decoder="p_g(o'|s_hat')")  # boucle fermée


# ---------------------------------------------------------------------------
# Les contrôles (sortie 0 si tous PASS)
# ---------------------------------------------------------------------------
def check_dimensions() -> tuple[bool, str]:
    missing = [d for d in DIMENSIONS if d not in GLP_POSITION]
    ok = len(DIMENSIONS) == 5 and not missing
    return ok, f"5 dimensions de design, GLP positionné sur chacune (manquants: {missing or 'aucun'})"


def check_glp_levels() -> tuple[bool, str]:
    names = [lv.name for lv in GLP_LEVELS]
    ok = names == ["bas", "intermédiaire", "haut"]
    return ok, f"3 niveaux du GLP = {names}"


def check_jepa_degenerate() -> tuple[bool, str]:
    d = DiracDelta(center=0.0)
    ok = d.support_size() == 1 and not d.is_probabilistic()
    return ok, "JEPA = masse de Dirac (support ponctuel, non probabiliste) -> dégénérée"


def check_generative_proper() -> tuple[bool, str]:
    g = GenerativeDistribution()
    ok = g.support_size() >= 2 and g.is_probabilistic()
    return ok, "GLP = distribution générative propre (support etendu, probabiliste)"


def check_closed_loop_decoder() -> tuple[bool, str]:
    ok = JEPA.decoder is None and GLP.is_closed_loop()
    return ok, "le décodeur g ABSENT de JEPA, PRESENT de GLP (ferme la boucle)"


def check_pan_factorization() -> tuple[bool, str]:
    f = GLP.factors()
    need = {"p_h(s_hat|o)", "p_f(s_hat'|s_hat,a)", "p_g(o'|s_hat')"}
    ok = len(f) == 3 and need.issubset(f)
    return ok, "p_PAN(o'|o,a) = p_h . p_f . p_g (3 facteurs)"


def check_diagnostic_property() -> tuple[bool, str]:
    # Le décodeur comme diagnostic : boucle fermée <=> ancrage dans l'observation.
    ok = GLP.is_closed_loop() and (JEPA.is_closed_loop() is False)
    return ok, "boucle fermée (décodeur) <=> supervision ancrée dans l'observation (diagnostic)"


CHECKS: list[tuple[str, Callable[[], tuple[bool, str]]]] = [
    ("dimensions", check_dimensions),
    ("glp-niveaux", check_glp_levels),
    ("jepa-degenerée", check_jepa_degenerate),
    ("glp-generative", check_generative_proper),
    ("boucle-fermée", check_closed_loop_decoder),
    ("factorisation-PAN", check_pan_factorization),
    ("propriété-diagnostic", check_diagnostic_property),
]


def run_checks() -> int:
    print(f"world_model_formalism — {len(CHECKS)} contrôles (GLP / PAN 2, arXiv 2507.05169)")
    fails = 0
    for name, fn in CHECKS:
        try:
            ok, detail = fn()
        except Exception as e:  # un contrôle qui lève = FAIL (jamais de crash silencieux)
            ok, detail = False, f"EXCEPTION: {e!r}"
        if not ok:
            fails += 1
        print(f"[{'PASS' if ok else 'FAIL'}] {name:18s} {detail}")
    print(f"--- {len(CHECKS) - fails}/{len(CHECKS)} PASS, {fails} FAIL ---")
    return 1 if fails else 0


def show() -> None:
    print("PAN 2 / GLP — formalisation (distillation de arXiv 2507.05169 + model card IFM/PAN2)\n")
    print("Cinq dimensions de design (position GLP):")
    for d in DIMENSIONS:
        print(f"  - {d:15s} {GLP_POSITION[d]}")
    print("\nTrois niveaux du GLP:")
    for lv in GLP_LEVELS:
        print(f"  - {lv.name:14s} {lv.mechanism}  ->  {lv.handles}")
    print("\nFactorisation:")
    print(f"  JEPA : {' . '.join(JEPA.factors())}   (boucle ouverte, décodeur absent)")
    print(f"  GLP  : {' . '.join(GLP.factors())}   (boucle fermée, décodeur présent)")
    print("\np_PAN(o'|o,a) = sum_{s_hat,s_hat'} p_h(s_hat|o) . p_f(s_hat'|s_hat,a) . p_g(o'|s_hat')")


def main(argv: list[str]) -> int:
    if len(argv) > 1 and argv[1] == "--check":
        if len(argv) > 2:
            print(f"usage: {argv[0]} --check", file=sys.stderr)
            return 2
        return run_checks()
    if len(argv) > 1 and argv[1] in ("-h", "--help"):
        print(__doc__)
        return 0
    if len(argv) > 1:
        print(f"usage: {argv[0]} [--check | -h]", file=sys.stderr)
        return 2
    show()
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
