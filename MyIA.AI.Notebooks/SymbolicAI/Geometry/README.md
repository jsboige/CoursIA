# SymbolicAI / Geometry

Verification algebrique de theoremes geometriques par encodage polynomial.

## Contenu

| Notebook | Sujet | Auteur | Date |
|---|---|---|---|
| [Geometry-1-Wu-Method.ipynb](Geometry-1-Wu-Method.ipynb) | Verification algebrique (Groebner + pseudo-division Wu) | myia-po-2027 | 2026-09-23 |

## Methodes couvertes

- **Pseudo-division** (Wu, 1978) - brique elementaire pour traiter les systemes polynomiaux multi-variable.
- **Bases de Groebner** (Buchberger 1976, Kapur 1986) - verificateur independant via sympy.
- **Validation croisee** - theoremes de geometrie prouves par deux methodes differentes.

## Theoremes temoins

1. **Pythagore** - `b^2 = a^2 + c^2` decoule de l'angle droit en B.
2. **Temoin negatif** - angle droit en B n'implique pas angle droit en A.

## Sources

- Wu, Wen-Tsun (1978/1986) - On the Decision Problem and the Mechanization of Theorem-Proving in Elementary Geometry.
- Kapur, Deepak (1986) - A Refutational Approach to Geometry Theorem Proving.
- Sinha, Prabhu, Kumaraguru, Bhat, Bethge (2024) - Wu's Method can Boost Symbolic AI, arXiv:2404.06405v2.
- Trinh, Luong et al. (Google DeepMind, 2024) - Solving Olympiad Geometry without Human Demonstrations (AlphaGeometry).

## Limites

- Pas d'inegalites (Wu traite les egalites et inegalites separement).
- Pas d'integration LLM (AlphaGeometry utilise un LLM pour constructions auxiliaires).
- Implementation Wu simplifiee (pseudo-division directe) ; cas reels a 5+ variables : Groebner sympy.

## Roadmap

- Geometry-2 : bissectrices (Wu)
- Geometry-3 : Pappus / Desargues (Groebner)
- Geometry-4 : integration LLM (type AlphaGeometry) - sous reserve

[<- SymbolicAI](../README.md)
