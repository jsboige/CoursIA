# Attribution Notice - Social Choice Theory (Lean 4)

This library formalizes key results in social choice theory in Lean 4.
It is derived from multiple open-source projects and academic work.

## Original Sources

### asouther4/lean-social-choice (Lean 3)
- **URL**: https://github.com/asouther4/lean-social-choice
- **License**: MIT
- **Usage**: Original Lean 3 formalization of Arrow's theorem and Sen's paradox.
  Ported to Lean 4 with significant modifications including the Geanakoplos (2005)
  proof approach for Arrow's theorem and bidirectional formulation for Sen's theorem.

### chasenorman/lean-social-choice (Lean 3 fork)
- **URL**: https://github.com/chasenorman/lean-social-choice
- **License**: MIT
- **Usage**: Fork with additional definitions and lemma structures used as reference
  during the Lean 4 port.

### DominikPeters/lean-social-choice (Lean 3 fork)
- **URL**: https://github.com/DominikPeters/lean-social-choice
- **License**: MIT
- **Usage**: Fork with alternative proof structures consulted during development.

## Academic References

- **Arrow, K.J.** (1951). *Social Choice and Individual Values*. Wiley.
- **Sen, A.** (1970). *Collective Choice and Social Welfare*. Holden-Day.
- **Geanakoplos, J.** (2005). "Three Brief Proofs of Arrow's Impossibility Theorem."
  *Economic Theory*, 26(1), 211-215.

## Mathematical Library

This project depends on **Mathlib**, the Lean 4 mathematical library:
- **URL**: https://github.com/leanprover-community/mathlib4
- **License**: Apache 2.0

## Lean Toolchain

- **Lean**: v4.28.0-rc1+
- **Lake**: v5.0.0+

----------------------------------------------------

État de licence des sources citées ci-dessus, mesuré le 2026-10-06
(vérification firsthand, cf #14955) :

- `asouther4/lean-social-choice` (amont principal) : **aucune licence** —
  `license: null` à l'API GitHub, aucun fichier LICENSE à la racine
  (contenu : `.github`, `.gitignore`, `README.md`, `leanpkg.toml`, `src`).
- `chasenorman/lean-social-choice` et `DominikPeters/lean-social-choice`
  (forks cités) : **introuvables** (HTTP 404 — dépôts supprimés ou
  renommés). La mention « License: MIT » ci-dessus ne peut plus être
  vérifiée à la source pour eux non plus.
- Fork restant (non cité ci-dessus) : `mdnestor/lean-social-choice`,
  `license: null`.

En conséquence, aucune copie de texte de licence n'est attachée à ce
répertoire en l'état : poser un `LICENSE-MIT.txt` de notre main
fabriquerait une permission qu'aucune source vérifiable n'accorde. Le
dérivé est conservé en l'état — arbitrage en cours sur #14955 (issue
amont demandant une licence, ou retrait du dérivé).
