import Lake
open Lake DSL

/-!
# Lake dédié `Compression_lean` — jumeau formel de la série Compression (EPIC #18706)

Formalisation Lean du cœur théorique des codes de compression : l'inégalité de
Kraft et le théorème de McMillan pour les codes préfixes, ancres formelles des
carnets Python `Compression/Compression-01-ShannonFano-Prefixe-Python.ipynb`
(pli 1, Shannon–Fano) et `Compression-02-HuffmanCanonique` (pli 2, Huffman
canonique). Décision D4 de l'EPIC #18706 : lake dédié, mathlib seule.

Convention des lakes frères (`learning_theory_lean`, `search_lean`) : le lake
est le livrable formel, `lake build` est la preuve d'exécution ; les carnets
Python de la série restent le vecteur pédagogique.
-/

package «compression_lean» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "db584cd6d46c92f209a44c0f1c829460d327499d"

/-- Modules racine du lake : `PrefixCodes` — codes préfixes et inégalité de
Kraft (pli 1/2 de #18706) : arbres de codes binaires, mots des feuilles, code
préfixe, somme de Kraft ≤ 1, arbre complet de profondeur k (2^k feuilles,
Kraft = 1 exactement), ancres numériques des carnets Python frères (sibling
EN : `PrefixCodes_en`) ; `Decode` — décodage préfixe et table de décodage
(pli 2 de #18706) : un pas de décodage le long de l'arbre, correction et
complétude du pas, décodage complet du flux, théorème de round-trip. -/
@[default_target]
lean_lib «PrefixCodes» where
  -- Module plat (fichiers racine, aucune arborescence `PrefixCodes/`) :
  -- pas de `.submodules`, cf la note `MathUniverse` de `learning_theory_lean`.
  globs := #[`PrefixCodes, `PrefixCodes_en, `Decode]
