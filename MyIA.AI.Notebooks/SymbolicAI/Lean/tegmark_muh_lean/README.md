# Mini-projet Lean pédagogique : structures mathématiques finies (Annexe A, Tegmark R16)

Formalisation **constructive** Lean 4 de la définition d'une *structure
mathématique finie* telle que donnée en Annexe A de Tegmark (2007), *The
Mathematical Universe* ([arXiv:0704.0646](https://arxiv.org/abs/0704.0646)).

## Source

- **R16** — *The Mathematical Universe*
  ([arXiv:0704.0646](https://arxiv.org/abs/0704.0646))
  PDF : `G:\Mon Drive\MyIA\IA\Bibliographie IA\Consciousness\2007 - Tegmark - The Mathematical Universe.pdf` (sha8 `85712871`)

Localisation papier : Annexe A §1 (définition générale), §2a (Boolean/NAND),
§2b (C₃), §2c (encoding scheme), §2d (complexité H(s)).

## Pourquoi ce projet ?

Tegmark (Annexe A §1) énonce que **l'équivalence de deux structures finies est
décidable par algorithme haltant** — c'est la base de la CUH (Computable
Universe Hypothesis) au §VII.E. Formaliser cette décidabilité constructivement
en Lean 4 :

  - **sécurise** le pont entre « structure mathématique » (concept) et
    « programme qui l'engendre » (artefact),
  - **isole** la définition générale de ses exemples (Boolean, C₂, C₃),
  - **illustre** la composition de relations (règle (3) du §1) sans dépendre
    de Mathlib.

## Modules

| Fichier | Contenu |
|---|---|
| `MUH/Structure.lean` | Signature d'une structure finie (sets + relations génératrices + arités/types + table de valeurs) |
| `MUH/Encoding.lean` | Encodage selon Tegmark §c + complexité H(s) |
| `MUH/Boolean.lean` | Algèbre de Boole à 2 éléments (1 générateur NAND + version 8 générateurs) |
| `MUH/Cyclic.lean` | Groupes cycliques C₂ et C₃ |
| `MUH/Decidable.lean` | Algorithme énumératif haltant (arité ≤ 2, cardinal ≤ 3) |

## Conventions

- **Toolchain** : Lean 4 v4.33.0 (migré depuis v4.32.x — cf. PR chore(lean) #16369 pour le précédent outil de la même série).
- **Pas de Mathlib** : la signature d'une structure finie et ses exemples
  n'ont besoin que des types de base (`Nat`, `Fin`, `List`, `Bool`, `Array`).
  Le théorème général de décidabilité (Tegmark §1) demanderait `Fin.pi` et
  `Finset.card` ; nous nous limitons à un cas restreint documenté.
- **i18n FR/EN** : pattern sibling pair (#4980). Les fichiers `MUH.lean` et
  `MUH.lean.en` ne portent que la docstring (byte-identity sur les imports).
- **Pas de PDF committé** : la source reste au gisement `G:\Mon Drive\MyIA\IA\Bibliographie IA`.

## Validation

```bash
$ lake build MUH
[run] lake build --no-build MUH
[build] MUH
✓ MUH (5 modules, 0 sorry)
```

## Issue liée

- Epic #16741 (Distillation corpus Tegmark)
- Issue #16753 — T12 (livrable demandé : structure finie + Aut(S) groupe +
  décidable par énumération haltante + exemples C₂/C₃/Boole-NAND)

## Voir aussi

- `finiteness_lean/` — précédent du même pattern (dérivées symboliques de
  Brzozowski, Lean 4 standalone, sans Mathlib).
- `coordinator-workflow.md` — le流程 de revision lake/coordinateur.
- `decidable_instance_propagation.md` — le piège d'instance `Decidable`
  sans contexte.