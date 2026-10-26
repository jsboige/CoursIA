# Attribution Notice - Social Choice Theory (Lean 4)

This library formalizes key results in social choice theory in Lean 4.
It is derived from multiple open-source projects and academic work.

> **⚑ Tombstone documentaire — la notice suit les sources, elle ne décrit plus rien ici.**
> Depuis la PR [#6058](https://github.com/jsboige/CoursIA/pull/6058) (EPIC
> [#4365](https://github.com/jsboige/CoursIA/issues/4365), 2026-07-11), les sept modules
> (`Basic`, `Framework`, `Arrow`, `Sen`, `Voting`, `MechanismDesign`, `SortedListCounting`)
> ont été absorbés **byte-identique** dans
> [`game_theory_lean/SocialChoice/`](../game_theory_lean/SocialChoice/), qui est le home
> canonique. Ce répertoire ne contient plus aucun `.lean`.
>
> **L'attribution ci-dessous reste due, et elle s'applique au home canonique.** La provenance et
> les obligations de licence voyagent avec le code, pas avec le dossier qui le contenait : c'est
> pourquoi cette notice est conservée plutôt que supprimée avec les sources.

## Original Sources

### asouther4/lean-social-choice (Lean 3)
- **URL**: https://github.com/asouther4/lean-social-choice
- **License**: **aucune trouvée** — `license: null` à l'API GitHub et aucun fichier `LICENSE`
  à la racine (mesure du 2026-10-06, cf. la note de fin de fichier et #14955). La mention
  « MIT » qui figurait ici n'était vérifiée par aucune source et a été retirée.
  **Licence demandée le 2026-10-25** ([asouther4/lean-social-choice#12](https://github.com/asouther4/lean-social-choice/issues/12)) :
  demande déposée auprès de l'amont, restée sans réponse à cette date — la mesure du
  2026-10-06 ci-dessus demeure donc celle en vigueur.
- **Usage** : formalisation Lean 3 du théorème d'Arrow et des lemmes de Sen ; notre portage
  Lean 4 en reprend `basic.lean` et `arrows_theorem.lean` (taux de reprise mesurés ci-dessous,
  section « Mesure de reprise »). L'approche de preuve d'Arrow et les manipulations de
  préférence `maketop` / `makebot` / `makeabove` **sont déjà dans l'amont** : son en-tête
  d'`arrows_theorem.lean` annonce suivre la première preuve de Geanakoplos (2005) et s'inspirer,
  pour ces trois fonctions, de la formalisation Isabelle/HOL. Notre portage **reprend** cette
  approche, il ne l'introduit pas.

### chasenorman/lean-social-choice (Lean 3 fork)
- **URL**: https://github.com/chasenorman/lean-social-choice
- **License**: MIT **déclarée, non vérifiable** — dépôt introuvable (HTTP 404) à la mesure
  du 2026-10-06.
- **Usage**: Fork with additional definitions and lemma structures used as reference
  during the Lean 4 port.

### DominikPeters/lean-social-choice (Lean 3 fork)
- **URL**: https://github.com/DominikPeters/lean-social-choice
- **License**: MIT **déclarée, non vérifiable** — dépôt introuvable (HTTP 404) à la mesure
  du 2026-10-06.
- **Usage**: Fork with alternative proof structures consulted during development.

## Mesure de reprise (2026-10-25)

Ce que le portage doit à l'amont, et ce qu'il ajoute. Méthode : intersection des **noms de
déclarations** (`theorem`, `lemma`, `def`, `abbrev`, `structure`, `inductive`, `class`,
`instance`) entre chaque module canonique et l'ensemble des six fichiers `.lean` de `src/`
amont ; les instances anonymes ne sont pas comptées.

La mesure dépend de la grammaire de déclaration retenue. Celle utilisée ici reconnaît les
déclarations précédées d'attributs et de modificateurs (`@[...]`, `private`, `protected`,
`noncomputable`, `partial`) et ne développe pas les déclarations composites ; le comptage est
fait sur le code hors commentaires. Une re-mesure indépendante du 2026-10-25, avec une
grammaire qui ne développe pas ces attributs, donne **23/27**, **3/17** et **3/44** pour
`Basic`, `Framework` et `Voting` au lieu de 25/29, 6/24 et 4/53 : la lecture — `Basic` et
`Arrow` sont le portage, le reste est ajouté — est identique dans les deux variantes. C'est
pourquoi la méthode est écrite ici : un chiffre de reprise n'est rejouable qu'avec la règle
de comptage qui l'a produit.

| Module canonique | Déclarations | Nom présent dans l'amont | Lecture |
|---|---|---|---|
| `Basic.lean` | 29 | **25** | portage de `basic.lean` |
| `Arrow.lean` | 29 | **19** | portage d'`arrows_theorem.lean` |
| `Framework.lean` | 24 | **6** | les 6 noms communs viennent d'`arrows_theorem.lean` (`makeabove`) ; le reste est propre |
| `Voting.lean` | 53 | **4** | ajout CoursIA (électeur médian, Split Cycle, Banks) — l'amont possède ses propres `split_cycle.lean` (28 déclarations sous la règle ci-dessus) et `stable_voting.lean` (56) : l'ajout est une réécriture, pas l'invention de ces concepts |
| `Sen.lean` | 4 | **0** | ajout CoursIA (paradoxe libéral, décisivité bidirectionnelle) |
| `MechanismDesign.lean` | 64 | **0** | ajout CoursIA (Vickrey, VCG) |
| `AMD.lean` | 16 | **0** | ajout CoursIA |
| `SortedListCounting.lean` | 5 | **0** | ajout CoursIA |

En résumé : `Basic` et `Arrow` sont un portage Lean 4 des fichiers `basic.lean` et
`arrows_theorem.lean` de l'amont ; `Sen`, le vote (électeur médian, Split Cycle, Banks), les
mécanismes (Vickrey, VCG) et le comptage sont des **ajouts CoursIA**.

## Academic References

Ces références nomment les **auteurs des théorèmes**, pas les auteurs du code amont — le code
amont est cité par le nom de son dépôt, plus haut.

- **Arrow, K.J.** (1951). *Social Choice and Individual Values*. Wiley.
- **Sen, A.** (1970). *Collective Choice and Social Welfare*. Holden-Day.
- **Geanakoplos, J.** (2005). "Three Brief Proofs of Arrow's Impossibility Theorem."
  *Economic Theory*, 26(1), 211-215.

## Mathematical Library

This project depends on **Mathlib**, the Lean 4 mathematical library:
- **URL**: https://github.com/leanprover-community/mathlib4
- **License**: Apache 2.0

## Lean Toolchain

Valeurs du port initial. Le pin effectif est celui du home canonique
([`game_theory_lean/lean-toolchain`](../game_theory_lean/lean-toolchain)) : ce répertoire n'a plus
de `lean-toolchain` depuis l'absorption.

- **Lean**: v4.28.0-rc1+
- **Lake**: v5.0.0+

----------------------------------------------------

État de licence des sources citées ci-dessus, **re-mesuré le 2026-10-25**
(vérification firsthand, cf #14955) :

- `asouther4/lean-social-choice` (amont principal) : **aucune licence déclarée** —
  `license: null` à l'API GitHub, aucun fichier LICENSE à la racine
  (contenu : `.github`, `.gitignore`, `README.md`, `leanpkg.toml`, `src`),
  dernier push 2021-12-24.
- `chasenorman/lean-social-choice` et `DominikPeters/lean-social-choice`
  (forks cités) : **introuvables** (HTTP 404 — dépôts supprimés ou renommés).
- Fork restant (non cité ci-dessus) : `mdnestor/lean-social-choice`,
  `license: null`.

En conséquence, aucune copie de texte de licence n'est attachée à ce
répertoire en l'état : poser un `LICENSE-MIT.txt` de notre main
fabriquerait une permission qu'aucune source vérifiable n'accorde. Le
dérivé est conservé en l'état, et la voie suivie est la demande de licence
à l'amont plutôt qu'un texte fabriqué : elle a été déposée le 2026-10-25
([asouther4/lean-social-choice#12](https://github.com/asouther4/lean-social-choice/issues/12))
et reste ouverte à cette date. C'est cette notice qu'il faudra mettre à
jour si la demande aboutit.
