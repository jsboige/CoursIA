# Attribution Notice - Social Choice Theory (Lean 4)

This library formalizes key results in social choice theory in Lean 4.
It is derived from multiple open-source projects and academic work.

> **⚑ Cette notice vit désormais à côté du code qu'elle couvre.**
> Depuis la PR [#6058](https://github.com/jsboige/CoursIA/pull/6058) (EPIC
> [#4365](https://github.com/jsboige/CoursIA/issues/4365), 2026-07-11), les sept modules
> (`Basic`, `Framework`, `Arrow`, `Sen`, `Voting`, `MechanismDesign`, `SortedListCounting`)
> ont été absorbés **byte-identique** dans ce répertoire. La notice les a suivis le
> 2026-11-02 (#24183, T1) ; le répertoire entier est descendu du hub `game_theory_lean` vers
> `GameTheory/SocialChoice/social_choice_core_lean` le 2026-11-08 (#24183, T3) — 21
> renommages R100, contenu inchangé. Son ancien emplacement `social_choice_lean/` n'en garde
> plus que **trois documents** (`README`, `STATUS`, `LEAN_PREREQUISITES`), dont la preuve de
> préservation est livrée dans le [README de la coquille](../../../social_choice_lean/README.md)
> (§« Preuve de préservation ») : deux d'entre eux portent un contenu unique et des liens
> entrants actifs, si bien que le dossier **ne peut pas** être retiré avant leur relocation
> (tranche T3 de #24183).
>
> **Depuis le 2026-11-02 (#24183, T1), deux formalisations indépendantes d'Arrow et de Sen
> coexistent, et le rôle de chacune est explicite :**
>
> - [`lean_game_defs/SocialChoice.lean`](../../../lean_game_defs/SocialChoice.lean) est la
>   **maison canonique** : cœur Lean seul, zéro dépendance, écrite intégralement par CoursIA
>   (tous les commits sont de `jsboige`, étages 1 à 5 du 2026-10-28 au 2026-11-01). Son
>   en-tête la dit « inspirée de » `asouther4/lean-social-choice` : inspiration, pas
>   portage — la mesure de reprise du présent fichier porte sur **les modules de ce
>   répertoire**, elle n'a pas été refaite sur cette formalisation-là.
> - [`Arrow.lean`](Arrow.lean) et [`Sen.lean`](Sen.lean) de ce répertoire sont la **preuve
>   alternative déclarée** : fondées sur Mathlib, plus générales (types arbitraires, agenda
>   local), et pour `Arrow.lean` un portage mesuré d'`arrows_theorem.lean` (19 noms sur 29).
>   Elles ne sont ni retirées ni dépréciées : elles enseignent une autre stratégie de preuve
>   sur les mêmes énoncés.
>
> **L'attribution ci-dessous reste due, et elle s'applique aux deux formalisations.** La
> provenance et les obligations de licence voyagent avec le code, pas avec le dossier qui le
> contenait : c'est pourquoi cette notice est conservée plutôt que supprimée avec les sources.

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

Le comptage est fait sur le code hors commentaires, en reconnaissant les déclarations
précédées d'attributs et de modificateurs (`@[...]`, `private`, `protected`,
`noncomputable`, `partial`) — un chiffre de reprise n'est rejouable qu'avec la règle de
comptage qui l'a produit (une re-mesure à grammaire plus stricte donne 23/27, 3/17 et 3/44
pour `Basic`, `Framework` et `Voting` : lecture inchangée).

La règle exacte, telle qu'elle a produit le tableau ci-dessous (appliquée au code dont les
commentaires `--` et les blocs `/- … -/` imbriqués sont retirés et les attributs `@[ … ]`
effacés) :

```
(?:^|\n)[ \t]*(?:(?:private|protected|noncomputable|partial|unsafe|scoped|local|public)[ \t]+|@\[[^\]\n]*\][ \t]*)*
(theorem|lemma|def|abbrev|structure|inductive|class|instance)[ \t]+
([A-Za-z_][\w'!?]*(?:\.[A-Za-z_][\w'!?]*)*)?
```

Les instances sans nom (`instance : Foo`) sont écartées, faute de nom capturé. Un nom est
« présent dans l'amont » quand son **dernier composant** figure parmi les 188 noms distincts
des six fichiers `.lean` de `src/`. Cette règle reproduit les huit lignes du tableau, ce qui
rend la mesure rejouable en un passage.

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

**`Sen` n'est donc pas un portage** : l'amont n'a pas de `Sen` à porter (0 nom repris sur 4
déclarations), et la licence de l'amont ne départage par conséquent **rien** entre les deux
formalisations de Sen — celle de ce répertoire et celle de `lean_game_defs/SocialChoice.lean`,
toutes deux écrites par CoursIA. Les deux énoncés d'Arrow, eux, sont indépendants dans leur
forme et leur stratégie de preuve (voir la comparaison au README de `lean_game_defs`) ; seule
celle de ce répertoire est un portage mesuré.

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

Valeurs du port initial. Depuis la descente en lake autonome (#24183, T3, 2026-11-08),
le pin effectif est celui du lake lui-même
([`../lean-toolchain`](../lean-toolchain), `v4.33.0`) — repris tel quel du hub
`game_theory_lean` au moment du déplacement, ainsi que le pin Mathlib du manifeste.

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
dérivé est conservé en l'état, et la voie suivie est la demande de licence
à l'amont plutôt qu'un texte fabriqué : elle a été déposée le 2026-10-25
([asouther4/lean-social-choice#12](https://github.com/asouther4/lean-social-choice/issues/12))
et reste ouverte à cette date. C'est cette notice qu'il faudra mettre à
jour si la demande aboutit.
