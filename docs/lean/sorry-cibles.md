# Sorry-cibles documentés — format et usage

Règle courte : [`.claude/rules/anti-regression.md`](../../.claude/rules/anti-regression.md), section « Sorry-cibles documentés ». Cette note en donne le format, les niveaux et le lien avec le harnais prover.

## Pourquoi

Mandat user du 2026-11-03, verbatim :

> « si on manque de sorry, notamment parce qu'on a fait l'effort de ne pas en truffer de partout, c'est peut-être le moment de réviser notre politique, quelques sorry de difficultés variées documentés étant tout à fait acceptable dans chacune de nos sous-séries »

Le harnais prover (`MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/prover/`, ping-pong #1453) sert à comparer plusieurs modèles sur les mêmes cibles. Il tourne sur des modèles chinois bon marché, sur Swift et Ornith-1.5-9B en local, et sur les petits et grands modèles d'OpenAI et d'Anthropic. Pour que cette comparaison dise quelque chose, il faut des cibles **réelles** et **graduées** dans nos lakes. Les démos de calibration ne suffisent pas. La retenue qui a gardé les lakes presque sans `sorry` a laissé le harnais sans gradient sur notre propre matière.

## Ce qui reste interdit

La règle HARD d'anti-régression ne change pas :

- remplacer une preuve existante par un `sorry` reste une régression, avec ou sans ligne de cible ;
- un module listé dans un `CERTIFIED.txt` (organe `scripts/lean/check_certified_sorry.py`) reste à 0 `sorry` ; une cible se pose dans un module non certifié ou explicitement exclu (`!nom.lean`) ;
- un `sorry` sans ligne de cible reste une PR contestée.

## Format

La docstring du théorème porte une ligne de cible :

```lean
/-- Unicité de l'équilibre dans le jeu à deux joueurs symétrique.

Cible prover : medium — `simp` puis `omega` échouent sur le cas `n = 0`,
le lemme `Finset.sum_comm` est probablement la clé. -/
theorem equilibre_unique (n : ℕ) : ... := by
  sorry
```

Le jumeau anglais (convention [lean-i18n](../../.claude/rules/lean-i18n.md)) porte la même ligne en anglais : `Prover target: medium — ...`. Les deux fichiers ne diffèrent que par leurs commentaires.

La ligne dit deux choses : le **niveau**, et **ce qui a déjà été tenté**. Sans la seconde, la cible n'apprend rien au harnais ni au lecteur.

## Niveaux

La ligne de cible retient quatre niveaux. Le champ `difficulty` des `DEMOS` du harnais (`prover/config.py`) en emploie neuf ; une démo se range dans la grille ci-dessous par la projection suivante : `trivial` et `simple` vers `easy`, `intermediate` vers `medium`, `advanced` vers `hard`, `open_problem` vers `very_hard`.

| Niveau | Ce que la preuve demande, à titre indicatif |
|---|---|
| `easy` | une tactique de bibliothèque (`simp`, `omega`, `decide`, `norm_num`) ou deux |
| `medium` | quelques lemmes Mathlib composés, une induction simple |
| `hard` | un lemme intermédiaire à inventer, une preuve de plusieurs dizaines de lignes |
| `very_hard` | une formalisation longue, ou un résultat de recherche |

Un `sorry` inscrit dans `HONEST_SORRIES` (`prover/config.py`) n'est **pas** une cible : il documente une barrière (classe `INTRINSIC`, #4039) que le harnais refuse d'attaquer. Il ne porte donc pas de ligne `Cible prover`. `very_hard` désigne une preuve difficile mais attendue ; une barrière connue relève du registre, pas de la grille.

« De difficultés variées » se lit sur la sous-série : ses cibles couvrent au moins deux niveaux. Une sous-série dont toutes les cibles sont `very_hard` ne mesure rien de plus qu'une sous-série sans cible.

## Compter et lister

- Compte réel avant/après, dans le body de la PR : `python scripts/lean/count_code_sorry.py --json`, champ `distinct_code_sorry` ([pr-review-discipline](../../.claude/rules/pr-review-discipline.md) §B.1).
- Le plancher du lake monte dans la même PR : `sorry-baseline` du workflow appelant `lean-build.yml`, ou entrée du lake dans `scripts/lean/ci_lakes.json`. La gate est bidirectionnelle : quand une cible est prouvée, le plancher redescend dans la PR de preuve.
- Inventaire des cibles : `git grep -n -i -e "cible prover" -e "prover target" -- "*.lean"`. Le motif est volontairement large : il retrouve aussi les cibles posées avant cette note sous des formes voisines (`-- PROVER TARGET:`, `BG-prover target`, `(cible prover BG)`). Les nouvelles cibles prennent le format ci-dessus.

## Ce qui n'existe pas encore

Aucun contrôle CI ne vérifie qu'un `sorry` ajouté porte sa ligne de cible. D'ici là, c'est la review qui le vérifie (§B.1 et cette note). Si l'oubli se répète, il faudra écrire ce contrôle, et non allonger cette note.
