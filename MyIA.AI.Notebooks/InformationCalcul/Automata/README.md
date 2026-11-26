# Automata — Automates et langages formels

Cette série part d'une machine très simple — un nombre fini d'états, aucune autre mémoire
que l'état courant — pour construire ensuite les langages qu'elle reconnaît, les expressions
qui les décrivent et les machines plus générales qui dépassent ses limites. Chaque notion est
**exécutée et confrontée à une référence indépendante**, plutôt que seulement énoncée.

Le fil rejoint directement les carnets de calculabilité et de complexité du hub : un automate
fini donne un exemple concret de machine dont le comportement peut être énuméré, minimisé et
comparé. Il sert aussi de socle aux automates symboliques, à l'apprentissage actif et aux
expressions régulières manipulées par les solveurs du dépôt.

## Objectifs d'apprentissage

À l'issue de la série, vous serez capable de :

1. **Reconnaître** un mot avec un automate déterministe ou non déterministe, y compris avec
   des epsilon-transitions.
2. **Déterminiser** un AFN par la construction des sous-ensembles de Rabin–Scott et mesurer
   que son langage est préservé.
3. **Minimiser** un AFD par l'algorithme de Hopcroft et relier les classes obtenues à
   l'unicité de Myhill–Nerode.
4. **Passer** entre automates et expressions régulières, puis reconnaître les limites des
   langages réguliers avant d'aborder machines de Turing et décidabilité.

## Notebooks

| Notebook | Public | Ce qu'on y apprend | Langue |
| --- | --- | --- | --- |
| [`Automata-01-AutomatesFinis-Python.ipynb`](Automata-01-AutomatesFinis-Python.ipynb) | Découverte | AFD et AFN, epsilon-clôture, déterminisation de Rabin–Scott, minimisation de Hopcroft ; vérification exhaustive de la parité et du suffixe `abb`, minimalité mesurée sur des présentations redondantes ; trois exercices | Français |
| [`Automata-01-AutomatesFinis-CSharp.ipynb`](Automata-01-AutomatesFinis-CSharp.ipynb) | Découverte | Jumeau .NET/C# du carnet précédent, BCL uniquement ; mêmes exemples, mêmes références externes et trois exercices répartis | Français |
| [`Automata-02-ExpressionsRegulieres-Python.ipynb`](Automata-02-ExpressionsRegulieres-Python.ipynb) | Découverte | Le théorème de Kleene dans les deux sens : arbre d'expression et construction de Thompson (expression vers AFN, deux états par nœud), élimination d'états (automate vers expression), aller-retour vérifié mot par mot contre `re.fullmatch`, coût mesuré sur deux familles paramétrées (AFD à `2^(n+1)` états, deux ordres d'élimination) ; trois exercices | Français |
| [`Automata-02-ExpressionsRegulieres-CSharp.ipynb`](Automata-02-ExpressionsRegulieres-CSharp.ipynb) | Découverte | Jumeau .NET/C# du carnet précédent, BCL uniquement, `Regex.IsMatch` ancré comme oracle ; mêmes constructions, mêmes mesures et trois exercices répartis | Français |

## Jumeau Python/C# — Automata-01

- [Version Python](Automata-01-AutomatesFinis-Python.ipynb)
- [Version C#](Automata-01-AutomatesFinis-CSharp.ipynb)

Les deux carnets parcourent les mêmes exemples déterministes : 2047 mots sur `{0,1}` pour
l'AFD de parité, 1023 mots sur `{a,b}` pour l'AFN du suffixe `abb`, avec zéro divergence
contre les références externes. La minimisation du cycle redondant produit deux classes dans
les deux langages. L'implémentation pédagogique est écrite à partir de zéro ; elle ne prétend
pas remplacer une bibliothèque d'automates de production.

## Jumeau Python/C# — Automata-02

- [Version Python](Automata-02-ExpressionsRegulieres-Python.ipynb)
- [Version C#](Automata-02-ExpressionsRegulieres-CSharp.ipynb)

Les deux carnets construisent et déconstruisent les mêmes automates : 20 états d'AFN pour
`(a|b)*abb` (deux par nœud), 5 états d'AFD après déterminisation et 4 classes d'états
équivalents, 127 mots acceptés sur 1023 ; les deux expressions produites par élimination
d'états (`0*|0*1(0|10*1)*10*` et `1*00*1(0|1)*`) coïncident à l'identique, de même que les
deux tables de coût — 513 états d'AFD pour `n = 8`, et 44 nœuds dans l'ordre inverse contre
634 dans l'ordre naturel. L'oracle externe diffère par la bibliothèque (`re.fullmatch` d'un
côté, `Regex.IsMatch` ancré de l'autre) ; les verdicts, eux, coïncident mot pour mot.

## Parcours

La série se lit dans l'ordre numérique. **Automata-01** est autonome : seules les collections
et itérateurs du langage choisi sont nécessaires. **Automata-02** ne suppose que ses
définitions (AFD, AFN, epsilon-transition) et apporte le pont entre les deux notations. Les
positions suivantes traiteront les automates à pile et les grammaires, puis les machines de
Turing et la décidabilité, selon la progression de l'EPIC
[#27158](https://github.com/jsboige/CoursIA/issues/27158).

## Liens avec les séries existantes

- [Complexity](../Complexity/README.md) : machines, coût du calcul et frontières de la
  calculabilité ; les automates finis fournissent ici le premier modèle exécutable.
- [Search-10 — automates symboliques](../../Search/Part1-Foundations/Search-10-SymbolicAutomata.ipynb)
  : généraliser les transitions à des prédicats.
- [SL-10 — apprentissage actif d'automates](../../SymbolicAI/SymbolicLearning/SL-10-ActiveAutomataLearning.ipynb)
  : apprendre un AFD par requêtes plutôt que le donner explicitement.
- [Lean-14 — finitude et dérivées](../../SymbolicAI/Lean/Lean-14-Finiteness-Derivatives.ipynb)
  : la route algébrique des dérivées de Brzozowski et son pendant formel.
- [Z3-04 — chaînes et regex](../../SymbolicAI/SMT/Z3-API/Z3-04-Strings-Regex-Python.ipynb) : le
  même objet, mais comme contrainte que le solveur décide plutôt que comme programme qu'on
  exécute — le pendant symbolique des conversions d'`Automata-02`.
