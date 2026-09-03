# Z3.Linq — recouvrement fork / amont (grain G1 de #14169)

**Mesure du 2026-09-03**, `endjin/Z3.Linq` (amont) vs `MyIntelligenceAgency/Z3.Linq` @ `e09dae6db773`
(sous-module `MyIA.AI.Notebooks/SymbolicAI/SMT/Z3.Linq`).

Ce fichier rend le grain **G1** de [#14169](https://github.com/jsboige/CoursIA/issues/14169) : pour chaque
PR amont ouverte, dire si la capacité existe déjà chez nous, et où. Il est le préalable déclaré de **G3**
(trancher la posture de fork) — il ne tranche rien lui-même.

## Ce que la mesure corrige d'abord : le compte

#14169 a été rédigée le 2026-09-01 sur **28 PRs** amont. Au 2026-09-03, `endjin/Z3.Linq` porte **42 PRs
ouvertes** ; le périmètre de ce ledger en retient **39** :

| Écarté | Pourquoi |
|---|---|
| #40 (`dependjinbot`, 2024-05-14), #42 (`dependabot`, 2026-08-25) | bumps de dépendance automatiques, pas des propositions de conception |
| #43 (`jsboige`, 2026-09-01) | **la nôtre** — c'est le grain G2, pas une PR amont à recouvrir |

Restent **39 PRs amont substantielles, #44 à #110** — soit **11 de plus que l'issue en deux jours**, dont
un bloc de refactoring du chemin de solve (#105-#109) et une conversion des démos (#110) qui n'existaient
pas quand l'issue a été écrite. L'amont n'a pas ralenti : il accélère.

Conséquence directe pour G3 : toute mesure de recouvrement est **datée**, celle-ci comprise. Elle se
refait avant de décider, elle ne se cite pas dans six semaines.

## Verdicts

Quatre valeurs. Les trois premières sont celles de #14169 ; la quatrième a dû être ajoutée parce que le
schéma à trois colonnes ne pouvait pas exprimer le résultat le plus important — **ce que nous avons et
que l'amont n'a pas**.

| Verdict | Sens |
|---|---|
| `REDONDANT` | même défaut, même correctif, atteint des deux côtés indépendamment |
| `DIVERGENT` | même capacité, **conception différente** — c'est là qu'un rebase fait mal |
| `NOUVEAU-POUR-NOUS` | l'amont apporte ce que notre fork n'a pas |
| `NOTRE-AVANCE` | nous l'avons, **aucune PR amont ne le touche** |

Les chemins de la colonne « notre équivalent » sont relatifs à la racine du sous-module ; le code du
fork vit sous `solutions/`, pas à la racine.

### Infrastructure et build

| PR amont | Notre équivalent | Verdict |
|---|---|---|
| #44 migration build ZeroFailed | — | `NOUVEAU-POUR-NOUS` |
| #45 .NET 10, Central Package Management, `.slnx` | `solutions/Z3.Linq/Z3.Linq.csproj` (format classique) | `NOUVEAU-POUR-NOUS` |
| #47 MiaPlaza.ExpressionUtils 1.3.1 (+ rupture d'API) | `solutions/Z3.Linq/ExpressionVisitor.cs` | `NOUVEAU-POUR-NOUS` |
| **#61 Microsoft.Z3 5.1.0 — binaires natifs Linux et arm64** | pin actuel Windows-x64 | `NOUVEAU-POUR-NOUS` **(le plus utile)** |
| #94 génération + validation de la doc XML | — | `NOUVEAU-POUR-NOUS` |
| #104 suite BenchmarkDotNet | `solutions/pb-bench/Program.cs` | `DIVERGENT` |
| #110 démos Spectre.Console mono-fichier | `solutions/Z3.Linq.Demo/Program.cs` | `DIVERGENT` **(voir Risques)** |

### Suite de tests amont (phase A) — aucun équivalent chez nous

#48 (Distinct partial-eval), #59 (solve + composition), #65 (marshalling), #67 (Optimize / OrderBy),
#69 (modes d'échec + rewriters), #71 (acceptance Sudoku + river crossing).

Tous `NOUVEAU-POUR-NOUS`. Nos 14 fichiers de tests (`solutions/Z3.Linq.Tests/`) couvrent **nos**
extensions — PB pondéré, UNSAT-core, bit-vectors, rationnels ; ils ne couvrent pas le noyau que ces six
PRs testent. Les deux suites sont **complémentaires**, pas concurrentes.

### Marshalling et sémantique — la zone de collision

| PR amont | Notre équivalent | Verdict |
|---|---|---|
| #73 peupler les symboles non interprétés | — | `NOUVEAU-POUR-NOUS` |
| #74 retirer les contraintes qui contournaient #51 | — | `NOUVEAU-POUR-NOUS` |
| **#77 constantes réelles en culture invariante** | `solutions/Z3.Linq/ExpressionVisitor.cs:866` | **`REDONDANT`** |
| #79 lire la valeur d'un champ de collection | `solutions/Z3.Linq/Environment.cs:12` (`CollectionHandling`) | `DIVERGENT` |
| #80 relire un float en float | `solutions/Z3.Linq/Theorem.cs:858-865` (chemin de lecture) | `DIVERGENT` |
| #81 lire l'élément décimal sélectionné | `solutions/Z3.Linq.Tests/RationalExactTests.cs` | `DIVERGENT` |
| #84 relire un DateTime en UTC | `solutions/Z3.Linq/ExpressionVisitor.cs:867-868` | `DIVERGENT` |
| **#86 satisfiabilité rapportée séparément** | `solutions/Z3.Linq/Explanation.cs:59` (`IsSatisfiable`) | **`DIVERGENT`** |
| #88 symboles `short` et `enum` | — | `NOUVEAU-POUR-NOUS` |
| #90 collections aux mêmes sortes que les scalaires | `solutions/Z3.Linq/Environment.cs:12` | `DIVERGENT` |
| #91 environnements anonymes | `solutions/Z3.Linq/Environment.cs:18`, `RecordEnvTheoryTests.cs` | `DIVERGENT` |
| #92 conversions numériques par sorte | `solutions/Z3.Linq/ExpressionVisitor.cs:258-264`, `Rational.cs` | `DIVERGENT` |
| #93 dimensionner les collections depuis l'instance | `solutions/Z3.Linq/Z3Context.cs` | `DIVERGENT` |
| **#95 DateTime encodé en ticks (et non en file time)** | `solutions/Z3.Linq/ExpressionVisitor.cs:868` | **`DIVERGENT` — défaut vivant, voir ci-dessous** |
| #96 solve borné + « Z3 n'a pas pu décider » | `solutions/Z3.Linq/Explanation.cs:20` (`Unknown`) | `DIVERGENT` |
| #98 borner chaque entier à la plage de son type | — | `NOUVEAU-POUR-NOUS` |
| **#99 ternaires + modulo réel/bitwise** | `solutions/Z3.Linq/ExpressionVisitor.cs:107-108, 204-212` (`MkIte`) | **`DIVERGENT`** |
| #100 visiteur en classe interne d'instance | `solutions/Z3.Linq/ExpressionVisitor.cs` (statique) | `DIVERGENT` |
| #101 `uint`/`ulong` en bit-vectors | `solutions/Z3.Linq/BitVecWidthAttribute.cs`, `Theorem.cs:555-559` | `DIVERGENT` |
| #102 `byte`/`sbyte`/`ushort` | — (0 occurrence) | `NOUVEAU-POUR-NOUS` |
| #103 deux défauts du code de solve-limits | suit #96 | `DIVERGENT` |
| #105 cache de réflexion par type | — | `NOUVEAU-POUR-NOUS` |
| #106 idiomes C# 14 sur le chemin de solve | — | `NOUVEAU-POUR-NOUS` |
| #107 extraction `MemberClrType` | — | `NOUVEAU-POUR-NOUS` |
| #108 extraction `Assert` | — | `NOUVEAU-POUR-NOUS` |
| #109 fusion des marshallers en `ReadZ3Value` | `solutions/Z3.Linq/Theorem.cs` (−133 lignes amont) | `DIVERGENT` |

## Le résultat qui ne rentrait pas dans le schéma : `NOTRE-AVANCE`

Onze sondes passées sur l'inventaire des fichiers touchés par les **39** PRs amont. Aucune de ces
capacités n'est touchée par aucune d'elles :

| Notre capacité | Où elle vit (`solutions/`) | PRs amont qui y touchent |
|---|---|---|
| UNSAT-core / explication | `Z3.Linq/Explanation.cs`, `Z3.Linq.Tests/ExplainUnsatCoreTests.cs` | aucune |
| Pseudo-booléen pondéré | `Z3.Linq.Tests/WeightedPbTests.cs`, `UnweightedPbTests.cs` | aucune |
| Bench PB natif vs `MkIte`+`MkAdd` | `pb-bench/Program.cs` | aucune |
| Largeur de bit-vector déclarée | `Z3.Linq/BitVecWidthAttribute.cs` | aucune |
| Choix du solveur | `Z3.Linq/SolverKind.cs` | aucune |
| Quantificateurs bornés | `Z3.Linq.Tests/BoundedQuantifierTests.cs` | aucune |
| `Sum` variadique | `Z3.Linq.Tests/SumVariadicTests.cs` | aucune |
| MaxSAT / contraintes souples | `Z3.Linq.Tests/AssertSoftMaxSatTests.cs` | aucune |
| Rationnels exacts | `Z3.Linq/Rational.cs`, `Z3.Linq.Tests/RationalExactTests.cs` | aucune |

**Le fork n'est pas en retard sur l'amont : il est ailleurs.** L'amont durcit le **noyau** (marshalling,
sortes, tests, build) ; nous avons construit des **capacités de modélisation** au-dessus. C'est le fait
qui rend G3 décidable, et il pointe vers « suivre l'amont sur le noyau, garder nos capacités » plutôt que
vers un choix binaire suivre/diverger.

## Un défaut vivant, trouvé en mesurant (#95)

L'amont ne fait pas que changer un encodage : il en donne la raison, et elle nous vise.

```
-  return context.MkInt(((DateTime)val).ToFileTimeUtc());
+  // ... A Windows file time counted from 1601 instead, so nothing earlier
+  //     could be written or read. See #83.
+  return context.MkInt(ToUtcTicks((DateTime)val));
```

Notre fork exécute **exactement** la ligne retirée, à `solutions/Z3.Linq/ExpressionVisitor.cs:868`. Notre
fork ne peut donc aujourd'hui **ni encoder ni relire une date antérieure à 1601** — silencieusement. Ce
n'est pas une divergence de style, c'est un défaut de domaine que nous portons.

Non corrigé ici : #14169 interdit de toucher au fork tant que G1 n'est pas rendu et que les PRs amont ne
sont pas atterries. **Le correctif se prend en aval de G3** ; le constat est consigné pour que la décision
le voie.

## Convergence indépendante (#77)

Amont : `MkReal(val.ToString())` → `InvariantCulture`, motivé par leur #52.
Nous : déjà `MkReal(Convert.ToString(val, CultureInfo.InvariantCulture))`, motivé par notre #4616
(`solutions/Z3.Linq/ExpressionVisitor.cs:861-866`, le commentaire de la ligne 864 nomme le défaut).

Le même défaut — le séparateur décimal d'une culture non anglophone que le parseur Z3 rejette — a été
trouvé et corrigé **des deux côtés, sans contact**. C'est le meilleur argument disponible pour la
convergence : deux équipes qui butent sur la même pierre valident la pierre.

## Risque à signaler avant tout bump (#110)

#110 **supprime** `examples/z3-problems.dib` (420 lignes) et `solutions/Z3.Linq.Demo/Program.cs`
(310 lignes) au profit de démos `demos/*.cs` Spectre.Console.

La surface exposée chez nous se compte, elle ne s'arrondit pas — sur les 18 notebooks de
`SMT/Z3-Linq2Z3/` :

| Dépendance au répertoire `../Z3.Linq/.deploy/` | Notebooks |
|---|---|
| `#r "../Z3.Linq/.deploy/Z3.Linq.dll"` (+ `Microsoft.Z3.dll`, `ExpressionUtils.dll`) | **16** |
| `Microsoft.Z3.dll` seul, sans `Z3.Linq.dll` (`10_Witness_Generation_Automata`) | 1 |
| aucun `#r` (`07_Meal_Planner_Data_External`) | 1 |

**17 des 18** dépendent donc du répertoire `.deploy/`, qui est **notre** convention de fork (produite
par `deploy.ps1` / `deploy.sh`), pas une convention amont. Un rebase qui absorbe #110 sans vérifier ce
chemin casse dix-sept notebooks d'un coup. G5 de #14169 couvre leur ré-exécution ; ce paragraphe nomme
la cause à surveiller.

## Portée de la mesure — ce qu'elle ne dit pas

- **Notre côté est ancré dans le code** : chaque `file:line` ci-dessus a été lu sur `e09dae6db773` au
  moment d'écrire ce fichier.
- **Le côté amont est ancré au niveau de l'inventaire des fichiers modifiés** (chemin, lignes
  ajoutées/retirées) pour les 39 PRs, et **au niveau du diff** pour les quatre rangées décisives
  (#77, #86, #95, #99) uniquement. Les verdicts `DIVERGENT` des autres rangées disent « même zone,
  conception différente », **pas** « j'ai relu les 39 diffs ligne à ligne ».
- Aucune PR amont n'est **mergée** : les 39 sont OPEN. Un verdict peut donc changer si le mainteneur
  révise avant merge.
- Les PRs amont fermées ou mergées avant #44 (historique 2024) sont hors mesure.

## Reproduction

```bash
gh pr list --repo endjin/Z3.Linq --state all --limit 120 \
  --json number,state,title \
  --jq '.[]|select(.state=="OPEN")|"\(.number)\t\(.title)"' | sort -n

gh api repos/endjin/Z3.Linq/pulls/<N>/files --paginate \
  --jq '.[]|"\(.additions)\t\(.deletions)\t\(.filename)"'

cd MyIA.AI.Notebooks/SymbolicAI/SMT/Z3.Linq/solutions && grep -rn --include=*.cs "<symbole>" .
```

## Voir aussi

- **#14169** — EPIC (G2 suivre notre PR amont #43 · G3 posture de fork · G4 proposer · G5 notebooks)
- **#1206** — EPIC parent ; `endjin/Z3.Linq#29` est notre issue d'origine (2023)
- [`.claude/rules/submodule-maintenance.md`](../../.claude/rules/submodule-maintenance.md) — les cinq
  sous-modules, ordre commit / push / bump
