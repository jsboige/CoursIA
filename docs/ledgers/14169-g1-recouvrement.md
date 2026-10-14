# Ledger G1 — Recouvrement 28 PRs amont endjin/Z3.Linq vs fork MyIntelligenceAgency/Z3.Linq

Sous-grain **G1** de l'EPIC #14169 (issue #16050). Suite directe du scanner préliminaire #16052 : ce ledger tranche les **18 PRs TBD** en verdicts définitifs et complète l'acceptance de #16050 (tableau 3 colonnes + `fichier:ligne` + faisabilité par `NOUVEAU-POUR-NOUS`).

## Base de mesure

| Objet | Valeur | Provenance |
|---|---|---|
| Fork mesuré | `MyIntelligenceAgency/Z3.Linq` @ **`20984bf`** | gitlink `main` courant |
| Pin cité par le body G1 | `e09dae6` | body #16050 (2026-09-13) |
| Écart `e09dae6..20984bf` | port d'**endjin#95** (DateTime round-trip via UTC ticks, PR #14594) + rebuild `.deploy` (#14605) + CI windows-latest | `git log e09dae6..20984bf` |

**Décision de périmètre** : G1-bis mesure contre `20984bf` — l'état que `main` porte — et non contre `e09dae6`. Conséquence immédiate documentée : la PR amont **#95 est déjà portée** dans le fork (`f0da578`, citée par #14594) ; son verdict se lit `REDONDANT` (équivalent livré par port, voir tableau).

## Pré-tri hérité du scanner (#16052)

22 PRs scannées sur les 28 du body EPIC : **1** EXCLU-TESTS (#74, aucun fichier hors `Z3.Linq.Tests/`), **3** INFRA build/packaging sans `*.cs` applicatif (#44, #45, #61 — non-bloquants, hors G1), **18** TBD → tranchées ci-dessous. Les 6 PRs tests-only pré-listées par l'EPIC (#48, #59, #65, #67, #69, #71) restent hors scope G1 par décision du body EPIC.

## Tableau des verdicts — 18 PRs TBD

Première passe par sous-agent (lecture diff + grep fork, preuves `fichier:ligne`), **adjudiquée par la lane** : verdict #86 ajusté de NOUVEAU-POUR-NOUS à DIVERGENT (voir note) — la sémantique statut-vs-solution existe déjà dans le fork via la surface `Explain` (`Explanation.cs:7-19`, `Theorem.cs:389-390` : « Unlike Solve() — which returns default(T) for every non-satisfiable outcome — this distinguishes the three Z3 statuses »), l'amont la livre sous la forme API TrySolve/TryOptimize : c'est la définition même du DIVERGENT. Les autres verdicts ont été confrontés à des greps indépendants de la lane (layout `solutions/Z3.Linq/`).

| # | Titre (abrégé) | Verdict | Évidence fork (`20984bf`) | Note |
|---|---|---|---|---|
| 47 | MiaPlaza.ExpressionUtils 1.2.0 → 1.3.1 + adaptation PartialEval | **NOUVEAU-POUR-NOUS** | `Z3.Linq.csproj:22` épingle 1.2.0 ; `ExpressionVisitor.cs:511` appelle la surcharge disparue en 1.3.x | Patch local propre (même call-site) |
| 73 | Model completion — symbole non contraint ne jette plus | **NOUVEAU-POUR-NOUS** | `Theorem.cs:653, 818, 826, 938, 1009` : `model.Eval(x)` sans `completion: true` (seul le witness fork `:202` l'active) | Port requis — 5 sites fork vs 4 upstream |
| 77 | MkReal invariant de culture | **REDONDANT** | `ExpressionVisitor.cs:866` `Convert.ToString(val, InvariantCulture)` (commentaire « B7, #4616 — the real-literal emission path ») | Même justification, livré indépendamment |
| 79 | Collection d'un field : `GetValue` au lieu du cast `FieldInfo` | **REDONDANT** | `Theorem.cs:635-636` `PropertyInfo.GetValue` / `FieldInfo.GetValue` | Livré sous une autre forme (délégation `ExtractCollection`) |
| 80 | Relire un float comme float (`float.Parse`) | **NOUVEAU-POUR-NOUS** | `Theorem.cs:678-679, 934-935` : `ParseRatNumAsDouble(...)` pour `TypeCode.Single` → double boxé → `ArgumentException` au `SetValue` (`:1061`) | Fix minimal (2 lignes) |
| 81 | Lire l'élément sélectionné, pas le tableau | **REDONDANT** | `Theorem.cs:938` évalue `numValExpr` (l'élément), jamais le tableau | — |
| 84 | DateTime relu en UTC (`FromFileTimeUtc`) | **REDONDANT** | via port #95 : `ExpressionVisitor.cs:1046` `ToUtcTicks`, `Theorem.cs:754` `new DateTime(ticks, DateTimeKind.Utc)` | Fork va plus loin (ticks > file time) |
| 86 | Statut de satisfiabilité séparé de la solution (TrySolve/TryOptimize/SolveOrNull/OptimizeOrNull) | **DIVERGENT** *(adjudiqué)* | Sémantique présente : `Explanation.cs:7-19` (Satisfiable/Unsatisfiable/Unknown, « gap B6 #4616 »), `Theorem.cs:389-390` `Explain()` ; formes Try\* absentes (`ISolveable{T}.cs:12` : seul `T? Solve()`) | La capacité (statut ≠ solution) existe via `Explain` ; l'API Try-pattern + intégration Solve/Optimize manque — sémantique voisine, surface différente |
| 88 | Symboles short et enum | **NOUVEAU-POUR-NOUS** (moitié marshalling) | Moitié visiteur **présente** (`ExpressionVisitor.cs:259-269`, Int16 par sort) ; marshalling : `Theorem.cs:660-662, 925-927` — `Int16` partage le bras `Int32` → int boxé → échec à l'écriture réflexive ; enum-int OK par conversion réflexe | Fix = bras `checked((short)…)` sur 2 sites |
| 90 | Sorts de collections = sorts scalaires | **REDONDANT** | `Theorem.cs:576-580` `GetArrayDomainSort` → `IntSort` ; `:585-605` range = sort scalaire | Sans les sorts BitVec/FP condamnés par upstream |
| 91 | Environnements anonymes via marshaller partagé | **NOUVEAU-POUR-NOUS** | `Theorem.cs:1007-1024` : branche anonyme avec marshaller bool/int dédié, `model.Eval(subEnv.Expr)` non gardé (`:1009`) | État pré-#75 ; le port réutilise `ConvertZ3Expression` (`:627+`) |
| 92 | Conversions numériques décidées par sort | **REDONDANT** | `ExpressionVisitor.cs:242-253` (cibles réelles) + `:259-269` (cibles entières) : dispatch sur le sort runtime | Couvre Single/Decimal/Int16/Int64 qu'upstream n'avait pas |
| 93 | Instance de `NewTheorem` = template (taille des collections) | **NOUVEAU-POUR-NOUS** | `Z3Context.cs:139-142` jette l'instance (`dummy`) ; grep `Template` = 0 ; sémantique fork d'une collection nulle = **collection vide silencieuse** (`Theorem.cs:771-778`) — troisième voie, ni NRE ni rejet nommé | Le port doit trancher cette sémantique |
| 94 | Documentation XML générée + doc-comments | **HORS-CAPACITE** | hunks = `.props`/`.csproj` + commentaires uniquement ; `GenerateDocumentationFile` absent du fork | Hygiène de build, zéro code de capacité |
| 95 | DateTime en ticks UTC (plage 0001-9999, garde) | **REDONDANT** | **Port déjà livré** : `f0da578` (ancêtre du pin, vérifié `merge-base --is-ancestor`) — `ExpressionVisitor.cs:1046-1049, 868`, `Theorem.cs:744-757, 936` | C'est le bump #14594 ; motive l'écart `e09dae6..20984bf` |
| 96 | Solve borné + `TheoremUndecidedException` + `CancellationToken` | **NOUVEAU-POUR-NOUS** | grep `Timeout|ResourceLimit|CancellationToken|rlimit` = 0 dans la capa ; `Theorem.cs:154` : UNKNOWN avalé en `default` | Le plus proche = `Explain` (statut Unknown exposé) — ne couvre ni Solve/Optimize ni les limites. **Dépend de #86** |
| 98 | Bornes de plage CLR sur entiers/DateTime (AssertBounds) | **NOUVEAU-POUR-NOUS** | grep `AssertBounds|MkGe|MkLe` = 0 ; entiers non bornés documentés (`Theorem.cs:737-738`) ; seule la garde read-side héritée de #95 (`:746`) | Hook prêt : `AssertConstraints<T>` (`Theorem.cs:256`, appelé `:147/:155/:223`) ; exclure les symboles BitVec fork (bornés par largeur) |
| 99 | Ternaire → MkIte ; diagnostics bitwise/modulo | **REDONDANT** (capacité) | Ternaire présent : `ExpressionVisitor.cs:107-108, 212-218` MkIte (« gap B2, #4616 ») ; manquent 2 messages de diagnostic plus honnêtes (`:29-38, :62-63`) | Non-bloquant |

## Synthèse chiffrée

| Verdict | Compte | PRs |
|---|---:|---|
| REDONDANT | **8** | #77, #79, #81, #84, #90, #92, #95, #99 |
| NOUVEAU-POUR-NOUS | **8** | #47, #73, #80, #88, #91, #93, #96, #98 |
| DIVERGENT | **1** | #86 |
| HORS-CAPACITE | **1** | #94 |

*Note de décompte* : #99 est REDONDANT en **capacité** (le ternaire — cœur du PR — est dans le fork) ; les deux raffinements de diagnostic manquants sont non-bloquants et suivis en note. Les 8 NOUVEAU se répartissent en **patches locaux** (#47, #80, #88-moitié-marshalling) et **ports structurels** (#73, #91, #93, #96, #98) ; la moitié API de #86 (Try-pattern) s'y ajoute si l'arbitrage DIVERGENT évolue vers un port.

## Notes de faisabilité (NOUVEAU-POUR-NOUS)

| # | Faisabilité du port | Détail |
|---|---|---|
| 47 | **Rebasable direct** | Le diff adapte le call-site `PartialEvaluator.PartialEval` (`ExpressionVisitor.cs:511`) qui existe à l'identique ; monter la version package suffit + le wrap-lambda |
| 80 | **Rebasable direct** | 2 lignes (`float.Parse` sur les 2 bras `TypeCode.Single`) |
| 88 | **Rebasable direct (partiel)** | Bras `checked((short)…)` sur `Theorem.cs:660-662` et `:925-927` ; le volet enum est déjà couvert par conversion réflexe |
| 73 | **Port requis** | 5 sites fork (structure `ExtractCollection`/`ConvertScalarExpr`) vs 4 upstream ; activer `completion: true` à chaque lecture modèle |
| 91 | **Port requis** | Remplacer le marshaller bool/int dédié par `ConvertZ3Expression` (existe `Theorem.cs:627+`) ; corrige au passage le null des objets imbriqués ; se renforce avec #73 |
| 93 | **Port + décision** | Le port doit trancher la sémantique fork « collection nulle = collection vide silencieuse » vs rejet nommé upstream |
| 96 | **Port requis, dépend de #86** | Le `CancellationToken` chevauche les signatures TrySolve/TryOptimize de #86 ; à porter ensemble |
| 98 | **Port requis** | Hook `AssertConstraints<T>` prêt ; gérer les Environment étendus fork (MultipleEnvironment, constants-mode) et exclure les symboles BitVec (déjà bornés par largeur) |

## Déblocage G2-G5

L'acceptance 4 de #16050 est satisfaite par ce ledger : G2 (notre PR upstream #43), G3, G4, G5 peuvent s'ouvrir. Rappel des garde-fous G1 : aucune PR sortante sans feu vert user (G4), pas de bump de submodule tant que G1 n'est pas rendu — G1 est rendu avec ce document.

## Méthode

Pour chaque PR : lecture du diff amont (fichiers de capacité, hors tests/README/build), recherche de l'équivalent dans le fork à `20984bf` (`git grep` / lecture `git show 20984bf:<fichier>`), verdict par la sémantique du code, pas par le titre. Preuve `fichier:ligne` exigée des deux côtés. Les verdicts `A-TRANCHER` du premier passage ont été arbitré à la lecture directe.
