# `dotnet-build/` — Recette de build des runtimes Tweety C# / IKVM

Ce dossier contient les **recettes de build** (POM shade + csproj) des runtimes .NET de Tweety.
Depuis l'alignement #19673, les **5 recettes « famille A »** (`pl`, `aspic`, `beliefdynamics`,
`dung`, `preferences`) déclarent **IKVM 8.15.0** — elles suivaient encore 8.14.0 alors que leurs
DLL committées référencent `IKVM.Runtime 8.15.0` (les recettes ne reproduisaient pas les binaires
livrés) ; les 14 autres recettes du dossier demeurent en 8.14.0. La cible de recompilation post-C190 (`JvmDowngrader`, bytecode Java 15→8) est
inchangée : la contrainte bytecode Java 8 (section suivante) porte sur le contenu du fat-jar.
La mesure runtime #19673 établit par ailleurs qu'une DLL bâtie sous 8.14.0 charge intégralement
sous runtime 8.15.0 (types exposés et instanciables). Toutes les recettes ciblent
`net8.0`. Chaque runtime compilé (`org.tweetyproject.tweety-<module>.dll`) est placé
**à côté du notebook** qui le charge.

## Fichiers — cluster `pl` (notebook [`../Tweety-02-Basic-Logics-CSharp.ipynb`](../Tweety-02-Basic-Logics-CSharp.ipynb))

| Fichier | Rôle | Committé ? |
|---------|------|-----------|
| `org.tweetyproject.tweety-pl.dll` (7.6 MB) | **Runtime** .NET de Tweety cluster `pl` (chargé par le notebook via `#r`) | Oui (pattern #4711) |
| `tweety-pl-full-1.30.jar` (6.9 MB) | Fat-jar Maven shade (artefact de build intermédiaire) | Non (gitignoré, reconstruit ci-dessous) |
| `build-tweety-pl-shade.pom.xml` | POM aggregator Maven shade (produit le fat-jar) | Oui (reproductibilité) |
| `build-TweetyShade.csproj` | Projet MSBuild `<IkvmReference>` (convertit le fat-jar en DLL) | Oui (reproductibilité) |

## Fichiers — cluster `beliefdynamics` (notebook [`../Tweety-04-Belief-Revision-CSharp.ipynb`](../Tweety-04-Belief-Revision-CSharp.ipynb))

| Fichier | Rôle | Committé ? |
|---------|------|-----------|
| `org.tweetyproject.tweety-beliefdynamics.dll` (10.3 MB) | **Runtime** .NET des opérateurs AGM (contraction, révision de Levi) | Oui (pattern #4711) |
| `tweety-beliefdynamics-full-1.30.jar` (9.6 MB) | Fat-jar Maven shade (artefact intermédiaire) | Non (gitignoré, reconstruit ci-dessous) |
| `build-tweety-beliefdynamics-shade.pom.xml` | POM aggregator Maven shade | Oui (reproductibilité) |
| `build-TweetyBeliefDynamicsShade.csproj` | Projet MSBuild `<IkvmReference>` | Oui (reproductibilité) |

### Contrainte bytecode Java 8 (piège majeur du cluster `beliefdynamics`)

IKVM 8.15 est un runtime **Java 8** : il **saute silencieusement** toute classe compilée en
bytecode major > 52 (Java 9+), avec un warning `IKVM0101 class format error "55.0"`. Le pom parent
de Tweety v1.30 compile par défaut en `source`/`target` **15** (plugin 2.3.2, bytecode major 59) →
**les opérateurs de révision seraient absents de la DLL**. La recette rebuild patche le pom parent
(maven-compiler-plugin 2.3.2 → 3.13.0, `source`/`target` 15 → `<release>8</release>`) avant
`mvn install` du module `beliefdynamics`, garantissant du major-52 IKVM-compilable. Vérification : `od -An -tu1 -j6 -N2 LeviMultipleBaseRevisionOperator.class` doit
afficher `52`.

## Recette de rebuild (si la DLL doit être régénérée)

Prérequis : JDK 17 (`JAVA_HOME`), Maven 3.9+, .NET SDK 8.0+, git. Tout le reste est automatisé par
[`rebuild-familyA-maven.sh`](rebuild-familyA-maven.sh), qui rejoue la chaîne complète mesurée sur #19673 :

1. **Clone** `TweetyProjectTeam/TweetyProject` tag `v1.30` (repo renommé — l'ancien nom 404) sous `.familyA-clone/`.
2. **Patchs idempotents Java 8** : parent pom (compiler 2.3.2 → 3.13.0, `<release>8</release>`) + les fichiers
   sources touchés (`Files.readString`/`Path.of`/`isBlank`/`strip`, switch-fléchés → if-else, `var` → types explicites)
   + suppressions ciblées (exemples `logics-pl`/`beliefdynamics`, `CmdLineSatSolver`, reasoners SAT/`SerialisedExtensionReasoner` — miroir de la stratégie `DUNG_130_EXCLUDE` de `rebuild-5shades.sh`).
3. **`mvn install -DskipTests`** sur les modules tête (`logics-pl`, `arg-dung`, `arg-aspic`, `beliefdynamics`)
   avec `-am` : **fermeture mesurée de la clôture transitive** (commons, math, logics-commons, plugin, logics-fol, agents,
   logics-pl, graphs, arg-dung, arg-deductive, comparator, beliefdynamics, arg-aspic), tous vérifiés bytecode major 52.
4. **Shade** des 4 poms (`mvn -f build-tweety-*-shade.pom.xml clean package`), copie immédiate du fat-jar —
   les 4 poms partagent `target/`, chaque `clean` efface le précédent.
5. **`dotnet build`** des 4 csproj (vider `$TMP/ikvm/cache/1/` avant — cache MSBuild keyé sur le hash du jar).
6. **Audit bytecode** des fat-jars (major ≤ 52 exigé).

```bash
bash rebuild-familyA-maven.sh
# 4 DLLs dans bin/Release/net8.0/, à copier à côté des notebooks
```

### Écarts mesurés DLL rebâties vs committées (sonde #19673)

La chaîne Maven **ne reproduit pas byte-identique** les DLL committées (bâties par la chaîne javac
manuelle `rebuild-5shades.sh`) ; les écarts de types publics `org.tweetyproject.*`, tous identifiés,
vont dans les deux sens et **aucun type consommé par les carnets n'est touché** (les 40
`Simple*Reasoner` de `arg.dung.reasoner` sont intacts des deux côtés) :

| DLL | tweety types committée → rebâtie | Retirés (patch Java 8) | Ajoutés (fermeture Maven complète) |
|-----|-----------------------------------|------------------------|------------------------------------|
| pl | 437 → 415 | 21 exemples `logics.pl.examples` + `CmdLineSatSolver` | — |
| aspic | 590 → 593 | idem + 4 reasoners SAT | 11 `dung.util`, 5 `dung.writer`, 4 `reasoner`, `graphs.util`, `dung.independence` |
| beliefdynamics | 601 → 657 | idem + 2 `beliefdynamics.examples` | idem + 14 `agents`, 11 `dung.analysis`, 8 `deductive.attacks` |
| dung | 563 → 570 | idem aspic | idem aspic |

Les types retirés étaient du code mort Java 9+ que l'ancienne chaîne laissait fuir ; les types
ajoutés sont des paquets que l'ancienne chaîne sous-compilait et que la fermeture Maven inclut.

## Pourquoi cette approche

- **maven-shade-plugin** (pas un zip-merge artisanal) : produit un fat-jar Maven cohérent qui
  préserve les métadonnées cross-module IKVM. Un zip-merge casse l'exposition des types
  (`new Proposition()` → CS0246).
- **`net8.0` pas `net10.0`** : le kernel `.net-csharp` fournit le runtime `System.Runtime`
  en version 8.0 ; un DLL `net10.0` compile `Proposition` mais lève `FileNotFoundException:
  System.Runtime 10.0.0.0` au premier appel méthode.

Voir `Tweety-02-Basic-Logics-CSharp.ipynb` pour l'utilisation. Epic #4667.

## Fichiers — IKVM shade (notebooks Tweety-5/7a/7b)

Issue **#10411** : cinq shades `build-Tweety<Module>Shade.csproj` sur le modèle
des onze existantes, chacune produisant `org.tweetyproject.tweety-<module>.dll`
committée (pattern #4711). Les cinq DLLs couvrent les modules argumentation
**non-shadés** par le 7a-shade précédent (`build-Tweety7aShade.csproj`) :

| Module | Version | Notebook consommateur | Statut |
|--------|---------|----------------------|--------|
| `bipolar` | 1.21 | `Tweety-07a-Extended-Frameworks-CSharp.ipynb` (cell 30+, ADF + Bipolar) | SOTA-OK |
| `social` | 1.21 | `Tweety-07a-Extended-Frameworks-CSharp.ipynb` (cell 28-29) | SOTA-OK |
| `setaf` | 1.21 | `Tweety-07a-Extended-Frameworks-CSharp.ipynb` (cell 30+, SetAF) | SOTA-OK |
| `extended` | 1.30 | `Tweety-07a-Extended-Frameworks-CSharp.ipynb` (EAF = Extended Argumentation Framework) | SOTA-OK |
| `weighted` | 1.30 | `Tweety-07a-Extended-Frameworks-CSharp.ipynb` (cell 26-27) | SOTA-OK |

### Pipeline de rebuild — `rebuild-5shades.sh`

Le script `rebuild-5shades.sh` produit les cinq fat-jars en un seul passage :

1. **Téléchargement** des jars Maven Central transitifs (commons/graphs/math/logics.commons/logics.pl/dung à 1.21 ou 1.30 selon le profil).
2. **Téléchargement** des sources jars (Maven Central ou GitHub tarball pour commons).
3. **Extraction** + patch (ojalgo `SuperimposedStore` import retiré dans `ClaimBasedTheory.java`).
4. **Compilation** `javac --release 8` des modules en ordre de dépendance
   (deux profils : `minimal` = commons/graphs/dung pour bipolar/social/setaf/extended ;
   `full` = commons/math/graphs/logics.commons/logics.pl/dung pour weighted).
5. **Shade** : `jar cf` consolide toutes les classes en un seul JAR `java8-shade`.
6. **Copie** dans `../libs/` (gitignored).
7. **Audit bytecode** : tous les `.class` doivent être major 52 (Java 8).

```bash
bash dotnet-build/rebuild-5shades.sh
# 5 jars dans libs/, prêts pour IKVM
```

### Pipeline DLL

```bash
cd MyIA.AI.Notebooks/SymbolicAI/Tweety/dotnet-build
for m in bipolar social setaf extended weighted; do
  cap="$(tr a-z A-Z <<< "${m:0:1}")${m:1}"
  dotnet build "build-Tweety${cap}Shade.csproj" -c Release || break
  cp "bin/Release/net8.0/org.tweetyproject.tweety-${m}.dll" "../"
done
# 5 DLLs au root de Tweety/, committées
```

### Smoke test (verdict SOTA-OK par module)

Smoke test exécuté via `dotnet run` (`/tmp/c211-smoke/`, programme `Program.cs`)
chargeant chaque DLL via `Assembly.LoadFrom` + `Activator.CreateInstance` sur
un type public concret du module. Résultats (5/5 PASS) :

| Module | Type public testé (verifié via `Assembly.GetTypes()`) | Verdict |
|--------|--------------------------------------------------------|---------|
| bipolar | `org.tweetyproject.arg.bipolar.reasoner.evidential.GroundedReasoner` | SOTA-OK |
| social | `org.tweetyproject.arg.social.examples.SafExample` | SOTA-OK |
| setaf | `org.tweetyproject.arg.setaf.examples.SetAfTheoryTest` | SOTA-OK |
| extended | `org.tweetyproject.arg.extended.reasoner.SimpleRecursiveExtendedCompleteReasoner` | SOTA-OK |
| weighted | `org.tweetyproject.arg.weighted.reasoner.SimpleWeightedCompleteReasoner` | SOTA-OK |

**Note :** la plupart des reasoners TweetyProject upstream (par ex.
`SimpleSocialCompleteReasoner`, `SimpleCompleteSetAfReasoner`) sont
**package-private en Java** (`org.tweetyproject.arg.social.reasoner.*`,
`org.tweetyproject.arg.setaf.reasoners.*` sans mot-clé `public`). IKVM
les matérialise correctement mais les marque `non-public` dans le DLL
(conséquence directe du modèle de visibilité Java → .NET). Les types
publics restants dans chaque module suffisent largement pour
l'instanciation et l'usage depuis les notebooks : voir le smoke test
ci-dessus pour les 5 classes publiques concrètes réellement utilisables.

### Verdict SOTA (registre #3801)

Cinq modules IKVM-compilables supplémentaires, au prix de la chaîne de
recompilation source `--release 8` (le pattern causal.sh de c.210). Le pipeline
générique `rebuild-5shades.sh` couvre désormais les cinq modules restants des
frameworks d'argumentation étendus — **sans dépendance Maven locale** (téléchargement
direct Maven Central + GitHub).
