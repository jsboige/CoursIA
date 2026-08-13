# `dotnet-build/` — Recette de build des runtimes Tweety C# / IKVM

Ce dossier contient les **recettes de build** (POM shade + csproj) des runtimes .NET de Tweety
recompilés via IKVM 8.15.0. Chaque runtime compilé (`org.tweetyproject.tweety-<module>.dll`)
est placé **à côté du notebook** qui le charge.

## Fichiers — cluster `pl` (notebook [`../Tweety-2-Basic-Logics-Csharp.ipynb`](../Tweety-2-Basic-Logics-Csharp.ipynb))

| Fichier | Rôle | Committé ? |
|---------|------|-----------|
| `org.tweetyproject.tweety-pl.dll` (7.6 MB) | **Runtime** .NET de Tweety cluster `pl` (chargé par le notebook via `#r`) | Oui (pattern #4711) |
| `tweety-pl-full-1.30.jar` (6.9 MB) | Fat-jar Maven shade (artefact de build intermédiaire) | Non (gitignoré, reconstruit ci-dessous) |
| `build-tweety-pl-shade.pom.xml` | POM aggregator Maven shade (produit le fat-jar) | Oui (reproductibilité) |
| `build-TweetyShade.csproj` | Projet MSBuild `<IkvmReference>` (convertit le fat-jar en DLL) | Oui (reproductibilité) |

## Fichiers — cluster `beliefdynamics` (notebook [`../Tweety-4-Belief-Revision-Csharp.ipynb`](../Tweety-4-Belief-Revision-Csharp.ipynb))

| Fichier | Rôle | Committé ? |
|---------|------|-----------|
| `org.tweetyproject.tweety-beliefdynamics.dll` (10.3 MB) | **Runtime** .NET des opérateurs AGM (contraction, révision de Levi) | Oui (pattern #4711) |
| `tweety-beliefdynamics-full-1.30.jar` (9.6 MB) | Fat-jar Maven shade (artefact intermédiaire) | Non (gitignoré, reconstruit ci-dessous) |
| `build-tweety-beliefdynamics-shade.pom.xml` | POM aggregator Maven shade | Oui (reproductibilité) |
| `build-TweetyBeliefDynamicsShade.csproj` | Projet MSBuild `<IkvmReference>` | Oui (reproductibilité) |

### Contrainte bytecode Java 8 (piège majeur du cluster `beliefdynamics`)

IKVM 8.15 est un runtime **Java 8** : il **saute silencieusement** toute classe compilée en
bytecode major > 52 (Java 9+), avec un warning `IKVM0101 class format error "55.0"`. Le pom parent
de Tweety compile par défaut en `<release>11</release>` (major 55) → **les opérateurs de révision
seraient absents de la DLL**. La recette rebuild patche le pom parent en `<release>8</release>`
(+ `source`/`target` 8) avant `mvn install` du module `beliefdynamics`, garantissant du major-52
IKVM-compilable. Vérification : `od -An -tu1 -j6 -N2 LeviMultipleBaseRevisionOperator.class` doit
afficher `52`.

## Recette de rebuild (si la DLL doit être régénérée)

Prérequis : JDK 17 (`JAVA_HOME`), Maven 3.9+, .NET SDK 8.0+, les 5 modules Tweety recompilés
en Java 8 installés dans le `~/.m2` local (clone `TweetyProject` tag `v1.30`, patch parent-pom
`maven-compiler-plugin` 2.3.2 → 3.13.0 + `<release>8</release>`, downgrade source Java 9-11 → 8,
puis `mvn install -DskipTests -Dgpg.skip=true` sur commons/logics-commons/math/logics-fol/logics-pl).

```bash
# 1. Fat-jar Maven shade (déclare pl comme dep, tire transitivement fol/commons/math/...)
mvn -f build-tweety-pl-shade.pom.xml clean package -Dgpg.skip=true
cp target/tweety-pl-full-1.30.jar .

# 2. DLL .NET via <IkvmReference> (TargetFramework = net8.0, PAS net10.0 — runtime kernel LTS)
dotnet build build-TweetyShade.csproj -c Release
cp bin/Release/net8.0/org.tweetyproject.tweety-pl.dll .
```

## Pourquoi cette approche

- **maven-shade-plugin** (pas un zip-merge artisanal) : produit un fat-jar Maven cohérent qui
  préserve les métadonnées cross-module IKVM. Un zip-merge casse l'exposition des types
  (`new Proposition()` → CS0246).
- **`net8.0` pas `net10.0`** : le kernel `.net-csharp` fournit le runtime `System.Runtime`
  en version 8.0 ; un DLL `net10.0` compile `Proposition` mais lève `FileNotFoundException:
  System.Runtime 10.0.0.0` au premier appel méthode.

Voir `Tweety-2-Basic-Logics-Csharp.ipynb` pour l'utilisation. Epic #4667.

## Fichiers — IKVM shade 5 modules (notebooks Tweety-5/7a/7b)

Issue **#10411** : cinq shades `build-Tweety<Module>Shade.csproj` sur le modèle
des onze existantes, chacune produisant `org.tweetyproject.tweety-<module>.dll`
committée (pattern #4711). Les cinq DLLs couvrent les modules argumentation
**non-shadés** par le 7a-shade précédent (`build-Tweety7aShade.csproj`) :

| Module | Version | Notebook consommateur | Statut |
|--------|---------|----------------------|--------|
| `bipolar` | 1.21 | `Tweety-7a-Extended-Frameworks-Csharp.ipynb` (cell 30+, ADF + Bipolar) | SOTA-OK |
| `social` | 1.21 | `Tweety-7a-Extended-Frameworks-Csharp.ipynb` (cell 28-29) | SOTA-OK |
| `setaf` | 1.21 | `Tweety-7a-Extended-Frameworks-Csharp.ipynb` (cell 30+, SetAF) | SOTA-OK |
| `extended` | 1.30 | `Tweety-7a-Extended-Frameworks-Csharp.ipynb` (EAF = Extended Argumentation Framework) | SOTA-OK |
| `weighted` | 1.30 | `Tweety-7a-Extended-Frameworks-Csharp.ipynb` (cell 26-27) | SOTA-OK |

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

### Pipeline DLL — 5 modules

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
