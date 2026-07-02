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
