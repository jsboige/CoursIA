# `dotnet-build/` — Recette de build du runtime Tweety C# / IKVM

Ce dossier contient la **recette de build** (POM shade + csproj) du runtime .NET de Tweety
(cluster `pl`) recompilé via IKVM 8.15.0. Le runtime compilé (`org.tweetyproject.tweety-pl.dll`)
est placé **à côté du notebook** [`../Tweety-2-Basic-Logics-Csharp.ipynb`](../Tweety-2-Basic-Logics-Csharp.ipynb).

## Fichiers

| Fichier | Rôle | Committé ? |
|---------|------|-----------|
| `org.tweetyproject.tweety-pl.dll` (7.6 MB) | **Runtime** .NET de Tweety cluster `pl` (chargé par le notebook via `#r`) | Oui (pattern #4711) |
| `tweety-pl-full-1.30.jar` (6.9 MB) | Fat-jar Maven shade (artefact de build intermédiaire) | Non (gitignoré, reconstruit ci-dessous) |
| `build-tweety-pl-shade.pom.xml` | POM aggregator Maven shade (produit le fat-jar) | Oui (reproductibilité) |
| `build-TweetyShade.csproj` | Projet MSBuild `<IkvmReference>` (convertit le fat-jar en DLL) | Oui (reproductibilité) |

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
