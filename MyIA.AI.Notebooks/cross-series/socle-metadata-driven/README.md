# Socle .NET metadata-driven

Ce projet est la **première existence pédagogique** du socle transverse
[`MyIA.AI.Shared`](../../../MyIA.AI.Shared/) (EPIC #7265, tranches A1 + A2). Le socle
compile, passe 48 tests — et jusqu'ici aucun notebook ne le référençait. Le notebook
[`Socle-Metadata-Driven.ipynb`](Socle-Metadata-Driven.ipynb) démontre le pattern
*metadata-driven* en trois moments, du plus mécanique au plus substantiel.

Il se classe dans `cross-series/` parce que le socle se définit lui-même comme un
**socle .NET transverse partagé** : il mobilise la notation générique (destination
`GradeBookApp`, #7265 A1) et les contraintes-comme-expressions (proche de
`Search/Part2-CSP/`, pépite B1 du patrimoine Aricie).

## Les trois moments

1. **Décoration → introspection (A1).** On décore un type avec `[MainCategory(...)]`
   et/ou `[AttributeContainer]`, on le découvre par réflexion via
   `ReflectedProviderContainer.FromAssembly<T>()` — sans aucune inscription explicite.
   Aucun registre à maintenir : la décoration suffit.

2. **Sérialisation pilotée par la décoration (A2).** Le même graphe `IChildEntity`,
   sérialisé en JSON par `MetadataJsonSerializer`, round-trippé : les types concrets des
   enfants sont préservés (via `$type`), le back-reference `Parent` (qui formerait un
   cycle) est droppé à la sérialisation puis reconstruit au chargement.

3. **Le prédicat universel Flee (la substance *low-code*).** Une règle métier écrite
   **en chaîne de caractères**, compilée à l'exécution par le moteur
   [Flee](https://github.com/arnonax/Flee) 2.0.0, évaluée comme prédicat sur les entités
   découvertes en (1). Flee est déclaré en dépendance du socle (`<PackageReference>`)
   mais **n'était jamais exercé** : ce notebook le met en œuvre. La règle vient de la
   **donnée** (config, CSV, saisie), pas du code, et change sans recompiler.

   > **Grammaire Flee.** Le moteur utilise une grammaire VB-like : opérateurs
   > `And` / `Or` / `Not`, `=` pour l'égalité, `<>` pour la différence — et non
   > `&&` / `==` du C#. Détail mis en évidence par cette première exécution réelle.

## Prérequis

Le notebook référence l'**assembly buildée** du socle (jamais le code n'est copié-collé).
Buildée une fois le socle, depuis la racine du dépôt :

```bash
dotnet build MyIA.AI.Shared/MyIA.AI.Shared.csproj
```

Le notebook charge ensuite l'assembly par un `#r` relatif (kernel `.net-csharp`) :

```csharp
#r "../../../MyIA.AI.Shared/bin/Debug/net9.0/MyIA.AI.Shared.dll"
```

Exécuter sur une machine où [.NET Interactive](https://github.com/dotnet/interactive)
est installé (kernel `.net-csharp`). Cible .NET 9.0.

## Exercices

Le notebook contient **3 exercices** répartis (non groupés en fin), chacun précédé d'un
markdown contexte + objectif + indice, stubbé sans erreur volontaire (règle C.1) :

1. Découvrir sa propre entité décorée (`[MainCategory("Logistique")]`).
2. Vérifier le round-trip JSON sur un graphe plus profond (back-references `Parent`).
3. Écrire une règle Flee compilée (filtrage par montant supérieur à la moyenne).

## Références

- EPIC **#7265** — récupération du patrimoine transverse Aricie (`Aricie.Shared` →
  `MyIA.AI.Shared`, net9.0). Tranches A1 (décoration), A2 (sérialisation JSON), A2+ (XML).
- Issue **#10161** — cadrage de ce notebook (le socle « 48 tests verts, 0 notebook »).
- Socle : [`MyIA.AI.Shared/README.md`](../../../MyIA.AI.Shared/README.md),
  [`MyIA.AI.Shared/MyIA.AI.Shared.csproj`](../../../MyIA.AI.Shared/MyIA.AI.Shared.csproj).
