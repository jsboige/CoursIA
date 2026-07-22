# MyIA.AI.Shared

Socle .NET transverse partagé de CoursIA. Cible désignée (EPIC **#7265**) pour
récupérer, dans un équivalent C# moderne (net9.0) d'`Aricie.Shared`, les composants
techniques transverses du patrimoine endormi d'Aricie (~10 ans de travail) :
UI / sérialisation / rule-engine metadata-driven. Les modules de **domaine**
(Trading : Converter E1, Backtester E2) atterrissent dans un projet dédié à côté,
dépendant de Shared seulement quand on y mutualise des structures réutilisables.

> Cadrage user 2026-07-19 (issue #7265) : *« transverse dans Shared, domaine en
> projet dédié »*.

## A1 — Décoration metadata-driven (ancre, #7265)

Première tranche de la fondation. Pose les primitives qui font tenir tout le reste :
**décorer un type → l'introspecter par réflexion, sans inscription explicite**.

### Primitives livrées

| Type | Rôle |
|------|------|
| `ComponentModel.Attributes.MainCategoryAttribute` | Décore un type avec une catégorie principale (groupement/introspection). |
| `ComponentModel.Attributes.AttributeContainerAttribute` | Marque un type comme conteneur d'entités enfants (racine de hiérarchie). |
| `ComponentModel.Entities.IChildEntity` | Entité hiérarchique (parent + enfants) — hiérarchie infinie. |
| `ComponentModel.Entities.ISimpleEntity` | Entité simple (feuille plate, non hiérarchique). |
| `ComponentModel.Entities.IMergeable` | Entité qui sait fusionner une instance compatible en elle-même. |
| `ComponentModel.Providers.ReflectedProviderContainer` | Provider reflection-driven : discover les types décorés/marqués et les expose (par catégorie, conteneurs, interfaces marqueuses). |

### Contrat décoration → introspection

```csharp
using MyIA.AI.ComponentModel.Attributes;
using MyIA.AI.ComponentModel.Entities;
using MyIA.AI.ComponentModel.Providers;

[MainCategory("Payment")]
public sealed class PaymentGateway : ISimpleEntity { public string Name => "gw"; }

// Aucune inscription : la décoration suffit.
var provider = ReflectedProviderContainer.FromAssembly<PaymentGateway>();
provider["Payment"];        // { PaymentGateway }
provider.SimpleEntities;    // { PaymentGateway }
provider.Categories;        // { "Payment" }
```

## A2 — Sérialisation légo JSON décoration-driven (#7265)

Deuxième tranche. Pose le sérialiseur JSON qui round-trip le modèle metadata A1 : on
sérialise un graphe décoré/marqué et on le recharge en un graphe équivalent, avec la
hiérarchie `IChildEntity` (types concrets des enfants, back-references `Parent`,
catégories redécouvrables) intacte.

| Type | Rôle |
|------|------|
| `ComponentModel.Serialization.MetadataContractResolver` | Contract resolver Newtonsoft qui pilote la sérialisation depuis la décoration A1. Casse le cycle parent/enfant en dropant le back-ref `Parent` (reconstruit au load). |
| `ComponentModel.Serialization.MetadataJsonSerializer` | Façade `Serialize` / `Deserialize<T>` : `TypeNameHandling.Auto` sur `Children` polymorphes pour reconstruire les types concrets, puis re-link des `Parent` post-load. |

### Contrat round-trip

```csharp
using MyIA.AI.ComponentModel.Serialization;

var folder = new ContentFolder();
folder.AddChild(new ContentItem { Title = "release-notes" });

var json = MetadataJsonSerializer.Serialize(folder);
var back = MetadataJsonSerializer.Deserialize<ContentFolder>(json);

back.Children[0];                  // ContentItem reconstruit via $type
back.Children[0].Parent;           // re-linké sur back (cycle cassé puis reconstruit)
```

**Caveat sécurité** : `TypeNameHandling.Auto` embarque des noms de types runtime et les
lie au load — approprié pour un socle interne sérialisant des graphes **de confiance**
(configs, arbres d'entités propres). **Ne pas** nourrir ce sérialiseur avec de l'input
non fiable (construire plutôt des `JsonSerializerSettings` en `TypeNameHandling.None`).

## A2+ — Sérialisation légo XML décoration-driven (#7265)

Complément XML de la tranche A2. Même objectif de round-trip du modèle metadata A1,
cette fois sur `System.Xml.Serialization`. `XmlSerializer` ne sait pas round-tripper un
`IReadOnlyList<IChildEntity>` (read-only + polymorphe), le graphe vivant est donc projeté
vers une forme sérialisable puis reconstruit au load.

| Type | Rôle |
|------|------|
| `ComponentModel.Serialization.XmlAwareContractResolver` | Plan décoration-driven : un discriminateur de type par type concret (les enfants polymorphes se reconstruisent dans leur type concret, pas `IChildEntity`) + les propriétés de valeur round-trippables par type (get+set publics, hors `IChildEntity.Parent` — le cycle est rebâti au load). |
| `ComponentModel.Serialization.NodeSurrogate` (+ `PropertySurrogate`) | La forme arborescente sérialisable XML. Projection du graphe vivant vers discriminateur de type + sac de propriétés + enfants récursifs. |
| `ComponentModel.Serialization.MetadataXmlSerializer` | Façade `Serialize` / `Deserialize<T>` : sérialise le graphe en XML indenté ; au load reconstruit l'arbre concret (instanciation par discriminateur, restauration des propriétés de valeur, re-link des `Parent` via `AddChild`). |

## Build & tests

```bash
dotnet build MyIA.AI.Shared.sln -c Release
dotnet test  MyIA.AI.Shared.sln -c Release
```

Solution `MyIA.AI.Shared.sln` (socle-only : lib + tests) pour un build/test isolé,
sans tirer `MyIA.AI.Notebooks`. La solution racine `MyIA.CoursIA.sln` référence déjà
le projet lib.

## A1+ — Hiérarchie de providers : 3 stratégies de découverte (#7265)

Complément de l'ancre A1. Pose les deux autres stratégies de découverte de la famille de
providers `Aricie.Shared`, afin que `ReflectedProviderContainer` (décoration) ne soit plus
seul : `SimpleProviderContainer` (enregistrement explicite plat) et `AutoProviderContainer`
(convention de nommage/namespace). Les trois partagent le contrat de lecture
`IProviderContainer` et le classifieur `ProviderModel` — un consommateur demande des types
sans se coupler au mode de découverte.

| Type | Rôle |
|------|------|
| `ComponentModel.Providers.IProviderContainer` | Contrat de lecture commun (catégories, `Containers`, `ChildEntities`, `SimpleEntities`, `Mergeables`). |
| `ComponentModel.Providers.ProviderModel` | Classifieur partagé (internal) : répartit un set de types en catégories + buckets marqueurs, tolérant aux types non chargeables. |
| `ComponentModel.Providers.SimpleProviderContainer` | Découverte par **enregistrement explicite** : `Register<T>("cat")` (aucune réflexion, aucune décoration). Un type peut être filé sous plusieurs catégories. |
| `ComponentModel.Providers.AutoProviderContainer` | Découverte par **convention** : `Func<Type, string?>` (suffixe de nom, segment de namespace…). `null` exclut le type. |

### Contrat 3 stratégies, 1 surface de lecture

```csharp
using MyIA.AI.ComponentModel.Providers;

// Décoration (A1) — un attribut suffit.
IProviderContainer reflected = ReflectedProviderContainer.FromAssembly<PaymentGateway>();

// Enregistrement explicite (A1+) — aucun attribut requis.
IProviderContainer simple = new SimpleProviderContainer()
    .Register<PaymentGateway>("Payment")
    .Register<ContentFolder>("Content");

// Convention (A1+) — règle de nommage, zéro attribut.
IProviderContainer auto = AutoProviderContainer.FromAssembly<PaymentGateway>(
    t => t.Name.EndsWith("Gateway") ? "Payment" : null);

// Même surface de lecture quel que soit le mode.
reflected["Payment"]; simple["Payment"]; auto["Payment"];
```

## Tranches livrées (mergers 2026-07-21)

Pipeline A1→A2 absorbé par 4 PRs mergées le 2026-07-21, dans cet ordre. Chaque PR
a livré ses primitives + sa batterie de tests xUnit ; **48/48 tests PASS** sur la
solution `MyIA.AI.Shared.sln` (couvrant les 4 tranches). Cette section sert
d'**index de traçabilité** pour quiconque navigue vers le socle depuis #7265
ou la pépite dispatch #8031 (déjà livrée avant sa création, voir note).

| Tranche | PR | Merged | Primitives livrées | Tests |
|---------|----|--------|--------------------|-------|
| **A1** ancre | [#7653](https://github.com/jsboige/CoursIA/pull/7653) | 2026-07-21 | 6 (`MainCategory`/`AttributeContainer` attrs + `IChildEntity`/`ISimpleEntity`/`IMergeable` + `ReflectedProviderContainer`) | 12 |
| **A1+** providers | [#7669](https://github.com/jsboige/CoursIA/pull/7669) | 2026-07-21 | 4 (`IProviderContainer`, `ProviderModel`, `SimpleProviderContainer`, `AutoProviderContainer`) | 18 |
| **A2** JSON | [#7661](https://github.com/jsboige/CoursIA/pull/7661) | 2026-07-21 | 2 (`MetadataContractResolver`, `MetadataJsonSerializer`) | 9 |
| **A2+** XML | [#7677](https://github.com/jsboige/CoursIA/pull/7677) | 2026-07-21 | 3 (`XmlAwareContractResolver`, `NodeSurrogate`, `MetadataXmlSerializer`) | 9 |

Vérification locale : `dotnet build MyIA.AI.Shared.sln -c Release` (0 warning,
0 error) + `dotnet test MyIA.AI.Shared.sln -c Release --no-build` (48/48 PASS).

> **Note** : la pépite dispatch **#8031** (« A1 socle + tests xUnit ») a été
> ouverte le 2026-07-22T20:13Z — **6h après** que les 4 PRs ci-dessus aient été
> mergées. La substance est intégralement livrée ; l'issue peut être fermée
> (coordinateur, règle worker #1502 — un worker ne ferme JAMAIS les issues).

## Tranches suivantes (hors cette ancre)

- **A3** — Object explorer UI : `AdvancedGridView`, `PropertyEditor`, filtres.

## Références

- EPIC **#7265** — index de la pompe patrimoine Aricie.
- `See #7265`.
