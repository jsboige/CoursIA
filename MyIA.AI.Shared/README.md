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

## Tranches suivantes (hors cette ancre)

- **A2** — Sérialisation légo (XML/JSON décoration-driven) :
  `XmlAwareContractResolver`, `DynamicSurrogate`, collections sérialisables.
- **A3** — Object explorer UI : `AdvancedGridView`, `PropertyEditor`, filtres.

## Références

- EPIC **#7265** — index de la pompe patrimoine Aricie.
- `See #7265`.
