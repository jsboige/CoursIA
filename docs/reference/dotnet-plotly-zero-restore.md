# Pattern .NET Interactive — figures Plotly « zero-restore » (technique C548-L2)

**Statut** : pattern cluster-wide validé (2026-07). Registre : EPIC **#3801** (SOTA axe-2, Prong-A « vrai outil, pas workaround dégradé »).
**Scope** : toute cellule de notebook `.NET Interactive` (C#) qui doit produire une **figure réelle** (bar chart, histogramme, courbe) là où un `#r "nuget: Plotly.NET…"` échoue.

## Problème — `#r "nuget:"` charting bloqué en headless

Les notebooks `.NET Interactive` exécutés en CI ou via Papermill headless ne peuvent pas restaurer les paquets NuGet de charting (`Plotly.NET`, `XPlot.Plotly`, …) : le restore `#r "nuget:"` est **bloqué cluster-wide** (verdict c.547-L1 = RECOVERABLE-ENV, règle F — cf [genai-config](../../.claude/rules/genai-config.md) et CLAUDE.md §F). Conséquence historique : les cellules retombaient sur un **workaround ASCII dégradé** (`new string('#', barLen)`), lui-même **interdit** par le Prong-A #3801 (cf [sota-not-workaround.md](../../.claude/rules/sota-not-workaround.md)).

## Solution — formatter HTML intégré au kernel, zéro NuGet

La technique **C548-L2 « zero-restore »** enregistre un formatter `text/html` sur un `record` porteur du markup Plotly, et injecte Plotly.js depuis le CDN. **Aucun paquet NuGet n'est restauré** : le kernel émet directement du HTML que le notebook rend comme `display_data` `text/html`.

### Préambule (idempotent, une fois par cellule)

```csharp
using Microsoft.DotNet.Interactive.Formatting;
using System.IO;
record PlotlyHtml(string Markup);
Formatter.Register(typeof(PlotlyHtml),
    (obj, writer) => ((TextWriter)writer).Write(((PlotlyHtml)obj).Markup), "text/html");
```

> Rappel C# : les directives `using` doivent précéder tout `namespace` / déclaration locale dans la cellule (CS1529, cf leçons C553-L1 / L504-L1) — placer le préambule **en tête** de cellule.

### Émission d'une figure

```csharp
var divId = "plt" + Guid.NewGuid().ToString("N");
var trace = System.Text.Json.JsonSerializer.Serialize(
    new Dictionary<string, object> {
        ["x"] = xValues, ["y"] = yLabels, ["type"] = "bar", ["orientation"] = "h",
        ["marker"] = new Dictionary<string,object>{ ["color"] = colors },
        ["text"] = xValues, ["textposition"] = "auto" });
var layout = "{\"title\":{\"text\":\"…\"}," +
             "\"xaxis\":{\"title\":{\"text\":\"…\"},\"zeroline\":true}," +
             "\"yaxis\":{\"title\":{\"text\":\"…\"}},\"margin\":{\"l\":120,\"r\":40}}";
var markup = "<div id=\"" + divId + "\"></div>" +
             "<script src=\"https://cdn.plot.ly/plotly-2.35.2.min.js\"></script>" +
             "<script>Plotly.newPlot('" + divId + "',[" + trace + "]," + layout + ")</script>";
display(new PlotlyHtml(markup));
```

Référence canonique complète : `MyIA.AI.Notebooks/Search/Part4-Metaheuristics/MGS-10-CenterBias.ipynb` cellule `[8]` (barre horizontale signée, split couleur `>=0` / `<0`, `zeroline`).

## Piège — le `layout` est le 3ᵉ argument de `Plotly.newPlot`, PAS un 4ᵉ trace

`Plotly.newPlot(divId, dataArray, layout)` prend le `layout` comme **3ᵉ argument**. L'erreur récurrente est de placer l'objet `layout` en **4ᵉ position du tableau `data`** : Plotly.js le parse alors comme un trace implicite (sans `x`/`y`, silencieusement ignoré) et **titre + labels d'axes + `barmode`/`zeroline` ne s'appliquent pas** au rendu (incident #6689 Infer-12, noté par la review §H.4). Toujours **fermer le tableau `data`** puis passer `layout` séparément : `Plotly.newPlot(id, [trace1, trace2], layout)`.

## Vérification (gate de merge)

Une conversion Prong-A .NET → Plotly est validée quand :

- `execution_count != null` sur la cellule convertie (gate #5214 pour .NET — l'advisory CI autorise à sauter la ré-exécution CI des notebooks .NET, **pas** à committer des sorties vides ; l'exécution locale reste obligatoire) ;
- la sortie committée contient un `display_data` `text/html` avec `Plotly.newPlot` **et** des tableaux `x`/`y` **non vides** (figure de données réelle, pas coquille vide) ;
- `0` motif `new string('#'` (barre ASCII de données) résiduel dans la source ;
- catalogue byte-identique à `main`.

Cf [sota-not-workaround.md](../../.claude/rules/sota-not-workaround.md) §Prong-A (5 verdicts SOTA) et [pr-review-discipline.md](../../.claude/rules/pr-review-discipline.md) §D/§H.

## QA visuelle — pourquoi le gate Plotly-CDN est *structurel*, pas un cycle vision par PR

La règle de routage vision ([model-delegation.md](../../.claude/rules/model-delegation.md) §« Capacité vision ») impose de faire vérifier tout rendu visuel par un modèle qui **voit** (MiniMax sur lane CoursIA-2, ou ai-01/Opus), jamais text-only sur une lane GLM. Cette exigence vise la classe de sortie où **« exister sur disque » ≠ « rend correctement »** : le raster statique (PNG matplotlib, image GenAI, screenshot de slide) peut être un bloc de couleur plat, une image blanche ou un placeholder — un défaut que **seul le regard** distingue d'une vraie figure (incident fondateur `workflow-orchestration.png`, 3 blocs plats consacrés comme « images générées »).

**La sortie Plotly `text/html` + CDN de la technique C548-L2 n'appartient PAS à cette classe.** Elle est **rendue côté client par Plotly.js** de façon **déterministe** : à partir d'un tableau `data` non vide, d'un `layout` bien placé (3ᵉ argument) et d'un CDN joignable, le SVG produit est une fonction pure des données sérialisées dans la cellule. Il n'existe **pas** de mode d'échec « bloc plat / image blanche » propre au client : le rendu échoue de façon **structurelle et détectable dans la source committée**, pas de façon silencieuse-visuelle. Les trois modes d'échec réels sont tous forensiques :

| Mode d'échec Plotly-CDN | Détection (sans regard) |
|-------------------------|-------------------------|
| Tableau `x`/`y` **vide** (coquille sans données) | grep sur la sortie : `x`/`y` non vides (déjà au gate de merge ci-dessus) |
| `layout` en **4ᵉ trace** au lieu de 3ᵉ argument (titre/axes/`barmode` non appliqués) | piège C450-L1 ci-dessus : vérifier `Plotly.newPlot(id, [traces], layout)` |
| **CDN absent** (`<script src="…plotly…">` manquant) | grep : présence du `<script src="https://cdn.plot.ly/…">` |

**Conséquence opérationnelle — le gate visuel de la classe Plotly-CDN = forensique + un spot-check de rendu par vague de rollout, PAS un aller-retour MiniMax par PR.** Le contrôle de merge d'une conversion C548-L2 est donc :

1. **Forensique par PR** (obligatoire, automatisable) : `x`/`y` non vides, `layout` en 3ᵉ arg, `<script>` CDN présent, `0` motif `new string('#'` résiduel — c'est le gate de merge de la section précédente.
2. **Spot-check de rendu par vague / par nouveau type de trace** (échantillon, pas exhaustif) : extraire le markup Plotly committé → HTML autonome → screenshot (Playwright) → **lire l'image** depuis un modèle qui voit (MiniMax/CoursIA-2 ou ai-01/Opus). Ce spot-check attrape les bugs de **génération de données** que le forensique ne voit pas (série toute à zéro, mauvais mapping de couleurs, axes inversés) et valide le pattern pour la vague — il n'a **pas** à être refait pour chaque PR une fois la classe validée.

Ainsi le routage vision reste correct **sans créer de goulot** : la classe où le regard est indispensable (raster statique) part vers MiniMax/ai-01 systématiquement ; la classe Plotly-CDN (déterministe côté client) est gatée par le forensique + un spot-check périodique. Validation empirique de ce partage : 3 conversions du rollout 2026-07 (#6696 barres groupées, #6698 barres + heatmap Viridis, #6700 courbe) rendues et **vues** — figures réelles conformes aux données, aucun bloc plat/placeholder (vision-audit ai-01, 2026-07-15).

## Notebooks utilisant le pattern (rollout 2026-07, #3801)

App-7b-Wordle-CSharp (#6683), GameTheory-15c-CooperativeGames (#6684), GameTheory-3-Topology2x2 (#6687), Infer-12-Modeles-Hierarchiques (#6689), Search MGS-10-CenterBias (#6692) — rollout continu sous l'EPIC #3801.

## Refactor possible (memo)

Extraire le préambule (`record PlotlyHtml` + `Formatter.Register`) dans un helper partagé chargé via `#load` (ex. `notebook-helpers/PlotlyHelper.cs`) éviterait la ré-inscription du formatter dans chaque cellule. Attention à la re-entry (`Formatter.Register` appelé par deux cellules) — la mitigation actuelle est un préambule **idempotent par cellule** ; un helper devrait garder l'enregistrement idempotent (garde `if`/registre statique).

## Voir aussi

- [sota-not-workaround.md](../../.claude/rules/sota-not-workaround.md) — Prong-A : vrai outil, jamais workaround dégradé (EPIC #3801)
- [pr-review-discipline.md](../../.claude/rules/pr-review-discipline.md) — §D (preuve d'exécution notebook) + §H (SOTA)
- [notebook-conventions.md](../../.claude/rules/notebook-conventions.md) — §Exécution (.NET Papermill `.net-csharp`)
- CLAUDE.md §F — environnement : réparer, jamais contourner
