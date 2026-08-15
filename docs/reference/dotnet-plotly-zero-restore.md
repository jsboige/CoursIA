# Pattern .NET Interactive — figures « zero-restore » (technique C548-L2, variante SVG inline)

**Statut** : pattern cluster-wide validé (2026-07). Registre : EPIC **#3801** (SOTA axe-2, Prong-A « vrai outil, pas workaround dégradé »).
**Scope** : toute cellule de notebook `.NET Interactive` (C#) qui doit produire une **figure réelle** (bar chart, histogramme, courbe) là où un `#r "nuget: Plotly.NET…"` échoue.

> **La charge utile est du SVG inline, pas du Plotly.js.** La variante d'origine de cette technique injectait Plotly.js depuis un CDN ; elle est **retirée** depuis #6927 / #6946 parce qu'elle rend **blanc** partout où le notebook est *consulté* plutôt qu'*exécuté*. Voir [§Variante retirée](#variante-retirée--plotlyjs-par-cdn-ne-plus-utiliser). Le nom de fichier reste `dotnet-plotly-zero-restore.md` pour ne pas casser les liens entrants ; l'épisode Plotly est documenté ci-dessous plutôt qu'effacé.

## Problème — `#r "nuget:"` charting bloqué en headless

Les notebooks `.NET Interactive` exécutés en CI ou via Papermill headless ne peuvent pas restaurer les paquets NuGet de charting (`Plotly.NET`, `XPlot.Plotly`, …) : le restore `#r "nuget:"` est **bloqué cluster-wide** (verdict c.547-L1 = RECOVERABLE-ENV, règle F — cf [genai-config](../../.claude/rules/genai-config.md) et CLAUDE.md §F). Conséquence historique : les cellules retombaient sur un **workaround ASCII dégradé** (`new string('#', barLen)`), lui-même **interdit** par le Prong-A #3801 (cf [sota-not-workaround.md](../../.claude/rules/sota-not-workaround.md)).

## Solution — SVG inline émis en `text/html`, zéro NuGet

La technique **C548-L2 « zero-restore »** fait émettre par le kernel un `text/html` contenant un **`<svg>` construit à la main**. Aucun paquet NuGet n'est restauré, **et** la figure est un artefact **persistant** dans le notebook committé : elle rend en kernel live, sur GitHub, sur nbviewer et hors-ligne.

Deux formes coexistent sur `main`, toutes deux valides — choisir selon que la cellule émet une ou plusieurs figures.

### Forme A — `record` + formatter (réutilisable sur plusieurs cellules)

```csharp
using Microsoft.DotNet.Interactive.Formatting;
using System.IO;
using System.Text;
record PlotSvg(string Markup);
Formatter.Register(typeof(PlotSvg),
    (obj, writer) => ((TextWriter)writer).Write(((PlotSvg)obj).Markup), "text/html");
```

puis `display(new PlotSvg(BuildBarSvgH(labels, values, titre, axeX)));`

Le formatter est enregistré **une fois** et le `record` reste disponible pour les cellules suivantes du même kernel — c'est la forme à préférer dès qu'un notebook trace plus d'une figure.

### Forme B — `display(HTML(...))` direct (figure unique, sans infrastructure)

```csharp
display(HTML(BuildBarSvgH(labels, values, titre, axeX)));
```

Pas de `record`, pas de `Formatter.Register`. Suffisant quand la cellule est autonome.

> Rappel C# : les directives `using` doivent précéder tout `namespace` / déclaration locale dans la cellule (CS1529, cf leçons C553-L1 / L504-L1) — placer le préambule **en tête** de cellule.

> Piège de localisation : sérialiser les coordonnées en **culture invariante** (`CultureInfo.InvariantCulture`). Une virgule décimale dans un attribut SVG (`x='12,5'`) casse silencieusement la géométrie — la figure s'affiche, déformée ou vide.

### Références canoniques (vérifiées sur `main`)

| Forme | Notebook | Cellule | Preuve |
|---|---|---|---|
| **A** (`record PlotSvg`) | `MyIA.AI.Notebooks/Search/Applications/CSP/App-7b-Wordle-CSharp.ipynb` | `[21]` (barres horizontales, entropie par mot) ; infra réutilisée en `[33]` | `execution_count: 11`, sortie `text/html` commençant par `<svg viewBox="0 0 720 460"` |
| **B** (`display(HTML(...))`) | `MyIA.AI.Notebooks/Search/Part4-Metaheuristics/MGS-10-CenterBias.ipynb` | `[8]` (barre horizontale signée, split couleur `>=0` / `<0`) | `execution_count: 5`, sortie `text/html` commençant par `<div><svg viewBox='0 0 720 374'` |

Les deux pointeurs sont **résolus firsthand** (index de cellule, `execution_count`, premiers octets de la sortie committée) et non recopiés d'un body de PR. C'est le minimum exigible d'une « référence canonique » : cf l'incident qui a produit cette section, [§Provenance](#provenance-de-cette-correction).

## Variante retirée — Plotly.js par CDN (ne plus utiliser)

La forme d'origine enregistrait un `record PlotlyHtml` porteur d'un `<div>` + `<script src="https://cdn.plot.ly/plotly-2.35.2.min.js">` + `Plotly.newPlot(...)`. **Elle est retirée**, et la raison n'est pas esthétique :

> Le graphe rend **uniquement dans un kernel .NET Interactive live avec Internet**. Partout où le notebook committé est *consulté* plutôt qu'*exécuté*, il est **blanc** : GitHub *sandbox et n'exécute pas* les `<script>` → div vide ; nbviewer / offline / CSP strict → le CDN ne charge pas → div vide.
> — investigation #6927 (firsthand, 2026-07-16), déclenchée par le user constatant qu'`Infer-17-Kalman-Filter` **n'affiche aucun graphique**

Ce n'était pas une perte de données (les `x`/`y` sont inline dans le script) mais une **régression de portabilité du rendu** : le jumeau Python (matplotlib) émettait un `image/png` persistant, les deux jumeaux divergeaient. #6927 a mesuré **8 notebooks** touchés ; #6946 a livré la première conversion.

**Ne pas reverter vers Plotly par principe** : le passage ASCII → Plotly (#6599) était une vraie amélioration Prong-A. Ce qui est proscrit est la **variante CDN-script**, qui ne produit aucun artefact statique. Une figure Plotly *interactive* reste défendable en kernel live si — et seulement si — un artefact statique accompagne la cellule.

### Piège historique (variante retirée uniquement)

`Plotly.newPlot(divId, dataArray, layout)` prend le `layout` comme **3ᵉ argument**. L'erreur récurrente était de le placer en 4ᵉ position du tableau `data` : Plotly.js le parsait comme un trace implicite silencieusement ignoré, et titre + labels + `zeroline` ne s'appliquaient pas (incident #6689 Infer-12). Conservé ici pour le diagnostic des notebooks non encore convertis — sans objet pour le SVG inline.

## Vérification (gate de merge)

Une conversion Prong-A .NET → figure réelle est validée quand :

- `execution_count != null` sur la cellule convertie (gate #5214 pour .NET — l'advisory CI autorise à sauter la ré-exécution CI des notebooks .NET, **pas** à committer des sorties vides ; l'exécution locale reste obligatoire) ;
- la sortie committée contient un `display_data` `text/html` porteur d'un **`<svg>` avec géométrie réelle** — au moins un `<rect>`/`<path>`/`<line>` dont les coordonnées ne sont pas toutes nulles (figure de données, pas cadre vide) ;
- **`0` occurrence de `cdn.plot.ly`** dans la source de la cellule, hors commentaire documentant la conversion ;
- `0` motif `new string('#'` (barre ASCII de données) résiduel dans la source ;
- catalogue byte-identique à `main`.

> Ce gate exigeait auparavant `Plotly.newPlot` **dans la sortie committée**. Aucune des cellules réellement converties sur `main` ne l'aurait passé : le gate rejetait les instances conformes et acceptait celles qui rendent blanc. C'est le défaut central corrigé ici.

## QA visuelle — ce que le forensique attrape, et ce qu'il n'attrape pas

La règle de routage vision ([model-delegation.md](../../.claude/rules/model-delegation.md) §« Capacité vision ») impose de faire vérifier tout rendu visuel par un modèle qui **voit**, jamais text-only. Elle vise la classe où **« exister sur disque » ≠ « rend correctement »**.

**Le SVG inline est forensiquement inspectable** — la géométrie est dans la sortie committée, en clair : un `<rect>` de largeur nulle, une série toute à zéro, un `viewBox` incohérent se lisent sans regard. C'est ce qui rend le gate ci-dessus efficace. Trois modes d'échec restent **invisibles au forensique** et exigent un regard :

| Mode d'échec | Détectable sans regard ? |
|---|---|
| Géométrie nulle / série vide / cadre sans données | **oui** — grep sur les coordonnées de la sortie |
| Séparateur décimal virgule (culture non invariante) | **oui** — grep `='\d+,\d` dans les attributs SVG |
| Couleurs illisibles, chevauchement de labels, axes inversés | **non** — spot-check visuel |

**Le contrôle de merge est donc : forensique par PR (obligatoire) + spot-check de rendu par vague ou par nouveau type de figure** — extraire le SVG committé → HTML autonome → screenshot → lire l'image depuis une lane qui voit (MiniMax/CoursIA-2 ou ai-01). Pas d'aller-retour vision à chaque PR une fois le type de figure validé.

## Provenance de cette correction

Cette section existe parce que la version précédente de ce fichier affirmait le contraire de ce qui précède, et que l'affirmation a survécu un mois à une review qui la contestait.

- **2026-07-15** — la doc est mergée (#6693) malgré une review `CHANGES_REQUESTED` signalant que sa « référence canonique » pointait une cellule sans figure copiable. Elle contenait aussi un raisonnement concluant que la classe Plotly-CDN **n'a pas besoin de QA visuelle par PR**, parce que le rendu client serait déterministe et ses modes d'échec tous forensiques — avec, en appui, un audit vision « 3 conversions rendues et **vues**, figures réelles ».
- **2026-07-16** — le user constate qu'un notebook de la famille n'affiche **aucun** graphique. L'investigation #6927 établit que **toute** la classe est blanche en consultation statique, sur 8 notebooks.

L'audit vision de la veille n'était pas faux : il avait regardé les bonnes figures **dans le mauvais renderer** (kernel live, où le CDN s'exécute). La table des « modes d'échec » de la doc en omettait un — le seul qui se produisait réellement — et son absence servait à conclure qu'on pouvait se passer du regard. C'est le mécanisme, plus que le contenu, qui vaut d'être retenu : **une preuve rendue sur une surface qui n'est pas celle du livrable ne prouve rien du livrable.**

Le pointeur `MGS-10 cell[8]`, lui, est devenu **exact** entre-temps, mais par accident : la cellule a été convertie en SVG inline par la vague #6927, si bien qu'elle contient désormais bien une barre horizontale signée — sous une technique que l'ancienne version de cette doc ne décrivait pas. La review avait raison au moment où elle l'a écrit.

## Notebooks du rollout (état mesuré sur `main`, 2026-08-15)

| État | Notebooks |
|---|---|
| **Converti** (SVG inline, plus de CDN dans la source) | `App-7b-Wordle-CSharp`, `MGS-10-CenterBias` |
| **Partiel** (SVG inline **et** cellules CDN résiduelles) | `GameTheory-3-Topology2x2-Csharp`, `Infer-17-Kalman-Filter`, `Sudoku-18-Comparison-Csharp` |
| **Non converti** (CDN seul → blanc en statique) | `Infer-11-Topic-Models`, `Infer-12-Modeles-Hierarchiques`, `DecInfer-6-Value-Information`, `DecInfer-7-Expert-Systems`, `DecInfer-8-Sequential` |

Mesure reproductible : source de cellule de code contenant `PlotSvg` / `cdn.plot.ly` / `PlotlyHtml`, sur `git ls-files "*.ipynb"`. Les 5 « non converti » + 3 « partiel » sont le reste du rollout #6927 sous l'EPIC #3801.

## Refactor possible (memo)

Extraire le préambule de la forme A (`record PlotSvg` + `Formatter.Register`) dans un helper partagé chargé via `#load` (ex. `notebook-helpers/PlotSvgHelper.cs`) éviterait la ré-inscription du formatter dans chaque notebook. Attention à la re-entry (`Formatter.Register` appelé deux fois) — la mitigation actuelle est un préambule **idempotent par cellule** ; un helper devrait garder l'enregistrement idempotent (garde `if`/registre statique).

## Voir aussi

- [sota-not-workaround.md](../../.claude/rules/sota-not-workaround.md) — Prong-A : vrai outil, jamais workaround dégradé (EPIC #3801)
- [pr-review-discipline.md](../../.claude/rules/pr-review-discipline.md) — §D (preuve d'exécution notebook) + §H (SOTA)
- [notebook-conventions.md](../../.claude/rules/notebook-conventions.md) — §Exécution (.NET Papermill `.net-csharp`)
- [model-delegation.md](../../.claude/rules/model-delegation.md) — §Capacité vision : router le QA visuel vers une lane qui voit
- #6927 (investigation blanc-en-statique, 8 notebooks) · #6946 (première conversion) · #6693 (la review dont la correction avait été ignorée)
- CLAUDE.md §F — environnement : réparer, jamais contourner
