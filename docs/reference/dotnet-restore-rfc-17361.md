# Reproduction et workaround : bug `#r nuget:` dans dotnet-interactive 1.0.617701 (po-2027)

**Issue** : #17361 — `env: restore #r nuget/#r file cassé dans dotnet-interactive sur po-2027 (les 2 builds) — re-exec .NET bloquée`

**Statut** : bug **réel mais non déterministe** — reproduit 3× le 2026-09-22 (c.760), non reproduit sur 2 re-tentatives le 2026-09-23 (c.803 cache chaud, c.807 cache froid — section *Mesures de reproduction*). Workaround identifié, fix de root cause **out-of-scope** (bug interne `Microsoft.DotNet.Interactive.PackageManagement`).

## Reproduction (3 probes livrés, 5 tentées)

**Tentées** (mesure first-hand c.760, po-2027) :

| # | Probe | Résultat |
|---|---|---|
| A | cellule unique avec `#r "nuget: IKVM, 8.15.0"` seul | ✅ restore OK |
| B | cellule 2 (post-A) avec `#r "nuget: QuikGraph, 2.5.0"` | ❌ `PackageRestoreResult..ctor ArgumentException: Must provide errors when succeeded is false` |
| C | cellule unique avec 2 `#r` consécutifs (`IKVM` puis `QuikGraph`) | ❌ même erreur |
| D | cellule unique avec `#r "file.dll"` (path local résolu via `Environment.SpecialFolder.UserProfile`) | ✅ restore OK |
| E | cellule post-D avec `#r "nuget: CsvHelper, 33.0.1"` | ❌ `ArgumentException` — `file.dll` ne réinitialise **pas** le `PackageRestoreContext` |

**Livrées dans `scripts/notebook_tools/probes/dotnet-restore-bug-17361.ipynb`** : A, D, E (3 cellules code, exécution Papermill c.760).

### Mesures de reproduction (historique)

| Cycle | Date | Conditions | Résultat |
|---|---|---|---|
| c.760 | 2026-09-22 (soir) | 3 exécutions (têtes `261d8aa709`, `03260ceae2`, run Papermill 01:42Z `exception: true`) | ❌ `ArgumentException` ×3 |
| c.803 | 2026-09-23 15:10Z | cache NuGet chaud (`csvhelper/33.0.1` présent) | ✅ restore OK |
| c.807 | 2026-09-23 17:44Z | cache NuGet **froid** (`33.0.1` purgé avant le run, re-téléchargé pendant) | ✅ restore OK |

L'hypothèse « cache chaud explique la non-reproduction » est **réfutée** par c.807 : même à cache froid, le 2ᵉ restore NuGet de la session (probe E, séquence identique A → D → E) a réussi. La précondition exacte du bug reste **inconnue**.

**Conclusion mesurée (c.760, à lire avec l'historique ci-dessus)** : le `PackageRestoreContext` interne était dans un état où `succeeded=false` était passé sans `errors` au **second restore NuGet dans une session kernel** — 3 fois sur 3 le 2026-09-22, puis plus jamais sur les re-tentatives du 2026-09-23. Pas une question de version ni de multi-cellules — la séquence « **2ᵉ restore NuGet au total** » est le déclencheur observé quand il se produit. B et C confirment (c.760) ; A isole l'état initial ; D montre le by-pass `file.dll` ; **E réfute l'hypothèse initiale** selon laquelle `file.dll` réinitialiserait le contexte (et disqualifie la workaround « mix file.dll + nuget intercalés »).

## Workaround applicable

**Précharger** les packages NuGet en assemblies locales (résolution + copie par helper Python), puis référencer par `#r "file.dll"` dans les notebooks :

```bash
# scripts/ci/dotnet_preload_packages.py — LIVRÉ (livrable 2)
# Lit une liste de packages, résout le cache NuGet global (ou le peuple par
# `dotnet restore` s'il est absent), copie les .dll dans `_deps/` et émet
# `_deps/.NET-packages.json` avec les lignes `#r` prêtes à coller.
python scripts/ci/dotnet_preload_packages.py QuikGraph==2.5.0 CsvHelper==33.0.1 IKVM
```

La copie est **à plat** dans `_deps/` — et non dans `.dotnet_packages/<pkg>/<ver>/`
comme l'esquissait la première rédaction de ce RFC : `#r` est résolu au parse-time
et exige un littéral relatif au notebook, dont la forme mesurée (c.790) est
`./_deps/<Dll>.dll`. Les dépendances transitives ne sont **pas** résolues — un
package qui en déclare (IKVM par exemple) doit les lister lui-même sur la ligne
de commande.

```csharp
// Dans un notebook .NET, au lieu de :
// #r "nuget: QuikGraph, 2.5.0"   ← a planté au 2ᵉ restore dans la session (c.760 ; non déterministe)

// Référencer une assembly locale — le `#r` est résolu au parse-time et exige un
// LITTÉRAL (ni variable ni interpolation) : la forme mesurée c.790/c.803 est le
// chemin RELATIF depuis le dossier du notebook :
// #r "./_deps/QuikGraph.dll"
// (DLL copiée au préalable depuis le cache NuGet vers _deps/, gitignore)
```

La mesure discriminante c.760 (probe E) **réfute** l'hypothèse initiale « `file.dll` réinitialise le `PackageRestoreContext` » : un `#r "nuget:"` après un `#r "file.dll"` a levé `ArgumentException` à chacune des 3 exécutions de c.760. **Mais** la re-production a échoué sur les 2 re-tentatives du 2026-09-23 (c.803 cache chaud, c.807 cache froid) : le bug est **non déterministe**. La recommandation reste néanmoins **univoque et défensive** : **préchargement complet seul** (tous les packages NuGet en `.dll` locaux, via `./_deps/` relatif et le helper `scripts/ci/dotnet_preload_packages.py`), pas de mix `file.dll` + `nuget` dans la même session kernel — quand l'exception se produit, elle tue la cellule sans contournement runtime.

## Pilot du livrable 3 : le remplacement n'est PAS équivalent (mesuré 2026-09-25)

Le livrable 3 (« convertir `#r "nuget:"` en `#r` local ») suppose que les deux formes sont interchangeables. **Elles ne le sont pas.** Mesure sur `MyIA.AI.Notebooks/Search/Part2-CSP/CSP-1-Fundamentals-CSharp.ipynb` — le notebook du dépôt le plus exposé au bug (3 restores NuGet dans une seule cellule, cellule 3 : `IKVM`, `IKVM.Image`, `IKVM.Image.runtime.win-x64`), exécuté sur po-2024 avec le kernel `.net-csharp` et le pin cluster `1.0.617701` :

| Bras | Cellule 3 (les `#r`) | Résultat | Diagnostic |
|---|---|---|---|
| **0 — original** | 3 × `#r "nuget:"` | **19/19 OK**, 0 erreur, 14,1 s | — |
| **A — converti** | 3 × `#r "./_deps/…"` (helper) | **16/19**, 3 erreurs (cellules 32, 34, 37) | `IKVM.Runtime.InternalException: Could not locate ikvm home path` |
| **C — mixte** | `IKVM` local + les 2 packages image en `nuget:` | **15/19**, 4 erreurs (cellule 3 *et* 32-37) | `IKVM.Image.targets(45,9): error MSB4036: Tâche "IkvmResolveNearestRuntimeIdentifier" introuvable` |

Le bras C est celui qui explique les deux autres : les trois `#r` ne sont pas de simples **références**, ce sont eux qui font restaurer à `Microsoft.DotNet.Interactive.PackageManagement` l'**arbre IKVM complet** (`IKVM.MSBuild` fournit la tâche MSBuild que `IKVM.Image.targets` invoque ; l'image `any/any` + `win-x64` fournit le home que `IKVM.Runtime` cherche au premier type `java.*`). Retirer ou scinder les `#r` casse ce graphe : le bras C échoue **dès la cellule 3** sur la tâche MSBuild manquante, le bras A va plus loin mais échoue au premier appel Java faute de home.

Deux conséquences pour le livrable 3, dans cet ordre :

1. **Il est réfuté pour la famille IKVM** — et cette famille est justement celle qui porte le plus de restores par cellule (Choco, Tweety, RDF.Net).
2. **`IKVM.Image` et `IKVM.Image.runtime.win-x64` ne sont pas exprimables en `#r` local du tout** : leurs dossiers `lib/<tfm>/` ne contiennent qu'un `_._`, la convention NuGet « ce TFM est compatible, mais ce package n'apporte aucune assembly ». Le helper le dit correctement (`aucune assembly dans …/lib`), ce qui n'est pas un défaut de l'outil mais la limite du remplacement.

S'y ajoute un coût de distribution, indépendant du bug : `_deps/` est **gitignore**, donc un notebook committé en `#r "./_deps/X.dll"` casse pour quiconque clone — un échec **déterministe** (« fichier introuvable ») en échange d'un bug **non déterministe**.

**Décision qui en découle** : le helper reste un **outil de réparation à la demande** — à invoquer quand l'exception se produit, sur le notebook concerné — et **non** une convention à généraliser aux notebooks pédagogiques. Le bras 0 montre au passage une 4ᵉ non-reproduction du bug : 3 restores dans une cellule, tous réussis (corrobore c.803 et c.807, après les 3 repros de c.760).

## Cause racine (out-of-scope)

Bug interne dans `Microsoft.DotNet.Interactive.PackageManagement.PackageRestoreResult..ctor` : lève `ArgumentException` si `succeeded=false` est passé avec `errors=null` ou vide. C'est un état que le code ne devrait jamais produire — probablement une race condition dans `RestoreAsync()`. Hypothèse **renforcée** par c.807 : la même séquence de commandes échouait le 2026-09-22 et réussit le 2026-09-23 (y compris à cache froid) — le facteur variable est le **chemin/timing interne du restore**, pas la séquence des `#r` ; une race sur un restore concurrent (latence réseau, résolution, écriture cache) reste l'explication la plus cohérente.

**À escalader upstream** : https://github.com/dotnet/interactive/issues (chercher `PackageRestoreResult..ctor ArgumentException`).

## Fix de root cause côté po-2027

**NON applicable localement** :
- Le pin `1.0.617701` (état cluster) ne corrige que le mono-restore, pas le multi
- Le `1.0.712001` (état-trouvé #17361) a un bug encore plus large (mono KO aussi)
- Pas d'option CLI `dotnet interactive jupyter` qui contourne

**Option à explorer** : mise à jour vers `Microsoft.DotNet.Interactive` >= 1.0.720000 si le bug y est fixé (à vérifier upstream).

## Livrables possibles (par ordre de coût)

1. **MAINTENU** : ce RFC documente le bug et la workaround pour les pairs.
2. **LIVRÉ (outillage)** : `scripts/ci/dotnet_preload_packages.py` + `scripts/tests/test_dotnet_preload_packages.py` (41 cas) + entrée `.gitignore` de `_deps/`. Usage retenu (cf pilot) : **réparation à la demande** sur un notebook qui a effectivement levé l'exception, **pas** une convention à généraliser.
3. **MOYEN TERME — RÉFUTÉ par la mesure** (pilot du 2026-09-25, section dédiée) : convertir tous les `.net-csharp` en `#r` local n'est pas un remplacement équivalent (les `#r "nuget:"` portent le graphe de restauration dont dépendent `IKVM.MSBuild` et le home JVM), et `_deps/` étant gitignore, la conversion rendrait le notebook déterministiquement cassé pour tout clone. **Ne pas lancer cet audit comme conversion de masse.** Le geste utile restant : convertir au cas par cas, **quand** l'exception s'est effectivement produite sur ce notebook.
4. **LONG TERME** : fix upstream + bump version cluster.
