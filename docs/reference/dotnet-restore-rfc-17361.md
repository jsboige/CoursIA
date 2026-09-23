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

```python
# scripts/ci/dotnet_preload_packages.py — TODO: à implémenter
# - Lit une liste de packages (ex: ikvm, quikgraph, csvhelper)
# - Pour chaque : nuget restore -> copie .dll dans .dotnet_packages/<pkg>/<ver>/
# - Émet un manifest .NET-packages.json avec paths résolus
```

```csharp
// Dans un notebook .NET, au lieu de :
// #r "nuget: QuikGraph, 2.5.0"   ← a planté au 2ᵉ restore dans la session (c.760 ; non déterministe)

// Référencer une assembly locale — le `#r` est résolu au parse-time et exige un
// LITTÉRAL (ni variable ni interpolation) : la forme mesurée c.790/c.803 est le
// chemin RELATIF depuis le dossier du notebook :
// #r "./_deps/QuikGraph.dll"
// (DLL copiée au préalable depuis le cache NuGet vers _deps/, gitignore)
```

La mesure discriminante c.760 (probe E) **réfute** l'hypothèse initiale « `file.dll` réinitialise le `PackageRestoreContext` » : un `#r "nuget:"` après un `#r "file.dll"` a levé `ArgumentException` à chacune des 3 exécutions de c.760. **Mais** la re-production a échoué sur les 2 re-tentatives du 2026-09-23 (c.803 cache chaud, c.807 cache froid) : le bug est **non déterministe**. La recommandation reste néanmoins **univoque et défensive** : **préchargement complet seul** (tous les packages NuGet en `.dll` locaux, via `./_deps/` relatif en attendant le helper `dotnet_preload_packages.py`), pas de mix `file.dll` + `nuget` dans la même session kernel — quand l'exception se produit, elle tue la cellule sans contournement runtime.

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
2. **COURT TERME** : `scripts/ci/dotnet_preload_packages.py` (helper ~50 lignes) + convention `.net-csharp` notebooks.
3. **MOYEN TERME** : audit complet de tous les notebooks `.net-csharp` pour convertir les `#r "nuget:"` en `#r "file.dll"`.
4. **LONG TERME** : fix upstream + bump version cluster.
