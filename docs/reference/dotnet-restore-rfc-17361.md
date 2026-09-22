# Reproduction et workaround : bug `#r nuget:` dans dotnet-interactive 1.0.617701 (po-2027)

**Issue** : #17361 — `env: restore #r nuget/#r file cassé dans dotnet-interactive sur po-2027 (les 2 builds) — re-exec .NET bloquée`

**Statut** : reproduction confirmée first-hand, workaround identifié, fix de root cause **out-of-scope** (bug interne `Microsoft.DotNet.Interactive.PackageManagement`).

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

**Conclusion mesurée** : le `PackageRestoreContext` interne reste dans un état où `succeeded=false` est passé sans `errors` dès le **second restore NuGet dans une session kernel**. Pas une question de version ni de multi-cellules — strictement "**2ᵉ restore NuGet au total**". B et C confirment ; A isole l'état initial ; D montre le by-pass `file.dll` ; **E réfute l'hypothèse initiale** selon laquelle `file.dll` réinitialiserait le contexte (et disqualifie la workaround « mix file.dll + nuget intercalés »).

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
// #r "nuget: QuikGraph, 2.5.0"   ← plante au 2ᵉ restore dans la session

// Utiliser un path résolu via le profil utilisateur :
var profile = Environment.GetFolderPath(Environment.SpecialFolder.UserProfile);
#r $"{profile}/.dotnet_packages/quikgraph/2.5.0/lib/netstandard2.0/QuikGraph.dll"
```

La mesure discriminante c.760 (probe E) **réfute** l'hypothèse initiale « `file.dll` réinitialise le `PackageRestoreContext` » : un `#r "nuget:"` après un `#r "file.dll"` lève toujours `ArgumentException`. Donc la workaround est **univoque** : **préchargement complet seul** (tous les packages NuGet en `.dll` locaux via le helper `dotnet_preload_packages.py`, pointant sur `%USERPROFILE%/.dotnet_packages/<pkg>/<ver>/`), pas de mix `file.dll` + `nuget` dans la même session kernel.

## Cause racine (out-of-scope)

Bug interne dans `Microsoft.DotNet.Interactive.PackageManagement.PackageRestoreResult..ctor` : lève `ArgumentException` si `succeeded=false` est passé avec `errors=null` ou vide. C'est un état que le code ne devrait jamais produire — probablement une race condition dans `RestoreAsync()`.

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
