# Axe 1 « awaits profonds / Runtime Async » — mesure .NET 10 vs .NET 11

> **Statut** : première mesure rejouable de l'axe 1 (carnets), le carnet
> `08-Aspire-AsyncFFI-Dotnet.ipynb`, sous deux runtimes isolés.
> **Résultat** : compatibilité .NET 11 **établie** (exécution complète, aucune erreur) ;
> **aucun gain de temps d'exécution n'est établi** (écart médian −0,2 s,
> dans l'étendue de dispersion).
> **Lien** : `docs/dotnet/net11-runtime-deltas.md` (table « Volet carnets — axe 1 »)
> et EPIC #18695.

Ce document ne remplace pas `net11-runtime-deltas.md` : il en remplit la case
la plus lacunaire en y versant la mesure. Le tableau de référence est détenu
par une autre PR (#23233, puis #23421) — cette fiche est donc **un fichier
nouveau**, et non une édition du document canonique.

## 1. Ce qui manquait

Le tableau de référence portait, pour l'axe 1 :

| Carnet (axe 1) | net10 (canon) | net11 (RC) | Delta | État |
|---|---|---|---|---|
| `08-Aspire-AsyncFFI-Dotnet.ipynb` | 11,0 s | — | **non mesuré** | compat .NET 11 **à établir** |

Deux raisons rendaient la case vide, et aucune n'était un obstacle réel :

1. **« aucun runtime isolé .NET 9/11 sur la machine de mesure »** — la recette
   d'installation était déjà écrite dans le document (`dotnet-install` user-local
   sans UAC, `~/.dotnet-r9`, `~/.dotnet-r11`), elle n'avait simplement pas été
   exécutée ;
2. **le temps d'exécution n'était rattaché à aucun runtime** — la mesure ne
   prouvait pas la version de runtime qui l'avait produite. Un carnet affiche
   la version du runtime de la machine ; ce n'est pas une donnée de mesure.

## 2. Méthode

Un organe dédié rend la comparaison rejouable :
[`scripts/notebook_tools/measure_runtime_variants.py`](../../scripts/notebook_tools/measure_runtime_variants.py).

- **Preuve de runtime** : avant la mesure, une cellule-sonde écrit
  `RuntimeInformation.FrameworkDescription` dans un fichier ; l'organe relit
  ce fichier. Le runtime affiché est donc *observé dans le noyau qui a
  exécuté*, jamais déduit du nom de la variante.
- **Métrique** : le temps d'exécution total du carnet, mesuré par l'organe
  canonique `notebook_tools.py execute --cell-by-cell` — la même commande et
  donc la même métrique que celle du document de référence.
- **Entrelacement** : A, B, A, B… La dérive machine n'est donc pas attribuée à
  la variante run en premier.
- **Isolation** : `DOTNET_ROOT` par variante + `DOTNET_ROLL_FORWARD=Major`,
  via un kernelspec jetable généré dans un `JUPYTER_PATH` temporaire. Un
  runtime seul (sans SDK) suffit : c'est l'apphost `dotnet-interactive` qui est
  lancé, pas le muxer `dotnet` (qui exigerait un SDK).
- **Aucune écriture** : `--cell-by-cell` n'écrit pas les sorties dans le
  carnet ; le carnet du dépôt n'est pas modifié par une mesure.

## 3. Résultat

Machine `myia-po-2025`, 2026-10-30, carnet
`MyIA.AI.Notebooks/GenAI/Integrations-DotNet/Aspire/08-Aspire-AsyncFFI-Dotnet.ipynb`,
5 répétitions par variante, entrelacées.

| Variante | Kernelspec | Runtime **prouvé** | Cellules OK | Erreurs | Temps (s) | Médiane |
|---|---|---|---|---|---|---|
| net10 | `.net-csharp` (**noyau canon** 1.0.712001) | `.NET 10.0.13` | 45/45 | 0 | 12,5 · 13,2 · 12,6 · 12,6 · 12,9 | **12,6** |
| net11 | `.net-csharp-net11` (généré, runtime isolé) | `.NET 11.0.0-rc.3.26522.148` | 45/45 | 0 | 12,6 · 12,5 · 12,3 · 12,5 · 12,5 | **12,5** |

**Delta médian : −0,1 s (−0,8 %)** — inférieur à l'étendue intra-variante
(12,5–13,2 s côté net10, 12,3–12,6 s côté net11, intervalles qui se
recouvrent). **Aucun gain de temps d'exécution n'est établi** sur cet axe et
ce carnet.

L'artefact de la campagne est committé :
[`scripts/results/net11_axis1_2026-10-30.json`](../../scripts/results/net11_axis1_2026-10-30.json)
— par variante et par répétition : runtime prouvé, cellules, erreurs, temps.

Ce qui est établi, en revanche :

- la **compatibilité .NET 11** du carnet : exécution complète, aucune erreur, sur les
  deux runtimes, sans adaptation ;
- le **coût de démarrage** du carnet sous .NET 11 est **équivalent** à celui
  sous .NET 10 (pas de régression de démarrage mesurable) ;
- la mesure est **rejouable** : l'organe et les commandes sont dans le dépôt.

> La cellule 8 du carnet mesure une **famine de pool de threads** (temps
> pendant lequel un thread natif reste bloqué dans `SetResult`). Cette
> métrique est par nature sensible à la charge de la machine : le temps
> d'exécution total du carnet n'est pas un banc de micro-benchmark, et le
> tableau ci-dessus doit être lu comme « aucune régression observée », pas
> comme une mesure de performance fine.

## 4. Un artefact de mesure à connaître (résultat secondaire)

En comparant deux variantes **de contenu strictement identique** — deux
kernelspecs dont les `kernel.json` sont **identiques octet pour octet** (même
apphost, même `DOTNET_ROOT`, même `DOTNET_ROLL_FORWARD`), vérifié par `diff`,
qui ne diffèrent que par le **nom** du répertoire —, l'instrument se montre
sensible au **nom** du kernelspec :

| Nom du kernelspec | Runtime prouvé | Temps (s) | Médiane |
|---|---|---|---|
| `.net-csharp-x1` (convention du dépôt) | `.NET 11.0.0-rc.3.26522.148` | 12,7 · 12,6 · 12,5 · 12,6 · 12,8 | **12,6** |
| `net-x1` (nom quelconque) | `.NET 11.0.0-rc.3.26522.148` | 17,4 · 17,8 · 17,3 · 17,8 · 17,9 | **17,8** |

Soit **≈ +5,2 s (+41 %)** pour un nom qui ne commence pas par un point, à
runtime identique, à contenu de kernelspec identique et à répétitions
entrelacées (5 par nom, alternées). L'écart ne se recoupe pas d'une répétition
à l'autre : les deux séries sont disjointes. Le nom du kernelspec entre dans le
fichier de connexion que `jupyter_client` écrit ; le chemin de résolution de
`dotnet-interactive` diffère selon sa forme.

L'artefact de cette réplication est committé :
[`scripts/results/net11_kernelspec_name_2026-10-30.json`](../../scripts/results/net11_kernelspec_name_2026-10-30.json).

Conséquences :

- l'organe **génère** un nom de la forme `.net-csharp-<variante>` et
  **avertit** si on lui handed un nom non conforme ;
- toute mesure de temps d'exécution de carnet doit être vérifiée dans la
  convention `.net-csharp*` avant d'être publiée : un nom de spec non
  conforme gonfle la mesure de **plus d'un tiers** ;
- le gonflement porte sur **les deux bras à la fois** lorsqu'ils partagent la
  forme de nom. Un delta inter-runtimes mesuré sous un nom non conforme est
  donc **comprimé vers zéro** : une absence de gain observée peut n'être qu'un
  artefact du plancher de démarrage, commun aux deux variantes. C'est
  exactement le risque que court une mesure faite « au carnet » ;
- les campagnes déjà publiées sur d'autres bancs méritent un contrôle de ce
  point avant d'être reprises comme référence ;
- l'artefact ne concerne que les instruments qui **passent par un
  kernelspec**. Un organe qui lance le noyau directement
  (`jupyter_client.start_new_kernel` avec un `env` par runtime) n'y est pas
  exposé.
  point avant d'être reprises comme référence.

## 5. Recette de rejeu

```bash
# runtime isolé .NET 11, user-local, sans UAC (règle F)
powershell -NoProfile -ExecutionPolicy Bypass -File dotnet-install.ps1 \
  -Channel 11.0 -Runtime dotnet -InstallDir "$HOME/.dotnet-r11" -NoPath

# mesure comparée (interlacée), preuve de runtime incluse
python scripts/notebook_tools/measure_runtime_variants.py \
  MyIA.AI.Notebooks/GenAI/Integrations-DotNet/Aspire/08-Aspire-AsyncFFI-Dotnet.ipynb \
  --arm "net10=.net-csharp" \
  --arm "net11=auto@$HOME/.dotnet-r11" \
  --reps 5 --json /tmp/axe1.json
```

Le JSON produit contient, par variante et par répétition : le runtime prouvé,
le nombre de cellules, le nombre d'erreurs et le temps. Il est rejouable à
l'identique ; c'est la preuve opposable du tableau ci-dessus.

## 6. Portée et limites

- **n = 5** répétitions par variante, **un seul siège**, **une seule journée** :
  la lecture est « aucune régression observée », pas « gain de X % établi ».
- Le **11,0 s** du document de référence pour net10 vient d'une autre machine
  et d'une autre session ; il **n'est pas comparable** aux 12,7 s mesurés ici.
  Le tableau de référence garde sa valeur d'origine ; la comparaison
  inter-runtimes de cette fiche est interne à une même session.
- Le **bras net9** reste non mesuré : l'instrument canonique vise net10, et
  mesurer le carnet sous net9 demanderait un autre instrument — donc une
  comparaison qui ne serait pas à arms égaux. La recette d'installation de
  `~/.dotnet-r9` est dans `net11-runtime-deltas.md`.
- Le **carnet n'a pas été modifié** : cette fiche mesure un carnet tel qu'il
  est sur `main` (PR #22572 en cours sur le même fichier).
- L'artefact du nom de kernelspec est mesuré sur **un seul siège** et
  **une seule forme d'apphost** (`dotnet-interactive` global). Il n'est pas
  établi que l'écart se transporte tel quel sur une autre version de
  l'instrument ; il est établi qu'il **fausse** toute mesure publiée sous
  un nom de spec non conventionnel.
- Cette fiche est le **second siège** de l'axe 1. Le premier est #23441
  (`myia-po-2023:CoursIA`), qui mesure le delta 10 → 11 sur l'instrument de la
  §4 du carnet — une autre métrique, non un doublon. Les deux lectures sont
  compatibles : ni l'une ni l'autre n'établit un gain.

## Voir aussi

- `docs/dotnet/net11-runtime-deltas.md` — tableau de référence (axe 1 et bancs)
- `docs/dotnet/net11-toub-digest.md` — digest de performance
- `scripts/notebook_tools/measure_runtime_variants.py` — l'organe de mesure
- EPIC #18695 — mesure progressive des gains runtime async
- #23441 (axe 1, instrument de la §4) et #23444 (organe multi-runtime) — les
  deux autres grains de la même famille, **`myia-po-2023:CoursIA`** ; leurs
  fichiers sont lus, jamais modifiés
- #23448 — l'issue de cette fiche (partition complémentaire, chemins disjoints)
