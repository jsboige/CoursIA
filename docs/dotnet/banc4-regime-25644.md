# Banc 4 : contrôle du régime de mesure sur .NET 9 et 10

Cette campagne complète le contrôle du banc 1 décrit dans [la note des deltas runtime](net11-runtime-deltas.md) et répond à une partie de [#25644](https://github.com/jsboige/CoursIA/issues/25644) : que devient le banc `prompt-settings` quand on change le nombre d'invocations et le tiering ? Elle ne mesure pas .NET 11. Les résultats sont propres à cet hôte et ne permettent pas d'établir un classement portable ni un mécanisme causal.

## Résultat

La dispersion est assez forte pour rendre plusieurs classements **indéterminés**. Le tableau donne les trois rapports appariés **moyenne .NET 10 / moyenne .NET 9**, par ordre de passe ; un rapport inférieur à 1 indique un temps inférieur pour .NET 10 dans cette paire. Chaque moyenne porte sur les `WorkloadResult` retenus par BenchmarkDotNet (BDN), et les trois passes, non les itérations, sont les répétitions.

| Méthode | Une invocation, défaut | Une invocation, tiering désactivé | Auto, défaut | Auto, tiering désactivé |
|---|---|---|---|---|
| `Signature_Matches` | 2,682 ; 0,670 ; 0,426 | 0,159 ; 0,929 ; 0,498 | 0,644 ; 0,862 ; 0,798 | 0,910 ; 0,948 ; 0,471 |
| `JsonSerialize_PromptSettings` | 2,512 ; 0,252 ; 0,839 | 4,049 ; 2,603 ; 3,661 | 0,357 ; 2,120 ; 1,335 | 1,400 ; 2,081 ; 1,295 |
| `RequestSettings_RoundTrip` | 0,176 ; 0,539 ; 0,524 | 1,872 ; 1,863 ; 2,135 | 0,470 ; 0,652 ; 1,620 | 1,370 ; 1,283 ; 3,595 |
| `Transform_InterpolateKeys` | 0,969 ; 1,010 ; 0,779 | 0,302 ; 2,852 ; 1,138 | 2,493 ; 1,020 ; 0,872 | 1,126 ; 0,967 ; 0,804 |

Les trois paires de `RequestSettings_RoundTrip` changent de côté entre défaut et tiering désactivé dans le régime à une invocation. C'est une observation sur cette campagne, pas une preuve que le tiering seul cause une inversion : ces configurations ne sont pas adjacentes dans le temps et leurs rapports varient beaucoup. Sur `JsonSerialize_PromptSettings` en auto et tiering par défaut, les trois rapports de 0,357 à 2,120 passent de part et d'autre de 1. Même lorsque trois rapports sont du même côté de 1, trois passes sur un seul hôte ne suffisent pas à garantir la reproductibilité.

Le rapport une invocation / auto varie lui aussi fortement. Par exemple, pour `Signature_Matches`, .NET 9 avec tiering par défaut, il vaut 185,45 ; 171,64 ; 302,10 selon la passe. Il ne reproduit donc pas quantitativement le facteur historique ×3 à ×55 et ne démontre pas son mécanisme. Les deux régimes sont mesurés dans la même passe, mais séparés dans le temps ; aucune correction de dérive n'est supposée.

## Profil par itération

Le rapport final de BDN ne publie qu'une moyenne par cellule : un passage du JIT du tier 0 au tier 1 pendant la fenêtre mesurée y devient invisible, et la moyenne publiée est alors un mélange. Le journal d'itérations, lui, garde l'ordre des quinze mesures. Cette section publie ce profil pour les 96 jambes, à partir des seules données JSON déjà déposées : [profil détaillé](banc4-regime-25644-profile.md) et [CSV](banc4-regime-25644-profile.csv), produits par [`scripts/benchmarks/bdn_iteration_profile.py`](../../scripts/benchmarks/bdn_iteration_profile.py).

**Méthode.** Pour chaque jambe, la série des quinze `WorkloadActual` est ramenée en microsecondes ; le point de coupe qui maximise le rapport des médianes avant/après est retenu, avec au moins trois itérations de chaque côté. Sur une série sans ordre temporel, ce maximum est toujours supérieur à 1 : il est donc confronté à 500 permutations de la même série (graine 20261115). La p-valeur est unilatérale et sa résolution vaut 1/501. Les deux fichiers se régénèrent à l'identique depuis le JSON (SHA-256 `603aa2822c532d18bd6880dc2e412fbc210c90076c488c8aa9f12e2c7f21ca67`) par :

```bash
python scripts/benchmarks/bdn_iteration_profile.py \
    --artifact docs/dotnet/banc4-regime-25644.json \
    --out-csv docs/dotnet/banc4-regime-25644-profile.csv \
    --out-md  docs/dotnet/banc4-regime-25644-profile.md
```

Les onze jambes dont la marche dépasse l'ordre aléatoire au seuil de 0,05, sur 96 :

| Méthode | Runtime | Régime | Tiering | Passe | Moyenne (µs/op) | Position | Rapport | p | Part |
|---|---|---|---:|---:|---:|---:|---:|---:|
| `Signature_Matches` | 9.0.22 | une invocation | défaut | 2 | 17,24 | 5 | 1,47 | 0,002 | 0,606 |
| `RequestSettings_RoundTrip` | 10.0.14 | auto | défaut | 2 | 25,70 | 8 | 3,82 | 0,004 | 0,590 |
| `Transform_InterpolateKeys` | 9.0.22 | auto | défaut | 1 | 6,77 | 3 | 3,98 | 0,010 | 0,411 |
| `RequestSettings_RoundTrip` | 9.0.22 | auto | défaut | 1 | 403,82 | 12 | 1,71 | 0,010 | 0,375 |
| `Transform_InterpolateKeys` | 9.0.22 | une invocation | désactivé | 2 | 62,09 | 3 | 4,46 | 0,012 | 0,591 |
| `Signature_Matches` | 10.0.14 | une invocation | désactivé | 1 | 74,40 | 3 | 1,50 | 0,012 | 0,950 |
| `JsonSerialize_PromptSettings` | 9.0.22 | auto | défaut | 1 | 130,90 | 12 | 4,07 | 0,014 | 0,703 |
| `Transform_InterpolateKeys` | 9.0.22 | auto | désactivé | 3 | 8,20 | 12 | 2,36 | 0,020 | 0,524 |
| `Signature_Matches` | 10.0.14 | une invocation | désactivé | 2 | 17,32 | 3 | 1,34 | 0,030 | 0,696 |
| `RequestSettings_RoundTrip` | 9.0.22 | auto | défaut | 2 | 39,42 | 4 | 2,77 | 0,040 | 0,347 |
| `Signature_Matches` | 9.0.22 | auto | désactivé | 1 | 0,23 | 4 | 1,87 | 0,040 | 0,256 |

*Position* : nombre d'itérations avant la marche. *Rapport* : médiane avant / médiane après. *Part* : fraction de la moyenne publiée qui disparaît si l'on prend la médiane d'après la marche comme coût établi.

**Le mélange est minoritaire dans cette campagne.** Onze jambes sur 96 au seuil de 0,05, dont quatre à 0,01 — contre une marche reproductible sur le banc 1. Le constat du banc 1 ne se transporte donc pas à l'ensemble du banc 4. Aucune dimension ne l'isole : 8 jambes sur 48 en .NET 9 contre 3 sur 48 en .NET 10, 4 sur 48 à une invocation contre 7 sur 48 en auto, 6 sur 48 avec tiering par défaut contre 5 sur 48 désactivé, et de 1 à 4 jambes sur 24 par méthode. Ce n'est pas la signature d'un régime.

**Le verdict ne dépend pas de la série retenue.** Le profil ci-dessus porte sur les quinze `WorkloadActual`, la série complète ; BDN publie sa moyenne à partir des `WorkloadResult` retenus, entre douze et quinze selon la jambe. Rejoué sur cette seconde série (`--kind result`), le relevé rend les **mêmes onze jambes** au seuil de 0,05, et trois au lieu de quatre au seuil de 0,01 : les rapports de médianes vont de 0,40 à 12,94 au lieu de 0,46 à 14,45. Le choix de la série ne fabrique donc pas le résultat.

**Ce que l'absence de détection ne dit pas.** Les 85 autres jambes ne sont pas exemptes de mélange : à quinze itérations et 40 à 80 % de dispersion, une marche tardive, partielle ou noyée dans le bruit n'est pas détectable. La non-significativité est une limite de puissance, pas une mesure d'absence.

**Les plus fortes inflations apparentes sont les moins significatives.** Six jambes portent une part supérieure à 0,90, c'est-à-dire une moyenne de dix à vingt-cinq fois la médiane d'après la marche. Toutes six sont dans le régime à une invocation, cinq à la première passe ; une seule franchit le seuil de 0,05. Les extrêmes : `Signature_Matches` 9.0.22, une invocation, tiering désactivé, passe 1 — moyenne 188,82 µs/op pour un régime établi de 7,40 µs, part 0,961, p = 0,56 ; et la même méthode en 10.0.14, un défaut, passe 1 — moyenne 202,26 µs pour 9,07 µs, rapport 14,45, p = 0,23. Sur ces jambes, la moyenne publiée surestime le régime établi d'un facteur 20 à 25, et l'ordre observé ne se distingue pourtant pas d'un mélange aléatoire. Une part élevée ne se publie donc jamais seule : sans le verdict de permutation, elle décrit une dispersion, pas une marche. La concentration dans la première passe du régime à une invocation désigne un endroit à instrumenter — l'échauffement et la calibration du premier lancement — elle n'établit pas le tiering comme cause.

**Une double unité dans le journal.** BDN choisit l'unité de la colonne par opération selon l'ordre de grandeur : sous la microseconde, il écrit `ns/op`, ailleurs `us/op`. Un premier relevé qui ne lisait que `us/op` n'a produit aucune erreur : il a rendu 84 jambes au lieu de 96, les douze `Signature_Matches` ayant silencieusement disparu du recensement. Le défaut est corrigé, un test le garde ([`scripts/tests/test_bdn_iteration_profile.py`](../../scripts/tests/test_bdn_iteration_profile.py)), et le lecteur qui réutilise le JSON rencontrera la même double unité.

**Ce que le profil ne démontre pas.** Une marche détectée n'identifie pas sa cause : le profil mesure un changement de régime dans la série, pas un passage de tier. La conclusion de la campagne reste celle du protocole — ni transition tier 0 → tier 1 démontrée, ni part précise du tiering, ni résultat sur .NET 11.

## Protocole et données

- Source inchangée : [`MyIntelligenceAgency/semantic-fleet`, commit `e675df97c4c511681c98d2d60ccd5fd26ce1b899`](https://github.com/MyIntelligenceAgency/semantic-fleet/tree/e675df97c4c511681c98d2d60ccd5fd26ce1b899/benchmarks/SemanticFleet.Benchmarks), quatre méthodes *single* d'origine ; BDN 0.15.8. Compilation Release unique ciblant `net9.0`, SDK 10.0.403. La compilation a utilisé `GITHUB_ACTIONS=true` : la condition existante de `dotnet/Directory.Build.targets` saute ainsi `dotnet format`, qui modifierait les sources ; le checkout est resté propre au pin. DLL SHA-256 `da0d4bee1e08c97a4b9c28dfdbc4c97ed76add795a8204a6fb11cab716b70d50`.
- Les 96 processus sont indépendants : 4 méthodes × 2 runtimes (9.0.22 et 10.0.14 via `dotnet exec --fx-version`) × 2 régimes × 2 états de tiering × 3 passes. Un filtre sélectionne une méthode par processus. Le job `InProcessEmit` du banc reste inchangé : cinq échauffements, quinze itérations, temps cible 100 ms, facteur de déroulement 1. `--invocationCount 1` fixe le premier régime ; sans cette option BDN calibre automatiquement le nombre d'appels. `DOTNET_TieredCompilation=0` désactive le tiering dans l'autre état.
- Les deux runtimes d'une paire sont lancés consécutivement. Les ordres runtime, régime et tiering sont inversés à la deuxième passe ; la première et la troisième ont le même ordre. Les comparaisons entre régimes ou états du tiering d'une même passe ne sont pas des lancements voisins. Aucune passe n'a été relancée ou écartée.
- Hôte Linux Debian 13, Xeon Platinum 8573C, cinq CPU visibles, quota cgroup de quatre CPU ; chaque processus est lancé avec `taskset -c 3,4` et le champ `Affinity` des CSV BDN vaut `11000`. Le champ `affinity` des relevés d'environnement désigne **le shell parent** (0–4), pas le processus mesuré. Charge moyenne à une minute relevée au début des jambes : 0,23 à 1,45. La campagne s'est déroulée de 01:57:30 à 02:06:15 UTC le 13 novembre 2026, sur un seul démarrage ; SHA-256 du fichier contenant l'identifiant de démarrage suivi d'un retour à la ligne : `97e40612c92a8907c03e45e278c98870bb88221ad06d9a18c7ce50161023795c`. L'hôte n'était pas dédié. Dans les 96 processus, BDN a signalé qu'il ne pouvait pas passer en priorité haute (« Permission denied »). Les variables `DOTNET_*` et `COMPlus_*` héritées n'ont pas été inventoriées par jambe ; les réglages explicites ci-dessus sont ceux du lanceur.

Les [données JSON](banc4-regime-25644.json) contiennent pour chaque jambe les en-têtes runtime/job, les quinze lignes `WorkloadActual`, toutes les lignes `WorkloadResult`, les sections natives `Warnings` et `Hints`, le CSV BDN et le SHA-256 de la console brute. Les valeurs et lignes de mesure sont recopiées sans modification ; seuls les chemins locaux sont omis de cette extraction. Les consoles brutes restent dans les preuves locales de la campagne ; leur hash permet de vérifier une copie. Les moyennes en nanosecondes sont recalculées en divisant le temps total de chaque `WorkloadResult` par son nombre d'opérations, puis en moyennant les résultats retenus. Le [manifeste SHA-256](banc4-regime-25644.sha256) couvre ces deux fichiers. Le [CSV des comparaisons](banc4-regime-25644.csv) conserve les moyennes, effectifs retenus et rapports pour chaque paire. Des valeurs ne sont arrondies que dans les tableaux de cette note.

BDN a signalé `MinIterationTime` pour 93 jambes, des valeurs aberrantes pour 70 et une distribution multimodale pour 8. Son filtrage automatique conserve entre 12 et 15 `WorkloadResult` sur les 15 `WorkloadActual` : ces séries sont toutes deux conservées afin de rendre ce filtrage visible. Les avertissements et la dispersion, particulièrement sensibles aux durées courtes et à l'hôte partagé, limitent l'interprétation ; les valeurs absolues ne sont pas une baseline. Les mesures ne démontrent ni une transition tier0 → tier1, ni la part précise du tiering, ni un résultat sur .NET 11.
