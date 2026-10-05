# Politique de données du dépôt

> Statut : **cadrage**, pas une doctrine exécutable. Chaque cas concret appelle un arbitrage dans la matrice §3. Réf. ticket **#13742**.

Ce document fixe les 4 catégories sous lesquelles ranger tout artefact **de donnée** — dataset, état de modèle, sortie d'exécution — qui se présente à un commit. Les binaires natifs **runtime** (DLL de dépendance consommées par le code) ne sont pas des données : ils sont arbitrés comme **exception native documentée** (§2.5), pas rangés dans une catégorie. Il ne décide pas *à la place* des contributeurs : il leur donne une grille. Le verdict final reste un arbitrage par ligne, versionné dans la PR qui modifie l'arborescence.

## 1. Quatre catégories

| Catégorie | Définition | Action attendue |
|---|---|---|
| **Curée** | Donnée _déjà_ triée pour servir la pédagogie : sous-échantillon, équilibré, documenté (origine, licence, cardinal). | **OK** dans le repo, fichier versionné normalement, avec un `*.md` adjacent (cardinal + source + licence). |
| **Brute téléchargeable** | Donnée source externe, potentiellement lourde (>= 1 Mo ou > 5 000 lignes). Régénérable par fetch script. | **gitignorer** + fournir un script `fetch_<dataset>.py` qui la (re)construit ; commit = scripts + petit échantillon-témoin en clair (≤ 200 lignes, pour démo). |
| **Checkpoint** | État de modèle ML (poids `.pt`, `.h5`, `.safetensors`, etc.) produit par un entraînement reproductible. | **Exception documentée** : ignoré par défaut ; si l'entraînement n'est PAS reproductible et le checkpoint est nécessaire à l'exécution du notebook, **git-LFS** ou un lien de téléchargement externe tracé dans le notebook. |
| **Trace** | Sortie d'exécution (logs, `.npz` d'activations, `.json` de résultats, profiling). | **Régénérable** : `gitignorer` + une cellule ou un script de régénération documenté qui la reconstruit, gardé sous contrôle versionné. Garder au plus 1 sample de référence en clair, pour les diffs visuels. |

## 2. Critères de décision par catégorie

Pour trancher un cas nouveau, **dans cet ordre** :

1. **La donnée est-elle _pédagogique_ et ≤ 5 Mo ?** Si oui → catégorie **curée**, versionnée.
2. **La donnée est-elle régénérable par un script qui tient en ≤ 200 lignes ?** Si oui → **brute téléchargeable** + script de fetch.
3. **La donnée est-elle un état de modèle, ou un artefact dont la perte prive un notebook d'exécution ?** → **checkpoint** + exception documentée.
4. **La donnée est-elle un sous-produit d'exécution (log, activation, profilage) ?** → **trace** + gitignore + cellule regenerate.
5. **Binaire natif runtime** (DLL de dépendance, consommée par le code) → **exception native documentée** : KEEP avec justification de référencement (csproj / appel dans le code), sans catégorie. Tout autre cas qu'aucune des 4 ne couvre → **escalader** sur l'issue parent du ticket : créer une exception 5ᵉ catégorie par PR documentée (pas en silence).

## 3. Arbitrage par cas concret (état first-hand)

Vérifications first-hand ([G.1](../CLAUDE.md)) — po-2024 :

### Cas **vérifiés** (verdict tranché)

| Binaire / dataset | Taille | Verdict | Justification first-hand |
|---|---:|---|---|
| `MyIA.Trading.Converter/7z-x64.dll` | 3,1 Mo | **EXCEPTION NATIVE — KEEP** (§2.5) | Référencé par `MyIA.Trading.Converter.csproj:30` (`<Content Include="7z-x64.dll">`) ET `CompressionHelper.cs:281-282` (fallback `ConfigurationManager.AppSettings["7zLocation"]` quand SharpCompress ne suffit pas). Suppression casserait la compilation du module C#. |
| `MyIA.Trading.Converter/7z-x86.dll` | 2,7 Mo | **EXCEPTION NATIVE — KEEP** (§2.5) | Idem, fallback 32 bits via `Environment.Is64BitProcess`. |
| `QuantConnect/Python/transformer_checkpoint.pt` | 42 Mo | **CHECKPOINT — LFS EXISTANT** | Tracké via **Git LFS** : pointeur de 133 octets (`size 43541550`, `git check-attr` → filter/diff/merge=lfs), vérifié firsthand. Exceptions gitignore dans **les deux** fichiers : racine `.gitignore:876` (`!MyIA.AI.Notebooks/QuantConnect/Python/transformer_checkpoint.pt`) et `MyIA.AI.Notebooks/QuantConnect/.gitignore:73` (`!Python/transformer_checkpoint.pt`, forme relative). Pas un `_best` — checkpoint daté. **Reste à vérifier** : que le notebook qui le consomme documente la provenance (entraînement référencé / geste de reproduction) ; sinon basculer vers le `_best` correspondant. |
| `ML/ML.Net/taxi-fare.csv` | 24 Mo (non tracké) | **NON-TRACKED — geste requis** | Introuvable dans `origin/main` (`git ls-tree -r` : aucun fichier `*taxi*`). Le registre canonique [`docs/notebook-metadata/DATASET_REGISTRY.md`](notebook-metadata/DATASET_REGISTRY.md) le classe **NON-TRACKED / hors registre** : présent localement comme artefact ~25 Mo non committé, référencé par les notebooks ML-2/ML-4, non reproductible par fork. La mesure « 24 Mo CURÉE — KEEP » de la version initiale mesurait l'artefact local, pas un fichier du dépôt. **Geste** : issue dédiée — committer un sous-échantillon ≤ 5 Mo avec `fetch_taxi_fare.py`, ou retirer la référence des notebooks (le registre tranche : « soit commit, soit supprimer la référence »). |
| `Search/Part2-CSP/org.chocosolver.solver.dll` | 11,9 Mo (copie unique) | **EXCEPTION VENDORED — DEDUPE livrée** | DLL **IKVM 8.15.0** (build .NET du JAR choco-solver 4.10.17 — pas un NuGet : le chargement direct du JAR via `#r` n'est pas pris en charge par IKVM, voie SOTA établie #4667/#3801). **8 consommateurs vivants mesurés** : les carnets `Search/Part2-CSP/CSP-*-Csharp`, `Sudoku/Sudoku-11-Choco-CSharp.ipynb`, `Sudoku/README.md`. Les DEUX copies trackées (`Search/Part2-CSP/` + `Sudoku/`) étaient **byte-identiques** (blob `02ef8ac5c4`, 11,9 Mo × 2) : la copie `Sudoku/` est retirée, `Sudoku-11-Choco-CSharp` référence la copie `Part2-CSP/` par chemin relatif (`#r "../Search/Part2-CSP/org.chocosolver.solver.dll"`), re-exécutée réellement (C.2). −11,9 Mo. |

### Cas **à re-vérifier** (rappel, hors scope de ce grain)

Ces lignes du ticket #13742 body ne sont **pas tranchées ici** : soit la mesure est à refaire (la 3ᵉ colonne du ticket dit « re-vérifier »), soit la décision demande un arbitrage séparé par PR spécialisée (datasets QC, junks `git rm`, politique de doublon, etc.). Chacune aura son issue + PR dédiée.

| Binaire / dataset | Taille (rapportée) | À re-vérifier |
|---|---:|---|
| `SymbolicAI/libs/native/` + `ext_tools/EProver/` | ~47 Mo | Doublons racine + ArgA → dedup |
| `SymbolicAI/SMT/Z3.Linq/` (fork git imbriqué) | 33 Mo | Statut vendored vs subtree |
| `QuantConnect/Python/*.pt` (multiasset, _best, etc.) | ~25 Mo | Exceptions gitignore couvrent-elles chacune ? |
| `QuantConnect/datasets/{forex,panier,crypto,binance,yfinance_cache}` | 157 Mo / 11 trackés | Aucun pattern gitignore datasets — politique CLAUDE.md « data QC LEAN hors repo » → gitignore + fetch script |
| `IIT/ICT-Series/traces/` (17 `.npz`) | 5,9 Mo | Régénérables (activations SAE) → gitignore + cellule regenerate + 1 sample de référence |
| `galois_lean/M23Lean4Web.lean` | 320 Ko | Fichier suspect (taille anormale pour un `.lean`) — inspecter le contenu |
| `partner-course-quant-trading/lean-workspace/data` | 242 Mo | README annonce cloud-first mais embarque des données — clarifier |

### §3.3 — Re-mesure first-hand du 2026-10-05 (po-2023)

Le tableau §3.2 avait été écrit sur des **mesures agent non vérifiées** ; la passe `git cat-file -s origin/main:<path>` du 2026-10-05 (lane myia-po-2023:CoursIA-2, cycle c.1045) a remplacé les chiffres rapportés par les chiffres réels **et** a croisé chaque cas avec la politique §1-§2. Le constat diverge de l'original sur **6 des 7 cas** ; un seul (ext_tools/EProver + libs/native) reste conforme à la mesure originelle. Les écarts par cas : 2 surestimations (`libs/native+EProver` ×2.2, `qc_datasets` ×14.6) + 1 sous-estimation (`ict_traces` ×4.2) + 1 correction de chemin (`galois_lean`) + 2 obsolètes (`z3linq` est un sous-module, `partner-course` est vide). Les agents de la passe initiale mesuraient le volume **disque local** (artefacts non commités inclus), pas les fichiers `origin/main`. **Aucun cas n'est tranché en `git rm` unilateral** par cette passe — la politique §4 reste : ticket dédié par cas, PR atomique.

| Cas (corps original) | Taille rapportée | Taille réelle (`origin/main`) | Catégorie §1 | Verdict 2026-10-05 | Geste requis |
|---|---:|---:|---|---|---|
| `SymbolicAI/libs/native/` + `ext_tools/EProver/` | ~47 Mo | **19,15 MiB** (ext_tools/EProver, 77 artefacts) + **3,56 MiB** (libs/native, 6 artefacts) — **22,7 MiB réel** | **EXCEPTION NATIVE — KEEP** (§2.5) | `!MyIA.AI.Notebooks/SymbolicAI/libs/native/` (gitignore ligne 566) + `!MyIA.AI.Notebooks/SymbolicAI/ext_tools/EProver/` (ligne 552) sont **déjà** des `!` (négation). Le statut est **vendored assumé**, pas « dédup à faire ». Le doublon évoqué (racine + ArgA) n'existe pas sur `main` : 6 artefacts seulement, tous racine (`SymbolicAI/libs/native/`). Aucun artefact ArgA-sibling. | **Aucun** — la dédup est un phantom ; fermer la ligne ou la déplacer en suivi bas-priorité (extension `native/` à inspecter au cas par cas). |
| `SymbolicAI/SMT/Z3.Linq/` (fork git imbriqué) | 33 Mo | **Sous-module git** — voir `.gitmodules` (cf [submodule-maintenance.md](reference/submodule-maintenance-detail.md) §1). Pas un fichier tracké. | **Sous-module vendored** (règle R7 submodule-maintenance) | Mesure `git submodule status` à passer en cycle `coordinateur` ; pas une ligne `git rm`. | **Suivi submodule-maintenance** (R7), pas une PR data-policy. |
| `QuantConnect/Python/*.pt` (multiasset, _best, etc.) | ~25 Mo | 5 lignes gitignore `!` (racine l.938-942 : `transformer_checkpoint.pt`, `transformer_multiasset_model.pt`, `best_ppo_model.pt`, `best_dqn_model.pt`, `lstm_attention_sp50.pt`) — **3 fichiers effectivement trackés** (`best_dqn_model.pt`, `best_ppo_model.pt`, `transformer_multiasset_model.pt`, mesurés par `git ls-tree -r origin/main --name-only`), les 2 autres (`transformer_checkpoint.pt`, `lstm_attention_sp50.pt`) sont **whitelistés mais non trackés** (gitignore négatif sans présence disque vérifiée). | **CHECKPOINT — LFS EXISTANT** (lignes analogues à `transformer_checkpoint.pt` §3.1) | 3 artefacts **trackés** en `!` + 2 whitelistés **non trackés** — pas 5 artefacts déjà suivis comme la version initiale le disait. À vérifier au cas par cas : (a) pour les 3 trackés, leur consommation effective par les notebooks ML ; (b) pour les 2 whitelistés, s'ils sont encore produits par un script d'entraînement ou s'ils sont des résidus à déwhitelister. | **Aucun** geste sec — PR dédiée par cas (consommateur manquant ou whitelist obsolète). |
| `QuantConnect/datasets/{forex,panier,crypto,binance,yfinance_cache}` | 157 Mo / 11 trackés | **10,79 MiB réel** sur `origin/main` : **15 fichiers** (mesurés par `git ls-tree -r origin/main --name-only | grep QuantConnect/datasets/`) — `crypto/BTC_USD_1h_stitched.csv` (8,79 Mo) + `crypto/BTC_USD_1h_stitched_report.json` (2,8 KiB) + 10× `yfinance/crypto_panier/*.csv` (~200-300 KiB chacun) + 2× `README.md` (en + `.en.md`) + 1× `panier/README.md` | **CURÉE — KEEP** (§1) | **Aucune trace QC LEAN non-curée.** Les 15 fichiers sont dans [`docs/notebook-metadata/DATASET_REGISTRY.md`](notebook-metadata/DATASET_REGISTRY.md) avec **SHA256 vérifié firsthand** (c.798, 2026-07-23) et licence **CC-BY-4.0** (`marche-public`). Le pattern gitignore **existe** : `MyIA.AI.Notebooks/QuantConnect/.gitignore:97` `!datasets/yfinance/crypto_panier/` (négation avec rationale). Le claim « Aucun pattern gitignore datasets » du corps original est **faux first-hand**. Les fetch scripts existent : [`scripts/datasets/stitch_crypto.py`](../scripts/datasets/stitch_crypto.py) (BTC_USD_1h_stitched), `download_yfinance.py` (crypto_panier), `download_binance_archive.py`, `dezip_forex.py`, `build_panier_anti_bias.py` — tous sur main, **mais le dataset commit est la version snapshot, pas une régénération à la demande**. | **Aucune** action de retrait — la curation est assumée par po-2024 (c.798). Au cas où le coordinateur veut basculer vers fetch+gitignore : PR dédiée par catégorie de dataset (BTC stitched / crypto panier / forex / binance), avec sample-témoin ≤ 200 entrées gardé en clair. |
| `IIT/ICT-Series/traces/` (17 `.npz` rapportés) | 5,9 Mo | **24,79 MiB réel** sur `origin/main` : **87 fichiers `.npz` + 2 PNG + 3 JSON = 92 fichiers au total** (mesurés par `git ls-tree -r origin/main --name-only | grep IIT/ICT-Series/traces/`), un **sous-comptage initial par ~5×** (vs rapport 17 npz → 87 npz) et **~4× sous-estimé en volume** (5,9 Mo vs 24,79 MiB réel). | **TRACE — KEEP** avec exception §2.3 « perte prive un notebook d'exécution » | **5 carnets exécutent** ces traces et **n'ont pas** de cellule de régénération tenant en ≤ 200 entrées (les traces viennent de modèles 9B-70B entraînés GPU-2, hors-budget script ≤ 200 entrées). Couverts par §2.3 : « artefact dont la perte prive un notebook d'exécution » → **exception documentée**, pas gitignore. Les fichiers sont **versionnés explicitement** (`git add`) avec un commentaire upstream au ticket initial (#5101 / #5643) qui assume cette politique. | **Aucune** action de retrait. La Gitignore déjà en place (`MyIA.AI.Notebooks/IIT/ICT-Series/.cache_temoins/`, `MyIA.AI.Notebooks/IIT/ICT-Series/results/grok_transformer/`) couvre les caches transitoires ; les traces versionnées sont le contrat d'exécution des carnets. **Documentation à compléter** : ajouter un `<traces/README.md>` qui nomme les 5 consommateurs et la politique « exception documentée §2.3 » — PR dédiée. |
| `galois_lean/M23Lean4Web.lean` (corps original dit `galois_lean/M23Lean4Web.lean`) | 320 Ko | **320 KiB (319 438 octets)**, mais le chemin exact est `MyIA.AI.Notebooks/SymbolicAI/Lean/galois_lean/Galois/M23Lean4Web.lean` (corps original avait un chemin obsolète). **8 115 entrées** au total. | **SOURCE — KEEP** (§1 curée / §2.5 vendored) | Le fichier est un **bundle Lean4Web single-file** du M22 + M23 (`card_M23 = 10200960`, `IsSimpleGroup M23`) prouvé par Schreier–Sims materialisé. **8115 entrées** est normal (pas un fichier suspect). Header vérifié firsthand : copyright 2026 Kenta, upstream `https://github.com/KitaKen1/finite-simple-groups-lean`, licence Apache-2.0 (cf `galois_lean/LICENSE-UPSTREAM` notice), vendored le 2026-08-11 comme proof layer de Lean-19 (M23 / inverse Galois). Faisabilité gate po-2026 (c.1039) : compile sous `v4.32.1`, `#print axioms` whitelist §B. | Aucun — le ticket contient un **mauvais chemin** (résidu du reclass galois_lean). À corriger dans le ticket body, pas dans le dépôt. |
| `partner-course-quant-trading/lean-workspace/data` | 242 Mo | **0 octet sur `origin/main`** — le répertoire `MyIA.AI.Notebooks/QuantConnect/partner-course-quant-trading/lean-workspace/` ne contient **aucun fichier** tracké (`git ls-tree -r origin/main --name-only | grep ...` = vide). | (N/A) | Le claim « 242 Mo embarquées » est **faux first-hand**. Les artefacts `obj/` et `bin/` du workspace Lean sont déjà gitignorés (racine .gitignore l.773-774 + l.777-778). Si des données existaient localement, c'étaient des artefacts de build non commités, déjà couverts par les patterns gitignore existants. | **Aucun** — la ligne est close obsolète. |

**Bilan global** : **7 cas sur 7 clos first-hand, 0 cas requérant `git rm` unilateral.** Les **15 fichiers** QC datasets (`crypto/BTC_USD_1h_stitched.csv`, 10× `yfinance/crypto_panier/*.csv`, 2× `README.md`, 1× `panier/README.md` + rapport JSON) sont **curés et documentés** (SHA256 vérifié, licence CC-BY-4.0) ; les **87 npz + 2 PNG + 3 JSON** ICT traces sont **exception documentée** ; les **3 fichiers trackés + 2 whitelistés** `QuantConnect/Python/*.pt` sont **mix documenté** ; les **22,7 MiB** de binaires `libs/native/` + `ext_tools/EProver/` sont **vendored assumé**. Aucun des 7 cas n'est un retrait sec.

Le seul geste de cohérence sortant de cette mesure est :
1. **Corriger le corps de #13742** : le tableau §3.2 (ci-dessus) doit être remplacé par ce §3.3 (mesures réelles). PR dédiée — ne pas merger avec une autre tranche de la file de réparation.
2. **Documenter l'exception §2.3 ICT traces** dans un `MyIA.AI.Notebooks/IIT/ICT-Series/traces/README.md` (PR dédiée, tranche suivante).
3. **Aucune autre action de retrait de données n'est due** par cette passe.

— lane `myia-po-2023:CoursIA-2`, cycle c.1045 (2026-10-05). Issue **#13742** ; cette section est une **mesure first-hand** de l'arbre, pas une relecture du ticket. **Re-mesure c.1045** : correction des décomptes `*.pt` (3 trackés + 2 whitelistés), `datasets/` (15) et `traces/` (87 npz + 2 PNG + 3 JSON) après relecture ai-01 du 2026-10-05 06:58Z (msg-20261005T045857-wpfhif) ; cf. `scripts/results/data_policy_rescan_2026-10-05.json` pour le détail.

## 4. Application aux PRs en cours

- **PR d'ajout d'un dataset nouveau** : doit citer ce document dans le body (1 ligne), ET dire dans quelle catégorie §1 il tombe, ET appliquer le geste correspondant §2.
- **PR d'ajout d'un notebook dépendant d'une donnée non versionnée** : doit fournir le `fetch_<dataset>.py` ET gitignorer la donnée brute.
- **PR de nettoyage** (lignes « à re-vérifier » §3.2) : doit ouvrir un ticket dédié par cas, **pas** régler plusieurs cas dans une même PR (PR atomique, R3 catalog-pr-hygiene).

## 5. Non-objectifs (ce que cette politique ne fait pas)

- Ne **décide pas** d'un cas concret : l'arbitrage §3 est figé mais **évolutif** ; chaque cas ajouté est une PR isolée.
- Ne **rassure pas** sur la licence d'une donnée : la licence est du ressort du contributeur qui l'ajoute, pas de cette politique.
- Ne **bloque pas** les exceptions : la 5ᵉ catégorie d'exception est ouverte (cf. §2.5), c'est un choix conscient.

## Origine

- Issue #13742 (arbitrage + politique de données, périmètre restreint assumé par po-2024:CoursIA-2).
- Chaque verdict est first-hand, pas une paraphrase du ticket ([G.1](../CLAUDE.md)).

— lane `myia-po-2024:CoursIA-2`, cycle c.868 (2026-09-02) — corps initial (sections 1-5).

— §3.3 ajoutée le 2026-10-05 par `myia-po-2023:CoursIA-2` (cycle c.1034) : re-mesure first-hand de l'arbre `origin/main` pour les 7 cas « à re-vérifier » de §3.2 (cf PR associée à cette annexe). Aucune ligne du §3.2 n'est tranchée en `git rm` unilateral par cette passe ; chaque cas reste suivi par PR spécialisée conformément à §4.
