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

Vérifications first-hand ([G.1](../../CLAUDE.md)) — po-2024 :

### Cas **vérifiés** (verdict tranché)

| Binaire / dataset | Taille | Verdict | Justification first-hand |
|---|---:|---|---|
| `MyIA.Trading.Converter/7z-x64.dll` | 3,1 Mo | **EXCEPTION NATIVE — KEEP** (§2.5) | Référencé par `MyIA.Trading.Converter.csproj:30` (`<Content Include="7z-x64.dll">`) ET `CompressionHelper.cs:281-282` (fallback `ConfigurationManager.AppSettings["7zLocation"]` quand SharpCompress ne suffit pas). Suppression casserait la compilation du module C#. |
| `MyIA.Trading.Converter/7z-x86.dll` | 2,7 Mo | **EXCEPTION NATIVE — KEEP** (§2.5) | Idem, fallback 32 bits via `Environment.Is64BitProcess`. |
| `QuantConnect/Python/transformer_checkpoint.pt` | 42 Mo | **CHECKPOINT — LFS EXISTANT** | Tracké via **Git LFS** : pointeur de 133 octets (`size 43541550`, `git check-attr` → filter/diff/merge=lfs), vérifié firsthand. Exceptions gitignore dans **les deux** fichiers : racine `.gitignore:876` (`!MyIA.AI.Notebooks/QuantConnect/Python/transformer_checkpoint.pt`) et `MyIA.AI.Notebooks/QuantConnect/.gitignore:73` (`!Python/transformer_checkpoint.pt`, forme relative). Pas un `_best` — checkpoint daté. **Reste à vérifier** : que le notebook qui le consomme documente la provenance (entraînement référencé / geste de reproduction) ; sinon basculer vers le `_best` correspondant. |
| `ML/ML.Net/taxi-fare.csv` | 24 Mo (non tracké) | **NON-TRACKED — geste requis** | Introuvable dans `origin/main` (`git ls-tree -r` : aucun fichier `*taxi*`). Le registre canonique [`docs/notebook-metadata/DATASET_REGISTRY.md`](../notebook-metadata/DATASET_REGISTRY.md) le classe **NON-TRACKED / hors registre** : présent localement comme artefact ~25 Mo non committé, référencé par les notebooks ML-2/ML-4, non reproductible par fork. La mesure « 24 Mo CURÉE — KEEP » de la version initiale mesurait l'artefact local, pas un fichier du dépôt. **Geste** : issue dédiée — committer un sous-échantillon ≤ 5 Mo avec `fetch_taxi_fare.py`, ou retirer la référence des notebooks (le registre tranche : « soit commit, soit supprimer la référence »). |
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

Le tableau §3.2 avait été écrit sur des **mesures agent non vérifiées** ; la passe `git cat-file -s origin/main:<path>` du 2026-10-05 (lane myia-po-2023:CoursIA-2, cycle c.1045) a remplacé les chiffres rapportés par les chiffres réels **et** a croisé chaque cas avec la politique §1-§2. Le constat diverge de l'original sur **6 des 7 cas** ; un seul (ext_tools/EProver + libs/native) reste conforme à la mesure originelle. Les écarts par cas : 2 surestimations (`libs/native+EProver`, `qc_datasets`) + 1 sous-estimation (`ict_traces`) + 1 correction de chemin (`galois_lean`) + 2 obsolètes (`z3linq` est un sous-module, `partner-course` est vide). Les agents de la passe initiale mesuraient le volume **disque local** (artefacts non commités inclus), pas les fichiers `origin/main`. **Aucun cas n'est tranché en `git rm` unilateral** par cette passe — la politique §4 reste : ticket dédié par cas, PR atomique. Le détail par cas (chemin, taille octet-par-octet, commande de mesure) vit dans `scripts/results/data_policy_rescan_2026-10-05.json` (artefact JSON miroir versionné) ; la prose ici porte uniquement les **prédicats** (catégorie §1, verdict, geste requis), conformément à la politique « totaux = catalogue, pas prose » (#9377).

| Cas (corps original) | Catégorie §1 | Verdict 2026-10-05 | Geste requis |
|---|---|---|---|
| `SymbolicAI/libs/native/` + `ext_tools/EProver/` | **EXCEPTION NATIVE — KEEP** (§2.5) | Négations gitignore **déjà en place** (section native du `.gitignore` racine) ; statut vendored assumé, pas de dédup à faire (le doublon évoqué n'existe pas sur main). | **Aucun** — la dédup est un phantom ; fermer la ligne ou la déplacer en suivi bas-priorité. |
| `SymbolicAI/SMT/Z3.Linq/` (fork git imbriqué) | **Sous-module vendored** (R7 submodule-maintenance) | Sous-module git (cf `.gitmodules`) ; pas une ligne data-policy. | **Suivi submodule-maintenance** (R7), pas une PR data-policy. |
| `QuantConnect/Python/*.pt` (multiasset, _best, etc.) | **CHECKPOINT — LFS EXISTANT** | Pattern gitignore couvre les noms attendus (section `*.pt` du `.gitignore` racine) ; quelques artefacts trackés en LFS (pointeurs de quelques centaines d'octets) + autres whitelistés non trackés (anciens ou résiduels à déwhitelister au cas par cas). | **Aucun** geste sec — PR dédiée par cas. |
| `QuantConnect/datasets/{forex,panier,crypto,binance,yfinance_cache}` | **CURÉE — KEEP** (§1) | **Aucune trace QC LEAN non-curée** : tous les fichiers (snapshot BTC stitched + panier yfinance + 2 README) sont dans `DATASET_REGISTRY.md` avec **SHA256 vérifié firsthand** (c.798) et licence **CC-BY-4.0**. Le pattern gitignore **existe** (`QuantConnect/.gitignore:97` `!datasets/yfinance/crypto_panier/`). Les fetch scripts sont déjà sur main (`scripts/datasets/stitch_crypto.py`, `download_yfinance.py`, etc.). | **Aucune** action de retrait — curation assumée par po-2024 (c.798). PR dédiée par catégorie au cas où basculement vers fetch+gitignore. |
| `IIT/ICT-Series/traces/` | **TRACE — KEEP** avec exception §2.3 | Des carnets ICT exécutent ces traces et n'ont pas de cellule de régénération tenant en ≤ 200 entrées (modèles 9B-70B entraînés GPU-2, hors-budget). La liste mesurée (chemin exact, cardinal, commande `git grep`) vit dans le JSON miroir — la prose ne porte plus le nombre. Couvert par §2.3 « artefact dont la perte prive un notebook d'exécution » → exception documentée, pas gitignore. | **Aucune** action de retrait. Documentation à compléter : `IIT/ICT-Series/traces/README.md` (PR dédiée, tranche suivante). |
| `galois_lean/M23Lean4Web.lean` (corps original : chemin obsolète) | **SOURCE — KEEP** (§1 curée / §2.5 vendored) | Bundle Lean4Web single-file M22+M23 (`card_M23 = 10200960`, `IsSimpleGroup M23`) ; chemin exact `SymbolicAI/Lean/galois_lean/Galois/M23Lean4Web.lean` (corps original avait un résidu). Apache-2.0 vendored 2026-08-11 (upstream KitaKen1/finite-simple-groups-lean). Compile sous `v4.32.1`, `#print axioms` whitelist §B. | **Aucun** — le ticket contient un mauvais chemin, à corriger dans le ticket body. |
| `partner-course-quant-trading/lean-workspace/data` | (N/A) | Le répertoire `MyIA.AI.Notebooks/QuantConnect/partner-course-quant-trading/lean-workspace/` ne contient **aucun fichier** tracké. Les artefacts `obj/` et `bin/` sont déjà gitignorés (sections `obj/bin` du `.gitignore` racine). | **Aucun** — la ligne est close obsolète. |

**Bilan global** : **7 cas sur 7 clos first-hand, 0 cas requérant `git rm` unilateral.** Aucun des 7 cas n'est un retrait sec. Les catégories §1 sont toutes couvertes : EXCEPTION NATIVE pour les binaires, CURÉE pour les datasets, CHECKPOINT pour les LFS, TRACE (avec §2.3) pour les activations de modèles 9B-70B, SOURCE pour les vendored Lean, sous-module pour les forks imbriqués. Le verdict est homogène : la politique de données est déjà appliquée ou déjà arbitrée, la passe n'ouvre aucun cas neuf.

Le seul geste de cohérence sortant de cette mesure est :
1. **Corriger le corps de #13742** : le tableau §3.2 (ci-dessus) doit être remplacé par ce §3.3 (mesures réelles). PR dédiée — ne pas merger avec une autre tranche de la file de réparation.
2. **Documenter l'exception §2.3 ICT traces** dans un `MyIA.AI.Notebooks/IIT/ICT-Series/traces/README.md` (PR dédiée, tranche suivante).
3. **Aucune autre action de retrait de données n'est due** par cette passe.

— lane `myia-po-2023:CoursIA-2`, cycle c.1045 (2026-10-05). Issue **#13742** ; cette section est une **mesure first-hand** de l'arbre, pas une relecture du ticket. **Re-mesure c.1045** : le détail chiffré (chemin exact, taille octet-par-octet, commande de mesure) vit dans `scripts/results/data_policy_rescan_2026-10-05.json` — clé `commandes:` pour les 5 cas, clé `cas[].taille_*` pour le reste. Conformément à #9377, la prose porte les **prédicats** ; le catalogue porte les **mesures**.

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
- Chaque verdict est first-hand, pas une paraphrase du ticket ([G.1](../../CLAUDE.md)).

— lane `myia-po-2024:CoursIA-2`, cycle c.868 (2026-09-02) — corps initial (sections 1-5).

— §3.3 ajoutée le 2026-10-05 par `myia-po-2023:CoursIA-2` (cycle c.1034) : re-mesure first-hand de l'arbre `origin/main` pour les 7 cas « à re-vérifier » de §3.2 (cf PR associée à cette annexe). Aucune ligne du §3.2 n'est tranchée en `git rm` unilateral par cette passe ; chaque cas reste suivi par PR spécialisée conformément à §4.
