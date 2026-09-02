# Politique de données du dépôt

> Statut : **cadrage**, pas une doctrine exécutable. Chaque cas concret appelle un arbitrage dans la matrice §3. Réf. ticket **#13742**.

Ce document fixe les 4 catégories sous lesquelles ranger tout artefact « donnée / binaire / dataset / trace / checkpoint » qui se présente à un commit. Il ne décide pas *à la place* des contributeurs : il leur donne une grille. Le verdict final reste un arbitrage par ligne, versionné dans la PR qui modifie l'arborescence.

## 1. Quatre catégories

| Catégorie | Définition | Action attendue |
|---|---|---|
| **Curée** | Donnée _déjà_ triée pour servir la pédagogie : sous-échantillon, équilibré, documenté (origine, licence, cardinal). | **OK** dans le repo, fichier versionné normalement, avec un `*.md` adjacent (cardinal + source + licence). |
| **Brute téléchargeable** | Donnée source externe, potentiellement lourde (>= 1 Mo ou > 5 000 lignes). Régénérable par fetch script. | **gitignorer** + fournir un script `fetch_<dataset>.py` qui la (re)construit ; commit = scripts + petit échantillon-témoin en clair (≤ 200 lignes, pour démo). |
| **Checkpoint** | État de modèle ML (poids `.pt`, `.h5`, `.safetensors`, etc.) produit par un entraînement reproductible. | **Exception documentée** : tracked en gitignore par défaut ; si l'entraînement n'est PAS reproductible et le checkpoint est nécessaire à l'exécution du notebook, **git-LFS** ou un lien de téléchargement externe tracé dans le notebook. |
| **Trace** | Sortie d'exécution (logs, `.npz` d'activations, `.json` de résultats, profiling). | **Régénérable** : `gitignorer` + une cellule `notebook_utils.regenerate(...)` qui la reconstruit, gardée sous contrôle versionné. Garder au plus 1 sample de référence en clair, pour les diffs visuels. |

## 2. Critères de décision par catégorie

Pour trancher un cas nouveau, **dans cet ordre** :

1. **La donnée est-elle _pédagogique_ et ≤ 5 Mo ?** Si oui → catégorie **curée**, versionnée.
2. **La donnée est-elle régénérable par un script qui tient en ≤ 200 lignes ?** Si oui → **brute téléchargeable** + script de fetch.
3. **La donnée est-elle un état de modèle, ou un artefact dont la perte prive un notebook d'exécution ?** → **checkpoint** + exception documentée.
4. **La donnée est-elle un sous-produit d'exécution (log, activation, profilage) ?** → **trace** + gitignore + cellule regenerate.
5. **Aucune des 4 ne tient ?** → **escalader** sur l'issue parent du ticket : créer une exception 5ᵉ catégorie par PR documentée (pas en silence).

## 3. Arbitrage par cas concret (état first-hand)

Tell c.745-L2 + c.854-L4 strict — vérifications firsthand c.868 (po-2024):

### Cas **vérifiés** (verdict tranché)

| Binaire / dataset | Taille | Verdict | Justification first-hand |
|---|---:|---|---|
| `MyIA.Trading.Converter/7z-x64.dll` | 3,1 Mo | **RÉFÉRENCÉ — KEEP** | Référencé par `MyIA.Trading.Converter.csproj:30` (`<Content Include="7z-x64.dll">`) ET `CompressionHelper.cs:281-282` (fallback `ConfigurationManager.AppSettings["7zLocation"]` quand SharpCompress ne suffit pas). Suppression casserait la compilation du module C#. |
| `MyIA.Trading.Converter/7z-x86.dll` | 2,7 Mo | **RÉFÉRENCÉ — KEEP** | Idem, fallback 32 bits via `Environment.Is64BitProcess`. |
| `QuantConnect/Python/transformer_checkpoint.pt` | 42 Mo | **EXCEPTION — à documenter** | Tracké via exception gitignore l.875 (à vérifier visuellement `MyIA.AI.Notebooks/QuantConnect/.gitignore`). Pas un `_best` — checkpoint daté. **Action proposée** : vérifier que le notebook qui le consomme documente l'origine (entraînement référencé) ; sinon basculer vers le `_best` correspondant. |
| `ML/ML.Net/taxi-fare.csv` | 24 Mo | **CURÉE — KEEP** | Dataset pédagogique ML.NET, documenté dans le notebook qui le consomme. Cardinal raisonnable (NYC Taxi, sous-échantillon). Licence d'origine New York City TLC Terms of Use. **À ajouter** : `data-policy.md` cité explicitement par le notebook (lien). |

### Cas **à re-vérifier** (rappel, hors scope de ce grain)

Ces lignes du ticket #13742 body ne sont **pas tranchées ici** : soit la mesure est à refaire (la 3ᵉ colonne du ticket dit « re-vérifier »), soit la décision demande un arbitrage séparé par PR spécialisée (datasets QC, junks `git rm`, politique de doublon, etc.). Chacune aura son issue + PR dédiée.

| Binaire / dataset | Taille (rapportée) | À re-vérifier |
|---|---:|---|
| `Search/.../org.chocosolver.solver.dll` | 12 Mo | Consommateur ? NuGet existe ? (vérif code → PR dédiée) |
| `SymbolicAI/libs/native/` + `ext_tools/EProver/` | ~47 Mo | Doublons racine + ArgA → dedup |
| `SymbolicAI/SMT/Z3.Linq/` (fork git imbriqué) | 33 Mo | Statut vendored vs subtree |
| `QuantConnect/Python/*.pt` (multiasset, _best, etc.) | ~25 Mo | Exceptions gitignore couvrent-elles chacune ? |
| `QuantConnect/datasets/{forex,panier,crypto,binance,yfinance_cache}` | 157 Mo / 11 trackés | Aucun pattern gitignore datasets — politique CLAUDE.md « data QC LEAN hors repo » → gitignore + fetch script |
| `IIT/ICT-Series/traces/` (17 `.npz`) | 5,9 Mo | Régénérables (activations SAE) → gitignore + cellule regenerate + 1 sample de référence |
| `galois_lean/M23Lean4Web.lean` | 320 Ko | Fichier suspect (taille anormale pour un `.lean`) — inspecter le contenu |
| `partner-course-quant-trading/lean-workspace/data` | 242 Mo | README annonce cloud-first mais embarque des données — clarifier |

## 4. Application aux PRs en cours

- **PR d'ajout d'un dataset nouveau** : doit citer ce document dans le body (1 ligne), ET dire dans quelle catégorie §1 il tombe, ET appliquer le geste correspondant §2.
- **PR d'ajout d'un notebook dépendant d'une donnée non versionnée** : doit fournir le `fetch_<dataset>.py` ET gitignorer la donnée brute.
- **PR de nettoyage** (lignes « à re-vérifier » §3.2) : doit ouvrir un ticket dédié par cas, **pas** régler plusieurs cas dans une même PR (PR atomique, R3 catalog-pr-hygiene).

## 5. Non-objectifs (ce que cette politique ne fait pas)

- Ne **décide pas** d'un cas concret : l'arbitrage §3 est figé mais **évolutif** ; chaque cas ajouté est une PR isolée.
- Ne **rassure pas** sur la licence d'une donnée : la licence est du ressort du contributeur qui l'ajoute, pas de cette politique.
- Ne **bloque pas** les exceptions : la 5ᵉ catégorie d'exception est ouverte (cf. §2.5), c'est un choix conscient.

## Origine

- Issue #13742 (arbitrage + politique de données, Tell c.745-L2 narrow assumé c.868 po-2024:CoursIA-2).
- Tell c.854-L4 strict : chaque verdict est first-hand — pas une paraphrase du ticket.

— lane `myia-po-2024:CoursIA-2`, cycle c.868 (2026-09-02).
