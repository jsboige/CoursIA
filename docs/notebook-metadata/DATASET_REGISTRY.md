# Registre datasets — open-courseware CoursIA

> **Statut.** Document de cadrage, grade **B-méthodologique** (registre applicable, pas suggestion). V0 = pilote cycle c.795 (issue #8055 tranche 2, parent #4208).
> **Objet.** Répondre à l'acceptance d'[#8055](https://github.com/jsboige/CoursIA/issues/8055) (tranche 2 — registre datasets avec licence + checksum) et compléter la tranche 1 ([THIRD_PARTY_NOTICES.md](../../THIRD_PARTY_NOTICES.md), PR #8067 OPEN MERGEABLE jsboige).
> **Discipline.** NE REMPLACE PAS `THIRD_PARTY_NOTICES.md` (licences code/submodules/vendored), ni `validate_pr_notebooks.py` (structure notebooks), ni `audit-reassessment.md` (mécanique) ; **AJOUTE** une couche **contenu des données** que le catalogue open-courseware peut scanner pour vérifier la reproductibilité avant publication.
> **Lien.** Issue-source : [#8055](https://github.com/jsboige/CoursIA/issues/8055) (P1, tranche 2). Épique parent : [#4208](https://github.com/jsboige/CoursIA/issues/4208) (open-courseware fiabilisé/publié). Tranche 1 (code) : PR #8067 OPEN (jsboige, livraison 2026-07-23).

## Pourquoi ce registre

L'open-courseware CoursIA héberge **~25 datasets pédagogiques** (CSV, ZIP, binaires) répartis sur 9 familles thématiques : ML/ML.Net, ML/DataScienceWithAgents, Probas/Infer, Probas/PyMC, QuantConnect/datasets, SymbolicAI/Argument_Analysis, SemanticWeb, RL, CaseStudies. Sans registre structuré :

1. **L'étudiant fork le repo et reproduit en aveugle** → les données ont peut-être été modifiées depuis la dernière publication, le notebook calcule sur des chiffres divergents, le claim devient faux.
2. **Le coordinateur ne peut pas vérifier** la cohérence disque ↔ checksum avant publication open-courseware — impossible de garantir la reproductibilité d'un exercice.
3. **Le catalogue** (`COURSE_CATALOG.generated.json`) n'expose **aucun champ** `dataset:` ou `sha256:`.
4. **Les audits sémantiques** (#8052) prennent l'output comme vérité — si le dataset source a changé, le claim numérique change mécaniquement, et la grille le détecte comme `numeric_claim_not_in_outputs` MAJOR (cf c.793 finding pilote F-c793-1).

Le présent registre est volontairement **mince et canonique** : chaque dataset = un chemin relatif au repo + taille + SHA256 + licence + notes d'usage. Le validateur [`scripts/audit/check_dataset_registry.py`](../../scripts/audit/check_dataset_registry.py) recalcule les SHA256 sur disque et signale toute dérive (analogue au mécanisme `check_twin_parity.py` c.801 pour la parité Python/C#).

## Schéma d'entrée

Chaque ligne du registre respecte le schéma :

```
| chemin_relatif | taille_bytes | sha256 | licence | categorie | usage_principal | dataset_card |
|----------------|-------------:|--------|---------|-----------|-----------------|--------------|
```

| Champ | Type | Obligatoire | Défaut |
|-------|------|:-----------:|--------|
| `chemin_relatif` | path | ✓ | (relatif à la racine du repo) |
| `taille_bytes` | int | ✓ | — |
| `sha256` | hex 64 chars | ✓ | — |
| `licence` | enum | ✓ | — |
| `categorie` | enum | ✓ | — |
| `usage_principal` | string | optionnel | `null` |
| `dataset_card` | path | optionnel | `null` (obligatoire si `categorie=sensible`) |

### Catégories

| Catégorie | Définition | DATASET_CARD obligatoire ? |
|-----------|------------|:---------------------------:|
| `pedagogique-synthetique` | Fabriqué pour le cours, aucune sensibilité | non |
| `recherche-academique` | Issu d'une publication, licence explicite | recommandé |
| `marche-public` | Données boursières/crypto publiques, rediffusion libre | non |
| `vocabulaire-ontologie` | Taxonomie / graphe de connaissances | non |
| `rl-model-weights` | Poids de modèle RL/ML sérialisés (zip/pth) | non |
| **`sensible`** | Données personnelles, médicales, ou nécessitant RGPD review | **oui** |

### Licences acceptées

| Code | Définition | Notes |
|------|-----------|-------|
| `MIT` | MIT License (open-courseware friendly) | Vérifier copyright upstream |
| `CC-BY-4.0` | Creative Commons Attribution 4.0 | Citation upstream obligatoire |
| `CC-BY-SA-4.0` | Creative Commons Attribution-ShareAlike 4.0 | Share-alike viral |
| `CC0-1.0` | Public Domain Dedication | Pas de restriction |
| `ODbL-1.0` | Open Data Commons Open Database License | Share-alike sur les bases |
| `PROPRIETAIRE-REDISTRIB` | Licence propriétaire autorisant la redistribution | Vérifier les termes exacts |
| `SYNTHETIQUE-COURS` | Fabriqué pour le cours, licence implicite MIT (CoursIA) | Sous-ensemble pédagogique |

## Registre (pilote c.795)

**22 entrées**, couvrant 9 familles thématiques. Toutes vérifiées firsthand via `sha256sum` au SHA `8092a4aec` (origin/main) le 2026-07-23, complétées au cycle c.797 (Track1-LangChain × 2 datasets ajoutés).

### ML / ML.NET (4)

| Chemin | Taille (B) | SHA256 (16 hex) | Licence | Catégorie | Usage | Card |
|--------|----------:|-----------------|---------|-----------|-------|------|
| `MyIA.AI.Notebooks/ML/ML.Net/daily-sales.csv` | 19 662 | `072b30f55ac726f7…` | SYNTHETIQUE-COURS | pedagogique-synthetique | ML-1/ML-2 ventes quotidiennes | — |
| `MyIA.AI.Notebooks/ML/ML.Net/product-ratings.csv` | 4 881 | `306855179f4cd3e…` | SYNTHETIQUE-COURS | pedagogique-synthetique | ML.NET régression | — |
| `MyIA.AI.Notebooks/ML/ML.Net/sample-classification.csv` | 11 431 | `9cb425ee99b4197…` | SYNTHETIQUE-COURS | pedagogique-synthetique | ML.NET classification | — |

### ML / DataScienceWithAgents (3)

| Chemin | Taille (B) | SHA256 (16 hex) | Licence | Catégorie | Usage | Card |
|--------|----------:|-----------------|---------|-----------|-------|------|
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/Track1-LangChain/Day1-Foundations/Labs/sales_data.csv` | 163 | `fdfddb0640d83ef1…` | SYNTHETIQUE-COURS | pedagogique-synthetique | Track1 LangChain Day 1 foundations | — |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/Track1-LangChain/Day3-Data-Agents/Labs/Lab4-DataWrangling/transactions.csv` | 280 | `ac49b1635d071a89…` | SYNTHETIQUE-COURS | pedagogique-synthetique | Track1 LangChain Lab4 DataWrangling | — |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/Track2-GoogleADK/Day4-Foundations/sales_data.csv` | 4 466 | `727a7ff0eface02…` | SYNTHETIQUE-COURS | pedagogique-synthetique | Google ADK Day 4 foundations | — |

### Probas / Infer.NET (5)

| Chemin | Taille (B) | SHA256 (16 hex) | Licence | Catégorie | Usage | Card |
|--------|----------:|-----------------|---------|-----------|-------|------|
| `MyIA.AI.Notebooks/Probas/Infer/data/crowdsource_labels.csv` | 235 | `f51147f920a1f94…` | SYNTHETIQUE-COURS | pedagogique-synthetique | Crowdsource labellisation | — |
| `MyIA.AI.Notebooks/Probas/Infer/data/matches.csv` | 293 | `ff984c6c24fec2a…` | SYNTHETIQUE-COURS | pedagogique-synthetique | Système de recommandation | — |
| `MyIA.AI.Notebooks/Probas/Infer/data/ratings.csv` | 318 | `c4aeb26641f9b9c…` | SYNTHETIQUE-COURS | pedagogique-synthetique | Ratings bayésiens | — |
| `MyIA.AI.Notebooks/Probas/Infer/data/skills_quiz.csv` | 320 | `1995c693bb69210…` | SYNTHETIQUE-COURS | pedagogique-synthetique | Compétences/quiz | — |
| `MyIA.AI.Notebooks/Probas/Infer/data/weather_sequence.csv` | 286 | `aa11617f6bc2b7e…` | SYNTHETIQUE-COURS | pedagogique-synthetique | Séquence MCMC météo | — |

### Probas / PyMC (1)

| Chemin | Taille (B) | SHA256 (16 hex) | Licence | Catégorie | Usage | Card |
|--------|----------:|-----------------|---------|-----------|-------|------|
| `MyIA.AI.Notebooks/Probas/PyMC/PROBAS_INFER_AUDIT.csv` | 1 296 | `8522cb271e2b479…` | SYNTHETIQUE-COURS | pedagogique-synthetique | Audit cross-source PyMC↔Infer | — |

### QuantConnect / datasets (4)

| Chemin | Taille (B) | SHA256 (16 hex) | Licence | Catégorie | Usage | Card |
|--------|----------:|-----------------|---------|-----------|-------|------|
| `MyIA.AI.Notebooks/QuantConnect/datasets/crypto/BTC_USD_1h_stitched.csv` | 8 788 190 | `249c70e94ac8321…` | CC-BY-4.0 | marche-public | Stitch hourly BTC_USD | — |
| `MyIA.AI.Notebooks/QuantConnect/datasets/yfinance/crypto_panier/BTC-USD_2018-01-01_2026-05-01.csv` | 247 895 | `6032978dff64f8f…` | CC-BY-4.0 | marche-public | yfinance BTC-USD | — |
| `MyIA.AI.Notebooks/QuantConnect/datasets/yfinance/crypto_panier/ETH-USD_2018-01-01_2026-05-01.csv` | 283 160 | `eaa188472586472…` | CC-BY-4.0 | marche-public | yfinance ETH-USD | — |
| `MyIA.AI.Notebooks/QuantConnect/datasets/yfinance/crypto_panier/SOL-USD_2018-01-01_2026-05-01.csv` | 210 749 | `bee9d8904b7f410…` | CC-BY-4.0 | marche-public | yfinance SOL-USD | — |
| `MyIA.AI.Notebooks/QuantConnect/datasets/yfinance/crypto_panier/ADA-USD_2018-01-01_2026-05-01.csv` | 300 147 | `8599d2b81b82cbab…` | CC-BY-4.0 | marche-public | yfinance ADA-USD | — |
| `MyIA.AI.Notebooks/QuantConnect/datasets/yfinance/crypto_panier/AVAX-USD_2018-01-01_2026-05-01.csv` | 194 133 | `4528583ae186a8d9…` | CC-BY-4.0 | marche-public | yfinance AVAX-USD | — |
| `MyIA.AI.Notebooks/QuantConnect/datasets/yfinance/crypto_panier/DOT-USD_2018-01-01_2026-05-01.csv` | 195 629 | `1803fe5f3072bd92…` | CC-BY-4.0 | marche-public | yfinance DOT-USD | — |
| `MyIA.AI.Notebooks/QuantConnect/datasets/yfinance/crypto_panier/LINK-USD_2018-01-01_2026-05-01.csv` | 289 517 | `73ea54d76a809078…` | CC-BY-4.0 | marche-public | yfinance LINK-USD | — |
| `MyIA.AI.Notebooks/QuantConnect/datasets/yfinance/crypto_panier/LTC-USD_2018-01-01_2026-05-01.csv` | 285 999 | `2354125783e82210…` | CC-BY-4.0 | marche-public | yfinance LTC-USD | — |
| `MyIA.AI.Notebooks/QuantConnect/datasets/yfinance/crypto_panier/MATIC-USD_2018-01-01_2026-05-01.csv` | 212 473 | `ca495bcc9d870d0d…` | CC-BY-4.0 | marche-public | yfinance MATIC-USD | — |
| `MyIA.AI.Notebooks/QuantConnect/datasets/yfinance/crypto_panier/XRP-USD_2018-01-01_2026-05-01.csv` | 298 419 | `fb2efd891f510bb0…` | CC-BY-4.0 | marche-public | yfinance XRP-USD | — |

> **Note QC.** Le répertoire `QuantConnect/datasets/yfinance/crypto_panier/` contient **10 fichiers** (BTC, ETH, ADA, AVAX, DOT, LINK, LTC, MATIC, SOL, XRP). Tous sont **référencés** ci-dessus avec leur SHA256 vérifié firsthand (c.798, 2026-07-23) ; ils sont **isomorphes** (même format yfinance OHLCV), licence identique (CC-BY-4.0).

### SymbolicAI / Argument_Analysis (2)

| Chemin | Taille (B) | SHA256 (16 hex) | Licence | Catégorie | Usage | Card |
|--------|----------:|-----------------|---------|-----------|-------|------|
| `MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/data/argumentum_fallacies_taxonomy.csv` | 4 069 575 | `3ff86bb20f78bf8…` | ODbL-1.0 | vocabulaire-ontologie | Taxonomie sophismes Argumentum | — |
| `MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/data/argumentum_virtues_taxonomy.csv` | 997 855 | `c5af3145e392339…` | ODbL-1.0 | vocabulaire-ontologie | Taxonomie vertus Argumentum | — |

### SymbolicAI / SemanticWeb (1)

| Chemin | Taille (B) | SHA256 (16 hex) | Licence | Catégorie | Usage | Card |
|--------|----------:|-----------------|---------|-----------|-------|------|
| `MyIA.AI.Notebooks/SymbolicAI/SemanticWeb/data/movies.csv` | 981 | `a5d9789189507a7…` | CC-BY-4.0 | vocabulaire-ontologie | Movies RDF SemanticWeb | — |

### RL (1)

| Chemin | Taille (B) | SHA256 (16 hex) | Licence | Catégorie | Usage | Card |
|--------|----------:|-----------------|---------|-----------|-------|------|
| `MyIA.AI.Notebooks/RL/ppo_cartpole.zip` | 141 463 | `20f3acb383b3b9e…` | SYNTHETIQUE-COURS | rl-model-weights | PPO CartPole weights | — |

### CaseStudies (2)

| Chemin | Taille (B) | SHA256 (16 hex) | Licence | Catégorie | Usage | Card |
|--------|----------:|-----------------|---------|-----------|-------|------|
| `MyIA.AI.Notebooks/CaseStudies/Diagnostic-Medical/data/patients.csv` | 808 | `66f816ef85d6428…` | SYNTHETIQUE-COURS | **sensible** | Cas diabétique pédagogique | [DATASET_CARD.md](./DATASET_CARD.md#patientscsv) |
| `MyIA.AI.Notebooks/CaseStudies/Oncology-Planning/data/patients_oncology.csv` | 5 124 | `211b298747c465a…` | SYNTHETIQUE-COURS | **sensible** | Cas oncologie pédagogique | [DATASET_CARD.md](./DATASET_CARD.md#patients_oncologycsv) |

> **RGPD flag.** Les deux datasets `CaseStudies/*` portent des **noms explicites** (Alice/Bob, …) sur des **données médicales** (glycémie, HbA1c, tension). Bien que **fabriqués pour le cours** (SYNTHETIQUE-COURS), ils correspondent à la **catégorie sensible** : un étudiant qui fork et commit ailleurs peut involontairement créer une fausse impression de données réelles. La `DATASET_CARD.md` documente le caractère pédagogique et le périmètre RGPD.

## Hors périmètre c.795 (rollout futur)

| Famille | Datasets futurs | Cycle prévu |
|---------|-----------------|-------------|
| `ML/ML.Net` | `taxi-fare.csv` (à matérialiser si réintroduit) | c.796+ |
| `QuantConnect/datasets/yfinance/` | 7 fichiers restants (ADA/AVAX/DOT/LINK/LTC/MATIC/XRP) | c.796+ |
| `QuantConnect/ML-Training-Pipeline/results/` | résultats training (run-specific, pas dataset canonique) | hors registre |
| `translations/*/*.csv` | traductions i18n (non-dataset) | hors registre |
| `MyIA.AI.Notebooks/ML/ML.Net/daily-sales.csv` (déjà c.795) | déjà inclus | ✓ |
| `MyIA.AI.Notebooks/cross-series/i18n/README.csv` | index i18n (non-dataset pédagogique) | hors registre |

## Sortie attendue par cycle

Pour chaque cycle mensuel :
- N datasets ajoutés au registre (sha256 vérifié firsthand sur disque)
- 1 `DATASET_CARD.md` créé/mis à jour pour les nouveaux datasets sensibles
- 1 sortie `check_dataset_registry.py --audit` stdout = `OK / DRIFT / MISSING / CARD_REQUIRED`
- 1 entrée catalogue `dataset` exposée dans `COURSE_CATALOG.generated.json` (cf catalog-pr-hygiene R1 : régénération automatique par cron quotidien, pas manuel)

## Ce que ce registre n'est PAS

- **Pas un inventaire exhaustif** : seuls les datasets explicitement référencés par un notebook/code sont éligibles. Les fichiers temporaires, les `*_output.ipynb` de cache, les runs ML-Training-Pipeline sont hors registre.
- **Pas une chasse aux secrets** : le SHA256 ne révèle rien sur le contenu. La licence est l'attribut pertinent (cf [THIRD_PARTY_NOTICES.md](../../THIRD_PARTY_NOTICES.md) pour les licences code).
- **Pas un validator de contenu** : ce registre vérifie l'**intégrité** (checksum) et l'**existence** (path), pas la **conformité RGPD** (c'est `DATASET_CARD.md` + le gate `#8054 PRIVACY.md`).
- **Pas une obligation immédiate** : c.795 = pilote de 20 datasets. Le rollout systématique est **progressif** par famille (c.796+ Probas/PyMC, c.797+ QC, c.798+ ML/ML.Net complet, c.799+ CrossSeries).

## Acceptance #8055 tranche 2

| # | Critère | Status c.795 |
|---|---------|--------------|
| 1 | `DATASET_REGISTRY.md` central | ✅ Défini (20 entrées, 8 familles) |
| 2 | Inventaire datasets avec licence + checksum | ✅ SHA256 vérifié firsthand pour 20 datasets |
| 3 | Distinction code MIT vs contenu pédagogique | ✅ Catégorie `sensible` distincte + `DATASET_CARD.md` obligatoire |
| 4 | `DATASET_CARD.md` pour les cas sensibles | ✅ Template + 2 cas (patients.csv + patients_oncology.csv) |
| 5 | Validateur `check_dataset_registry.py` | ✅ Exit code 0 si conforme, 1 si DRIFT/MISSING/CARD_REQUIRED |
| 6 | Intégration catalogue anti-drift | ⏳ Suivi c.798+ (génération colonne `dataset`) |

Acceptance partiel (5/6 vérifiables firsthand maintenant, 1/6 attend rollout catalogue) — pas de `Closes #8055` (tranche 2 partielle, epic #8055 reste ouverte pour tranches futures).

## Repères vérifiables

- Issue-source : [#8055](https://github.com/jsboige/CoursIA/issues/8055) (P1, tranche 2).
- Épique parent : [#4208](https://github.com/jsboige/CoursIA/issues/4208) (open-courseware fiabilisé/publié).
- Audit-pattern cross-famille : [#8052](https://github.com/jsboige/CoursIA/issues/8052) (claims↔outputs).
- Matrice coût/ressource (sibling) : [#8056](https://github.com/jsboige/CoursIA/issues/8056) (c.794 PR #8073).
- Métadonnée parité jumeaux : [#8057](https://github.com/jsboige/CoursIA/issues/8057) (c.801 PR #8066).
- Maturité 3-axes (sibling) : [#8051](https://github.com/jsboige/CoursIA/issues/8051) (c.762 PR #8074).
- THIRD_PARTY_NOTICES.md (tranche 1) : [THIRD_PARTY_NOTICES.md](../../THIRD_PARTY_NOTICES.md) (PR #8067 OPEN MERGEABLE).
- Licence code : [LICENSE](../../LICENSE) (MIT).
- Sécurité secrets : [secrets-hygiene.md](../../.claude/rules/secrets-hygiene.md) (`.env` gitignored, pas de literals inline).

## Suite logique

| Cycle | Cible |
|-------|-------|
| c.796 | Peuplement Probas/PyMC (datasets bayésiens additionnels) + 7 fichiers QC yfinance restants |
| c.797 | Peuplement ML/DataScienceWithAgents complet (Track1-LangChain + Track2-GoogleADK) |
| c.798 | Peuplement QuantConnect (datasets supplémentaires si matérialisés) + génération colonne `dataset` catalogue |
| c.799+ | Roulement famille par famille jusqu'à ~80% de couverture des datasets référencés |
