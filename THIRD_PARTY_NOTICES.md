# Mentions légales tierces — Third-Party Notices

> Inventaire des licences des **sous-modules** et **bibliothèques vendored**
> inclus dans ce dépôt. Le code du dépôt lui-même est sous licence **MIT**
> (cf. [`LICENSE`](LICENSE) — Copyright © 2022 Jean-Sylvain Boige).
>
> Cette notice ne couvre que le **code** tiers directement inclus dans l'arbre
> du dépôt. Les **datasets, médias, poids de modèles et corpus** (potentiellement
> sous licence distincte) sont suivis séparément — voir la section « Hors-périmètre ».
> Source : issue #8055.

## 1. Code du dépôt

| Composant | Licence | Détenteur du copyright |
|-----------|---------|------------------------|
| CoursIA (ce dépôt) | **MIT** | © 2022 Jean-Sylvain Boige |

Badge : `License: MIT`.

## 2. Sous-modules git

Chaque sous-module est pinné à un commit précis (cf. `.gitmodules` +
`git submodule status`). La licence applicable est celle du dépôt amont au
commit pinné.

| Sous-module | Dépôt amont | Commit pinné | Licence (SPDX) | Copyright |
|-------------|-------------|--------------|----------------|-----------|
| forge-std | <https://github.com/foundry-rs/forge-std> | `b3bc8b154382` | **Apache-2.0** | Copyright Contributors to Forge Standard Library |
| openzeppelin-contracts | <https://github.com/OpenZeppelin/openzeppelin-contracts> | `5a3b28fc5` | **MIT** | © 2016-2026 Zeppelin Group Ltd |
| account-abstraction ⚠️ | <https://github.com/eth-infinitism/account-abstraction> | `1c6b669d0` | **GPL-3.0-only** | GNU GPL v3.0 |
| MetaGeneticSharp | <https://github.com/jsboige/MetaGeneticSharp> | `0433fad0c` | **MIT** | © 2020-2026 Jean-Sylvain Boige & contributors |
| Z3.Linq | <https://github.com/MyIntelligenceAgency/Z3.Linq> | `b68438c89` | **MIT** | © Bart De Smet, Ricardo Niepel, Jean-Sylvain Boige, Karel Frajtak, endjin |
| Automata | <https://github.com/MyIntelligenceAgency/Automata> | `cfbf436af` | **MIT** † | © Microsoft Corporation |
| Argumentum ⚠️ | <https://github.com/ArgumentumGames/Argumentum> | `7e72f3e5d` | **LGPL-3.0-only** | GNU LGPL v3.0 |
| semantic-fleet | <https://github.com/MyIntelligenceAgency/semantic-fleet> | `0468481f5` (branche `stable-from-v0343`) | **MIT** | © 2023 MyIA |

> **⚠️ Copyleft (à vérifier avant publication open-courseware, epic #4208).**
> `account-abstraction` est sous **GPL-3.0-only** et `Argumentum` sous
> **LGPL-3.0-only**. Ces licences copyleft imposent des obligations de
> redistribution (notamment la GPL-3.0, virale sur la distribution). Si le
> projet publie ou distribue le code de ces sous-modules, une revue
> licence-compatibilité est requise. En usage interne / build-time / sous-module
> non distribué, les obligations sont allégées.
>
> **† Automata — licence effective = MIT.** Le fichier `LICENSE` commence par une
> ligne-titre `Automata.NET` qui fait que l'API GitHub classifie la licence comme
> `NOASSERTION`, mais le corps est **verbatim** le texte standard de la licence
> MIT (© Microsoft Corporation). Ne pas se fier au seul badge de l'API GitHub ici.

## 3. Bibliothèques vendored (copiées dans l'arbre)

| Bibliothèque | Chemin | Licence | Copyright |
|--------------|--------|---------|-----------|
| difflogic (Petersen, NeurIPS 2022 — _Differentiable Logic Gate Networks_) | `MyIA.AI.Notebooks/SymbolicAI/SymbolicLearning/vendor/difflogic/` | **MIT** | © 2021-2023 Dr. Felix Petersen |
| Metagol (programmation logique inductive) | `MyIA.AI.Notebooks/SymbolicAI/SymbolicLearning/vendor/metagol/` | **BSD-3-Clause** | © 2016, Metagol authors |

> `foundry-lib/` (`MyIA.AI.Notebooks/SymbolicAI/SmartContracts/foundry-lib/`)
> est un **échafaudage propre** au projet (`foundry.toml` + `lib/`) qui consomme
> les trois sous-modules Solidity ci-dessus (forge-std, openzeppelin-contracts,
> account-abstraction) ; ce n'est pas une bibliothèque tierce à part entière.

## 4. Dépendances Lake (Lean)

Les projets Lean déclarent leurs dépendances dans `lakefile.lean` / `lake-manifest.json`.
Elles sont **résolues au build** (téléchargées par Lake dans `.lake/packages/`), non
copiées dans le dépôt. Principale dépendance tierce notable :

| Dépendance | Source | Commit pinné | Licence |
|------------|--------|--------------|---------|
| Mathlib 4 | <https://github.com/leanprover-community/mathlib4> | cf. `lake-manifest.json` par projet | Apache-2.0 |
| SocialChoiceLean (Dominik Peters) | <https://github.com/DominikPeters/SocialChoiceLean> | `355075e3` | _à confirmer_ |

> `social_choice_lean_peters/` est une **visite guidée locale** (propre au dépôt)
> qui importe la bibliothèque Lake de Peters comme dépendance — ce n'est pas une
> copie vendored de son code.

## 5. Hors-périmètre (suivi séparément, tranche 2 de #8055)

Les éléments suivants ne sont **pas** couverts par cette notice et feront l'objet
d'un registre dédié (issue #8055, tranche 2) :

- **Datasets** : MNIST, données de marché QuantConnect, corpus d'argumentation,
  données étudiantes (privées GDrive) — nécessitent URL + version + licence + checksum.
- **Poids de modèles GenAI** : Qwen, Stable Diffusion, etc. — licence propre au modèle.
- **Médias pédagogiques / extraits** : figures, illustrations, extraits d'ouvrages —
  licence potentiellement distincte du code MIT.
- **Dépendances runtime** (pip / nuget / npm) : non copiées dans le dépôt, déclarées
  dans les `requirements.txt` / `*.csproj` — licence de chaque paquet gérée par son gestionnaire.

## 6. Distinction code vs contenu pédagogique

La licence **MIT** couvre le **code** de ce dépôt. Les **supports pédagogiques**
(narration, exercices, choix didactiques) sont l'œuvre de l'auteur et leur
réutilisation est régie par la même licence MIT, sauf mention contraire explicite
dans le répertoire concerné (ex. médias/extraits tiers — cf. § 5).

---

**Statut** : tranche 1 de #8055 (THIRD_PARTY_NOTICES central — sous-modules +
vendored). La tranche 2 (registre datasets + DATASET_CARD + licences modèles GenAI)
reste à livrer — l'issue reste ouverte. Mettre à jour cette notice si un sous-module
est ajouté/supprimé/mis à jour (cf. `git submodule status`).
