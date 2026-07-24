# Dataset Cards — fiches descriptives par dataset

> **Statut.** Document de cadrage, grade **B-méthodologique** (template applicable). V0 = pilote cycle c.795 (issue #8055 tranche 2).
> **Objet.** Répondre à l'acceptance d'[#8055](https://github.com/jsboige/CoursIA/issues/8055) (DATASET_CARD pour les cas sensibles) et préparer la **gate fuzzy-match RGPD** (#8054).
> **Discipline.** NE REMPLACE PAS `DATASET_REGISTRY.md` (inventaire canonique) ; **AJOUTE** une couche descriptive **par dataset sensible** : finalité pédagogique, périmètre RGPD, procédure de re-validation en cas de fork.
> **Lien.** Issue-source : [#8055](https://github.com/jsboige/CoursIA/issues/8055) (tranche 2). Privacy parent : [#8054](https://github.com/jsboige/CoursIA/issues/8054) (PRIVACY.md, PR #8063 OPEN MERGEABLE jsboige).

## Pourquoi des Dataset Cards

Un dataset pédagogique qui contient des **noms explicites** ou des **données médicales simulées** peut être confondu avec un dataset réel par un étudiant qui fork. La `DATASET_CARD.md` :

1. **Documente le caractère synthétique** explicitement (`SYNTHETIQUE-COURS`, fabriqué pour le cours, aucune correspondance avec des patients réels).
2. **Limite la réutilisation** en rappelant que toute redistribution doit conserver la mention `synthétique`.
3. **Précise le périmètre RGPD** (données fictives → pas de base légale à déclarer, mais procédure de suppression fin de semestre par mesure de précaution).
4. **Fournit une procédure de re-validation** si le fork détecte une modification du SHA256 (cf `check_dataset_registry.py --audit`).

## Template standard (à dupliquer pour chaque dataset sensible)

```markdown
### `<chemin_relatif>`

**Catégorie** : <categorie>
**Licence** : <licence>
**Taille** : <taille_bytes> B
**SHA256** : `<sha256>`
**Date de validation** : <YYYY-MM-DD>
**Validateur** : <agent ou "manual">

#### Finalité pédagogique

<1-3 phrases : ce que le notebook apprend avec ce dataset, ce que l'étudiant doit observer.>

#### Composition

- **Lignes** : <N>
- **Colonnes** : <liste>
- **Sensibilité** : <description explicite de la nature des données : noms fictifs, valeurs simulées, etc.>
- **Période temporelle** : <si applicable, ex: "2023-01 à 2023-12">

#### Procédure de re-validation

Si le SHA256 change après fork :
1. Vérifier que le diff ne modifie pas les colonnes sensibles (noms, identifiants).
2. Confirmer que le nouveau contenu reste **synthétique** (re-grep `head -3 <fichier>`).
3. Mettre à jour le SHA256 dans `DATASET_REGISTRY.md` + ce fichier.

#### Périmètre RGPD

- **Données réelles ?** : <OUI/NON — explicite>
- **Si OUI** : base légale, durée de conservation, procédure de suppression.
- **Si NON (synthétique)** : mention pédagogique explicite à conserver dans toute redistribution.

#### Caveats

- <Limitations connues>
- <Cas où le dataset NE DOIT PAS être utilisé>
```

---

## Cas pilotes c.795

### `CaseStudies/Diagnostic-Medical/data/patients.csv`

**Catégorie** : **sensible** (noms explicites + données médicales)
**Licence** : `SYNTHETIQUE-COURS` (MIT CoursIA)
**Taille** : 808 B
**SHA256** : `66f816ef85d64289af30cc429b632344b9522fc686a9276c72dc3d128d67cc4b`
**Date de validation** : 2026-07-23
**Validateur** : po-2025 (Claude M3) — `sha256sum` firsthand origin/main SHA `8092a4aec`

#### Finalité pédagogique

Cas diabétique pédagogique pour `CaseStudies/Diagnostic-Medical/`. Démontre le raisonnement clinique : corrélation glycémie à jeun / postprandiale / HbA1c, déclenchement d'un plan de soin selon les seuils ADA. L'étudiant apprend à **formuler un diagnostic** sans outil ML, puis à vérifier la cohérence d'un classificateur.

#### Composition

- **Lignes** : 5 patients
- **Colonnes** : `id`, `nom`, `age`, `glycemie_jeun`, `glycemie_postprandiale`, `hba1c`, `symptomes`, `antecedents`, `pression_arterielle`, `imc`
- **Sensibilité** : NOMS EXPLICITES (Alice, Bob, …) + données médicales (glycémie, tension). **Aucun patient réel n'est concerné** — toutes les valeurs sont construites pour le cours.
- **Période temporelle** : N/A (snapshot instantané)

#### Procédure de re-validation

Si le SHA256 change après fork :
1. `head -3 <fichier>` — confirmer que les noms restent des prénoms courants (Alice, Bob, …) et non des vrais identifiants.
2. Vérifier que les colonnes médicales restent dans des plages physiologiques cohérentes (HbA1c < 15 %, glycémie < 500 mg/dL).
3. Mettre à jour SHA256 + date dans `DATASET_REGISTRY.md`.

#### Périmètre RGPD

- **Données réelles ?** : **NON** — explicite.
- **Mention obligatoire en redistribution** : "Données synthétiques à visée pédagogique, toute ressemblance avec des patients réels serait fortuite."
- **Procédure de suppression fin de semestre** : aucune (données non-réelles). Conservation indéfinie autorisée.

#### Caveats

- Ne pas utiliser comme input d'un système de diagnostic médical réel.
- Ne pas augmenter le nombre de patients avec de vrais identifiants sans gate `GradeBookApp/PRIVACY.md`.

---

### `CaseStudies/Oncology-Planning/data/patients_oncology.csv`

**Catégorie** : **sensible** (noms explicites + données oncologie)
**Licence** : `SYNTHETIQUE-COURS` (MIT CoursIA)
**Taille** : 5 124 B
**SHA256** : `211b298747c465a33bd8ccae9c8c0aa682cd49c7f230d1dc6223d329d265ff16`
**Date de validation** : 2026-07-23
**Validateur** : po-2025 (Claude M3) — `sha256sum` firsthand origin/main SHA `8092a4aec`

#### Finalité pédagogique

Planification oncologie pour `CaseStudies/Oncology-Planning/`. Démontre l'ordonnancement de séances de chimiothérapie sous contraintes (disponibilité machine, toxicité cumulative, intervalles inter-séances). L'étudiant apprend à formuler un **problème de planification** et à vérifier la cohérence d'un solveur CSP.

#### Composition

- **Lignes** : N (≈50 patients)
- **Colonnes** : `id`, `nom`, `age`, `type_cancer`, `stadification`, `traitement_propose`, `duree_seance_min`, `machine_assignee`, `disponibilite`, `toxicite_cumulative`, `intervalle_jours`
- **Sensibilité** : NOMS EXPLICITES + diagnostic oncologique. **Aucune correspondance avec de vrais patients** — données construites pour le cours.
- **Période temporelle** : N/A (snapshot)

#### Procédure de re-validation

Si le SHA256 change après fork :
1. `head -3 <fichier>` — confirmer que les noms restent synthétiques et les diagnostics dans des catégories génériques (sein, poumon, colon, …) sans détails histopathologiques.
2. Vérifier que les colonnes de planification restent cohérentes (durée séance 30-240 min, intervalle 7-28 jours).
3. Mettre à jour SHA256 + date dans `DATASET_REGISTRY.md`.

#### Périmètre RGPD

- **Données réelles ?** : **NON** — explicite.
- **Mention obligatoire en redistribution** : "Données synthétiques à visée pédagogique, toute ressemblance avec de vrais patients serait fortuite."
- **Procédure de suppression fin de semestre** : aucune (données non-réelles). Conservation indéfinie autorisée.

#### Caveats

- Ne pas utiliser pour entraîner un modèle de prédiction oncologique réel.
- Le terme "oncologie" est sensible : la `DATASET_CARD` doit toujours accompagner toute redistribution.

## Suite logique

| Cycle | Cible |
|-------|-------|
| c.796 | DATASET_CARD pour 7 fichiers QC yfinance (BTC, ETH, ADA, AVAX, DOT, LINK, LTC, MATIC, SOL, XRP) — volatilité crypto, pas PII |
| c.797 | DATASET_CARD pour ML/DataScienceWithAgents (Track1 + Track2 sales_data.csv) |
| c.798 | Audit croisé DATASET_CARD ↔ catalogue (si une entrée dataset sensible est référencée par un notebook sans card → `CARD_REQUIRED` MAJOR) |

## Voir aussi

- [DATASET_REGISTRY.md](./DATASET_REGISTRY.md) — inventaire canonique avec SHA256
- [THIRD_PARTY_NOTICES.md](../../THIRD_PARTY_NOTICES.md) — licences code/submodules/vendored
- [PRIVACY.md (à venir, PR #8063)](../../GradeBookApp/PRIVACY.md) — politique RGPD GradeBookApp
- [secrets-hygiene.md](../../.claude/rules/secrets-hygiene.md) — pas de secrets inline
