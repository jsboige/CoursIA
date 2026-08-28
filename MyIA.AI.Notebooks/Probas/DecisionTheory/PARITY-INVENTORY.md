# Inventaire de parité — Série `DecisionTheory/` (DecInfer ⇄ DecPyMC)

> Snapshot pré-merge daté du **HEAD `87dffc2bd9c`**, branche `feature/12933-decision-parity-inventory`,
> tranche **P0** de l'[EPIC #12933](https://github.com/jsboige/CoursIA/issues/12933) (« Renumérotation
> paritaire des séries parallèles — stabiliser les identifiants sans uniformiser les contenus »).
>
> Cette table est l'**inventaire des paires**, le pendant DONNÉES de la garde structurelle
> `NUMBERING-DRIFT` livrée par [PR #13017](https://github.com/jsboige/CoursIA/pull/13017) (po-2023).
> Sans inventaire, le verdict NUMBERING-DRIFT ne dispose pas d'un mapping de référence pour
> argumenter les tranches de renommage à venir.

## Périmètre strict de la tranche

- **Fichiers concernés** : `MyIA.AI.Notebooks/Probas/DecisionTheory/**` (lecture seule sur les
  notebooks ; création du présent Markdown).
- **Hors scope** : `scripts/notebook_tools/check_twin_parity.py` (claim po-2023 délimité) —
  cette tranche ne touche ni le checker, ni le registre `twin_pairs.d/_schema.yaml`, ni les
  paires qui y sont déjà catalogées (cf §6 ci-dessous).
- **Aucun renommage**, aucun `git mv`, aucun PR composite. Le livrable est un fichier Markdown
  seul, mergeable indépendamment des campagnes de parité à venir.

## Vue d'ensemble — l'arc commun et ses extensions

```
DecInfer/  (10 notebooks : 8 C#/.NET + 2 Lean 4)
  └── DecInfer-1  Utility-Foundations        (aligne)
        DecInfer-2  Lean-ExpectedUtility     (companion Lean, suffixe)
        DecInfer-3  Utility-Money            (decalé)  ─┐
        DecInfer-4  Multi-Attribute          (decalé)   │ arc commun
        DecInfer-5  Decision-Networks       (decalé)   │ 6 paires
        DecInfer-6  Value-Information        (decalé)   │ décalées
        DecInfer-7  Expert-Systems           (decalé)   │
        DecInfer-8  Sequential               (decalé)  ─┘
        DecInfer-9  Lean-Gittins             (companion Lean, suffixe)
        DecInfer-10 Thompson-Sampling        (aligné au DecPyMC-7 multi-section, extension unilatérale)

DecPyMC/   (9+ notebooks : NUTS/ADVI Python)
  └── DecPyMC-1   Utility-Foundations       (aligné) ←─────────────┐
        DecPyMC-2   Utility-Money           (decalé)               │ gap de
        DecPyMC-3   Multi-Attribute         (decalé)               │ 1 cran
        DecPyMC-4   Decision-Networks       (decalé)               │ sur
        DecPyMC-5   Value-Information       (decalé)               │ 6 paires
        DecPyMC-6   Expert-Systems          (decalé)               │ communes
        DecPyMC-7   Sequential + Bandits    (decalé) ──────────────┘
        DecPyMC-8   Actuarial-Credibility   (extension unilatérale)
        DecPyMC-9   Prime-Pure-Chargement   (extension unilatérale)
        DecPyMC-12  Frequence × Severite    (PR #12920 en file CI — pre-merge snapshot)
```

## 1. Table de parité numérique — verdict par concept (aligné au HEAD `87dffc2bd9c`)

| # | Concept partagé | DecInfer | DecPyMC | Verdict numérique | Paire commune ? |
|---|---|---|---|---|---|
| 1 | Fondations de l'utilité (axiomes VNM, utilité espérée) | `DecInfer-1-Utility-Foundations` | `DecPyMC-1-Utility-Foundations` | **aligné** (1 ↔ 1) | ✅ |
| 2 | Utilité et monnaie (St-Petersbourg, CARA/CRRA) | `DecInfer-3-Utility-Money` | `DecPyMC-2-Utility-Money` | **décalé** (3 ↔ 2) | ✅ |
| 3 | Décision multi-attributs (MAUT, SMART, swing weights) | `DecInfer-4-Multi-Attribute` | `DecPyMC-3-Multi-Attribute` | **décalé** (4 ↔ 3) | ✅ |
| 4 | Réseaux de décision (diagrammes d'influence) | `DecInfer-5-Decision-Networks` | `DecPyMC-4-Decision-Networks` | **décalé** (5 ↔ 4) | ✅ |
| 5 | Valeur de l'information (EVPI, EVSI) | `DecInfer-6-Value-Information` | `DecPyMC-5-Value-Information` | **décalé** (6 ↔ 5) | ✅ |
| 6 | Systèmes experts (Minimax, regret) | `DecInfer-7-Expert-Systems` | `DecPyMC-6-Expert-Systems` | **décalé** (7 ↔ 6) | ✅ |
| 7 | Décision séquentielle (MDPs, valeur/politique, bandits) | `DecInfer-8-Sequential` | `DecPyMC-7-Sequential` | **décalé** (8 ↔ 7) | ✅ |
| 7' | Thompson Sampling bayésien (bandits) | `DecInfer-10-Thompson-Sampling` | inclus dans `DecPyMC-7-Sequential` | **extension unilatérale** | ❌ (pas une paire) |

**Verdict synthèse** :
- **1 paire alignée** (Utility-Foundations).
- **6 paires communes décalées d'un cran** (la numérotation DecInfer a été décalée par
  l'insertion de DecInfer-2 — companion Lean — entre le N°1 et le N°3 subséquent).
- **1 extension unilatérale** côté DecInfer (Thompson Sampling disaggregated).
- **2 extensions unilatérales** côté DecPyMC (Actuarial-Credibility, Prime-Pure-Chargement),
  plus une 3ᵉ en route (Frequence × Severite, PR #12920 pre-merge).

## 2. Cause structurelle du décalage

L'EPIC #12933 a déjà diagnostiqué la cause (cf body §La cause n'est pas un mauvais contenu) :
> `DecInfer-2-Lean-ExpectedUtility` est un companion formel légitime, mais son insertion dans
> la séquence principale a décalé tous les concepts communs suivants.

Le même mécanisme vaut pour `DecInfer-9-Lean-Gittins` (companion Lean, intercalé en N°9, suivi
du Thompson Sampling en N°10). Les companions Lean NE DEVRAIENT PAS décaler le compteur commun,
mais le système de numérotation initial les a traités comme des entrées à part entière.

## 3. Recommandations de mapping (proposition, **non livrée**)

L'EPIC #12933 énonce le principe directeur :
> **Parité des identifiants, liberté des contenus.**

Trois voies possibles (à arbitrer en EPIC, pas dans cette tranche) :

| Voie | Description | Effet sur les notebooks | Risque |
|---|---|---|---|
| **(a) Suffixe compagnon** (recommandée par le principle directeur) | Renommer `DecInfer-2-Lean-ExpectedUtility` → `DecInfer-1b-Lean-ExpectedUtility` (companion de #1, suffixe `b`). Idem `DecInfer-9-Lean-Gittins` → `DecInfer-8b-Lean-Gittins`. Les DecInfer-3..8 restent alignés avec DecPyMC-2..7. | 2 `git mv` + réparations de liens entrants (REVIEW, datasets, manifestes) ; pas de renommage côté PyMC. | Faible (companions explicites, déjà conventionnés `App-Nb` / `SW-Nb`). |
| **(b) Re-numérotation totale PyMC** | Renommer `DecPyMC-2..7` → `DecPyMC-3..8` pour s'aligner à DecInfer. Coûteux en références entrantes. | 6 renommages + réparations systématiques des liens Python (catalogue, baselines, tests). | Élevé (les notebooks PyMC sont les plus référencés par les notebooks Causal-Bridges et autres arcs). |
| **(c) Slot compagnon vide PyMC** | Ajouter `DecPyMC-1b` et `DecPyMC-8b` vides (companion slot non rempli) pour préserver la parité des nombres, sans toucher au contenu PyMC. | 2 fichiers stubs vides, déclaration d'absence. | Faible techniquement, fort symboliquement (pourquoi des fichiers vides ?). |

**Voie (a) est la moins invasive** et **respecte la convention pré-existante** (`App-Nb`,
`SW-Nb` suffixes compagnons) déjà documentée dans le registre `_schema.yaml` (cf lecture
po-2023, 2026-08-25). Une fois la décision rendue, cette section sera reprise dans une
tranche de mapping dédiée.

## 4. Extensions unilatérales (ni décalées, ni alignées — à documenter tel quel)

| Extension | Justification | Jumeau attendu ? |
|---|---|---|
| `DecInfer-10-Thompson-Sampling` | Extension dédiée bayésienne (regret vs ε-greedy/UCB1) — détails méthodologiques qui dépassent la couverture `DecPyMC-7` (qui inclut Thompson mais dilué dans MDP+bandits). | Non prévu. À vérifier si une future refonte `DecPyMC-10b` est légitime. |
| `DecPyMC-8-Actuarial-Credibility` | Extension actuarielle (théorie de la crédibilité Bühlmann-Straub) propre à PyMC. Aucun pré-requis d'un équivalent Infer.NET. | Documenter comme extension unilatérale autorisée. |
| `DecPyMC-9-Prime-Pure-Chargement` | Extension actuarielle (théorie de la prime pure, méthodes de chargement) propre à PyMC. | Documenter comme extension unilatérale autorisée. |
| `DecPyMC-12-Frequence-Severite-Hierarchique` (PR #12920, pre-merge) | Extension actuarielle (partial pooling fréquence × sévérité). Reflète la spécialisation PyMC en actuariat. | À documenter une fois la PR mergée (snapshot actuel = pre-merge, file CI). |

**Aucune de ces extensions ne constitue une violation de la parité numérique** — elles n'ont
pas de jumeau côté DecInfer et la convention autorise explicitement les extensions unilatérales
(EPIC #12933 §Principe directeur).

## 5. État du registre `twin_pairs.d/` (snapshot au HEAD)

```
$ ls scripts/notebook_tools/twin_pairs.d/ | grep -iE "(dt-?|dec(dt|infer|pymc))" | head
(no output)
```

**Constat vérifié** : le registre `twin_pairs.d/` ne catalogue **aucune** des paires
`DecInfer-N ↔ DecPyMC-N` (il catalogue les paires `probas-1..19` du corpus bayésien
Infer ⇄ PyMC, cf fichiers `probas-1-setup.yaml` à `probas-19-survival-analysis.yaml`).

**Conséquence** : la garde structurelle `NUMBERING-DRIFT` livrée par PR #13017 ne **peut pas**
détecter le décalage DecisionTheory tant que les paires ne sont pas ajoutées au registre.

**Recommandation (proposition, **non livrée**)** : ouvrir une tranche **#12933-P0bis-ajout-registre**
pour créer `scripts/notebook_tools/twin_pairs.d/dt-1-utility-foundations.yaml` à
`dt-7-sequential.yaml` (7 paires communes) + 2 fichiers `dt-ext-{8,9}-*.yaml` pour marquer
explicitement les extensions unilatérales. Chaque fichier suit le format `_schema.yaml`.

## 6. Traçabilité du snapshot (SHA-256 partiels, 12 chars, HEAD `87dffc2bd9c`)

| Fichier | SHA-256[:12] |
|---|---|
| `DecInfer-1-Utility-Foundations.ipynb` | `95e3f0de1967` |
| `DecInfer-2-Lean-ExpectedUtility.ipynb` | `fc68d29f5607` |
| `DecInfer-3-Utility-Money.ipynb` | `5d9730fcdfca` |
| `DecInfer-4-Multi-Attribute.ipynb` | `43c7a0f7e033` |
| `DecInfer-5-Decision-Networks.ipynb` | `5f0a534d7a9e` |
| `DecInfer-6-Value-Information.ipynb` | `84dbb0657965` |
| `DecInfer-7-Expert-Systems.ipynb` | `395123d8c37b` |
| `DecInfer-8-Sequential.ipynb` | `17f2afe786af` |
| `DecInfer-9-Lean-Gittins.ipynb` | `b3428a08ced3` |
| `DecInfer-10-Thompson-Sampling.ipynb` | `fc01f40aa3b8` |
| `DecPyMC-1-Utility-Foundations.ipynb` | `ed6ab40b030f` |
| `DecPyMC-2-Utility-Money.ipynb` | `b873c515ac49` |
| `DecPyMC-3-Multi-Attribute.ipynb` | `a12850b5e41d` |
| `DecPyMC-4-Decision-Networks.ipynb` | `9369a916c6b5` |
| `DecPyMC-5-Value-Information.ipynb` | `d6a1dd6c3332` |
| `DecPyMC-6-Expert-Systems.ipynb` | `7cc021bf6890` |
| `DecPyMC-7-Sequential.ipynb` | `8c26ed12eca0` |
| `DecPyMC-8-Actuarial-Credibility.ipynb` | `911917b37be5` |
| `DecPyMC-9-Prime-Pure-Chargement.ipynb` | `da07ee1592e0` |

## 7. Critères d'acceptation EPIC #12933 touchés par cette tranche

- [x] **Table d'inventaire** de toutes les familles parallèles, avec verdict `alignée / décalée / extension légitime / fausse paire` — cette tranche couvre la famille **DecisionTheory** (cf §1).
- [ ] Mapping DecisionTheory arbitré — relevant d'une tranche ultérieure (voies a/b/c, §3).
- [ ] Concepts communs `DecInfer` ⇄ `DecPyMC` portant le même identifiant, ou divergence explicitement justifiée — voir §1 (état des lieux pré-merge).
- [ ] `Infer-1..19` ⇄ `PyMC-1..19` préservé et enregistré comme invariant — hors périmètre de cette tranche (couvert par po-2023 calibration 157/157).
- [x] Aucune référence entrante réparée — cette tranche n'effectue **aucun** renommage.
- [ ] Aucun churn manuel du catalogue généré — non applicable (catalogue non touché).
- [x] Garde automatisé NUMBERING-DRIFT (PR #13017) — **livré par po-2023**, complémentaire à cette table.
- [x] Aucun notebook rendu artificiellement identique — cette tranche ne modifie aucun notebook.

## 8. Liens et précédents

- [EPIC #12933](https://github.com/jsboige/CoursIA/issues/12933) — ligne directrice de la parité
- [PR #13017](https://github.com/jsboige/CoursIA/pull/13017) — garde NUMBERING-DRIFT (po-2023, calibration 157/157)
- [PR #12920](https://github.com/jsboige/CoursIA/pull/12920) — DecPyMC-12, pré-merge snapshot documenté §4
- #5361 — précédent Probas/Infer ⇄ Probas/PyMC alignement 1-19 (cf body EPIC)
- #4956 — marathon de parité .NET ⇄ Python
- #5081 — renumérotation narrative des séries
- #12904 — expansion actuarielle en cours, dont DecPyMC-12 fait partie
- `MyIA.AI.Notebooks/Probas/DecisionTheory/README.md` — convention durable du portage
- `scripts/notebook_tools/twin_pairs.d/_schema.yaml` — schéma du registre (à compléter par §5)

---

*Snapshot généré pour la tranche **P0 DecisionTheory** de l'EPIC #12933. Aucune modification de
notebook. Aucune nouvelle entrée dans le registre `twin_pairs.d/`. Voir §6 pour la traçabilité
SHAs au HEAD `87dffc2bd9c`.*
