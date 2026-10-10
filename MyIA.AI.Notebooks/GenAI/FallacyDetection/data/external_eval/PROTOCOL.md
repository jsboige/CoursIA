# Protocole d'annotation — test externe humain du corpus académique

Issue #20222 (grain 1) · tranche C de #17578 · EPIC #10355.
Critères fixés à l'ouverture de #20222 — ce document est leur mise en œuvre opérationnelle.

## 1. Objet

Mesurer, par des évaluateurs humains indépendants, que les paires
*(texte académique, nœud de taxonomie)* du corpus aligné portent une étiquette
qu'un humain peut retrouver. C'est la condition préalable au gate de Phase 3
(macro-F1 > baselines, ≥ 4 graines, Diebold-Mariano) : entraîner un modèle sur
des étiquettes qu'aucun humain ne retrouve mesurerait le bruit, pas la capacité.

## 2. Instrument

L'échantillon est produit par `scripts/fallacy_detection/sample_external_eval.py`
(corpus-agnostique : il consomme le JSONL aligné dès que la table d'alignement
(#20028) est mergée) :

```bash
python scripts/fallacy_detection/sample_external_eval.py \
    --input <corpus_aligne.jsonl> \
    --out-dir MyIA.AI.Notebooks/GenAI/FallacyDetection/data/external_eval/run1 \
    --n 200 --min-per-family 10 --seed 42
```

L'outil garantit, par construction et par tests (`tests/test_sample_external_eval.py`) :

- **plancher stratifié** : chaque famille de premier niveau ≥ 10 paires, sinon refus fail-closed nommant la famille déficiente ;
- **aveugle structurel** : `sheet.jsonl` (feuille évaluateur) ne contient jamais le nœud cible **ni sa famille de premier niveau** (la liste fermée des familles reste connue des évaluateurs — c'est l'espace de réponse du passage 1 — mais la famille correcte d'un item est la première moitié de la réponse : la porter sur la feuille rendrait le seuil « branche » du §4 circulaire) ; `key.jsonl` (correction, qui porte la famille pour la stratification) est un fichier séparé ;
- **reproductibilité** : même graine = même échantillon (SHA-256 de la feuille consigné dans `manifest.json` avec empreintes de la source et de la clé).

## 3. Évaluateurs

- **≥ 3 évaluateurs indépendants** (l'arbitrage du panel — qui sont les humains, et sous quelle modalité — est l'objet de la question user Q25, registre de la lane).
- **Passage 1 « annotation nue » (obligatoire)** : l'évaluateur voit le texte et la liste des familles de premier niveau ; il choisit la famille, puis le nœud dans la famille. Il ne voit **ni la définition des nœuds, ni aucun exemple** — c'est le passage qui mesure la retrievability « à froid ».
- **Passage 2 « avec définitions » (optionnel, séparé)** : mêmes items, définitions des nœuds visibles. Il mesure l'apport des définitions, jamais il ne remplace le passage 1.

## 4. Mesures (seuils annoncés avant la mesure)

| Mesure | Niveau | Seuil annoncé |
|---|---|---|
| Accord inter-annotateurs (alpha de Krippendorff) | nœud exact | ≥ 0,60 |
| Accord inter-annotateurs (alpha de Krippendorff) | branche de 1er niveau | ≥ 0,70 |
| Exactitude humaine moyenne vs étiquette corpus | nœud exact | rapportée + IC Wilson 95 % |
| Exactitude humaine moyenne vs étiquette corpus | branche de 1er niveau | rapportée + IC Wilson 95 % |

Le calcul se fait sur la **feuille de tous les évaluateurs du passage 1** ; le
passage 2 est rapporté séparément. Aucun seuil n'est ajusté après coup.

## 5. Désaccords

- Toute paire à **désaccord majoritaire** (aucun nœud majoritaire chez les évaluateurs) part en **re-vue** : les évaluateurs revoient l'item avec la définition du nœud cible visible et peuvent réviser leur choix ; le verdict final est consigné.
- **Aucune réécriture silencieuse du corpus** : si la re-vue conclut que l'étiquette du corpus est fausse, la correction passe par une PR dédiée avec justification par item — le présent protocole ne modifie pas la donnée qu'il mesure.

## 6. Données et lieux

- Feuilles d'annotation remplies, réponses brutes et identités des évaluateurs : **hors dépôt** (GDrive privé, données PII).
- Seul un **agrégat anonymisé** (tables de ce document, comptes, alphas) peut être cité dans une PR.

**Condition d'aveuglement — ce qui ne doit pas atteindre l'évaluateur.** La feuille d'annotation ne porte ni le nœud cible ni sa famille de premier niveau (§2), mais cela ne suffit pas : l'échantillonneur est **déterministe**, donc quiconque détient à la fois la graine, le manifeste et le corpus aligné peut rejouer le tirage et **reconstruire la clé**. L'aveuglement tient donc à une règle de circulation, pas à une propriété du fichier :

| Document | Destinataire | Pourquoi |
|---|---|---|
| `sheet.jsonl` (feuille aveugle) | l'évaluateur | ne porte ni nœud, ni famille, ni graine, ni rang — les identifiants sont adressés par le contenu |
| `key.jsonl` (correction) | l'organisateur seul | porte le nœud cible |
| `manifest.json` (graine, effectifs, empreintes) | l'organisateur seul | la graine y est en clair, et elle suffit à rejouer le tirage |

Un identifiant qui afficherait la graine (forme `eval-<graine>-<rang>`) la donnerait à lire sur la feuille ; l'échantillonneur produit donc des identifiants opaques, adressés par le contenu de l'item.
- Le corpus source et ses NOTICE de licence gouvernent l'échantillon dérivé (cf. #20217 : MAFALDA verbatim, licences vérifiées firsthand).

## 7. État

- [x] Instrument d'échantillonnage + tests (ce grain).
- [ ] Échantillon réel : dès le merge de la table d'alignement (#20028), une commande (§2) produit `run1`.
- [ ] Panel d'évaluateurs : arbitrage user Q25 (recommandation lane : étudiants des cours, TP guidé).
- [ ] Campagne d'annotation + mesures (§4) + re-vues (§5).
