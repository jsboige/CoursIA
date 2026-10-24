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

L'outil garantit, par construction et par tests (`scripts/fallacy_detection/tests/test_sample_external_eval.py`) :

- **plancher stratifié** : chaque famille de premier niveau ≥ 10 paires, sinon refus fail-closed nommant la famille déficiente ;
- **aveugle structurel** : `sheet.jsonl` (feuille évaluateur) ne contient jamais le nœud cible **ni sa famille de premier niveau** (la liste fermée des familles reste connue des évaluateurs — c'est l'espace de réponse du passage 1 — mais la famille correcte d'un item est la première moitié de la réponse : la porter sur la feuille rendrait le seuil « branche » du §4 circulaire) ; `key.jsonl` (correction, qui porte la famille pour la stratification) est un fichier séparé ;
- **reproductibilité** : même graine = même échantillon (SHA-256 de la feuille consigné dans `manifest.json` avec empreintes de la source et de la clé).

### 2 bis. Rendu de la feuille et conversion des réponses

`sheet.jsonl` est un fichier aveugle, pas un document : il ne s'ouvre pas avec
une consigne. `render_annotation_sheet.py` le rend lisible et referme la chaîne
entre l'échantillonneur (§2) et le mesureur (`score_external_eval.py`) :

```bash
# document Markdown + gabarit de réponses CSV, pour un évaluateur
python scripts/fallacy_detection/render_annotation_sheet.py render \
    --sheet .../run1/sheet.jsonl \
    --vocab <corpus_aligne.jsonl> \
    --out-dir .../run1/pass1/<pseudonyme> --label <pseudonyme>

# gabarit rempli -> forme consommée par le mesureur
python scripts/fallacy_detection/render_annotation_sheet.py convert \
    --answers .../pass1/<pseudonyme>/answers_<pseudonyme>.csv \
    --vocab <corpus_aligne.jsonl> \
    --out .../pass1/<pseudonyme>.jsonl
```

Trois points que le rendu tient par construction (`tests/test_render_annotation_sheet.py`) :

- **l'aveuglement est vérifié à l'entrée** : une feuille portant un champ autre que `item_id` et `text` est refusée — passer `key.jsonl` par erreur échoue au lieu de publier les étiquettes ;
- **l'espace de réponse est la liste des nœuds**, groupée par famille, sans définition ni exemple : c'est exactement ce que le passage 1 du §3 autorise à montrer ;
- **une faute de frappe est refusée à la conversion**, avec son numéro de ligne, plutôt que de devenir une note vide au calcul d'alpha ; une feuille partiellement remplie est refusée par défaut (`--allow-partial` la convertit en annonçant les lignes écartées).

Le document et le gabarit ne dérivent que de la feuille aveugle : aucune
étiquette cible ne s'y trouve. La clé, le manifeste et les feuilles remplies
restent soumis au §6.

## 3. Évaluateurs

- **≥ 3 évaluateurs indépendants** (la **voie** — pilote ou campagne — a été tranchée par la question user Q25 le 2026-10-12 ; l'identité des évaluateurs et la modalité de recrutement restent à décider au moment de l'exécution).
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
- [x] Échantillon réel `run1` (2026-10-20, table mergée via #20315 ; **re-émis le 2026-10-23** après le fix dedup du builder) : le corpus aligné (225 paires, `data/academic/aligned/`) est construit par `build_aligned_eval_corpus.py` — 128 joins exacts, 97 par pont déclaré (un rationale par pont), 44 exclus motivés, **unicité (texte, nœud) garantie à l'émission** (3 paires démultiplicées fusionnées, libellés sources dans `source_labels` ; la première émission dupliquait des paires, ce qui rendait la campagne inmesurable — c.6373865101). Tirage : 200 items, graine 42, stratifiés sur **6 familles** (17-56 par famille) ; la 7ᵉ (Tricherie) est **mesurée à 0 paire source** dans le gold MAFALDA entier — aucun span ne porte son unique label L2 (`Fallacy of proportion`). `sheet.jsonl` / `key.jsonl` / `manifest.json` (empreintes SHA-256 de la source, de la feuille et de la clé) vivent hors dépôt : `G:\Mon Drive\MyIA\IA\external-eval-20222\run1\` (circulation §6 — organisateur seul) ; la première émission (défectueuse, jamais circulée) est préservée dans `run1-superseded-20261023\`.
- [x] **Reproductibilité de `run1` confirmée par un second tirage indépendant** (2026-10-24, lane `myia-po-2028:CoursIA`) : relancé sur le corpus aligné courant, `--n 200 --min-per-family 10 --seed 42`, le tirage rend un `sheet.jsonl` **octet pour octet identique** à celui de `run1` — même empreinte source `8f2dc776…`, même empreinte feuille `f66058b6…`, même empreinte clé `4b66ace4…` et mêmes effectifs par famille (17/22/56/44/27/34). La propriété « même graine = même échantillon » du §2 est donc tenue par une mesure, pas seulement par un test unitaire. Copie du tirage conservée hors dépôt : `…\external-eval-20222\run1-200-po2028\sample\` — `run1\` reste la référence de la campagne.
- [x] **Chaîne complète exercée de bout en bout** (2026-10-24, même lane) : `sample_external_eval.py` → `render_annotation_sheet.py render` → `… convert` → `score_external_eval.py`. Contrôle d'étanchéité **de plomberie, pas une mesure** : trois feuilles de réponses recopiées depuis la clé elle-même donnent alpha nœud 1,000, alpha branche 1,000, exactitude 1,000 (IC Wilson 0,994-1,000) et 0 item à revoir. Ce que ce contrôle prouve est que la feuille rendue est **remplissable** et que le mesureur consomme la forme exacte que `convert` produit ; il ne dit **rien** de l'accord entre humains (§4), et ses artefacts portent `_plumbing_control` dans leur chemin pour ne jamais être pris pour une campagne.
- [x] **Feuilles d'annotation du passage 1 rendues** (2026-10-24) : trois documents de 200 énoncés (`eval_a`, `eval_b`, `eval_c`), chacun avec son gabarit CSV et son manifeste de rendu, sous `…\external-eval-20222\run1-200-po2028\pass1\`. L'espace de réponse fermé y est la section « 6 familles, 16 nœuds » ; aucun énoncé ne porte son nœud ni sa famille (vérifié : la feuille ne porte que `item_id` et `text`). Une feuille par évaluateur, le critère 2 exigeant trois évaluateurs indépendants.
- [ ] **Panel humain** : Q25 est **répondue** depuis le 2026-10-12 (« OK pour i ou ii », citée dans le corps de #22233) — le pilote 30-50 paires est autorisé, cette ligne ne décrit donc plus un arbitrage en attente mais une **exécution** : recruter ≥ 3 évaluateurs indépendants, leur remettre les feuilles du passage 1, récupérer les CSV remplis. Choix de la voie (pilote 30-50 paires avant la campagne complète, ou campagne 200 directe) à trancher par le coordinateur.
- [ ] Campagne d'annotation + mesures (§4) + re-vues (§5) — aucune des deux ne peut être produite par un agent : elles exigent des évaluateurs humains.
