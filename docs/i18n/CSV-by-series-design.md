# CSV-by-series i18n infrastructure — design doc (EPIC #4957, Phase 1)

> **Statut** : design doc + pilote fonctionnel (Issue #4957, acceptée 2026-07-07 par ai-01
> deep-queue directive msg-20260707T170624-wmu0m5). **Phase 1** = design + script + pilote
> sur 1 série courte. Phase 2 (workflow CI drift-flag + rollout multi-série) hors scope PR.

## Contexte

85 fichiers `.en.md` existent déjà dans le repo (cf. `find MyIA.AI.Notebooks -name
'*.en.md' | wc -l`). Le pattern est manuel : un dev crée `README.en.md` en miroir du
`README.md` FR, sans outillage de synchronisation, sans garde-fou drift. Conséquences
observées (sondage échantillon 2026-07-07) :

- **désynchronisation FR↔EN** : la EN n'est souvent qu'un **résumé** de la FR, pas une
  traduction 1:1. Exemple canonique = `cross-series/README.en.md` (résumé court) vs
  `cross-series/README.md` (~50 lignes de prose détaillée). Le EN « survole » et **perd
  de l'information** ;
- **drift invisible** : quand le FR est modifié, personne ne pense à mettre à jour le
  EN. Aucun CI ne le signale ;
- **passage à l'échelle impossible** : passer d'1 langue (EN) à 8 langues (FR + EN + ES +
  DE + IT + PT + JA + ZH + RU, comme Argumentum) **à la main** est intractable (cf.
  `Argumentum/data/argumentum_fallacies_taxonomy.csv` 1552 sophismes × 7 langues ≈ 11000
  lignes de CSV, déjà géré en CSV, mais l'inverse pour de la prose markdown n'existe pas).

EPIC #1650 (traduction multilingue Phase 0.5) a résolu la **préservation** des
originaux anglais en `.en.md` (cf. `.claude/rules/readme-french-first.md` Règle 2).
#4980 (Lean i18n) a introduit la convention **FR canonique + `.en.md` mirror**. **#4957
est la phase suivante** : **rendre scalable le pattern CSV-driven**, sans casser
l'existant.

## Objectif

Une infrastructure i18n qui :

1. **traite la prose markdown comme une ressource structurée** (1 cellule FR = 1 ligne
   CSV), source de vérité = FR canonique ;
2. **génère automatiquement** les `.en.md` (et futures autres langues) à partir du CSV ;
3. **détecte le drift** en CI : si la FR bouge mais le CSV n'est pas régénéré → PR rouge ;
4. **conserve** le pattern existant (FR canonique + `.en.md` mirror + 0 coût `lake
   build`) sans rien casser.

## Format CSV

Le CSV est **par série** (1 fichier CSV par dossier qui contient un `README.md` FR + ≥1
`.en.md`). Format :

```csv
key,fr,en
"# <h1>","# Projets cross-séries","# Cross-Series Projects"
"## Pourquoi des projets cross-séries ?","Les séries du cours isolent...","The course series..."
"intro.para1","Ce répertoire rassemble des **projets transversaux**...","Showcase projects that span..."
"intro.para2","Là où chaque série enseigne *une* famille...",""
table.projects.header.1,"Projet","Project"
table.projects.header.2,"Description","Description"
table.projects.header.3,"Séries mobilisées","Domains"
table.projects.row.1.col.1,"[matching-cv/](matching-cv/)","[matching-cv/](matching-cv/)"
...
```

### Contraintes

| Aspect | Choix | Justification |
|--------|-------|---------------|
| **Séparateur** | virgule | standard RFC 4180 ; pas d'Excel-fr-FR |
| **Quote** | `"..."` toujours | permet virgules, sauts de ligne, retours chariot |
| **Headers obligatoires** | `key,fr,en,...` | header = langues cible (1 col par langue) |
| **Ordre colonnes** | langues après `key` | permet d'ajouter une langue sans tout réordonner |
| **Langues initiales** | FR + EN | déjà actées par EPIC #4980 ; ES/DE/IT/PT/JA/ZH/RU = ajout futur Phase 2 |
| **Clé `key`** | dot-path hiérarchique | lisible, machine-greppable, extensible |
| **Cellules absentes** | chaîne vide `""` | tolère les langues incomplètes (EN résumé ≠ EN 1:1) |

### Clés canoniques

Convention de nommage pour `key` :

| Pattern | Sens | Exemple |
|---------|------|---------|
| `# <h1>` | titre de niveau 1 | `# Projets cross-séries` |
| `## <h2>` | titre de niveau 2 | `## Pourquoi des projets cross-séries ?` |
| `<section>.para<N>` | paragraphe dans une section | `intro.para1` |
| `table.<name>.header.<col>` | en-tête de tableau | `table.projects.header.1` |
| `table.<name>.row.<R>.col.<C>` | cellule (R,C) de tableau | `table.projects.row.1.col.1` |
| `<section>.list.item<N>` | item de liste numérotée | `focus.list.item1` |
| `<section>.quote` | blockquote | `focus.note` |
| `<section>.raw<N>` | contenu verbatim (code, URL, etc.) | non recommandé (échapper) |

### Cellules `raw`

Pour les contenus où la traduction littérale est impossible (URLs, code blocks, chemins
relatifs), deux options :

1. **clé identique FR et EN** (markdown link *textuel* entre guillemets CSV, pas un vrai lien vers une ressource) : `url.matching_cv, "[matching-cv project](. / path / to / matching-cv/)", "[matching-cv project](. / path / to / matching-cv/)"` — les espaces dans `(. / path / to / …)` empèchent le parseur Markdown d'interpréter le pattern comme un lien cliquable
2. **clé `raw.<section>`** : pas traduite, passée verbatim au renderer

Recommandé = option 1 (le plus explicite, le moins de cas spéciaux dans `render.py`).

## Source de vérité

**FR est canonique.** Le pipeline est :

```
README.md (FR, canonique, versionné)
   │
   ├──> scripts/i18n/sync.py   (extrait cellules, génère/met à jour README.csv)
   │       │
   │       └──> README.csv     (intermédiaire, versionné)
   │
   └──> scripts/i18n/render.py (lit README.csv, regénère README.en.md)
           │
           └──> README.en.md   (artefact, versionné)
```

### Quand regénérer ?

| Événement | Action | Outillage |
|-----------|--------|-----------|
| Modification du FR | 1) `sync.py` régénère `README.csv` (ajoute nouvelles clés, met à jour FR) 2) CI signale drift si CSV pas régénéré | `sync.py` + workflow `i18n-drift.yml` (Phase 2) |
| Première introduction d'une langue | `render.py --lang es` crée `README.es.md` à partir du CSV (cellules FR vides → fallback sur FR) | `render.py` |
| Modification d'une cellule EN | édition manuelle du CSV (puis `render.py` regénère `.en.md`) ou édition directe du `.en.md` puis `sync.py --reverse-en` resynchronise le CSV | les deux scripts |

### Le CSV est-il versionné ?

**Oui.** Justification :

- le CSV est l'artefact interlingua qui permet l'audit (qui a traduit quoi, dans quelle
  langue, avec quelle qualité) ;
- regénérer le CSV à partir du FR **perd les traductions** déjà saisies dans les autres
  colonnes ;
- diff-reviewable : une PR qui modifie `README.csv` est lisible comme une PR de
  traduction ;
- taille négligeable : 50 lignes de prose × 8 langues × 50 séries ≈ 20 000 lignes de CSV,
  < 1 MB.

### Anti-patterns interdits

| Anti-pattern | Pourquoi |
|--------------|----------|
| Régénérer le CSV **depuis** le `.en.md` | inverse le sens canonique ; casse les traductions des autres langues |
| Garder les traductions dans des fichiers `.json` séparés | pas diff-friendly, pas merge-friendly, pas grep-friendly |
| Mettre le CSV dans un submodule Argumentum | c'est un artefact par série, pas global |
| Auto-traduction via LLM en CI sans review humaine | hallucination, faux confiance, qualité médiocre (cf. #5644 Sweety docs précédent) |

## Outillage

### `scripts/i18n/sync.py`

**Rôle** : extraire les cellules markdown du `README.md` FR, mettre à jour le `README.csv`
existant (ajout nouvelles clés, mise à jour FR, préservation colonnes autres langues).

**CLI** :

```bash
python scripts/i18n/sync.py \
    --fr README.md \
    --csv README.csv \
    [--dry-run] [--verbose]
```

**Sortie** :

```
[sync] cross-series/README.md → cross-series/README.csv
  +intro.para2 (NEW)
  ~intro.para1 (FR updated, EN preserved)
  =# <h1> (unchanged)
  ...
  12 keys synced, 1 new, 0 stale, 0 removed.
```

**Algorithme** (≤80 lignes de Python standard) :

1. parseur markdown **maison** minimaliste (h1, h2, paragraphes, listes, tableaux,
   blockquotes, code blocks) — pas de dépendance externe pour rester CPU-only et
   hermétique ;
2. extraction cellules selon conventions de clés ;
3. diff avec le CSV existant ;
4. mise à jour : ajout nouvelles clés (avec EN vide si pas dans EN actuel), mise à jour
   FR (préservation colonnes autres langues), suppression clés absentes du FR
   (avertissement mais préserve avec `STALE:` prefix si demandé).

**Garde-fous** :

- `--dry-run` : imprime le diff sans écrire ;
- warning si une clé EN devient vide (perte de traduction) ;
- warning si le FR contient des **caractères de contrôle** non-ASCII (cf. lesson
  `cjk-post-edit` filter).

### `scripts/i18n/render.py`

**Rôle** : lire le `README.csv`, regénérer les `.en.md` (et futures autres langues) en
respectant la structure markdown d'origine.

**CLI** :

```bash
python scripts/i18n/render.py \
    --csv README.csv \
    --fr README.md \
    --out README.en.md \
    --lang en
    [--lang es --out README.es.md]
    [--dry-run] [--verbose]
```

**Sortie** :

```
[render] cross-series/README.csv → cross-series/README.en.md (lang=en)
  12 cells rendered, 1 fallback (key=intro.para2 → FR), 0 missing.
```

**Algorithme** (≤100 lignes) :

1. lit le CSV en `dict[str, dict[str, str]]` (clé → langue → texte) ;
2. lit le FR pour reconstituer la **structure** markdown (ordre des sections, niveaux de
   titres, présence de tableaux) ;
3. pour chaque cellule FR, substitue par la cellule EN si non-vide, sinon conserve le FR
   (avec marqueur `[fallback:fr]` en commentaire HTML si verbose) ;
4. réassemble le markdown en respectant l'ordre du FR.

**Garde-fous** :

- validation que **toutes** les clés FR ont une colonne dans le CSV (sinon erreur) ;
- validation que **toutes** les lignes CSV ont une clé correspondante dans le FR
  (warning : clé orpheline) ;
- `--diff` : imprime le diff entre le `.en.md` actuel et le nouveau, sans écrire.

## Pilote fonctionnel : `cross-series/`

**Série pilote** : `MyIA.AI.Notebooks/cross-series/` (13 lignes de EN, ~50 lignes de FR,
1 tableau, 1 blockquote, 1 lien). Critères :

- **TRÈS petit** : pilote testable en < 5 secondes ;
- **désynchronisation naturelle** : le EN actuel est un résumé, le FR est détaillé —
  démontre précisément le besoin ;
- **sans risque** : pas critique, pas dans le marathon #4956, pas dans une EPIC majeure ;
- **structure représentative** : a un titre, des paragraphes, un tableau, un blockquote
  — exerce tous les types de cellules.

### Livrables pilote

| Fichier | Type | Lignes |
|---------|------|--------|
| `docs/i18n/CSV-by-series-design.md` | NEW | (ce fichier) |
| `scripts/i18n/sync.py` | NEW | ≤80 |
| `scripts/i18n/render.py` | NEW | ≤100 |
| `scripts/i18n/tests/test_sync_render.py` | NEW | 11+ tests pytest |
| `MyIA.AI.Notebooks/cross-series/i18n/README.csv` | NEW | pilote exemple, ~20 lignes |
| `MyIA.AI.Notebooks/cross-series/i18n/README.en.md` | NEW (regénéré) | pilote, ≥13 lignes |
| `MyIA.AI.Notebooks/cross-series/i18n/sync.log` | NEW | trace du sync pilote |

### Critères d'acceptation du pilote

1. **Round-trip exact** : `sync.py` + `render.py` sur le pilote produisent un `.en.md`
   byte-identique au `.en.md` actuel si on édite uniquement le FR (test
   `test_round_trip_idempotent`) ;
2. **Nouvelle clé** : ajouter une section dans le FR → sync ajoute la clé au CSV →
   render produit un `.en.md` avec la section traduite (EN vide → fallback FR avec
   marqueur) ;
3. **Préservation colonne EN** : modifier une cellule FR existante → sync préserve la
   traduction EN actuelle (test `test_sync_preserves_translations`) ;
4. **CPU 1 cycle** : sync + render sur `cross-series/` < 2 secondes (machine standard) ;
5. **0 dépendance externe** : que `python -c 'import sys; sys.version_info >= (3,10)'` ;
   `argparse` + `csv` + `pathlib` + `re` + `dataclasses` de la stdlib.

## Limites & hors-scope (Phase 2)

| Item | Phase | Justification |
|------|-------|---------------|
| **Workflow GitHub Actions `i18n-drift.yml`** | Phase 2 | nécessite décision user sur politique de merge (drift = warning ou error ?) |
| **Rollout multi-série** (Probas, ML, Lean…) | Phase 2 | nécessite scan préliminaire des 85 `.en.md` existants, désambiguïsation clé-par-clé |
| **8 langues** (ES, DE, IT, PT, JA, ZH, RU) | Phase 2+ | nécessite coordination Argumentum (qui a déjà fait ça pour la taxonomie des sophismes) |
| **Auto-traduction LLM assistée** | Phase 3+ | nécessite décision user sur le provider + budget + politique de review |
| **Moteur de rendu Markdown typé** (CommonMark) | Phase 2 | `sync.py` actuel = parser markdown minimaliste maison ; acceptable pour Phase 1, à remplacer si la complexité augmente |

## Risques identifiés

| Risque | Probabilité | Impact | Mitigation |
|--------|-------------|--------|------------|
| Sync rate des cellules (false positive "drift") | M | M | dry-run obligatoire en premier, audit humain avant commit |
| Round-trip FR→CSV→EN pas byte-identique (encodage, sauts de ligne) | M | F | test_round_trip_idempotent obligatoire, normalisation EOL `LF` |
| Pollution cross-série (un sync écrit dans le mauvais dossier) | F | M | `--fr` + `--csv` obligatoires, validation que le CSV est dans le même dossier que le FR |
| Conflit avec submodule Argumentum si Argumentum a son propre i18n | F | F | Argumentum est dans un submodule séparé ; ce design doc ne s'applique qu'au workspace principal |
| Rollout sans decision user sur les 7 langues cibles | F | M | Phase 1 = FR+EN uniquement ; langues additionnelles = Phase 2 avec decision user explicite |

## Liens internes

- EPIC #1650 — traduction multilingue (Phase 0.5 = préservation `.en.md`)
- EPIC #4980 — Lean i18n (convention FR canonique + `.en.md` mirror, pilote #4998 MERGED)
- `.claude/rules/readme-french-first.md` — règle HARD doc primaire FR
- `docs/harness/reference/procedures-recurrentes.md` §workflow PR (10 étapes)
- `docs/anti-regression-detail.md` — protocole suppression de code (anti-régression)

---

*Design doc rédigé 2026-07-07 par `myia-po-2025:CoursIA-2` (c.292), MSG ai-01
msg-20260707T170624-wmu0m5. Phase 2 = decision user sur CI drift-flag + rollout multi-série.*
