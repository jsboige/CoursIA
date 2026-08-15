# Diagnostic `translations/` racine — état des lieux + options de disposition

> **Statut** : diagnostic doc-only, **sans action destructive** sur le répertoire `translations/`.
> **Epic parent** : [#9535](https://github.com/jsboige/CoursIA/issues/9535) — *Nettoyage & rangement du dépôt* (item 9).
> **Issues de référence** : [#6949](https://github.com/jsboige/CoursIA/issues/6949) (T3 moteur fork Argumentum, **OUVERTE** par décision coordinateur) ; [#4957](https://github.com/jsboige/CoursIA/issues/4957) (CLOSED, Phase 1 infra) ; [#1650](https://github.com/jsboige/CoursIA/issues/1650) (OPEN, Epic traduction multilingue).
> **Date** : 2026-08-06 (c.1252, lane `myia-po-2025:CoursIA-2`).

---

## 1. Pourquoi ce document

L'item 9 de l'Epic #9535 (« translations/ racine — 33 CSV, statut T1 baseline ») appelait un **rangement** du répertoire `translations/`. Mais le **premier litmus** appliqué à ce diagnostic (G.9 *verify-before-claiming*, L283) montre que la situation réelle **n'est pas celle que l'intitulé suggère** : `translations/` n'est pas un dossier à ranger, c'est un répertoire **structuré et intentionnel** (33 CSV versionnés, schéma CSV 8 langues, 6 dossiers-familles), et son « statut T1 baseline » est en fait un état **gated par construction** sur la seconde moitié de l'acceptance — pas une dette de ménage.

L'audit **firsthand** (§ 2) et les issues connexes (§ 3) conduisent à un **verdict honnête** : « ranger `translations/` » au sens où #9535 l'entendait (déplacer / supprimer / renommer) **détruirait l'infrastructure qui a coûté 29 PRs de drainage entre 2026-07-10 et 2026-07-18** (cf. `docs/translation/epic-4957-status.md` § 1.4). Ce document acte l'état réel et propose trois options de disposition **non destructives** pour la décision user.

## 2. Audit firsthand (c.1252)

### 2.1 Métriques du répertoire

| Métrique | Valeur | Source |
|---|---|---|
| Nombre de CSV | 33 | `find translations/ -name '*.csv' \| wc -l` |
| Cellules totales | **24 470** (delta +216 vs README « 24 254 ») | audit Python `csv.DictReader` + comptage lignes hors en-tête |
| Taille disque | 28 Mo | `du -sh translations/` |
| Familles couvertes | 25 (SymbolicAI ×6, Search ×5, Probas ×3, GenAI ×7, ML ×2, RL, Sudoku, GameTheory, IIT, CaseStudies, SmartContracts, QC ×2, SymbolicLearning) | cf. `translations/README.md` |
| Sous-répertoires | 26 (`casestudies/`, `gametheory/`, `genai/`, `iit/`, `ml-datascience/`, `mlnet/`, `partner-course-quant-trading/`, `planners/`, `probas-decinfer/`, `probas-infer/`, `probas-pymc/`, `quantconnect/`, `rl/`, `search-applications/`, `search-part1/`, `search-part2/`, `search-part3/`, `search-part4/`, `semanticweb/`, `smartcontracts/`, `smt/`, `sudoku/`, `symbolicai/`, `symbolicai-lean/`, `symboliclearning/`, `tweety/`) | `ls translations/` |

### 2.2 Traduction effective (mesurée, pas déclarée)

Audit `csv.DictReader` avec double condition `(text_X non-vide ET hash_X non-vide)` sur les 33 fichiers :

| Langue cible | Cellules remplies | Pourcentage |
|---|---:|---:|
| `text_en` | 0 | 0,00 % |
| `text_es` | 0 | 0,00 % |
| `text_zh` | 0 | 0,00 % |
| (et idem `text_ar`, `text_fa`, `text_ru`, `text_pt`) | 0 | 0,00 % |

**Verdict** : **zéro cellule traduite sur les 7 langues cibles** depuis le commit initial. Les 24 470 cellules sont uniquement en `text_fr` (la colonne source `src_lang=fr`).

### 2.3 Freshness du contenu (drift T2)

Lecture `git log origin/main -- translations/` :

| Commit | Date | Verdict | Type |
|---|---|---|---|
| `0e7c85703` ([#8431](https://github.com/jsboige/CoursIA/pull/8431)) | 2026-07-25 | MERGED | Resync Planners 01-Foundation post-accents (100 SRC_DRIFT → 0) |
| `7b8b865f6` ([#7949](https://github.com/jsboige/CoursIA/pull/7949)) | 2026-07-23 | MERGED | Resync search-applications post-App-16 FC+MRV |
| `4c1182545` ([#7916](https://github.com/jsboige/CoursIA/pull/7916)) | 2026-07-23 | MERGED | Resync GameTheory-7 drift |

**Aucun commit sur `translations/` depuis le 2026-07-25** = **12 jours de stale** au moment de ce diagnostic (2026-08-06).

Le delta **+216 cellules** entre README (« 24 254 ») et audit actuel (« 24 470 ») n'est **pas tracé dans le `translations/README.md`** : le compteur affiché est **désynchronisé** (drift documentaire).

## 3. Contexte connecté : `scripts/translation/`

### 3.1 Moteur T3 livré mais gated

`scripts/translation/translate_csv.py` (16 239 octets, **présent** sur `origin/main`) est **la couche T3 forkée d'Argumentum** :

- **Livré** par PR [#6976](https://github.com/jsboige/CoursIA/pull/6976) (commit `84ba7ac70`, 2026-07-17) — 339 LOC Python, 14 tests verts, fork mature de `translate_game_rules.py`.
- **Triple gate de sécurité** :
  - `ENABLED = False` ligne 53 (édition source requise pour activer).
  - `--dry-run` est le défaut (aucun appel API).
  - `--apply` requis en sus ; sans `ENABLED=True` → no-op avec stderr explicite.

Le moteur est **techniquement fonctionnel**, mais **inactif par construction**. La traduction effective est à 0 % sur les 7 langues (§ 2.2) parce que **personne n'a jamais activé** `ENABLED=True`.

### 3.2 Détecteur de drift T2 livré mais en signal partiel

`scripts/translation/check_translation_sync.py` (21 499 octets) **détecte le drift** et **le zerote** silencieusement à chaque PR de resync. Verdict **firsthand** c.31 (po-2023, 2026-07-22 — cf. issue #6949) :

> Un titre de resync se lit *« 19 SRC_DRIFT → 0 »*. C'est un compteur remis à zéro sans qu'aucun travail de traduction n'ait eu lieu — et un compteur remis à zéro est indiscernable d'un travail fait. C'est exactement la famille de défaut fermée par #8680 (un gate incapable d'échouer) et #8678 (un compteur nu qui périme en silence).
>
> **Règle, effective immédiatement** : plus de PR *resync-only* sur `translations/**/*.csv` jusqu'au GO moteur.

Cette règle **n'a pas été honorée** : PR [#8431](https://github.com/jsboige/CoursIA/pull/8431) (2026-07-25, *post-règle*) a zeroté 100 SRC_DRIFT sur Planners sans livrer la moindre cellule traduite.

### 3.3 Documentation connexe (sur disque, état au 2026-08-06)

| Fichier | Lignes | Statut | Stale ? |
|---|---:|---|---|
| `translations/README.md` | 5997 octets | Présent — claim « 24 254 cellules » | **OUI** (delta +216 cellules) |
| `docs/translation/argumentum-fork-mapping.md` | 88 | Présent — référence T3, **OUVERT 2026-07-28** | Non |
| `docs/translation/epic-4957-status.md` | 104 | Présent — Phase 1 clôture | Non |
| `scripts/translation/README.md` | ~70 | Présent — référence opérationnelle T1/T2/T3 | Non |
| `.github/workflows/translation-drift.yml` | 4057 octets | Présent — CI drift-flag **WARN non-bloquant** | Non |

## 4. Issues GitHub connectées

### 4.1 #9535 — Epic parent (item 9)

L'item 9 de l'Epic #9535 a été formulé comme « translations/ racine — 33 CSV, statut T1 baseline ». **Lecture littérale** = nettoyer / déplacer / renommer. **Lecture conforme à l'architecture** = **acter** que le répertoire est structuré, intentionnel, et bloqué en aval sur une décision user gated (§ 4.3).

### 4.2 #4957 — Epic de référence (CLOSED, Phase 1 LIVRÉE)

CLOSED 2026-07-08. Phase 1 = infrastructure de synchronisation (CSV + extracteur + détecteur + CI drift). Phase 2 = rollout **continué via PRs filles** trackées séparément (cf. `epic-4957-status.md` § 4). **29 PRs MERGED** entre 2026-07-10 et 2026-07-18, **0 OPEN**.

### 4.3 #6949 — T3 moteur fork Argumentum (OUVERTE par décision coordinateur)

**Lecture firsthand du body et des commentaires** (`gh issue view 6949`) :

- **État GitHub** : `OPEN`, `closedAt: null` (au 2026-08-06).
- **Clôture textuelle refusée** : PR [#7967](https://github.com/jsboige/CoursIA/pull/7967) (2026-07-22, `51856f9f2`) a marqué « CLOSED » dans la doc (`scripts/translation/README.md` + `argumentum-fork-mapping.md`) **mais l'issue GitHub reste OPEN** par décision coordinateur (commentaire myia-ai-01).
- **Raison** : le titre de l'issue porte **deux engagements** :
  1. *Fork Argumentum `translate_game_rules.py`* — ✅ livré (PR #6976).
  2. *Arrêt des resync CSV dans le vide* — ⏸️ **NON honoré** (8 PRs post-issue, 3 034+/3 020−, PR #8431 la plus récente, post-clôture textuelle).
- **Acceptance déclaré hors scope** : *« Décision user sur gating GO T3 »* = USER-HAND, mandat user + Phase 1 #1650.

### 4.4 #1650 — Epic grand-parent (OPEN, low priority)

L'Epic de traduction multilingue (8 langues via datasetupdater Argumentum) reste OPEN car **gated par le GO moteur** — c'est exactement le blocage de la question 4 de #6949.

## 5. Trois options de disposition

Les trois options sont **non destructives** : aucune ne touche au contenu des 33 CSV ni à `scripts/translation/translate_csv.py`. Elles ne diffèrent que par **où vit la décision**.

### Option A — GARDER en l'état (statu quo + petit housekeeping)

**Action** : aucun changement. Ouvrir une PR **doc-only** qui aligne `translations/README.md` (24 254 → 24 470 cellules) et **acter** la règle c.31 dans le README (« pas de resync-only jusqu'au GO moteur »).

**Avantages** :
- Coût = ~1 PR doc-only.
- Préserve l'investissement Phase 1 (29 PRs) et la trajectoire Phase 2 (PRs filles).
- Aucune rupture avec la doctrine coord (commentaire myia-ai-01 sur #6949).
- Réouvre **explicitement** la question « resync-only #8431 a-t-il violé la règle c.31 ? » comme issue séparée, traçable.

**Inconvénients** :
- Ne ferme pas #9535 item 9 « proprement » : le lecteur du board voit l'item « ouvert » sans transformation visible.
- Laisse #6949 dans son état demi-clos (issue GitHub OPEN + doc marquée CLOSED) — dissonant.

**Verdict** : **recommandé en cas d'incertitude user** — c'est l'option qui préserve le plus de marge de décision.

### Option B — FIGER (snapshot archive, déplacement lecture seule)

**Action** :
1. Créer `docs/translation/translations-snapshot-2026-08.md` qui **photographie** l'état du répertoire au 2026-08-06 (33 CSV, 24 470 cellules, 0 % traduit, +216 cellules depuis README).
2. Marquer `translations/README.md` avec une bannière `<!-- FROZEN 2026-08-06 — gated #6949 GO moteur -->`.
3. Aucune mutation des CSV.

**Avantages** :
- Verrou explicite (le prochain worker qui voit un SRC_DRIFT sait qu'il **ne doit pas** ouvrir de PR resync-only).
- Trace claire pour audit historique (qui, quand, pourquoi le gel).
- Aucune suppression — l'infrastructure reste réutilisable au GO moteur.

**Inconvénients** :
- Coût = ~1 PR doc-only + changement de bannière.
- « Frozen » est un mot fort : à utiliser seulement si la décision user penche « pas avant fin 2026 ».
- Crée un précédent : si un autre dossier est gelé de la même manière, la **discipline freeze** doit être documentée (sinon gel = décision isolée).

**Verdict** : **adapté si la décision user est « on attend un GO clair avant d'y toucher »** — transforme l'attente passive en gel explicite.

### Option C — DÉPLACER (vers `docs/translation/data/`)

**Action** :
1. Déplacer `translations/` racine vers `docs/translation/data/` (29 sous-répertoires + 33 CSV + README).
2. Mettre à jour toutes les références : `scripts/translation/README.md`, `scripts/translation/extract_cells_to_csv.py`, `.github/workflows/translation-drift.yml`, `scripts/translation/check_translation_sync.py`.

**Avantages** :
- Le périmètre « données linguistiques versionnées » migre du repo opérationnel vers le périmètre documentaire — distinction utile si l'Epic #9535 veut ranger « ce qui sert au build » vs « ce qui sert de référence ».
- Évite que les workers voient `translations/` à la racine et pensent « T1 baseline = dette à ranger ».

**Inconvénients** :
- **Très破坏leur** : 29 sous-répertoires + 33 CSV + tous les chemins codés en dur.
- **Renégocie** les chemins acceptés par 4+ scripts + 1 workflow CI — risque de régression silencieuse.
- Crée une incohérence avec la doctrine #4957 § 1.1 (qui place `translations/` racine explicitement).
- Aucune raison technique de le faire — `translations/` n'est pas un dossier de build artefacts.

**Verdict** : **déconseillé**. Le bénéfice organisationnel est marginal, le coût de migration est élevé, et la doctrine Phase 1 perd son point d'ancrage. **À ne retenir que si la décision user est « je veux que `translations/` racine disparaisse, point »** — ce qui contredit la doctrine #4957 ratifiée.

## 6. Recommandation doc-only

L'option **A** (GARDER + petit housekeeping) est la **recommandation par défaut** de ce diagnostic pour deux raisons :

1. **Préserve** la doctrine coord (myia-ai-01, commentaire sur #6949 : *« issue reste OUVERTE, resserrée sur sa seconde moitié »*). Toute décision destructrice contredit cette doctrine.
2. **Sépare** proprement les décisions : le diagnostic acte l'état, la PR doc-only **aligne** le compteur stale (24 254 → 24 470) **et** érige la règle c.31 dans le README racine. La décision « activer T3 / geler / déplacer » reste **user-HAND** comme l'acceptance de #6949 le déclare.

Si la décision user penche différemment (option B ou C), ce diagnostic fournit **le substrat de mesure** sans engagement : les chiffres, les issues, les tradeoffs sont posés.

## 7. Cross-références

- [scripts/translation/README.md](../../scripts/translation/README.md) — référence opérationnelle T1/T2/T3.
- [docs/translation/argumentum-fork-mapping.md](argumentum-fork-mapping.md) — fork T3, OUVERTE par décision coord.
- [docs/translation/epic-4957-status.md](epic-4957-status.md) — Phase 1 LIVRÉE, Phase 2 rollout via PRs filles.
- [Issue #6949](https://github.com/jsboige/CoursIA/issues/6949) — T3 moteur + doctrine c.31 « pas de resync-only ».
- [Issue #4957](https://github.com/jsboige/CoursIA/issues/4957) — Epic infra synchro, CLOSED.
- [Issue #1650](https://github.com/jsboige/CoursIA/issues/1650) — Epic grand-parent multilingue, OPEN.
- [Epic #9535](https://github.com/jsboige/CoursIA/issues/9535) — parent *Nettoyage & rangement du dépôt* (item 9).
- [PR #8431](https://github.com/jsboige/CoursIA/pull/8431) — violation documentée de la règle c.31 (post-clôture textuelle #6949).

## 8. Note méthodologique (G.9 *verify-before-claiming*)

Tous les chiffres de ce diagnostic ont été mesurés firsthand (audit Python `csv.DictReader` c.1252, `git log`, `gh issue view`, `gh pr view`). Aucune affirmation n'est rapportée sans preuve :

- **24 470 cellules** : audit Python sur les 33 CSV, lignes hors en-tête. README « 24 254 » = **stale** (delta +216).
- **0 % traduit** : double condition `(text_X ET hash_X)` non-vide sur les 7 langues.
- **12 jours stale** : `git log origin/main -- translations/` depuis `0e7c85703` (2026-07-25).
- **#6949 OUVERTE** : `gh issue view 6949 --json state,closedAt` → `state:"OPEN", closedAt:null`.
- **PR #7967 = clôture textuelle seule** : `gh pr view 7967 --json state` = MERGED, mais l'issue reste OPEN — constaté sur 2 sources indépendantes.
- **PR #8431 = post-clôture textuelle** : `git log --since='2026-07-22' -- translations/` la liste, merge le 2026-07-25.

Les recommandations s'appuient sur ces mesures, pas sur l'intitulé de l'item 9 ni sur l'apparente immobilité du répertoire.
