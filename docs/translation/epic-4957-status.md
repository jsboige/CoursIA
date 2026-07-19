# Epic #4957 — État de clôture (Phase 1 infrastructure de synchronisation traduction)

> **Statut** : Phase 1 LIVRÉE. Phase 2 (rollout) en cours via PRs filles trackées séparément.
> **Issue** : [#4957](https://github.com/jsboige/CoursIA/issues/4957) — infra de synchronisation traduction.
> **Epic parent** : [#1650](https://github.com/jsboige/CoursIA/issues/1650) — traduction multilingue du dépôt.
> **Fermeture** : ce document sert de **référence pérenne** (cf. [harness-hygiene.md](../../.claude/rules/harness-hygiene.md)) pour quiconque rouvre l'Epic ou suit la continuation Phase 2. L'Epic est techniquement close au sens des acceptance criteria initiaux ; le périmètre Lean FR/EN et la couche T3 sont **explicitement hors-scope** par décision user ratifiée.

---

## 1. Périmètre LIVRÉ (Phase 1)

### 1.1 Infrastructure (scripts + CI)

| Composant | Chemin | Statut |
|---|---|---|
| Extracteur T1 (cellules → CSV) | `scripts/translation/extract_cells_to_csv.py` (16 959 octets) | Livré, déterministe byte-identique |
| Détecteur de drift T2 | `scripts/translation/check_translation_sync.py` (9 353 octets) | Livré, mode CI `--check` non-bloquant |
| Moteur T3 (fork Argumentum) | `scripts/translation/translate_csv.py` (16 239 octets) | Starter livré ([#6976](https://github.com/jsboige/CoursIA/pull/6976)), `ENABLED=False` + `--dry-run` défaut (gated #6949) |
| Workflow CI drift | `.github/workflows/translation-drift.yml` (4 057 octets) | Livré, WARN non-bloquant (commentaire user 2026-07-08) |
| Doc moteur T3 | `docs/translation/argumentum-fork-mapping.md` (5 724 octets) | Livré |
| README scripts | `scripts/translation/README.md` (70 lignes) | Livré |

### 1.2 Schéma CSV ratifié (#4957 §1)

`translations/<famille>/<série>.csv` — une ligne par cellule de notebook (cf. `scripts/translation/README.md` § Schéma CSV pour la spécification complète) :

```
notebook, cell_id, cell_type, src_lang, src_hash,
text_fr, text_en, text_es, text_ar, text_fa, text_zh, text_ru, text_pt,
hash_fr, hash_en, hash_es, hash_ar, hash_fa, hash_zh, hash_ru, hash_pt
```

`src_hash` = sha256(16) du texte normalisé (rstrip/ligne + strip newline terminal → pas de faux-drift cosmétique). Le couple `(src_hash, hash_<lang>)` détecte le drift dans les **deux sens**.

### 1.3 Verdicts de drift (T2)

| Verdict | Sens |
|---|---|
| `IN_SYNC` | `src_hash` et `hash_<lang>` matchent les notebooks courants |
| `SRC_DRIFT` | le notebook source a bougé depuis la dernière synchro → retraduction requise |
| `TRAD_DRIFT` | une traduction a été éditée à la main sans répercussion sur le CSV |
| `MISSING_LANG` | le notebook `xxx_<lang>.ipynb` n'existe plus alors qu'un hash était déposé |
| `ORPHAN_ROW` | la ligne CSV référence un `cell_id` absent du notebook source (cellule supprimée) |

### 1.4 PRs MERGED (29 entre 2026-07-10 et 2026-07-18)

Chronologie de drainage (extrait, cf. `gh pr list --search "4957" --state all` pour la liste exhaustive) :

| Lot | PRs | Type |
|---|---|---|
| Seeds Phase 2 initiaux | #5892, #5937 | Seed CSV RL (17 notebooks) + CaseStudies |
| Resyncs c.458-c.471 | #6527, #6555, #6598, #6624, #6638, #6646, #6660, #6679, #6708, #6713, #6730+ | Drift-resync multi-familles |
| Seeds Phase 0.5 baseline | #6754, #6756, #6769, #6770, #6777, #6778, #6783, #6784, #6833, #6841, #6858, #6862 | 12 familles (SemanticWeb, Tweety, GenAI ×6, ML, SymbolicAI/Lean) |
| Resyncs c.583-c.601 | #6878, #6939, #6943, #6945, #6947, #6969, #7140, #7164, #7194, #7207 | Drift-resync + consolidation GenAI sous `translations/genai/` (Option A) |
| Batch forensic pre-merge | #5801 (CLOSED superseded) | Phase 2 Probas/Infer, remplacé par #6533 + #6708 |

**Verdict pool** : 29 MERGED + 1 CLOSED superseded, **0 OPEN**.

---

## 2. Arbitrages user ratifiés (session 2026-07-08)

Ces décisions sont **structurantes** et s'imposent à toute continuation :

1. **CI drift-flag = WARN** (non-bloquant d'abord) ; durcissement `error` une fois le corpus stabilisé. Cf. `scripts/translation/check_translation_sync.py --check` (exit 0 même si drift).
2. **Langues = FR+EN d'abord** ; les 6 autres (ES/DE/IT/PT/JA/ZH/RU) une fois la parité EN↔FR atteinte. → colonnes CSV `key,fr,en` **maintenues** (rétro-compatible si ajout futur).
3. **Rollout périmètre** = sous-ensemble priorisé (arbitrage coordinateur) — pas les ~60 séries d'un coup. Priorité : séries à `README.md` FR + `.en.md` désynchronisé existant (les 85 `.en.md` actuels sont souvent des résumés ≠ 1:1) → resync d'abord celles-là, en commençant par `cross-series/` (pilote #5657) + séries à forte visibilité (ML, GenAI, ICT).
4. **Moteur auto-trad** = LLM direct (Mistral/GLM/Claude) pour les propositions de resync ; le moteur Argumentum scripté est gated #1271, on ne l'attend pas. L'humain valide les propositions ; le CSV FR reste source de vérité.

**Clarification user 2026-07-02** (commentaire #4957) : la question FR/EN laissée ouverte initialement **ne portait pas sur les READMEs** (qui suivent tous [readme-french-first.md](../../.claude/rules/readme-french-first.md) / #1650), mais sur **les fichiers `.lean` eux-mêmes**. Cette question est **trackée dans [#4980](https://github.com/jsboige/CoursIA/issues/4980)** (Lean i18n : inventaire FR/EN par lake + convention de traduction) et **explicitement hors-scope pour #4957**.

---

## 3. Dépendances externes (hors-scope explicite)

| Tracker | Périmètre | Pourquoi hors-scope #4957 |
|---|---|---|
| [#4980](https://github.com/jsboige/CoursIA/issues/4980) | Lean FR/EN docstrings/commentaires | Décision user 2026-07-02 — relégué à un track dédié (po-2026 territory) |
| [#6949](https://github.com/jsboige/CoursIA/issues/6949) | T3 moteur fork Argumentum | Gated par activation moteur (ENABLED=False + dry-run par défaut) ; prochaine itération = suivi dédié |
| [#1650](https://github.com/jsboige/CoursIA/issues/1650) | Phase 2+ rollout (multilingue général) | #4957 = infrastructure de synchro uniquement ; le rollout = PRs filles trackées séparément |
| #1271 (gated) | Moteur Argumentum scripté générique | Argumentum = fallback ; le cours = LLM direct par user-decision 2026-07-08 |

---

## 4. Continuité Phase 2 (PRs de seed/résync trackées hors #4957)

La Phase 2 (rollout sous-ensemble priorisé, FR+EN first) **continue via PRs séparées** qui ne ferment PAS #4957 (périmètre différent — production de traductions plutôt qu'infrastructure). Chaque PR fille documente son périmètre dans son propre body.

**Convention de continuation** :
- PRs de seed CSV : `feat(translation,<famille>): seed CSV <série> (Phase 2 #4957 seed)`
- PRs de resync drift : `chore(translation,#4957): resync <famille> CSV drift (N SRC_DRIFT → 0)`
- Body doit référencer cet Epic pour traçabilité mais **PAS utiliser `Closes #4957`** (l'Epic reste close).

---

## 5. Voir aussi

- [scripts/translation/README.md](../../scripts/translation/README.md) — référence opérationnelle des 3 couches T1/T2/T3
- [docs/translation/argumentum-fork-mapping.md](argumentum-fork-mapping.md) — mapping fork Argumentum → CoursIA (T3)
- [Issue #4957](https://github.com/jsboige/CoursIA/issues/4957) — design de l'infrastructure
- [Epic #1650](https://github.com/jsboige/CoursIA/issues/1650) — traduction multilingue du dépôt (parent)
- [Issue #4980](https://github.com/jsboige/CoursIA/issues/4980) — Lean i18n (FR/EN docstrings, sister track)
- [Issue #6949](https://github.com/jsboige/CoursIA/issues/6949) — T3 moteur fork Argumentum (gated)
- [.github/workflows/translation-drift.yml](../../.github/workflows/translation-drift.yml) — CI drift-flag WARN
