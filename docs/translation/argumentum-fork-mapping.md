# Mapping de fork Argumentum → CoursIA (moteur T3)

> **Statut** : référence pérenne pour la couche T3 (moteur de traduction).
> Issue [#6949](https://github.com/jsboige/CoursIA/issues/6949) — **CLOSED 2026-07-22 (c.757)** : livrable court-terme expédié. PRs du scope original : #6980 (ce doc, `fb9bff827`) + #6976 (fork code T3, `84ba7ac70`).
> Fork code : PR #6976 (`scripts/translation/translate_csv.py`).
> Travaux d'harmonisation post-issue : #7615 (env-hermetic provider-keys), #7714 (WRONG_SCRIPT, c.734), #7731 (FR_CONTAM, c.738).
> Épics parents : [#4957](https://github.com/jsboige/CoursIA/issues/4957) (infra synchro), [#1650](https://github.com/jsboige/CoursIA/issues/1650) (traduction multilingue).
> **Hors scope gated** : activation T3 (`ENABLED=True`) — mandat user + Phase 1 [#1650](https://github.com/jsboige/CoursIA/issues/1650) ; T4 re-import CSV → notebooks — post-activation.

## 1. Pourquoi forker Argumentum

Le dépôt CoursIA consomme, depuis mi-2026, un flux de PR dites « resync CSV »
(`extract_cells_to_csv.py --update` + `check_translation_sync.py`) qui drainent
les `SRC_DRIFT` entre les notebooks source et le CSV pivot `fr`. **Ces PR ne
produisent aucune cellule traduite** en 7 langues cibles : la couche T3 (le
vrai moteur de traduction) était gated ([#1650](https://github.com/jsboige/CoursIA/issues/1650) Phase 1), donc les resyncs
étaient du bruit de fond — 1-2 h d'agent + 1 merge de coordinator chacune pour
zéro valeur linguistique.

Le submodule `ArgumentumGames/Argumentum` (pin `7e72f3e5d`, v0.9.0) contient un
**système de traduction multilingue mûr et fonctionnel** (29 outils Python +
moteur .NET 9 `DatasetUpdater`). Plutôt que de réinventer un moteur, on **fork
les patterns identifiés** côté CoursIA, en s'appuyant sur l'exploration du
2026-07-17.

## 2. Ce qu'on fork, ce qu'on laisse

| Élément Argumentum | Statut CoursIA | Décision |
|---|---|---|
| `tools/dnn_i18n/translate_game_rules.py` (193 LOC, gpt-5.5) | Fork → `scripts/translation/translate_csv.py` (#6976) | **Forked** — script Python pur, zéro dépendance Argumentum-specific, déjà 80 % du travail T3 |
| `multilingual-drift-audit.py` (453 LOC, 5 classes drift) | `check_translation_sync.py` (T2, 4 verdicts) | **Laissé** — T2 CoursIA est livré ; harmonisation des 5 classes = travail futur optionnel |
| Moteur .NET `DatasetUpdater/*.cs` (gpt-5.4-mini, function calling) | — | **Laissé** — trop couplé au schéma 2sxc ; le fork Python `urllib` suffit et reste auditable |
| `.keys/openai-key.txt` (clés sur disque) | `os.getenv("OPENAI_API_KEY")` | **Refusé** — violerait [secrets-hygiene.md](../../.claude/rules/secrets-hygiene.md) règle 1-3 (clés env-only, jamais de littéral/fichier) |
| Format entrée 2sxc JSON (`EntityID`/`StaticName`/`Value`) | CSV RFC 4180 (`notebook`/`cell_id`/`text_fr`) | **Adapté** — voir §3 |

## 3. Mapping de schéma (Argumentum → CoursIA)

| Aspect | Argumentum | CoursIA T1/T2 (livré) | CoursIA T3 (fork #6976) |
|---|---|---|---|
| Identifiant de cellule | `EntityID` + `StaticName` | `notebook` + `cell_id` (composite) | Idem |
| Source FR | `Value` (2sxc) | `text_fr` (FR = source canonique) | Lit `text_fr` |
| 7 langues cibles | `en, ru, pt, es, ar, fa, zh` | `text_<lang>` + `hash_<lang>` | **Identique** — mapping exhaustif confirmé |
| Cache / resume | JSON output reuse | — | `text_<lang>` non-vide = déjà traduit (skip) |
| Sortie | re-import JSON 2sxc | — | Réécrit le CSV (`text_<lang>` + `hash_<lang>`) |
| Hash drift | — | `cell_hash = sha256(normalize)[:16]` | **Réutilisé tel quel** (cohérence T2) |

## 4. Lessons apprises d'Argumentum (intégrées au fork)

1. **gpt-5.5 specifics** (verified #499 pilot, 2026-06-16) : pas de `temperature`
   (HTTP 400 sur reasoning models) ; `max_completion_tokens` (pas `max_tokens`),
   floor 1500 / cap 8000, sized au champ ; `reasoning_effort=low`. Fork direct.
2. **Préservation structurelle** : Argumentum préserve les entités HTML (`&amp;`
   `&nbsp;`). CoursIA préserve **fences de code**, **inline code**, **math**
   (`$...$`), **structure Markdown** (headings, listes, liens). Le code lui-même
   n'est jamais traduit.
3. **Script natif dans la langue cible** : Cyrillic (ru), CJK (zh), arabe (ar/fa).
4. **Fallback provider** : OpenAI direct en primaire, OpenRouter en fallback
   401/429. Conservé dans le fork.
5. **Gating `Enabled=false`** jusqu'à GO user (Argumentum `docs/dnn-localization/457-document-tier-translation-workflow.md` §3, submodule `ArgumentumGames/Argumentum`) : le fork
   ajoute un double gate `ENABLED=False` (module) + `--dry-run` (défaut CLI).

## 5. Séquencement T0 → T3

```text
T0  (manuel)      notebooks source FR = source canonique
T1  extract       extract_cells_to_csv.py  →  CSV pivot (text_fr + hash_fr)         [livré]
T2  drift-check   check_translation_sync.py → verdicts IN_SYNC / SRC_DRIFT / ...    [livré, CI non-bloquant]
T3  translate     translate_csv.py (#6976)  →  text_<lang> + hash_<lang>            [starter livré, GATED]
T4  re-import     patcher xxx_<lang>.ipynb depuis le CSV + Papermill re-exec         [à venir, #1650]
```

**Activation T3** (moyen terme, après GO user) :

1. Éditer `ENABLED = True` dans `translate_csv.py`.
2. Définir `OPENAI_API_KEY` (env, jamais de littéral).
3. Premier run sur 1 CSV test : `python translate_csv.py --csv <x.csv> --smoke --apply`.
4. Audit post-run : `check_translation_sync.py <x.csv>` → `TRAD_DRIFT` doit tomber à 0.

## 6. Voir aussi

- [Issue #6949](https://github.com/jsboige/CoursIA/issues/6949) — motivation, scope (PR #1 doc + PR #2 code), arrêt des resync vides. **CLOSED 2026-07-22** (cf. bloc Statut ci-dessus).
- [Issue #4957](https://github.com/jsboige/CoursIA/issues/4957) — design de l'infra (schéma CSV, sémantique drift).
- [Epic #1650](https://github.com/jsboige/CoursIA/issues/1650) — traduction multilingue du dépôt.
- PR #6976 — fork code (`scripts/translation/translate_csv.py` + 14 tests).
- PR #6980 — ce document + README T3 status.
- PRs d'harmonisation (post-issue, hors scope original) : #7615, #7714, #7731.
- [`scripts/translation/README.md`](../../scripts/translation/README.md) — workflow T1→T2→T3 + bloc `## Issue #6949 — Status de clôture` (c.757).
- Argumentum source (submodule pin `7e72f3e5d`) : `tools/dnn_i18n/translate_game_rules.py`.
