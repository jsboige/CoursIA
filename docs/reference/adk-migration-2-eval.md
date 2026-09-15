# Audit migration ADK 2.0 — `google-adk==2.8.0` sur Track2-GoogleADK

**Issue :** #14498
**Date :** 2026-09-13
**Lane :** myia-po-2027:CoursIA-2
**Verdict :** NO MIGRATION IMMEDIATE — chaîne 2.8.0 safe, bump à 2.9.0 optionnel post umbrella #13925.

## TL;DR

| Question | Verdict |
|---|---|
| Relation `pypi google-adk` ↔ `adk.dev/2.0` | **Même lignée.** `adk.dev/2.0` est la doc officielle de la release inaugurale 2.x. |
| Migrer maintenant ou finir umbrella #13925 ? | **Finir l'umbrella d'abord.** Chaîne 2.8.0 stable, 2.9.0 n'apporte rien d'utilisé. |
| Impact sur Labs 8/9 ? | **Aucun mesuré** — patterns publics stables 1.x → 2.9.0. À vérifier post-bump. |

## 1. Relation pypi `google-adk` ↔ `adk.dev/2.0`

| Source | Date | Information |
|---|---|---|
| [pypi.org/project/google-adk](https://pypi.org/project/google-adk/) | 2026-09-10 | Latest = `2.9.0`. `2.0.0` GA = 2026-05-19. **Distinct major line 2.x.** |
| [adk.dev/2.0/](https://adk.dev/2.0/) | 2026-05-19 | Python 2.0.0 GA 2026-05-19, Go 2026-06-30, TypeScript 2026-08-21. |
| Changelog upstream | 2026-09-10 | 2.9.0 = 9ᵉ release incrémentale sur la lignée 2.x. |

**Conclusion** : `adk.dev/2.0` est la documentation de la release inaugurale 2.x (= pypi `google-adk==2.0.0`), pas une release séparée. `google-adk==2.8.0` est sur la même lignée. **Pas de rebrand à faire**.

## 2. Breaking changes entre 2.0.0 et 2.9.0 (changelog upstream)

| Version | Date | Breaking | Impact `utils/adk_runtime.py` |
|---|---|---|---|
| 2.6.0 | 2026-07-29 | Artifacts namespace par app | **Aucun** — runtime n'utilise pas d'artifacts. |
| 2.9.0 | 2026-09-10 | `InMemorySessionService` lève `SessionNotFoundError` sur session inconnue | **Risque modéré** — à surveiller si session purgée entre 2 appels. |
| 2.9.0 | 2026-09-10 | `before_tool_callback` déplacé per-tool | **Aucun** — runtime ne définit aucun callback. |
| 2.9.0 | 2026-09-10 | Workflow node resumption rerun failed | **Aucun** — runtime n'utilise pas Workflow Graph. |
| 2.9.0 | 2026-09-10 | GCS tool local paths confined to `local_file_root` | **Aucun** — runtime ne configure pas GCS tool. |

**Aucun breaking entre 2.0.0 → 2.8.0** sur les patterns consommés par `utils/adk_runtime.py`.

## 3. Patterns utilisés par `utils/adk_runtime.py` (mesuré)

Énumération exhaustive (Tell c.1031-L1 ★ NEW) — fichier `MyIA.AI.Notebooks/ML/DataScienceWithAgents/Track2-GoogleADK/utils/adk_runtime.py` (355 LOC) :

| Pattern ADK 2.x | Usage | Sensibilité |
|---|---|---|
| `google.adk.agents.Agent` | `build_data_agent()` | Aucun — API publique stable. |
| `google.adk.models.lite_llm.LiteLlm` | instantiation provider | Aucun. |
| `google.adk.runners.Runner` | `Runner(...)` | Aucun. |
| `google.adk.sessions.InMemorySessionService` | `InMemorySessionService()` | **Modéré 2.9.0** — `SessionNotFoundError`. |
| `runner.run_async(...)` | async iterator d'events | Aucun. |
| `event.author`, `event.usage_metadata`, `event.get_function_calls()`, `event.get_function_responses()`, `event.error_code`, `event.error_message` | lecture attributs | Aucun — public stable. |

**Patterns NOT utilisés** (immunisés aux breakings) : `_run_async_impl`, `generate_content`, `enqueue_event`, `context.session.events.append`, override `BaseAgent`. **Aucun callback** (`BeforeAgentCallback`/`AfterAgentCallback`/`before_tool_callback`) redéfini dans le runtime.

## 4. Recommandation

1. **Court terme** (c.1126 → fin umbrella #13925) : ne pas toucher `google-adk==2.8.0`. Chaîne #13948 documentée et safe.
2. **Moyen terme** (post Labs 13-17) : PR dédiée de bump `google-adk==2.9.0` (1 ligne requirements.txt + changelog intégré). Re-exécution Labs 8/9 sur 2.9.0 pour vérifier `NO REGRESSION` (diff < 1% sur Sharpe/CAGR/MaxDD).
3. **Si Labs 13-17 ont besoin d'une feature 2.9.0-only** : PR anticipée avec justification body + tests de non-régression Labs 8/9. **Pas de bump automatique**.

## 5. Anti-patterns évités

- **Pas de bump automatique** sur la foi d'un changelog upstream — audit first-hand `grep utils/adk_runtime.py` montre qu'aucun breaking 2.6.0–2.9.0 ne touche le code du track.
- **Pas de "migration 2.0"** comme si la ligne 2.0 était séparée — c'est la même lignée que `2.8.0`.
- **Pas de prétention "amélioration"** sans mesure — bump 2.9.0 n'apporte aucune nouvelle feature utilisée par le track.

## Tell contextuel

- Tell c.1069 ★★ strict honnêteté référentielle — la préoccupation user portait sur « adk.dev/2.0 » comme release séparée ; c'est la doc, pas une release.
- Tell c.692-L1 strict anti-composite — audit borné à `utils/adk_runtime.py` + `requirements.txt`, pas de touche aux Labs.
- Tell c.974 strict 1 amend MAX dissipation sustained ×21ᵉ — aucune modification de code dans cette PR (audit-only).
- Tell c.1031-L1 ★ NEW — énumération exhaustive des surfaces ADK 2.x consommées par le runtime.
- Tell c.1058 strict 3 surfaces — vérification first-hand pypi + adk.dev + grep runtime.
- Tell c.745 ★★★ first-hand — toutes les conclusions s'appuient sur du code lu + changelog upstream.

— lane myia-po-2027:CoursIA-2, c.1126 2026-09-13
