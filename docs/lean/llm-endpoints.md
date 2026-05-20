# Lean Prover LLM Endpoints

Configuration des providers LLM utilises par le multi-agent prover dans `MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/prover/`.

**Cles et URLs concretes** : stockees dans `MyIA.AI.Notebooks/SymbolicAI/Lean/.env` (gitignored). Ne **JAMAIS** committer ce fichier. Si une cle semble invalide, tester avec `curl /v1/models` avant de demander a l'user.

## Providers

| Provider key | Type | Modele | Usage | Comportement |
|--------------|------|--------|-------|--------------|
| `zai` | Cloud dedie Lean | `glm-5.1` | **Powerful** — reasoning model | Heavy thinking : ~99% des completion_tokens vont en `reasoning_content`. 1 prompt simple peut consommer 2048 tokens en raisonnement seul. **Exiger `max_tokens >= 8192` et timeout per-call >= 300s**. |
| `local` | Cluster interne reverse-proxy | `qwen3.6-35b-a3b` | **Fast** — modeste mais rapide | Modere : ~5s pour 293 tokens dont ~270 reasoning. Plus rapide que zai mais reste thinking-aware. Attention au nom de modele (`.6` pas `.5`, changement silencieux 2026-05-11). |
| `openrouter` | OpenRouter API | `anthropic/claude-sonnet-4.5` (powerful) / `google/gemma-3-27b-it:free` (fast) | Backup powerful, free tier rate-limite | Bon fallback Director. Free tier limite ~50 req/jour. |
| `anthropic` | Anthropic API directe | `claude-sonnet-4-5` | **Reserve** — pas encore wire | Le framework actuel utilise `OpenAIChatCompletionClient` only. Necessiterait un client Anthropic natif. |

**Mappage** : la cle `provider="..."` dans `prover/config.py PROVIDERS` correspond a la colonne `Provider key`.

## Pieges connus

1. **`finish_reason: "length"` premature** : sur `glm-5.1` avec `max_tokens <= 2048`, toute la fenetre passe en reasoning. La completion s'arrete avant production de contenu utile. Toujours `max_tokens >= 8192`.

2. **Reasoning content separe** : GLM-5.1 met `content` separe de `reasoning_content` dans la reponse JSON. Le framework `agent_framework_openai` gere `text_reasoning` content type via `Content.from_text_reasoning()` — verifie OK 2026-05.

3. **Local LLM ports DOWN** : ai-01 ports 5001/5002 (vLLM mini/medium) ont ete observes DOWN cycliquement (Cycle 20 Track 1 po-2023 escalation). Toujours preferer l'endpoint reverse-proxy public (`local` provider key) plutot que `localhost:500X`.

4. **Nom de modele case-sensitive** : si une cle valide retourne 404, verifier le nom exact via `curl /v1/models` avant de presumer une cle expiree.

## Cout indicatif (estimation 2026-05)

| Provider | Cycle prover BG 20 iter (~40min) |
|----------|----------------------------------|
| `zai` glm-5.1 | bas (provider promo) |
| `local` qwen3.6 | gratuit (infra interne) |
| `openrouter` claude-sonnet-4.5 | ~0.50-2 USD par BG selon profondeur |
| `openrouter` gemma-3-27b free | gratuit (rate-limited) |

Pour les sorrys very_hard, le Director (Opus 4.7 via OpenRouter ou Anthropic direct) est obligatoire et augmente le cout. Tracer les couts via `bg_logs/ai01_demo<N>_*.log`.

## Voir aussi

- [docs/lean/prover_iteration_history.md](prover_iteration_history.md) — Architecture iterations F6-F11, B3
- [docs/lean/stable_marriage_intractable_diagnosis.md](stable_marriage_intractable_diagnosis.md) — 6 sorrys remaining, root causes
- [.claude/rules/lean-lake-build-required.md](../../.claude/rules/lean-lake-build-required.md) — Lake build SUCCESS obligatoire avant merge
- [.claude/rules/lean-prover-bg-systematic.md](../../.claude/rules/lean-prover-bg-systematic.md) — BG iter systematique post-PR/msg po-2026
