# Registre des axes distillables — série *The Unexpected AI Stack: C#/.NET*

**EPIC parent** : [#10473](https://github.com/jsboige/CoursIA/issues/10473) — *Série *The Unexpected AI Stack: C#/.NET* — porter ses axes dans CoursIA (Aspire, OTEL, CSharpRepl, Roslyn, EF Core)*
**Issue de veille** : [#10475](https://github.com/jsboige/CoursIA/issues/10475) — *Veille série : registre des parutions et distillation en grains*
**Origine** : [*The Unexpected AI Stack: C#/.NET*](https://chrlschn.dev/blog/2026/08/the-unexpected-ai-stack-csharp-dotnet-part-1/) (Charles Chen, chrlschn.dev) — Parts 1 à 5 (2026-08-11 → 2026-08-17)

---

## Objet

Le présent registre est le **livrable transversal** de l'EPIC #10473 mentionné dans son body (« chaque grain en remplit une ligne **avec du code exécuté**, jamais avec de la prose ») : la **table de parité visée** actualisée au fil des distillations. Pour chaque axe annoncé par la série source, on consigne l'état du dépôt (livré / à ouvrir / non-distillable), la référence issue/PR, et la **différentielle Python ⇄ .NET** rendue visible par le grain.

Le registre **n'est pas une spec** — il est une **photographie** honnête du delta entre ce que la série promet et ce que le dépôt a déjà livré. Les écarts sont la matière première des prochains grains.

---

## Table des axes (état mesuré sur `origin/main` au 2026-08-26)

| Axe (série source) | État dépôt | Issue / PR de référence | Diff Python ⇄ .NET rendue | Prochaine tranche |
|---|---|---|---|---|
| **Aspire — encapsulation du runtime** | **Livré** (6 notebooks `MyIA.AI.Notebooks/GenAI/Integrations-DotNet/Aspire/01-06`) | [#10473](https://github.com/jsboige/CoursIA/issues/10473) | Orchestration programmable C# (analogie Pulumi/CDK) vs `docker-compose`/Tilt (YAML déclaratif). `aspire run --isolated` pour isolation ports par worktree | Densification continue (`#11271` Epic densité) |
| **OpenTelemetry via dashboard Aspire** | **Livré partiellement** (notebook `03-Aspire-Observabilite.ipynb` ; base #11530 Serilog+OTel+ActivitySource, complément [#11952](https://github.com/jsboige/CoursIA/pull/11952) po-2026 6/10 critères) | [#11927](https://github.com/jsboige/CoursIA/issues/11927) (CLOSED) → [#11530](https://github.com/jsboige/CoursIA/pull/11530) + [#11952](https://github.com/jsboige/CoursIA/pull/11952) | OTEL SDK + collecteur à câbler vs dashboard Aspire cible OTLP incluse, interrogeable en CLI | **En cours** : [#12540](https://github.com/jsboige/CoursIA/issues/12540) → PR [#12550](https://github.com/jsboige/CoursIA/pull/12550) OPEN (po-2025, tranche 2 — WithLogging natif + instrumentation HttpClient) ; résiduel après : Exercice 4 BackgroundService + vérif `aspire otel spans` |
| **CSharpRepl — scripté** | **Livré** | [#10897](https://github.com/jsboige/CoursIA/issues/10897) → PR [#10944](https://github.com/jsboige/CoursIA/pull/10944) | `connect --streamPipedInput` vs `pdb`/`%autoreload` IPython | Densification Scrutor/minimal API + AppHost frontend (**différés** par body #10897) |
| **CSharpRepl — attaché à un process .NET vivant** (`#wrap` / `#replace`) | **Livré** (notebook [`Vibe-Coding/docs/CSharpRepl-Live-Patching.ipynb`](../../Vibe-Coding/docs/CSharpRepl-Live-Patching.ipynb), 20/20 cellules code exécutées) | [#10802](https://github.com/jsboige/CoursIA/issues/10802), [#10971](https://github.com/jsboige/CoursIA/issues/10971) → PR [#10806](https://github.com/jsboige/CoursIA/pull/10806) MERGED (b96df2a3cc3) + densification [#11332](https://github.com/jsboige/CoursIA/pull/11332) | `#wrap`/`#replace` à chaud sur un process attaché vs `pdb`/`%autoreload` IPython | Densification continue (EPIC #11271) |
| **Roslyn — analyseurs statiques comme garde-fous** | **Livré** (3 analyseurs : AGENTGUARD001 `.Result/.Wait`, AGENTGUARD002 `async void` + exemption handler, AGENTGUARD003 `Task.Run` nu) | [#11849](https://github.com/jsboige/CoursIA/issues/11849) → PR [#11866](https://github.com/jsboige/CoursIA/pull/11866) ; E1 `async void` [#12533](https://github.com/jsboige/CoursIA/issues/12533) ; E2 `Task.Run` feu [#13400](https://github.com/jsboige/CoursIA/issues/13400) | Analyseurs dans la compilation vs `mypy`/`ruff` (hors compilation) | Itération E3 restante (variante furtive `GetAwaiter().GetResult()`, exemption `Result<T>`, extension `Task.Factory.StartNew`) à mesure des findings de couverture |
| **EF Core — requêtes vérifiées à la compilation** | **Livré** | [#12381](https://github.com/jsboige/CoursIA/issues/12381) → PR [#12393](https://github.com/jsboige/CoursIA/pull/12393) | ORM à l'exécution vs vérifié à la compilation — `EF.CompileQuery` (mesuré 2,78×), `ToQueryString()`, `FromSqlInterpolated` | Livré : notebook `GenAI/Integrations-DotNet/EFCore/01-EFCore-Requetes-Compilees.ipynb` ; densification continue possible (EPIC #10473) ; rangé dans le hub .NET via #13581 T2 |
| **Channels / Orleans** | **Non distillable** | Aucun issue ni notebook | Concurrence native + modèle d'acteurs vs `asyncio`/`ray` | **Différé** par body #10473 (« aucun Aspire ni CSharpRepl **en CI** … mentionnés comme atouts de la pile ») |
| **Aspire AppHost orchestrant pile GenAI** (ComfyUI/Qwen/vLLM) + `run --isolated` | **Livré** (AppHost [`GenAiStack.AppHost/`](GenAiStack.AppHost/apphost.cs) + jumeau worktree [`GenAiStack.AppHost-wt2/`](GenAiStack.AppHost-wt2/apphost.cs) = les 2 instances isolées de l'acceptance, notebook [`01-Aspire-Orchestration-GenAi.ipynb`](01-Aspire-Orchestration-GenAi.ipynb), README, échantillon d'appel réel) | [#10838](https://github.com/jsboige/CoursIA/issues/10838), [#10857](https://github.com/jsboige/CoursIA/issues/10857) → PR [#10846](https://github.com/jsboige/CoursIA/pull/10846) MERGED (2026-08-14T04:19Z) | AppHost orchestre la pile réelle vs `docker-compose`/`Helm` pour la pile Python. Le 3ᵉ AppHost [`GenAiStackReel.AppHost/apphost.cs`](GenAiStackReel.AppHost/apphost.cs) (notebook [`02-Aspire-GenAiStack-Reel.ipynb`](02-Aspire-GenAiStack-Reel.ipynb)) **référence** comfyui/vllm comme connection strings au lieu de les conteneuriser — choix d'architecture documenté dans son en-tête : singletons GPU en production, ne pas dupliquer 24 Go de VRAM par worktree ; seul le service léger (whisper-api) est orchestré en conteneur | Densification continue (#11271) |
| **Copilot SDK binding C# (Part 3)** | **Livré** (tranche A4 EPIC #11516) | [#11926](https://github.com/jsboige/CoursIA/issues/11926) → PR [#12004](https://github.com/jsboige/CoursIA/pull/12004) (c.1301+268) | SDK officiel C# + réutilisation credentials OAuth GitHub vs appel API BYOK Azure OpenAI | BYOK Azure (Exercice 3), `OnPermissionRequest` avancée, Aspire AppHost integration (cf. [#10857](#) — à rouvrir), TUnit.Testcontainers |
| **Testcontainers + transactions (Part 4)** | **Livré** (Part 4 publiée le 2026-08-15 : « Setting up the test foundations using Testcontainers and transactions » ; distillée par #11516) | [#11516](https://github.com/jsboige/CoursIA/issues/11516) → PR [#11557](https://github.com/jsboige/CoursIA/pull/11557) MERGED — TUnit + Testcontainers Postgres + rollback isolation ; axe A4 de la digestion Parts 3-5 | Containers éphémères par test avec rollback transactionnel vs `pytest-docker` | Densification continue (#11271) |
| **Mistral Vibe worker integration (axe 11 — orchestration agents LLM)** | **Livré** (tranche c.280 + c.283 registre) | [#12012](https://github.com/jsboige/CoursIA/issues/12012) → PR [#12018](https://github.com/jsboige/CoursIA/pull/12018) MERGED (c.1301+280, `feat(vibe,#12012): Mistral Vibe worker integration — harnais .vibe/`) | Worker LLM non-Anthropic (`mistral-medium-3.5`) aligné sur le protocole Claude Code (cycle Phase 1→1.5→2→3→4, MCP `roo-state-manager` override local). Config `~/.vibe/config.toml` (Rust tool) vs `~/.claude.json`/`settings.json` (JSON), `commands/continue.md` Markdown commun. SOTA-OK (s'aligne sur stack existant, ne contourne aucun outil). | Validation cycle worker complet end-to-end (déjà testé lecture ; reste write) ; alignement avec les 9 workers Claude Code existants (Mistral Vibe = 10ᵉ worker, file ai-01 bottleneck 31 PRs) ; configuration `schtask` via ai-01 (cadence 30 min staggered) |

---

## Grains fantômes L1500-B — diagnostic révisé au 2026-08-26 : tous livrés, le fantôme était la mesure

**Correction 2026-08-26 (firsthand, PR-by-PR)** : les 4 lignes ci-dessous affirmaient « 0 PR, 0 notebook sur disque » — c'était **faux sur les deux comptes** pour les 3 issues distinctes. Les livraisons existent et sont MERGED ; la mesure du 2026-08-20 les a ratées (les chemins réels diffèrent de ceux spécfiés dans les bodies : le notebook CSharpRepl vit dans `Vibe-Coding/docs/`, pas `GenAI/CSharpRepl/` — et la recherche par `closedByPullRequestsReferences` est muette quand une PR écrit `See #N` au lieu de `Closes #N`, exactement la convention que cette série impose).

| Issue | Titre | Livraison réelle (vérifiée 2026-08-26) |
|---|---|---|
| [#10802](https://github.com/jsboige/CoursIA/issues/10802) | CSharpRepl attaché à un process .NET vivant (`#wrap`/`#replace`) | PR [#10806](https://github.com/jsboige/CoursIA/pull/10806) MERGED — notebook `Vibe-Coding/docs/CSharpRepl-Live-Patching.ipynb` (`git log --follow` : b96df2a3cc3) + densification #11332 |
| [#10838](https://github.com/jsboige/CoursIA/issues/10838) | Aspire AppHost orchestrant la pile GenAI locale + `run --isolated` | PR [#10846](https://github.com/jsboige/CoursIA/pull/10846) MERGED 2026-08-14 — 2 AppHost (GenAiStack + -wt2 = les 2 instances isolées), notebook 01, README |
| [#10857](https://github.com/jsboige/CoursIA/issues/10857) | `feat(genai,#10473): AppHost Aspire sur notre pile réelle (ComfyUI/Qwen)` | Doublon de #10838 — couvert par la même #10846 ; l'architecture GenAiStackReel (comfyui/vllm en connection strings, whisper orchestré) documente le choix « singletons GPU » |
| [#10971](https://github.com/jsboige/CoursIA/issues/10971) | Notebook CSharpRepl attaché + introspection | Doublon de #10802 — couvert par #10806 |

**Leçon (pour la mesure, pas pour les issues)** : une détection de « grain fantôme » qui s'appuie sur `closedByPullRequestsReferences` + un chemin spécfié dans un body détecte les PRs `See`-référencées à un autre chemin comme « rien ». Toute conclusion « à rouvrir » doit d'abord passer par `git log --follow -- <chemin-réel>` + `gh pr list --state all --search <sujet>` — les 4 ancres de L576, pas une seule. **Aucune de ces issues n'est à rouvrir.**

---

## Conventions

- **Tagging** : `Grain: <TIER>/<GENRE> — lane <machine:workspace> — prev: <TIER>/<GENRE> #<PR>` en première ligne de body PR.
- **G-VAR-3** : adjacent à un grain DEEP/MED = OK ; 2× même GENRE LIGHT consécutif = ban.
- **Voir aussi** : `variation-protocol.md` (G-VAR-1/G-VAR-3/G-VAR-2 + tier litmus), `catalog-pr-hygiene.md` (catalogue byte-identique à main, JAMAIS regen catalogue sur branche feature).
- **Source canonique** : issue de veille [#10475](https://github.com/jsboige/CoursIA/issues/10475) (à mettre à jour au fil des parutions).

---

## Historique des tranches distillables (mesuré sur `origin/main` au 2026-08-26T13:0xZ)

| Tranche | PR | Lane | Date merge | Axe couvert | Commentaire |
|---|---|---|---|---|---|
| AppHost orchestration GenAI (#10838/#10857) | [#10846](https://github.com/jsboige/CoursIA/pull/10846) | n/a | MERGED 2026-08-14T04:19Z | AppHost orchestrateur + `run --isolated` | 2 AppHost (GenAiStack + -wt2), notebook 01, README — cf. diagnostic révisé §fantômes |
| CSharpRepl attaché process vivant (#10802/#10971) | [#10806](https://github.com/jsboige/CoursIA/pull/10806) | n/a | MERGED 2026-08-14T04:17Z | CSharpRepl `#replace`/`#wrap`/`#patches`/`#revert` + mode pipe | Notebook `Vibe-Coding/docs/CSharpRepl-Live-Patching.ipynb` + densification #11332 |
| Part 2 zeeq-tmpl (#10897) | [#10944](https://github.com/jsboige/CoursIA/pull/10944) | n/a | MERGED | CSharpRepl scripté + Mise + Scrutor | Tranche 2 distillation — axes 4/5/6 clos |
| SK-4 §6 OpenTelemetry spans gen_ai (#10474) | [#10964](https://github.com/jsboige/CoursIA/pull/10964) | myia-po-2023:CoursIA | MERGED 2026-08-14T16:30Z | OTEL spans gen_ai réels | Section 6 du notebook SK-4 |
| 01-Aspire-Orchestration cellule 16 (#11701) | [#11847](https://github.com/jsboige/CoursIA/pull/11847) | n/a | MERGED | AppHost orchestration | Fix cellule 16 (cmd.exe + timeout HttpClient) |
| Roslyn analyseurs garde-fous (#11849) | [#11866](https://github.com/jsboige/CoursIA/pull/11866) | n/a | MERGED | Roslyn AGENTGUARD001 dans la compilation | Notebook 06 + AgentGuard.Analyzers/Demo/Verifier |
| Copilot SDK distillation (A4 EPIC #11516) | [#12004](https://github.com/jsboige/CoursIA/pull/12004) | myia-po-2025:CoursIA-2 | MERGED | Copilot SDK + Channel<string> + Scrutor IEndpoint | Quota GitHub Copilot mensuel épuisé (graceful try/catch fallback) |
| Testcontainers + TUnit + rollback (Part 4, #11516) | [#11557](https://github.com/jsboige/CoursIA/pull/11557) | n/a | MERGED 2026-08-18T08:30Z | Testcontainers Postgres + isolation transactionnelle | Axe Part 4 de la digestion Parts 3-5 |
| 03-Aspire-Observabilite Serilog+OTel (#11516) | [#11530](https://github.com/jsboige/CoursIA/pull/11530) | n/a | MERGED 2026-08-18T19:36Z | Serilog + OpenTelemetry + ActivitySource call-site | Axe Part 5, base OTEL du notebook 03 |
| Registre des axes distillables (#10475) | [#12007](https://github.com/jsboige/CoursIA/pull/12007) | n/a | MERGED 2026-08-21T01:14Z | Livrable transversal | Le présent registre |
| Mistral Vibe worker (#12012) | [#12018](https://github.com/jsboige/CoursIA/pull/12018) | n/a | MERGED 2026-08-21T01:10Z | Worker LLM non-Anthropic sur protocole Claude Code | Axe 11 orchestration agents |
| EF Core requêtes vérifiées à la compilation (#12381) | [#12393](https://github.com/jsboige/CoursIA/pull/12393) | myia-po-2024:CoursIA | MERGED 2026-08-23T06:46Z | EF Core — requêtes vérifiées à la compilation | Notebook 01-EFCore-Requetes-Compilees + registre EF Core |

---

**Statut** : registre **actif**, tenu par issue de veille [#10475](https://github.com/jsboige/CoursIA/issues/10475). Au fil des parutions de chrlschn.dev, ajouter un onglet « Source canonique » + une ligne dans la table. Au fil des distillations livrées, ajouter une ligne dans l'historique avec PR + commit + axe couvert.

Voir aussi : [EPIC #10473](https://github.com/jsboige/CoursIA/issues/10473) · [README GenAI](../../README.md) · [docs/genai-services.md](../../../../docs/genai/genai-services.md) (en cours de régénération).