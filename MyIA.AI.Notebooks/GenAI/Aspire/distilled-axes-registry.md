# Registre des axes distillables — série *The Unexpected AI Stack: C#/.NET*

**EPIC parent** : [#10473](https://github.com/jsboige/CoursIA/issues/10473) — *Série *The Unexpected AI Stack: C#/.NET* — porter ses axes dans CoursIA (Aspire, OTEL, CSharpRepl, Roslyn, EF Core)*
**Issue de veille** : [#10475](https://github.com/jsboige/CoursIA/issues/10475) — *Veille série : registre des parutions et distillation en grains*
**Origine** : [*The Unexpected AI Stack: C#/.NET*](https://chrlschn.dev/blog/2026/08/the-unexpected-ai-stack-csharp-dotnet-part-1/) (Charles Chen, chrlschn.dev) — Parts 1 à 5 (2026-08-11 → 2026-08-17)

---

## Objet

Le présent registre est le **livrable transversal** de l'EPIC #10473 mentionné dans son body (« chaque grain en remplit une ligne **avec du code exécuté**, jamais avec de la prose ») : la **table de parité visée** actualisée au fil des distillations. Pour chaque axe annoncé par la série source, on consigne l'état du dépôt (livré / à ouvrir / non-distillable), la référence issue/PR, et la **différentielle Python ⇄ .NET** rendue visible par le grain.

Le registre **n'est pas une spec** — il est une **photographie** honnête du delta entre ce que la série promet et ce que le dépôt a déjà livré. Les écarts sont la matière première des prochains grains.

---

## Table des axes (état mesuré sur `origin/main` au 2026-08-20)

| Axe (série source) | État dépôt | Issue / PR de référence | Diff Python ⇄ .NET rendue | Prochaine tranche |
|---|---|---|---|---|
| **Aspire — encapsulation du runtime** | **Livré** (6 notebooks `MyIA.AI.Notebooks/GenAI/Aspire/01-06`) | [#10473](https://github.com/jsboige/CoursIA/issues/10473) | Orchestration programmable C# (analogie Pulumi/CDK) vs `docker-compose`/Tilt (YAML déclaratif). `aspire run --isolated` pour isolation ports par worktree | Densification continue (`#11271` Epic densité) |
| **OpenTelemetry via dashboard Aspire** | **Livré partiellement** (notebook `03-Aspire-Observabilite.ipynb` section 5, 6 exercices) | [#11927](https://github.com/jsboige/CoursIA/issues/11927) → PR [#11952](https://github.com/jsboige/CoursIA/pull/11952) (po-2026, 6/10 critères) | OTEL SDK + collecteur à câbler vs dashboard Aspire cible OTLP incluse, interrogeable en CLI | Compléter les 3 critères partiels (Exercice 4 BackgroundService + Exercice 5 `WithLogging` + vérif `aspire otel spans`) |
| **CSharpRepl — scripté** | **Livré** | [#10897](https://github.com/jsboige/CoursIA/issues/10897) → PR [#10944](https://github.com/jsboige/CoursIA/pull/10944) | `connect --streamPipedInput` vs `pdb`/`%autoreload` IPython | Densification Scrutor/minimal API + AppHost frontend (**différés** par body #10897) |
| **CSharpRepl — attaché à un process .NET vivant** (`#wrap` / `#replace`) | **Livré ailleurs** (correction 2026-08-23) | Substance portée par `Vibe-Coding/docs/CSharpRepl-Live-Patching.ipynb` — PR [#10806](https://github.com/jsboige/CoursIA/pull/10806) MERGED (+ densité [#11332](https://github.com/jsboige/CoursIA/pull/11332)), vérifié sur disque. Les issues [#10802](https://github.com/jsboige/CoursIA/issues/10802)/[#10971](https://github.com/jsboige/CoursIA/issues/10971) restent CLOSED à juste titre | `#wrap`/`#replace` à chaud sur un process attaché vs `pdb`/`%autoreload` IPython | Rien à rouvrir — l'axe vit dans la série Vibe-Coding, pas sous `GenAI/CSharpRepl/` |
| **Roslyn — analyseurs statiques comme garde-fous** | **Livré** (+ itération E1) | [#11849](https://github.com/jsboige/CoursIA/issues/11849) → PR [#11866](https://github.com/jsboige/CoursIA/pull/11866) ; E1 : [#12533](https://github.com/jsboige/CoursIA/issues/12533) (`AGENTGUARD002` async void + exemption sémantique handler) | Analyseurs dans la compilation vs `mypy`/`ruff` (hors compilation) | Itération E2 restante (`AGENTGUARD003` `Task.Run` feu, stub posé dans le notebook 06) à mesure des findings de couverture |
| **EF Core — requêtes vérifiées à la compilation** | **Non distillable** | Aucun issue ni notebook | ORM à l'exécution vs vérifié à la compilation | **À ouvrir** — axe promis par la Part 1, jamais porté. Tranche naturelle = EF Core vs `peewee`/`SQLAlchemy` dans une série existante |
| **Channels / Orleans** | **Non distillable** | Aucun issue ni notebook | Concurrence native + modèle d'acteurs vs `asyncio`/`ray` | **Différé** par body #10473 (« aucun Aspire ni CSharpRepl **en CI** … mentionnés comme atouts de la pile ») |
| **Aspire AppHost orchestrant pile GenAI** (ComfyUI/Qwen/vLLM) + `run --isolated` | **Fermé sans livraison** (grain fantôme L1500-B) | [#10838](https://github.com/jsboige/CoursIA/issues/10838), [#10857](https://github.com/jsboige/CoursIA/issues/10857) — toutes deux CLOSED + `closedByPullRequestsReferences: []` | AppHost orchestre la pile réelle (GenAI/Inference containers) vs `docker-compose`/`Helm` pour la pile Python | **À rouvrir** — `GenAiStackReel.AppHost/apphost.cs` existe sur disque mais n'intègre pas les containers ComfyUI/Qwen/vLLM (à vérifier firsthand au prochain cycle) |
| **Copilot SDK binding C# (Part 3)** | **Livré** (tranche A4 EPIC #11516) | [#11926](https://github.com/jsboige/CoursIA/issues/11926) → PR [#12004](https://github.com/jsboige/CoursIA/pull/12004) (c.1301+268) | SDK officiel C# + réutilisation credentials OAuth GitHub vs appel API BYOK Azure OpenAI | BYOK Azure (Exercice 3), `OnPermissionRequest` avancée, Aspire AppHost integration (cf. [#10857](#) — à rouvrir), TUnit.Testcontainers |
| **Testcontainers + telemetry (Part 4)** | **Annoncé non publié** | Aucun issue ; auteur chrlschn.dev signale la Part 4 mais ne l'a pas publiée | Sub-process ephemeral containers vs `pytest-docker` | **À ouvrir** au prochain parutions tracker |
| **Mistral Vibe worker integration (axe 11 — orchestration agents LLM)** | **Livré** (tranche c.280 + c.283 registre) | [#12012](https://github.com/jsboige/CoursIA/issues/12012) → PR [#12018](https://github.com/jsboige/CoursIA/pull/12018) MERGED (c.1301+280, `feat(vibe,#12012): Mistral Vibe worker integration — harnais .vibe/`) | Worker LLM non-Anthropic (`mistral-medium-3.5`) aligné sur le protocole Claude Code (cycle Phase 1→1.5→2→3→4, MCP `roo-state-manager` override local). Config `~/.vibe/config.toml` (Rust tool) vs `~/.claude.json`/`settings.json` (JSON), `commands/continue.md` Markdown commun. SOTA-OK (s'aligne sur stack existant, ne contourne aucun outil). | Validation cycle worker complet end-to-end (déjà testé lecture ; reste write) ; alignement avec les 9 workers Claude Code existants (Mistral Vibe = 10ᵉ worker, file ai-01 bottleneck 31 PRs) ; configuration `schtask` via ai-01 (cadence 30 min staggered) |

---

## Grains fantômes à rouvrir (L1500-B ★★★)

3 issues de l'EPIC #10473 ont été **fermées sans livraison substance** (`closedByPullRequestsReferences: []` pour toutes) :

| Issue | Titre | État substance | Diagnostic |
|---|---|---|---|
| [#10802](https://github.com/jsboige/CoursIA/issues/10802) | CSharpRepl attaché à un process .NET vivant (`#wrap`/`#replace`) | CLOSED, 0 PR, 0 notebook sur disque | **Réouvrir** — body spécifie déjà `MyIA.AI.Notebooks/GenAI/CSharpRepl/01-CSharpRepl-Attache-Process-Vivant.ipynb` non créé. Pattern L1500-B : claim fantôme |
| [#10838](https://github.com/jsboige/CoursIA/issues/10838) | Aspire AppHost orchestrant la pile GenAI locale + `run --isolated` | CLOSED, 0 PR | **Réouvrir** — corps promettait orchestration ComfyUI/Qwen. `GenAiStackReel.AppHost/apphost.cs` existe mais n'intègre pas les containers réels |
| [#10857](https://github.com/jsboige/CoursIA/issues/10857) | `feat(genai,#10473): AppHost Aspire sur notre pile réelle (ComfyUI/Qwen)` | CLOSED, 0 PR | Doublon de #10838 — **réouvrir** en doublon clarifié ou marquer comme alias |
| [#10971](https://github.com/jsboige/CoursIA/issues/10971) | Notebook CSharpRepl attaché + introspection | CLOSED, 0 PR, 0 notebook sur disque | Doublon de #10802 — même diagnostic L1500-B |

Ces grains fantômes sont la **différence entre « fermer une issue » et « fermer une acceptance »** : `stateReason: COMPLETED` ne vaut que si la PR est listée dans `closedByPullRequestsReferences`. **Convention c.1301+269** : tout grain de cette série doit porter `See #10473` (jamais `Closes` — l'EPIC vit tant que la série publie) et être rattaché à un PR réelle.

---

## Conventions

- **Tagging** : `Grain: <TIER>/<GENRE> — lane <machine:workspace> — prev: <TIER>/<GENRE> #<PR>` en première ligne de body PR.
- **G-VAR-3** : adjacent à un grain DEEP/MED = OK ; 2× même GENRE LIGHT consécutif = ban.
- **Voir aussi** : `variation-protocol.md` (G-VAR-1/G-VAR-3/G-VAR-2 + tier litmus), `catalog-pr-hygiene.md` (catalogue byte-identique à main, JAMAIS regen catalogue sur branche feature).
- **Source canonique** : issue de veille [#10475](https://github.com/jsboige/CoursIA/issues/10475) (à mettre à jour au fil des parutions).

---

## Historique des tranches distillables (mesuré sur `origin/main` au 2026-08-20T21:55Z)

| Tranche | PR | Lane | Date merge | Axe couvert | Commentaire |
|---|---|---|---|---|---|
| AppHost orchestration GenAI (#10473) | [#10838](https://github.com/jsboige/CoursIA/issues/10838) | n/a | **CLOSED sans PR** | AppHost orchestrateur | **Grain fantôme** — réouvrir |
| Part 2 zeeq-tmpl (#10897) | [#10944](https://github.com/jsboige/CoursIA/pull/10944) | n/a | MERGED | CSharpRepl scripté + Mise + Scrutor | Tranche 2 distillation — axes 4/5/6 clos |
| SK-4 §6 OpenTelemetry spans gen_ai (#10474) | [#10964](https://github.com/jsboige/CoursIA/pull/10964) | n/a | MERGED | OTEL spans gen_ai réels | Section 6 du notebook SK-4 |
| 01-Aspire-Orchestration cellule 16 (#11701) | [#11847](https://github.com/jsboige/CoursIA/pull/11847) | n/a | MERGED | AppHost orchestration | Fix cellule 16 (cmd.exe + timeout HttpClient) |
| Roslyn analyseurs garde-fous (#11849) | [#11866](https://github.com/jsboige/CoursIA/pull/11866) | n/a | MERGED | Roslyn AGENTGUARD001 dans la compilation | Notebook 06 + AgentGuard.Analyzers/Demo/Verifier |
| Copilot SDK distillation (A4 EPIC #11516) | [#12004](https://github.com/jsboige/CoursIA/pull/12004) | myia-po-2025:CoursIA-2 | OPEN (c.1301+268) | Copilot SDK + Channel<string> + Scrutor IEndpoint | c.1301+268 livré substance — Quota GitHub Copilot mensuel épuisé (graceful try/catch fallback) |

---

**Statut** : registre **actif**, tenu par issue de veille [#10475](https://github.com/jsboige/CoursIA/issues/10475). Au fil des parutions de chrlschn.dev, ajouter un onglet « Source canonique » + une ligne dans la table. Au fil des distillations livrées, ajouter une ligne dans l'historique avec PR + commit + axe couvert.

Voir aussi : [EPIC #10473](https://github.com/jsboige/CoursIA/issues/10473) · [README GenAI](../../README.md) · [docs/genai-services.md](../../../../docs/genai-services.md) (en cours de régénération).