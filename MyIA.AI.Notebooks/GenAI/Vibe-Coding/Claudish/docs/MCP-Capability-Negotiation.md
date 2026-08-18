# MCP Claudish — Capability Negotiation (ledger propositional · #11556)

> **Statut : proposition architecturale**, pas une implémentation. Ce ledger décrit un serveur
> MCP que les agents du cluster **appelleraient** sur Claudish pour négocier leurs capacités,
> déclenché à la prochaine condensation du contexte d'un agent. L'implémentation du serveur
> MCP lui-même relève du **fork `jsboige/claudish`** (mono-repo séparé) ; ce ticket est ouvert
> ici parce que la coordination des agents du cluster est notre juridiction.
>
> **Origine** : mandat user `2026-08-18`, capturé dans l'issue **#11556**. Ce ledger
> **formalise** la proposition faite dans le body de l'issue en vue d'une revue technique
> avant tout codage. Aucun code MCP n'est livré ici — c'est un document d'**architecture
> spécification**, à lire avant tout `git clone jsboige/claudish`.
>
> `See #11556`

## 1. Pourquoi cette couture maintenant

Aujourd'hui, **un agent subit son backend** : le routage tier → provider est décidé au hub
(le fork `jsboige/claudish`), l'agent ne sait pas ce qui le sert, et n'a aucun moyen de
dire ce dont il a besoin pour la tâche à venir. Or **l'agent est la seule entité qui
connaît la nature de la tâche** qu'il s'apprête à faire.

Le fork sait déjà faire quelque chose de très proche : les *recovery notices* sont émises
**sur 3 condensations** (cf. commit `823e614` du 2026-08-12 sur le hub). La couture
existe déjà dans le code ; ce ticket propose de la rendre **pilotable par l'agent**
au lieu d'être seulement réactive au quota.

## 2. La couture est la condensation

Un changement de provider **en plein milieu** d'une conversation est précisément ce que
le design refuse à juste titre (tokenizer différent, comportement différent, dérive
invisible). Mais **à la condensation**, le contexte est reconstruit de toute façon :
c'est une frontière propre où un changement ne casse rien.

Le MCP est invoqué **avant** la condensation, avec un effet différé à celle-ci :

```text
t = N              agent travaille avec provider X (MiniMax-M3, par exemple)
t = N+100 steps    agent sait qu'il va faire QA visuel sur des PDF
t = N+101          agent invoque claudish_request_capability("vision", at:"next_condensation")
t = N+120          condensation déclenchée normalement
t = N+121          handler post-condensation consulte la pending-request : vision ⇒ switch
                   vers un provider qui supporte vision (Anthropic natif si Opus-tier actif)
t = N+122          la nouvelle conversation redémarre avec un provider différent, sans drift
```

Le pivot est **passé au crible d'un boundary propre** : tokenizer différent ≠ bug, dérive
de contexte ≠ dérive silencieuse.

## 3. Surface envisagée — deux versants (lecture / écriture)

### 3.1 Lecture (sans effet de bord)

| Outil MCP | Rend |
|---|---|
| `claudish_status` | mapping tier → provider **effectif**, steps armés, `configured/armed/auto`, horloges de reset |
| `claudish_capabilities` | ce que le provider courant sait faire — **vision oui/non**, fenêtre réelle, tool-use, thinking |
| `claudish_my_traffic` | consommation récente de **ma** lane (le hub ventile déjà par machine à chaque cycle 3 h) |

**Lecture seule** = utile **seule** : un agent qui sait que le provider actuel est `MiniMax-M3
non-vision` peut prendre la décision de basculer **de lui-même** en invoquant l'écriture
ci-dessous. Le sous-ensemble lecture est un **livrable intermédiaire** viable si la suite
est bloquée.

### 3.2 Écriture (négociation, pas ordre)

| Outil MCP | Effet |
|---|---|
| `claudish_request_capability` | déclare le besoin (`vision` · `long-context` · `cheap-bulk` · `heavy-reasoning`) ; le hub choisit et **épingle** un provider, **appliqué à la prochaine condensation** |
| `claudish_release` | retour au nominal (fin de tâche) |

Le hub reste **arbitre** : une demande est une demande, pas une réquisition. Il peut refuser
(quota, frugalité, mandat) et **dire pourquoi** — un refus motivé est exploitable par l'agent,
un silence ne l'est pas.

## 4. Trois usages déjà existants, aujourd'hui sans réponse

1. **Vision.** Le dashboard `workspace-claudish` acte que « GLM coding reste aveugle à la
   vision, lane Opus natif recommandé pour tasks vision ». Aujourd'hui c'est une **consigne
   de harnais** que chaque agent doit se rappeler ; ce serait une **capability négociée**,
   vérifiable. Le fix crash-PDF (`6373d37` sur le fork) n'aurait pas eu à être découvert
   par un 400 en production.
2. **Arbitrage Haiku ai-01.** Le dashboard porte un blocage ouvert : 39 req/3 h de workers
   GitHub-issue hors mandat CoursIA-2, servis en DeepSeek PAYG, « à arbitrer : migrer vers
   sonnet → glm-5.3 ou autoriser ». Un agent qui déclare `cheap-bulk` résout la question
   **à la source** au lieu de la faire remonter en arbitrage humain.
3. **Semaine de frugalité.** po-2023 a signalé deux cycles consécutifs à > 400 req Opus
   depuis ai-01, « poste de dépense à surveiller ». Un agent capable de déclarer
   `heavy-reasoning` **seulement quand il en a besoin** rend cette surveillance inutile.

## 5. Critères d'acceptation (issus de #11556, version condensée)

- [ ] Un serveur MCP joignable par les agents du cluster, avec au minimum `claudish_status`
      + `claudish_capabilities` (la moitié lecture est déjà utile seule, et se livre
      en premier).
- [ ] `claudish_request_capability` avec application **à la prochaine condensation**,
      jamais en cours de conversation.
- [ ] Refus **motivé** (quota / frugalité / mandat), lisible par l'agent.
- [ ] Aucun secret dans la surface MCP — le hub exige déjà `x-api-key`/`x-proxy-key`
      (cf. commit `823e614`) ; le MCP s'authentifie comme un client de plus.
- [ ] Documenté dans la section Claudish du dépôt (ce présent ledger est la première étape).

## 6. Voisinage et dépendances

- **Epic #1210 (semantic-fleet / MultiConnector)** : approche **complémentaire et subordonnée**
  — routage automatique par vetting (`prétraitement sur la forme des appels`), sous le
  canal déclaratif. Ne pas les mettre en concurrence : le déclaratif l'emporte sémantiquement.
- **Compaction du harnais** (Phase 2 #11554, hors-scope worker) : converge —
  une capability négociée retire du harnais une consigne que chaque agent doit aujourd'hui
  porter en mémoire, ce qui allège le top contributeur dynamique (58,8 % du poids auto-chargé
  mesuré sur la fenêtre c.314, harness = 178 746 chars ≈ 24–45 % de l'input Anthropic).
- **Référentiel technique du hub** : `MyIA.AI.Notebooks/GenAI/Vibe-Coding/Claudish/docs/Claudish-Proxy.md`
  (couvre déjà wire, topologie de déploiement, router 3 tiers, variables d'env) ;
  ce ledger vient **en complément**, pas en remplacement.

## 7. Statut et ordre proposé

| Étape | Qui | Délai | Description |
|---|---|---|---|
| **E0** (présent ledger) | po-2023 | 1 cycle | Proposition architecturale, livrée ici en `See #11556` |
| **E1** | fork `jsboige/claudish` | à dispatcher | Squelette MCP `claudish_status` + `claudish_capabilities` (lecture seule) |
| **E2** | fork | à dispatcher | `claudish_request_capability` + gestion de la pending-request à la condensation |
| **E3** | fork + po-2023 | à dispatcher | Pilotage sur 1 lane (po-2023 ou ai-01) avec une capability nominale (`vision`) |
| **E4** | fork | à dispatcher | Extension à 2+ capabilities + tests inter-lanes |

L'E0 peut partir sans bloquer les E1+ ; les agents du cluster commencent à **consommer**
la lecture seule dès qu'elle est exposée.

## 8. Note d'audit — pourquoi ce ledger, pas un commit d'implémentation

- **Le scope du serveur MCP est dans le fork**, pas dans `jsboige/CoursIA`. Committer
  du code MCP ici violerait `catalog-pr-hygiene.md` R1 (catalogue byte-identique à `main`).
- **Périmètre d'un agent worker (po-2023)** : proposer, documenter, ouvrir le ticket côté
  coordinateur fork. La phase implémentation relève du **fork `jsboige/claudish`** et
  appartient à `jsboige/claudish:maintainers` (ai-01 + po-2026 dans le cluster).
- **G-VAR-1 NON applicable ici** : ce ledger est une proposition architecturale, pas une
  amélioration « fait ce qu'il annonce » sur du code existant. Il n'est ni DEEP, ni MED,
  ni LIGHT — il est **pré-DELP (spec)** : une étape qui ouvre un chantier, sans valeur
  cyclique G-VAR. À dispatcher en `MED/ledger` (catalogue) une fois la proposition
  acceptée, ou en `Closes #11556` si rejetée.

## Voir aussi

- Issue **#11556** (mandat user 2026-08-18 + body original de la proposition)
- Epic parent **#1210** (semantic-fleet, complémentaire et subordonné)
- `MyIA.AI.Notebooks/GenAI/Vibe-Coding/Claudish/README.md` (état du fork opérationnel 2026-08)
- `MyIA.AI.Notebooks/GenAI/Vibe-Coding/Claudish/docs/Claudish-Proxy.md` (référentiel technique)
- Phase 2 #11554 (compaction du harnais) — convergence naturelle si ce MCP est livré
- Commit `823e614` sur `jsboige/claudish` (recovery notices sur 3 condensations — la couture déjà là)
