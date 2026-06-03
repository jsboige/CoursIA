# Regles vigilance G.1-G.9 — anti-complaisance (detail)

Resume operationnel : CLAUDE.md section G.

S'applique a **tous les agents** (executants, coordinateur, reviewers humains et bots). Ces regles sont permanentes : elles ne se relachent ni avec la pression deadline, ni avec la confiance accumulee, ni avec un APPROVED bot.

---

## G.1 — Verifier les claims contre le code, pas contre les rapports

Avant de croire qu'un feature manque, qu'une API n'existe pas, qu'un fichier est introuvable, qu'un agent X "n'est pas connecte" : `grep` / `Glob` / `Read` le codebase. Affirmer une absence sans verification = source #1 de faux diagnostics qui se propagent en cascade.

Avant de relayer un diagnostic technique d'un autre agent dans un dispatch ou un bilan : exiger la preuve (ligne de code citee, log d'erreur copie, output compilateur). Pas de propagation par confiance. Si le diagnostic se revele faux apres relais, le coordinateur partage la responsabilite.

**Incident 2026-05-07** : agent a affirme "MultiAgentSorryProver doesn't exist" pendant 3 sessions, alors qu'il etait fully implemented dans `prover/agents.py`, `prover/workflow.py`, `prover/tools.py`, `prover/provers.py`. Cf [.claude/rules/verify-before-claiming.md](../.claude/rules/verify-before-claiming.md).

**Incident 2026-05-24 (#274)** : ai-01 a ferme #274 (ComfyUI-RookieUI) sur un verdict "NO-GO (scope mismatch)" repris d'un audit po-2023 anterieur, SANS relire le body de l'issue. Or l'audit evaluait RookieUI contre une exigence "UI d'edition video" que #274 n'a JAMAIS formulee (#274 demande une sidebar generation d'IMAGE style A1111) — issue mal attribuee, l'audit confondait #274 avec une autre. Pire, la close a AJOUTE un rationale fabrique ("overlaps Forge/SDNext, no pedagogical value") contredisant le body. Detecte par le user ("Pure hallucination, tu as lu l'issue ?"), reverte (reopen + rétractation). **Lecon (G.1 + G.9) : un verdict est un claim comme un autre — son label ne dispense pas de relire la source qu'il pretend juger. Fermer une issue sur un label sans confronter son raisonnement au body = hallucination par procuration.**

---

## G.2 — Metriques honnetes, pas binaires

`sorry count = 0` n'a aucune valeur sans `lake build SUCCESS` post-modification. Un theoreme supprime, un identifiant inexistant injecte, une preuve qui ne compile pas = sorry count peut etre 0 ET le port casse.

**Pour Lean / Coq / Agda, trois preuves obligatoires dans le body PR** :
1. `grep -c sorry` avant/apres
2. `lake build` SUCCESS log (lien CI ou commit local prouvable)
3. Proof integrity check SUCCESS (axiom check)

**Pour ML/trading** : `BEATS majority` n'a aucune valeur sur 1 seed × 1 fold. Multi-seed >=4 + walk-forward 5-fold + edge >= 2 sigma cross-seed + transaction costs documentes ou le verdict est **invalide** (pas "promising", pas "encouraging" — invalide).

**Pour notebooks** : `Papermill SUCCESS` en mot-cle ne prouve rien. Coller les premieres lignes des outputs reels.

**Pour services ops** : `200 OK` sur /health ne prouve pas que le service fait son travail. Test E2E reproductible obligatoire (curl + verification du payload retourne).

---

## G.3 — Pas de "DONE" sur progres marginal

Si N tracks dispatchees → M < N livrees : rapporter `M/N livrees, (N-M) restantes : <liste>`. Pas de `Cycle X complete` quand Track 1 (le HIGH) n'est pas fait et 7 LOW le sont.

Si sorry count passe de N a N-1 : rapporter `1/N elimine, (N-1) restants`. Pas de "DONE Voting".

Si fix corrige 5/7 cellules : rapporter `5/7, 2 restantes : <liste>`. Pas de "DONE notebook".

**Pourcentage explicite ou liste residuelle obligatoires.**

---

## G.4 — Composites trop larges = split obligatoire

Une PR qui depasse l'un de ces seuils doit etre fractionnee en PRs coherentes par feature avant merge :

| Metrique | Seuil "split required" |
|----------|------------------------|
| `additions + deletions` | > 3000 lignes hors notebooks |
| `changedFiles` | > 15 fichiers (hors `_output.ipynb` et donnees) |
| Features distinctes dans `## Summary` | > 4 |
| Domaines (ML + Lean + GenAI melanges) | > 1 |

Le coordinateur **conteste** (commentaire CHANGES_REQUESTED) au lieu de merger. Le reviewer bot DOIT poster CHANGES_REQUESTED.

---

## G.5 — Shopping cart interdit

Un dispatch > 5 tracks par agent encourage le shopping (LOW d'abord, HIGH reportes). Cibler **2 deep tracks max par agent** par cycle, avec **criteres de sortie verifiables** (compile log, multi-seed verdict, build SUCCESS, healthcheck E2E). Pas de Track LOW pour combler.

Si un agent finit ses 2 tracks avant la coord finale : il attend, il n'invente pas une 3e mission. Laisser les LOW au cycle suivant.

---

## G.6 — Coordinateur : audit avant merge cascade

Avant un batch de merges : lire les bodies, verifier au moins **un claim** de chaque PR contre le diff reel. Pas de "5 PRs APPROVED par bot, je merge en 5 minutes".

Si une PR a 0 review humain ET le bot APPROVE : c'est le **minimum** acceptable, mais le coordinateur reste responsable du contenu. Si le claim est faux, c'est le merge qui est en cause, pas le bot.

**Lire le diff > lire le titre. Lire le body > lire le mergeStateStatus. Verifier le claim > faire confiance au rapport.**

---

## G.7 — Stagnation cross-cycle = escalade

Si un blocage technique persiste sur N cycles consecutifs (ex: rebase qui ne se fait pas, sorry qui ne baisse pas, service qui reste DOWN) : le coordinateur **n'attend pas un cycle de plus**. Il prend l'action lui-meme (rebase, fix, escalade user) ou ferme la PR/issue.

Si un agent rapporte "BLOCKED" sans preuve concrete (compile log, error message, screenshot) : ne pas accepter. Demander la preuve avant de re-dispatcher.

---

## G.8 — Bots reviewers : pas de rubber-stamp

Pattern interdit : APPROVE > 3 PRs en < 10 minutes. Probable rubber-stamp. Le coordinateur conteste systematiquement et bloque les PRs jusqu'a re-review serieuse.

Pattern interdit : APPROVED sur composite > 3000 lignes / 15 fichiers. Le bot DOIT detecter et poster CHANGES_REQUESTED.

Pattern interdit : APPROVED sur micro PR docs < 20 lignes isolee. Le bot DOIT detecter et exiger groupement.

Cf [.claude/rules/pr-review-discipline.md](../.claude/rules/pr-review-discipline.md) pour la grille complete.

---

## G.9 — Culture du doute

Avant d'envoyer un rapport ou de merger : se demander explicitement "est-ce que je pourrais avoir tort ?". Si oui, verifier. Une affirmation surprenante (ex: "le multi-agent prover existe deja") merite verification avant relais.

Avant d'accepter une "breakthrough" rapportee par un agent (sorry 5→0, BEATS magique, service restaure en 5min) : reproduire au moins 1 element du resultat. Les vrais succes resistent a la verification ; les faux positifs s'effondrent.

---

## References connexes

- [.claude/rules/verify-before-claiming.md](../.claude/rules/verify-before-claiming.md) — Verifier avant de claimer un feature absent
- [.claude/rules/anti-regression.md](../.claude/rules/anti-regression.md) — Anti-regression code metier
- [.claude/rules/pr-review-discipline.md](../.claude/rules/pr-review-discipline.md) — Discipline review PR
- [.claude/rules/audit-reassessment.md](../.claude/rules/audit-reassessment.md) — Verifier audit avant fix
- [docs/regles-validation-detail.md](regles-validation-detail.md) — Regles H.1-H.7 validation notebooks
