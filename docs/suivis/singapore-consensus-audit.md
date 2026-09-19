# Audit du cluster CoursIA selon les 10 principes du Singapore Consensus

> Issue [#16757](https://github.com/jsboige/CoursIA/issues/16757) — Epic [#16741](https://github.com/jsboige/CoursIA/issues/16741), arc B « ouverte, responsable, prouvable, explicable ». Doc de cadrage + audit réel du harnais. Livrée par la lane `myia-po-2023:CoursIA`.

## Source et méthode

- **Grille source** : R11 — *The 2026 Singapore Consensus on Global AI Safety Research Priorities* (Casper et al., [arXiv:2608.14611](https://arxiv.org/abs/2608.14611)), **companion report on agentic risk management**, principes P1-P10 (pages 67-90 du companion). PDF local : `G:\Mon Drive\MyIA\IA\Bibliographie IA\XAI\2026 - Casper et al - ...pdf`, sha8 `134E9DA8` (vérifié).
- **Sujet de l'audit** : le cluster CoursIA tel qu'il tourne — coordinateur `ai-01`, workers `po-2023` à `po-2027`, lanes `machine × workspace`, dashboards RooSync, organes CI GitHub, règles `.claude/rules/` auto-chargées.
- **Ancrage** : chaque principe est confronté au harnais **réel** — règles citées par fichier, incidents documentés par numéro, pratiques vécues (cet audit est écrit depuis une lane worker, le jour même où la PR #16846 a traversé preflight, guards, DWELL et re-runs : la matière est firsthand).
- **États** : **RENFORCE** (pratique en place, preuve citée) · **PARTIEL** (pratique existante mais lacunaire) · **MANQUANT**.

## Récapitulatif

| # | Principe (companion) | Notre réalisation | État |
|---|---|---|---|
| P1 | Least Privilege | Harnais serré : deny-list, verrous de lane, secrets hors repo | PARTIEL |
| P2 | Traceable Identity | Lane `machine:workspace` + claims GitHub on-behalf-of | PARTIEL |
| P3 | Auditability | Dashboards append-only + archives, DM, verdicts forensiques | RENFORCE |
| P4 | Validated Deployment | PR gates, preflight adjoint, DWELL, discipline de review | RENFORCE |
| P5 | Adversarial Resilience | Red-team des organes (réévaluation d'audits ~60 % FP), anti-complaisance | PARTIEL |
| P6 | Multi-Agent Stability | Anti-collisions ([CLAIMED], guards CI) mais cascades vécues | PARTIEL |
| P7 | Runtime Assurance | Protocole anti-condensation (lectures complètes, DM, drift scans) | RENFORCE |
| P8 | Interruptibility | TaskStop/cron/DWELL, Stop & Repair, réversibilité git | RENFORCE |
| P9 | Legibility | Rapports [DONE], lignée de grains, harnais 3 tiers | RENFORCE |
| P10 | Human Oversight | Registre user-question, gouvernance l.87, autonomie graduée | RENFORCE |

---

## P1 — Least Privilege → harnais serré et verrous de lane

**Définition (companion)** : capacités bornées au minimum nécessaire à la tâche courante, restriction dynamique, isolation d'exécution.

**Mesuré chez nous** :
- **Deny-list outillage** : `EnterPlanMode`/`ExitPlanMode`/`AskUserQuestion`/`NotebookEdit` refusés par `settings.json` ; mode auto-approve pour le reste (harnais serré 15/09, #3657). Les questions bloquantes sont structurellement impossibles — le registre les remplace.
- **Verrous de lane** : un worker ne merge pas (`MergePullRequest` absent du compte), ne fait jamais `gh auth switch`, ne lance jamais `/coordinate` (leçon #1502), pas de force-push (`git-workflow.md`, incident fondateur 2026-03-13), pas de push direct sur `main`.
- **Isolation de travail** : arbre partagé sale → worktree isolé obligatoire (`git worktree add`), WIP d'autrui jamais stashé ni touché.
- **Secrets** : uniquement en fichiers gitignored (`.secrets/master.env`), jamais inline, jamais de valeurs sur les dashboards (noms de variables seulement).

**Écart** : nos agents tournent avec les permissions utilisateur complètes de leur machine hôte (pas d'isolation conteneur par lane) ; le scoping est **statique par lane** (règles durables) plus que **dynamique par tâche** — le companion demande un périmètre qui évolue avec la tâche. ÉTAT : **PARTIEL**.

## P2 — Traceable Identity → lane + claims on-behalf-of

**Définition** : identifiants uniques vérifiables, credentials scopés, time-limited, non transférables ; délégation « on-behalf-of » prouvée.

**Mesuré** :
- Chaque agent s'identifie par sa **lane** `machine:workspace` sur chaque post dashboard (champ author), chaque claim GitHub (`[CLAIMED] #N — lane <machine:workspace> — <ts UTC> — scope — paths:`), chaque tag de grain (`Grain: <TIER>/<GENRE> -- lane ...`).
- Commits : `Co-Authored-By` systématique ; PR : attribution de lane + trailer de génération.
- Le **claim GitHub est notre on-behalf-of** : l'agent n'agit jamais comme l'utilisateur, il déclare au nom de qui il travaille — exactement l'inversion demandée par l'OpenID Foundation citée par le companion (« agents should no longer act as if they are the user »).

**Écart** : l'identité GitHub reste un compte partagé du repo (pas de credential cryptographique distinct par agent ni par session) ; les credentials ne sont ni time-limited ni à ré-attestation. La traçabilité tient par **convention de prose** (tags, claims), pas par preuve cryptographique. ÉTAT : **PARTIEL**.

## P3 — Auditability → dashboards, DM, verdicts forensiques

**Définition** : décisions et actions reconstructibles et vérifiables ; logs, tamper-evidence, reconstruction post-incident.

**Mesuré** :
- **Dashboards RooSync** : intercom append-only avec auto-condensation à 92 % **et archivage** (rien ne disparaît sans trace) ; consultation en début de session **complète** (`section:"all"` obligatoire, leçon #2306 : lire `status` seul laisse les ASK invisibles).
- **DM inter-machines** : survive à la condensation — canal de décision (le steer coordinateur doit atteindre l'inbox, pas seulement le dashboard).
- **Verdicts forensiques normalisés** : `EXEC_PROVED` / `STRUCTURAL_ONLY` / `SUSPECT_REGRESSION` (H.5) parsés depuis le diff JSON des notebooks ; `LAST_REAL_EXEC` / `NEVER_EXECUTED_SINCE_<date>` (H.6 audit-history).
- **conversation_browser + indexation sémantique** : toute conversation passée est retrouvable (croisement technique/conversationnel/sémantique, protocole SDDD).

**Écart** : l'append-only est une **convention**, pas une preuve cryptographique (pas de chaînage de hachés à la AGENTSAFE) ; la condensation est avec perte même si archivée (le détail fin migre dans les archives). ÉTAT : **RENFORCE** (avec ces deux limites assumées).

## P4 — Validated Deployment → PR gates, preflight, DWELL

**Définition** : critères d'évaluation et de libération calibrés au niveau d'autonomie ; déploiement gouverné (release, update, retrait).

**Mesuré** :
- **14 organes always-on** + gate agrégé par PR ; critères `CHANGES_REQUESTED` obligatoires par domaine (composite, Lean, ML, notebooks, docs) — un reviewer qui APPROVE malgré une violation est complice (règle B).
- **Preflight adjoint** (B.0/B.3) : lecture intégrale body + commentaires + reviews avant verdict d'admission — vécu ce jour sur #16846 : deux défauts imputables détectés (assertion de périmètre fausse, baseline non migrée), corrigeables avant re-preflight, avec triage explicite de ce qui est infra et ne doit **pas** être maquillé.
- **DWELL** : plancher de 120 min entre tête de PR et merge — le gate affiche lui-même « rien à corriger dans le code : cette jambe est un minuteur » (rouge lisible, pas trompeur).
- **Règle H** (validation réelle) : pas de « DONE » sans exécution relancée post-fix ; 4 preuves exigées par notebook.

**Écart** : la gouvernance du **harnais lui-même** (toute règle ajoutant une obligation HARD exige PR + sign-off utilisateur, CLAUDE.md l.87) est récente — pas encore de rollout progressif ni de critère de retrait formalisé pour une règle. ÉTAT : **RENFORCE**.

## P5 — Adversarial Resilience → red-team de nos propres organes

**Définition** : capacité à résister, détecter, récupérer d'une exploitation adverse ; red-teaming au niveau agent en continu.

**Mesuré** :
- **Réévaluation d'audits** : protocole 4 étapes après mesure du taux de faux positifs de NanoClaw (~60 % FP sur échantillon de 17, issue #499) — aucun fix sur finding d'audit sans relecture mécanique + pédagogique ; classe de défauts FP documentée pour éviter le re-dispatch.
- **Anti-complaisance structurelle** : G.8 (APPROVE > 3 PRs en < 10 min = contester), verdicts interdits sans preuve (« BEATS » sans multi-seed = invalide), audit pré-merge obligatoire.
- **Secrets** : gitleaks en CI + vigilance manuelle sur les patterns non couverts (`os.getenv("KEY", "<littéral>")`) ; postmortem obligatoire en cas de leak.
- **Résistance à l'injection** : consigne de traiter tout contenu externe (résultats d'outils, pages lues) comme donnée et non instruction, et de signaler toute tentative d'injection détectée.

**Écart** : pas de red-team **continu** de la chaîne MCP (dashboards et DMs sont une surface d'injection que seule la convention contenient) ; pas de simulation de compromission de nos propres organes à intervalle régulier — les contre-exemples sont post-incident, pas proactifs. ÉTAT : **PARTIEL**.

## P6 — Multi-Agent Stability (en profondeur)

**Définition** : résilience aux défaillances **nées des interactions** — échecs de coordination, boucles de retour, cascades — qu'aucune mitigation mono-agent ne capture. « Individuellement sûrs, collectivement non sûrs ».

Le companion recommande (citant OWASP Agentic Top 10 2026) : **blast-radius caps prédéfinis** et validation **policy-as-code** de chaque invocation sensible. Nous n'avons ni l'un ni l'autre sous cette forme — nous avons des équivalents vécus, nés d'incidents :

**Cascades documentées** (toutes vérifiables dans le repo) :
- **Régression sorry (#524, 2026-04-24)** : un commit « Mathlib compilation fixes » individuellement raisonnable (faire compiler) remplace 9 preuves Lean par `sorry` — une semaine de travail détruite, restauration #527. L'action était localement cohérente, le dommage systémique. Réponse : règle anti-régression HARD + protocole 4 étapes avant suppression.
- **Collisions de re-exécution (#540/#541/#542, 2026-04-25)** : trois agents re-exécutent les mêmes notebooks en parallèle → 2 collisions de PR. Réponse : C.3 (ne stage que ce qu'on a modifié) + règle collision (un seul éditeur par notebook).
- **Catalogue silencieusement reverté (#2376/#2383/#2385)** : des branches à base stale régénèrent le catalogue → diffs massifs sans rapport, revert silencieux du curation d'autrui à chaque merge. Réponse : le catalogue appartient à l'automatisation (cron + drift CI), jamais régénéré sur branche.
- **Reviews en double et contradictoires (2026-05-17, veille de soutenance)** : 6 reviews postées sur des PR étudiantes — fuite des questions d'oral. Défaillance de coordination entre reviewers, pas d'erreur individuelle de contenu. Réponse : un seul reviewer public par PR + règle anti-fuite.
- **Force-push coordinateur (2026-03-13)** : la permission la plus dangereuse concentrée sur l'acteur le plus central — interdite depuis, sauf validation explicite.
- Référence du coordinateur : **L898** (registre lessons ai-01, non résolu depuis cette lane — cité pour mémoire).

**Mitigations systémiques en place** : `[CLAIMED]`/`[RELEASED]` (anti-double-claim avec preuve sha), un sujet par PR, guards de collision en CI, ancres disjointes pour merges commutatifs (#11690), cross-post à point de rendez-vous unique (un seul endroit fait foi), `always-pick-next` (une candidate bloquée n'arrête pas la lane), cap 3-IDLE, **un seul observateur par condition asynchrone**.

**Écart structurel** : le repo partagé est notre **moteur de corrélation** — tout le monde écrit dans le même arbre, les échecs se propagent par merge successifs. Le companion (Cube Sandbox, Anthropic Managed Agents) répond par isolation par agent et bornes numériques ; nous répondons par conventions et guards. Aucun plafond chiffré de rayon d'explosion (ex. « max N fichiers touchés par cycle et par lane ») n'est codé. ÉTAT : **PARTIEL** — le plus instructif des dix : nos pires incidents sont tous de cette classe.

## P7 — Runtime Assurance (en profondeur : la dérive d'état entre sessions)

**Définition** : l'état accumulé et les actions de l'agent continuent de satisfaire les propriétés validées au fil des changements d'environnement ; détection de dérive **indépendante du propre compte-rendu de l'agent**.

C'est exactement notre problème quotidien : un worker renaît toutes les 30 minutes avec un contexte vierge, sur un dashboard condensé, face à un arbre possiblement stale. Notre protocole anti-condensation :

- **Lecture complète en début de session** : `section:"all"` obligatoire (jamais `status` seul — #2306) ; inbox DM en premier (le DM survit à la condensation).
- **Anti-phantom** : le drift scan doit partir d'un **worktree frais** (88 % de faux positifs mesurés sur arbre partagé dirty) ; label `base-stale-14d` + rebase frais avant push.
- **Steer grondé firsthand** (Règle 5 coordinateur) : un steer rédigé depuis un status condensé qui hallucine est un **phantom** — le worker brûle ses cycles à le réfuter. Exigence : vérifier chaque grain avant dispatch (`gh issue view`, jamais depuis le condensé).
- **Leçons vécues de dérive** : « phantom-tool-name » (conclure qu'un outil n'existe pas alors qu'il vit sur une branche PR ouverte — règle: `git log --all --grep` avant d'affirmer une absence) ; mémoires horodatées avec avertissement de péremption, re-vérifiées avant usage.
- **L'ordonnanceur juge, pas l'agent** : le DWELL est un minuteur hors de la boucle de raisonnement de l'agent ; les checks CI relisent l'état live, pas l'auto-déclaratif (« b0: » auto-déclaré sera confronté à l'organe — #16838, en cours).

**Écart** : la détection de dérive repose sur la **discipline de relecture** (règles) plus que sur des mécanismes automatiques indépendants — l'équivalent des « auxiliary agents » d'IBM (surveillance parallèle au agent primaire) n'existe pas ; nos bots reviewers s'en approchent mais ne tournent qu'aux événements PR. ÉTAT : **RENFORCE** (protocole vécu et codifié, mécanisation partielle).

## P8 — Interruptibility → TaskStop, cron, DWELL, Stop & Repair

**Définition** : possibilité sûre de suspendre, rediriger, arrêter, **inverser** à tout instant ; mécanismes hors de portée de l'agent (non-tamperables) ; intervention graduée.

**Mesuré** :
- **Arrêt** : `TaskStop` (avec leçon vécue : tuer par ligne de commande pour éviter les orphelins de race) ; crons et monitors **session-only** — mourir avec la session, jamais de timer fantôme inter-session.
- **Redirection sans arrêt** : le DWELL inverse la charge — « c'est la candidate qui attend, pas la lane » ; `always-pick-next` reprend une autre tâche pendant qu'une condition asynchrone murit.
- **Graduation** : deny-list (interdit) → rate-limit (QC 10 appels/min flotte) → DWELL (temporisation) → re-run ciblé (`gh run rerun --failed`) → TaskStop. Équivalent vécu de la « containment ladder » d'IBM.
- **Inversion** : interdiction de force-push = toute l'histoire reste inversiblement manipulable (cherry-pick vers branche propre en cas de leak) ; Stop & Repair : jamais maquiller une sortie de cellule, corriger la cause et re-exécuter.
- **Hors de la boucle de l'agent** : le harnais (settings, CI, cron système) réside hors du raisonnement de l'agent — l'agent ne peut pas voter pour ses propres permissions.

**Écart** : pas d'**undo stack** agent (Google « agent undo stacks » : grouper les actions d'un agent en blocs inversibles d'une unité) — nos actions atomiques inversibles sont git-commits et PRs, mais un cycle de 2 h qui a side-tracké 3 dossiers ne se défait pas d'un geste. ÉTAT : **RENFORCE**.

## P9 — Legibility → [DONE], lignée de grains, harnais 3 tiers

**Définition** : le processus de décision représentable en termes accessibles ; l'auditability reconstruit, la legibility **fait comprendre**.

**Mesuré** :
- **Rapport [DONE]** formaté (livrable, PR#, résiduel) ; interdiction des états terminaux illisibles (« CLEAN_DONE 0-PR », « rien à faire ») — un état illisible est un échec de méthode, pas un état.
- **Lignée de grains** : `Grain: <TIER>/<GENRE> -- lane ... -- prev: <TIER>/<GENRE> #<PR>` — chaque livraison cite sa précédente : la chaîne complète des livraisons d'une lane se lit comme un journal.
- **3 tiers d'information** (harnais succinct / docs pérennes / dashboard éphémère) : le détail va où il se conserve, le harnais reste lisible.
- **Rouges lisibles** : le DWELL s'annonce comme minuteur ; un gate rouge avec subchecks verts est diagnostiqué comme DWELL, pas laissé ambigu (leçon pr-gate-dwell-red-legibility).
- **Arbitrage par pull** (#3656) : les questions à l'utilisateur vivent dans un registre consultable, rendu **en bloc** en fin de session — le plan lui-même reste dans un scratchpad dont seul le **chemin** est rendu.

**Écart** : la condensation des dashboards abîme rétrospectivement le « pourquoi » (le « quoi » est archivé) ; nos « Minimal Explanation Packet » (body de PR : grain + résumé + preuves + verdict SOTA) ne sont pas normalisés pour la lecture non-agent. ÉTAT : **RENFORCE**.

## P10 — Human Oversight → registre, gouvernance l.87, autonomie graduée

**Définition** : décisions humaines structurées à des points d'intervention définis, calibrées au risque/réversibilité ; **autonomie gagnée**, pas accordée par défaut.

**Mesuré** :
- **Registre user-question** (#3656) : l'utilisateur arbitre **par pull** — chaque entrée porte « ce qui est attendu du user » et « comment vérifier qu'elle est morte » ; une question répondue sort des ouvertes, sinon elle se représente au cycle suivant. Exemple vivant : arbitrage de seuil densité en attente (#16673, [ASK Emerjesse]).
- **Gouvernance l.87** : toute règle du harnais ajoutant une obligation HARD exige PR + sign-off utilisateur avant merge — le harnais ne s'auto-durcit pas.
- **Autonomie graduée vécue** : workers (exécutent) < coordinateur (merge via compte dédié, jamais le sien) < utilisateur (force-push, secrets, arbitrage). L'équivalent des quatre déclencheurs IMDA se lit dans nos règles : actions à enjeu (merge), irréversibles (force-push interdit), comportement aberrant (G.9 culture du doute avant verdict/close), limites définies par l'utilisateur (HARD stops, ex. Lean interdit sur po-2023).
- **Résistance à la fatigue d'approbation** : le companion cite (DeepMind Agent Traps) l'approval-fatigue comme vecteur d'attaque de l'humain — notre registre par pull est précisément la réponse structurelle : zéro interruption, restitution groupée, questions mortes retirées.

**Écart** : la charge de review humaine finale reste concentrée sur une personne (l'utilisateur) pour tout ce qui est subjectif — le batch review du registre atténue mais ne supprime pas le goulot. ÉTAT : **RENFORCE**.

---

## Lecture critique inverse

### Où le companion nous devance

1. **Undo stacks** (Google Cloud) : grouper les actions d'un agent en blocs inversibles d'une unité. Nos cycles ne se défont que granulairement (commit par commit).
2. **Blast-radius caps chiffrés** (OWASP Agentic Top 10) : plafonds prédéfinis testés en déploiement. Nos guards réagissent au diff réel, mais aucun plafond quantitatif par lane/cycle n'est posé d'avance.
3. **Policy-as-code par invocation** : chaque invocation d'outil sensible validée contre une règle formelle. Nos deny-lists sont statiques et globales, pas par contexte de tâche.
4. **Tamper-evidence cryptographique** (IBM AGENTSAFE : chaînage de preuves) : notre append-only est conventionnel.
5. **Credentials éphémères task-scopés** : notre identité de lane est durable et déclarative, non prouvée.
6. **Isolation d'exécution par agent** (conteneurs, OS-kernel par agent — Cube Sandbox) : nos lanes partagent des hôtes Windows avec les permissions utilisateur.
7. **Surveillance auxiliaire indépendante en continu** : nos bots reviewers ne s'éveillent qu'aux événements PR.

### Où nous devançons le companion

1. **DWELL** : temporiser le merge au profit de l'observabilité — le companion ne pose aucun équivalent du plancher 120 min.
2. **Lignée de grains** (`prev:` chaîné par livraison) : un journal de provenance des actions par lane, lisible en une ligne par PR.
3. **Vocabulaire forensique normalisé** (`EXEC_PROVED`/`STRUCTURAL_ONLY`/`SUSPECT_REGRESSION`, `LAST_REAL_EXEC`) : la preuve d'exécution est un type de donnée, pas une prose.
4. **Protocole anti-condensation** : le companion traite la dérive d'état comme préoccupation émergente (P7) ; nous l'avons vécue jusqu'à la codifier (lectures complètes, DM résilient, anti-phantom, re-vérification des mémoires).
5. **Arbitrage par pull** : le registre user-question avec entrées mortelles (champ « comment vérifier qu'elle est morte ») est plus opérationnel que le « human oversight » général du companion — il répond à l'approval-fatigue par construction.
6. **Dashboards auto-gouvernés** : auto-condensation à seuil mesuré avec archivage — la mémoire collective grandit sans accumulateur illimité.

## Recommandations (bornées)

Aucune de ces recommandations n'entre en vigueur sans PR dédiée + sign-off utilisateur (gouvernance l.87). Elles sont classées par coût décroissant :

1. **Cap de rayon d'explosion** (P6) : un plafond chiffré de fichiers touchés par PR existe déjà (G.4 : 15 fichiers) — l'étendre à un plafond **par cycle et par lane** (ex. 3 PRs en flight max) formaliserait ce que G.5 dit déjà en creux.
2. **Red-team périodique des organes** (P5) : une issue récurrente mensuelle « injecter un FP connu et vérifier la détection » transformerait l'audit-reassessment post-incident en contrôle proactif.
3. **Journal de why anti-condensation** (P9) : condenser en préservant une ligne de motif par entrée archivée.

## Voir aussi

- Règles sources : `.claude/rules/` (`git-workflow.md`, `pr-review-discipline.md`, `coordinator-discipline.md`, `proactive-coordination.md`, `user-blocker-signaling.md`, `secrets-hygiene.md`, `harness-hygiene.md`, `sota-not-workaround.md`, `audit-reassessment.md`, `model-delegation.md`)
- Détails incidents : `docs/reference/regles-vigilance-detail.md`, `docs/reference/regles-validation-detail.md`, `docs/reference/secrets-and-coord-detail.md`
- Epic : [#16741](https://github.com/jsboige/CoursIA/issues/16741) (corpus Tegmark) ; voisines d'arc : #16754 (Backdoor Code rejoué), #16756 (boussole interp→preuve), #16759 (MUH/Tegmark-Schmidhuber)
