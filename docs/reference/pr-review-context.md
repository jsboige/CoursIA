# PR Review Discipline — Contexte, incident, anti-patterns

Document de référence détaillant les seuils auto-loaded de [.claude/rules/pr-review-discipline.md](../../.claude/rules/pr-review-discipline.md).

## Contexte (incident 2026-05-08)

Règle créée 2026-05-08 après constat user "vous êtes tous trop complaisants, on n'avance pas". Audit cycles 5-7 :
- 9/10 PRs nuit du 7→8 APPROVED par clusterManager-Myia sans contestation
- #801 mega-composite 7183 lignes / 41 files
- #806 +2 lignes
- #807 +46 lignes doc
- #791 du 7/05 +3561/-3543 prover refactor caché derrière "shapley sorry 2→1"

Cette rule s'applique à **tous les reviewers**, humains et bots (clusterManager-Myia, jsboige self-bot, ai-01 coordinateur).

## Anti-pattern : APPROVED en lot batch

Si un reviewer APPROVE >3 PRs dans une fenêtre <10 minutes : flag automatique, probable rubber-stamp.

## Mention explicite des bots

**@clusterManager-Myia** : ces critères s'appliquent en priorité. Première ligne de défense. Si APPROVE une PR violant un des critères, le coordinateur ai-01 conteste explicitement et la PR est bloquée jusqu'au split / fix.

**@jsboige (self-review bot)** : self-approval sans valeur GitHub. Reste en COMMENTED + signale les violations dans le body.

## Workflow ai-01 (coordinateur)

Avant tout merge cascade, ai-01 lit :
1. `gh pr view <N> --json files,additions,deletions,body,reviews` (pas juste `mergeStateStatus`)
2. Vérifie chacun des critères A-G applicables (cf rule)
3. Si violation : commente sur la PR (`gh pr comment <N>`) avec demande explicite (split, multi-seed, sorry-count, etc.) + ne merge pas
4. Si conforme : merge avec mention dans le bilan dashboard

Pas de merge en parallèle 5 PRs sans avoir lu les 5 bodies.

## Détails par critère

### Critère D : preuve d'exécution notebook
- Pas de validation visuelle (PPTX/Slidev) jamais "OK" sur "j'ai screenshotté". Liens vers screenshots obligatoires.
- Sortie `papermill` ou kernel exec — pas juste "Papermill SUCCESS" en mot-clé, coller les premières lignes des outputs.

### Critère E : anti-pattern visé
PRs micro qui inflate le compteur "PRs livrées" sans valeur réelle (#806 +2 lignes, #807 +46 lignes doc seul). Doc/README/CLAUDE.md/rules :
- Single PR < 50 lignes : refuser, exiger groupement avec autre PR du même cycle
- Single PR < 20 lignes : refuser systématiquement (commit direct sur main si trivial)
- Multiple READMEs touchés sans cohérence cross-series : refuser, exiger un seul focus

### Liens internes

- Criteres multi-seed (ML) : cf [.claude/rules/pr-review-discipline.md](../../.claude/rules/pr-review-discipline.md) section C
- Bot reviews pour dispatch : cf [.claude/rules/pr-review-discipline.md](../../.claude/rules/pr-review-discipline.md) section G
- Review state filter : cf [.claude/rules/verify-before-claiming.md](../../.claude/rules/verify-before-claiming.md)
- [.claude/rules/anti-regression.md](../../.claude/rules/anti-regression.md)
- CLAUDE.md section B (Reviews PR 5 points obligatoires)

---

## Incidents fondateurs des critères A-H

Détail déporté de [`.claude/rules/pr-review-discipline.md`](../../.claude/rules/pr-review-discipline.md).

### B.3 — le gate `proof-integrity` était structurellement aveugle au `native_decide` (corrigé #8740, issue #8738)

Le parser lisait la sortie de `#print axioms` **ligne par ligne**. Les noms d'axiomes natifs (`<theoreme>._native.native_decide.ax_1_1`, ~58 caractères) débordent la largeur de pretty-print de Lean et forcent un retour à la ligne — la déclaration entière était alors **silencieusement ignorée**.

Le gate était donc aveugle à la classe **exactement la plus dangereuse** : `native_decide` réduit par le noyau natif *sans preuve*, ce qui vide le théorème de son contenu tout en affichant un vert. **Conséquence de review : un `proof-integrity SUCCESS` daté d'avant le 2026-07-28 ne prouve rien sur `native_decide`** — ne pas l'accepter comme preuve.

Reproduction locale du check :

```bash
cd agent_tests/
python -c "from lean_server import LeanVerifier; print(LeanVerifier('<lake-root>').check_axioms('<Module>', fail_on_sorry=True))"
```

### B.3 — pourquoi la whitelist interdit les wildcards

`allow-axioms` liste les axiomes tolérés **un par un**. C'est un mécanisme à cliquet : tout nouveau `native_decide` introduit produit un nom **absent de la liste**, donc le gate rougit. Un motif générique (`*native_decide*`) détruirait cette propriété — le gate ne pourrait plus jamais rougir sur la classe qu'il est censé attraper, et un gate qui ne peut plus rougir n'est pas un gate.

### C — les trois contre-exemples ML inscrits (σ sans DM, DM sur perte symétrique, DM linéaire = biais)

**(1) `edge_sigma` seul ne prouve rien.** `edge_sigma = +19.97σ` avec `DM p = 0.236` n'est **pas** un BEATS (`validate_xrp_dt_holdout.py`, holdout_fresh du 06/08). Le dénominateur de `edge_sigma` mesure la dispersion **inter-seeds** — c'est-à-dire la *reproductibilité de la procédure*, pas la *significativité de l'edge*. σ croît donc sans borne quand les seeds s'accordent, que l'edge soit réel ou non. Un σ élevé sans DM est un flag « noise », jamais une preuve.

**(2) Le test DM porte sur une perte de précision ; `linear` est un contrôle de biais.** `mse` et `mae` sont **symétriques** (`(-e)² = e²`, `|-e| = |e|`) : elles rendent des `dm_stat` / `p_value` **bit-identiques** pour une série et son exact opposé — correct : deux prévisions opposées sont également précises, le DM dit exactement cela. La perte linéaire signée (`loss_fn="linear"`) distingue le signe mais mesure le **biais** (`d_mean = mean(e_a) − mean(e_b) = biais_a − biais_b`), pas la précision : aveugle à la dispersion, elle déclare « BEATEN » un modèle strictement plus précis face à une baseline plus biaisée (#10956, #10961 CE1). Elle ne porte pas la jambe DM de la conjonction §C ; elle la complète comme **rapport de biais obligatoire** par modèle.

Mesure d'intégration (#10232), série gagnante `e` vs son opposé `-e` contre baseline nulle :

| `loss_fn` | `dm_stat` pour `e` | `dm_stat` pour `-e` | Discriminant ? |
|---|---|---|---|
| `mse` | 10.0754 | 10.0754 | **non** |
| `linear` | −0.1771 | +0.1771 | **oui** (signes opposés) |

Le tableau montre les deux instruments et leur angle mort : `mse`/`mae` mesurent la précision (insensibles au signe), `linear` distingue le signe mais mesure le biais. La jambe DM de §C porte donc sur une perte de précision ; `linear` reste disponible comme contrôle de biais (détection de sous/sur-prévision). Pin de régression : `test_dm.py::test_linear_loss_distinguishes_opposite_series` (valide — signes opposés = déclaration de biais, pas de précision).

**Instance fondatrice du rapport de biais par modèle — #10938.** Le point (7) de la règle (`mean(e)` signé ou biais OOS, modèle ET baseline, dans le body) est né d'un `har_bias_oos = −0.227` (#10938) non déclaré, découvert **après** qu'une lecture avait été construite sur l'edge qu'il portait : c'est précisément le contrôle que le rapport de biais par modèle aurait fait apparaître avant. Un edge porté par le biais (pas par la précision) se déclare comme tel.

### D.5 — #8479 MusicGen : l'alignement qui enshrine un nombre périssable

Notebook MusicGen 02-3 : le RTF documenté `0.5-2x` a été « aligné » en `0.21-0.24x` **sur un run non-optimisé**, alors qu'une re-exécution Stop-&-Repair était **déjà due** sur ce notebook (cellule cassée).

Deux fautes cumulées : (a) la valeur ré-alignée est un **nombre de perf** sur un notebook **re-exécutable localement** — elle devait venir d'une re-exec fraîche, pas d'un markdown-align sur l'ancien output ; (b) une re-exec étant déjà due, l'alignement devait y être **foldé**, pas livré en PR markdown séparée. Enshriner un nombre qui changera au prochain passage kernel *est* la dérive que C.4 interdit.

### D — #5214 : l'advisory .NET lu comme un permis d'outputs vides

PRs Tweety-3 C# (#5194 / #5199 / #5202) mergées avec des notebooks à `execution_count: null` **et** `outputs: []`, au motif de l'advisory .NET.

L'advisory dit que la **CI** ne peut pas Papermill-exécuter du .NET Interactive (pas de kernel en CI). Il ne dit rien sur l'exécution **locale**, qui est disponible sur chaque worker (`dotnet-interactive`, règle F). Une cellule .NET committée doit donc porter `execution_count != null` = preuve d'exécution locale. `scripts/notebook_tools/validate_pr_notebooks.py` FAIL désormais dessus (verdict H.5 `STRUCTURAL_ONLY`), et ne tolère `null` que là où l'exécution locale est réellement impossible : QC Cloud (besoin QuantBook), Lean (advisory propre).

### E — #5345 Probas : l'intro corrigée, la liste laissée périmée

Plainte user 2026-07-04. La PR corrigeait l'intro et les compteurs d'un README de série tout en laissant, cent lignes plus bas, une **liste de notebooks PyMC obsolète** et un **arbre de structure périmé**.

D'où la clause « audit fichier ENTIER » : le format slim `+5/−5` du rollout README ne dispense pas de l'audit — il le **plafonne à tort**. Quand une série a subi un changement structurel, la passe DOIT être fichier-entier.

Audit associé au même mandat : Tweety / GameTheory / Search = **stale-body sévère** ; SymbolicLearning / SemanticWeb / SmartContracts = ciblé ; Sudoku = trivial.

### Émission du verdict — instance fondatrice et mesure (#14682)

**#14658** : réserve qualifiée « le seul point bloquant pour un LGTM plein », posée en **prose française sans marqueur** → invisible à l'organe B.0 (`scripts/check_unaddressed_nits.py`, `CONCERN_MARKERS`), `rc=0`, merge passé.

**Ne pas élargir `CONCERN_MARKERS`** — mesure #14682, scan de 80 PRs mergées : un filet à mots de prose (« bloquant », « à corriger », « est faux ») **sur-accuse d'un facteur 5** (4 détections sur 5 = de la prose qui *décrit* un blocage de job ou de garde, pas qui *pose* une réserve). Le contrat est côté **émission** : le reviewer pose `CHANGES_REQUESTED` / `[Hermes] COMMENT_WITH_CONCERNS` / 🟡 / 🔴, il ne rédige pas « il faudrait corriger » en prose libre.

### Répondre à une réserve — la forme sûre et les formes pièges (#17071)

Symétrique du contrat ci-dessus, et non documenté jusqu'ici : savoir **poser** un verdict ne dit pas comment y **répondre** sans en **créer** un. Une réponse d'auteur qui **cite** le token redevient elle-même une réserve B.0 — la PR, déjà réparée, reste bloquée **à fond réparé** : une lane ne peut pas se dé-bloquer en répondant.

Table de vérité mesurée le 2026-09-21 sur l'organe lui-même (`classify(author, body)` + `_strip_quoted` + `_strip_mentioned_verdicts`, auteur = login de lane non-bot) :

| Forme répondue | `classify()` | Mécanisme |
|---|---|---|
| `CONCERNS` nu en prose | `BOT-CONCERN` | marqueur vivant (`CONCERN_MARKERS`), casse-sensible |
| `CHANGES_REQUESTED` nu | `BOT-CONCERN` | marqueur vivant |
| token **en gras** (seul ou après `Verdict :`) | `BOT-CONCERN` | `BLOCK_VERDICTS = ("**BLOCKED**", "BLOCKED  PR")` — le gras **est** la forme d'émission |
| `Verdict : <token>` | `BOT-CONCERN` | les deux-points font du méta-nom un **label d'émission** |
| token encagé (backticks, `« »`, apostrophes, bloc de code, gras **+** backticks) | `None` | `_strip_quoted` (`_QUOTED_RANGES`) neutralise la plage citée |
| `verdict <token>` **sans** deux-points | `None` | `_MENTION_VERDICT_INLINE` : `verdict(?![:.])\s+\w+` = position de **mention** |
| narration de levée | `None` | registre `LIFT_MARKERS` |
| token de blocage **nu** | `None` | **résidu assumé** — le matcher éviterait le tag de protocole de lane `[BLOCKED] …` et la négation « n'est plus BLOCKED » |

**La forme sûre** : encager **le token lui-même** (backticks, guillemets, apostrophes, bloc de code) — ou le nommer en position de **mention** (`suite à ta réserve`, `verdict X` **sans** deux-points). Le corollaire est ce qui se rate le plus : encager un mot **voisin** ne protège rien. Dans la forme réellement mesurée, le seul backtick de la phrase entourait un autre mot (`b0`) et **pas** le token, écrit en gras nu — le token est resté `BOT-CONCERN`.

**Deux pièges adjacents.** (1) Ne pas compter sur le token de blocage **nu** : c'est un faux négatif **choisi**, pas un filet — il tient à un contrat explicite de l'organe. (2) Ne pas confondre **disponible** et **honnête** : la voie de levée « issue de suivi » n'a de sens que s'il reste un **résidu** à tracer ; ouvrir une issue creuse pour éteindre une réserve morte est une falsification, pas une levée.

**Contrôle positif de la recommandation (4/4).** Les formes conseillées ci-dessus ne sont pas seulement réputées muettes, elles le sont mesurément : la phrase même que citait la piste correspondante (« Réponse à ta réserve du head … : les deux blockers sont traités ») rend `None`, la variante à token encagé rend `None`, et la position de mention (`suite à ton verdict <token>` **sans** deux-points) rend `None`. Le contrôle **négatif** tient aussi : une réponse qui **réitère** la réserve (`Re: … le <token> tient`) rend `BOT-CONCERN` — la forme sûre ne rend donc pas l'organe aveugle à une réserve réaffirmée, ce qui est précisément le risque qui écartait l'élargissement aux formes d'adresse.

**Mécanique — trois couches, dans cet ordre.** Une forme répondue traverse trois filtres avant que `classify()` ne rende un verdict ; savoir lequel traite quoi évite de « corriger » la mauvaise couche :

1. `_strip_quoted` — la plage **citée** (backticks, guillemets typographiques, apostrophes, bloc de code) est remplacée par une espace. C'est la couche qui **encage**, et elle n'agit que sur la plage exacte : d'où le corollaire « encager le voisin ne protège rien ».
2. `_strip_mentioned_verdicts` — les **positions de mention**, dont `_MENTION_VERDICT_INLINE` (le méta-nom **ne doit pas** être suivi de `:` ou `.`). C'est la couche qui sépare `verdict X` de `Verdict : X`.
3. `has_live_marker` sur `CONCERN_MARKERS` (concaténé avec `BLOCK_VERDICTS`, `APPROVAL_REFUSALS` et les glyphes de sévérité) — chaque occurrence **survivante** est re-testée contre sa fenêtre de citation (`_is_cited`, bornée au **paragraphe**, et qui ne lit que le **dernier mot** placé devant le token).

Les **symboles** sont cités plutôt que des numéros de ligne : un numéro de ligne périmé dans une doc durable est exactement la classe d'incident que le dépôt a déjà consignée (critère D.5). Le contrat d'**émission** (#14682) et cette forme de **réponse** sont les deux faces du même problème, et élargir le filet reste écarté pour la raison mesurée là-bas — la voie sûre est de rédiger la réponse autrement, pas d'ajouter une exception au scanner.

**Corollaire opérationnel — nommer le token sans se créer de réserve.** Trois surfaces, trois régimes, et les confondre est la cause des instances mesurées :

- un **commentaire** ou une **review** est classé par `classify()` : la forme sûre ci-dessus s'y applique, sans exception ;
- un **body de PR** n'est pas lu par cet organe (il lit commentaires et reviews) — mais il est lu par d'autres gardes, donc y **cager** le token reste la bonne habitude, et pour la même raison : un token nu y est un token qu'un futur organe pourra lire comme émis ;
- le **dossier `[ADJOINT PREFLIGHT]`** est le seul endroit conçu pour qu'une mesure **nomme** le token sans se créer de réserve : `_strip_adjoint_dossier` retire les blocs bien délimités, et un commentaire qui **ouvre** sur un bloc est un dossier **dans son intégralité** (#17065) — la prose qui **suit** le marqueur fermant est lue comme la **narrative** du dossier, pas comme des remarques. Deux bornes, mesurées au même moment : la prose qui **précède** le bloc reste lue normalement, et un bloc **malformé** (ouvrant sans fermant) n'inertit rien.

**Pourquoi la voie sûre plutôt qu'un filet plus large.** L'organe assume explicitement l'asymétrie : *la sous-accusation coûte un merge, la sur-accusation coûte une relecture* — c'est ce qui justifie les faux négatifs **choisis** (token de blocage nu, émission sans gras) et ce qui rend toute exception de prose plus coûteuse que le piège qu'elle ferme. Une lane n'a donc pas besoin que le scanner reconnaisse sa réponse : elle a besoin de savoir **quelle forme** est muette, ce que la table ci-dessus donne.

**Ce que cette section ne tranche pas (#17071).** Elle documente la **forme sûre** et la mesure qui la fonde — elle ne modifie **aucune ligne d'organe**. Les trois pistes de #17071 restent ouvertes : (1) étendre `CITERS` aux formes d'adresse (`Re:`, `@login`, « au head <sha> ») ; (2) cette documentation ; (3) la résolution par thread inline. La piste 1 reste l'arbitrage le plus lourd, pour la raison déjà écrite dans l'issue — écarter le token derrière un `Re:` écarterait aussi les vraies réponses **réitérant** la réserve, et le contrôle négatif ci-dessus (réponse qui réitère → `BOT-CONCERN`) mesure cette borne.

**Instance fondatrice (mesurée 2/2).** Les deux dossiers `[ADJOINT PREFLIGHT]` du 2026-09-21 (#16098, #16196) : mes propres commentaires de mesure — dont la prose citait le token en gras — ont été classés `BOT-CONCERN` **2/2**, le geste de mesure **ajoutant** une ligne à ce qu'il mesurait. Remède appliqué : la mesure vit dans le champ `b0:` du dossier, **jamais** dans un commentaire de prose à côté. Le cas **#16441** (une réponse d'adresse citant la réserve traitée) est l'instance qui a ouvert #17071 ; il est **rapporté par l'issue** avec sa propre reproduction (`python scripts/check_unaddressed_nits.py 16441 --json`) et n'est pas reproduit par la table ci-dessus, dont les lignes sont des formes synthétiques.

### B.1 — pourquoi pas `grep -c sorry` (mesure 2026-08-14)

Sur les 21 lakes : **484 faux `sorry` pour 21 réels (23×)** — `grep -c sorry` compte la prose (docstrings, `-- commentaires`, feuilles de route). **9 lakes à 0 réel** affichent des comptes naïfs positifs ; ex. `grothendieck_lean` : 68 naïfs, 0 réel — un reviewer appliquant `grep` à la lettre exigerait la justification de 68 `sorry` qui n'existent pas. L'instrument : `python scripts/lean/count_code_sorry.py --json`, champ `distinct_code_sorry` (la même mesure que le gate CI `sorry-filter-mode: real` de `lean-axiom.yml`).

### D.6 — récurrences du ratchet `Output-failure`

- #13517 : PR #13036 (LDA) — bannières `TOOL_FAILURE 0 → 21`, `MACHINE_PATH 0 → 14`, **approuvée par Hermes** alors que le garde rend `rc=1`.
- #3473 (juin 2026) : famille ~15 filles de bannières d'échec passées sous la détection d'erreurs Python classique.
- #11693 (18/08) et #11685 : remplacements de rendus SVG/figures par des bannières « program is not installed ».

## Incident fondateur B.0 — PR #10761 (récit déporté de CLAUDE.md, 2026-08-21)

**Incident fondateur — PR #10761** : mergée le 2026-08-14T04:15Z sous `myia-ai-01` malgré 2 nits user du 2026-08-13T11:07 (**17 h avant**) et une review Hermes `COMMENT_WITH_CONCERNS` confirmant ces 2 nits + 3 points neufs. `mergeStateStatus: CLEAN`, `reviews[].state: COMMENTED` : les deux champs qu'un merge-gate lit d'ordinaire étaient verts, et le notebook a été mergé en attribuant à tort le théorème de Sendov à T. Tao (la preuve est de **Lech Mazur** ; Tao en signe la digestion, il l'écrit lui-même). Epic de reprise : **#11044**.

> **Cette attribution est corrigée depuis** — `e1ad7868a` (PR #11065, Epic #11044) : Lean-19 et Lean-20 portent désormais « preuve L. Mazur, digestion T. Tao ». Le récit ci-dessus reste le fondement de la règle — le merge fautif a bien eu lieu — mais l'état du dépôt n'est plus celui-là, et ce fichier est chargé par chaque agent à chaque session : y laisser un présent périmé, dans la règle même qui exige de vérifier ses affirmations, apprend l'inverse de ce qu'elle demande. **La classe de défaut, elle, reste vivante** (#11110 Lidman, #11127 Gill) : une citation se vérifie contre la source, et *après* avoir établi qu'une référence est fausse, il reste à lire **qui a signé** la vraie avant de conclure sur l'attribution — « l'article n'existe pas » et « l'attribution est fausse » sont deux propositions distinctes.

## Levée B.0 — les instances qui fondent « un AUTEUR et une HEURE » (récits déportés de CLAUDE.md, 2026-09-13)

`CLAUDE.md` §B.0 pose la prescription — *une levée porte un auteur et une heure ; sans les deux, ce n'est pas une levée* — et renvoie ici pour les faits qui l'ont fait écrire. Les deux instances ne se recouvrent pas : la première est un défaut d'**auteur**, la seconde un défaut d'**heure**.

### Qui lève — #12798 : la réserve d'un tiers éteinte par l'auteur de la PR

Une review `[Hermes] COMMENT_WITH_CONCERNS` a été portée comme levée par une **phrase de l'auteur de la PR lui-même**. Se lever soi-même une réserve posée par un tiers n'est pas y répondre : c'est la **déclarer** répondue — et `reviews[].state` ne distingue pas les deux cas.

Ce que la réserve visait était réel : le livrable committé était un **stub rendant `Cle presente False`**, sous un body annonçant `SOTA-OK`. La phrase de levée n'a rien corrigé ni argumenté ; elle a seulement fermé le canal par lequel le défaut se voyait. D'où la clause : **l'auteur d'une PR ne lève pas la réserve d'un tiers**, quelle que soit la qualité de sa réponse. Ce qui la lève est le tiers lui-même, un thread inline résolu, ou une issue de suivi nommée avant le merge.

### Quand lève — #12347 : la levée postée 32 s APRÈS le merge

Chronologie mesurée, sur une seule journée :

| Heure (UTC) | Événement |
|---|---|
| 17:03:20Z | `CHANGES_REQUESTED` posée |
| 21:23:56Z | `gh pr merge` — la réserve est encore vivante |
| **21:24:28Z** | levée postée — **32 s après le merge**, et annotée comme telle par son auteur |

Aucune ignorance n'est en cause : l'auteur de la levée savait qu'il écrivait après le merge, et l'a écrit. Rien ne contraignait l'ordre — c'est précisément ce que la règle contraint désormais. **Un commentaire de merge est un compte-rendu, jamais une porte** : ce qui lève doit exister *avant* `gh pr merge`, sans quoi la levée documente le merge au lieu de l'autoriser.

### Ce qu'un commit ne lève pas — #10761, le rebase muet

Sur #10761 (récit complet ci-dessus), le « traitement » des deux nits du 2026-08-13T11:07 fut un **rebase à 19:41** qui n'adressait ni l'un ni l'autre. Un push muet est **indiscernable d'un push qui répond** : le diff ne dit pas quelle remarque il prétend traiter, et le compteur de commits postérieurs à une review ne mesure donc rien. Ce qui lève une remarque est **une phrase**, pas un SHA.

### Où lève — #16780 : le waiver par pointeur vers un fichier local

Sur #16670, un commentaire fut posté dont le **corps entier** était `@C:\Users\jsboi\AppData\Local\Temp/a16670.md` — la trace visible de `gh ... --body "@$TEMP/a16670.md"` là où `--body-file` était voulu (`gh` n'expande pas `@file`, il poste la chaîne littérale). Le harnais de merge lut ce corps comme un **waiver DWELL L3** et nourrit une escalade de merge avec. Mais le fichier visé vit sur **une machine tierce** : aucun lecteur de la PR — ni ai-01, ni un bot, ni un contributeur — ne peut l'ouvrir. Le signal ne porte aucun contenu vérifiable ; tout son sens tient dans le *nom du fichier*. **Une autorisation que personne ne peut relire est une autorisation fabriquée.**

La convention est tranchée par écrit (#16780) : **un waiver par pointeur est interdit**. Si un waiver compte pour un merge, sa **substance** est sur la PR — une phrase qui dit ce qui est levé et pourquoi. Le scratchpad garde le détail, la PR porte la décision. Le garde `scripts/check_local_path_waivers.py` (check advisory câblé dans `local-path-waiver-guard.yml`) rougit sur tout commentaire dont le corps est un chemin seul ou contient un segment de profil Windows `[A-Za-z]:[\/]Users[\/]` — contrôle positif : le corps #16670 exact, rejoué en test unitaire (le commentaire original a été supprimé par le user).
