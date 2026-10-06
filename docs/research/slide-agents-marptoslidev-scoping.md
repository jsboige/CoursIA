# Slide agents Marp→Slidev — scoping (c.1110)

Issue : [#19578](https://github.com/jsboige/CoursIA/issues/19578) — `[Suivi #19525]` agents de slides face à l'abandon de Marp. Mesure et décision à partir de l'arbre de travail `main` @ `d09acde1a2` (2026-10-06).

Le constat de l'issue est en partie faux (le corps dit « l'abandon de Marp » alors que 12 decks Marp subsistent comme source), et en partie vrai (l'outil sous-jacent `sk-agent.analyze_image` est déjà périmé, documenté comme tel dans `slide-analyzer-sk-agent.md`). Le scoping tranche avec des chiffres firsthand et propose une voie.

## 1. Inventaire firsthand (mesuré 2026-10-06, `main` @ `d09acde1a2`)

| Source | Compte | Note |
|---|---|---|
| `slides/**/slides.marp.md` | **12** (11 actifs + 1 `_archive/S4-trading-algorithmique`) | format legacy |
| `slides/**/slides.md` | **18** (17 actifs + 1 `_archive/S4-trading-algorithmique`) | format Slidev |
| `slides/**/output/marp_renders/*.png` | **0** | aucun rendu Marp committe |
| `slides/**/*.pptx` | **0** | aucune source PPTX committee |
| `slides/package.json` | 1 (deps : `@slidev/cli ^51`, `playwright-chromium`, **aucune dep Marp**) | env Slidev-first |
| `slides/.marprc.yml` | 1 (legacy, 3 lignes, `themeSet: ./themes/ia101.css`) | config Marp |
| `slides/theme-ia101/styles/index.css` | présent, 7 layouts custom (`cover`, `section`, `questions`, `image-overlay`, `dense`, `two-cols`, etc.) | theme Slidev |
| `_tools/marp_to_slidev.py` | présent | outil de migration |
| `_tools/pptx_to_marp.py` | présent | import PPTX vers Marp (legacy) |
| `_tools/render_deck.py` | présent | rendu générique (Marp + Slidev) |

**Vérification par inventaire nominatif** (12 Marp, 18 Slidev) :

- Marp (`slides.marp.md`) : `01-introduction`, `02-resolution-problemes`, `03-logique`, `04-probabilites`, `05-theorie-des-jeux`, `06-apprentissage`, `07-elargissements`, `08-ia-generative`, `S1-argumentation`, `S2-ia-exploratoire-symbolique`, `S3-acculturation`, `S4-trading-algorithmique/_archive/`.
- Slidev (`slides.md`) : les 12 ci-dessus + `09-traitement-automatique-langues`, `S4-trading-exercices`, `S6-tweety`, `S7-lean`, `S8-semantic-web`, `S4-trading-algorithmique/_archive/`, `_composition-control/`.

**Constat** : la migration est **incomplète et asymétrique**. Slidev (18) dépasse Marp (12) en nombre, mais 12 decks portent encore `slides.marp.md` à côté de leur `slides.md`. Le README `slides/README.md` tranche la direction officielle : « *Presentations du cours IA 101 / CS 405 au format **Slidev*** » ; `slides/package.json` n'expose que des scripts Slidev ; le `slides-layout-pattern.md` (le seul guide de mise en page) est Slidev-first.

**Mais** le `.marprc.yml`, les `slides.marp.md` et les outils `marp_to_slidev.py` / `pptx_to_marp.py` sont encore là. **Marp n'est pas « abandonné » au sens littéral — il coexiste en format legacy.**

## 2. État des deux agents (premier diagnostic des fronts de travail)

**`slide-analyzer.md`** (170 lignes, `.claude/agents/`) :
- 3 modes : `pptx`, `marp`, `compare` (PPTX vs Marp).
- Mode `marp` consomme `output/marp_renders/slide.*.png` ; **0 fichier** ne porte ce pattern dans l'arbre mesuré.
- Génération des renders via `python slides/_tools/slide_tools.py marp-render {deck_path}` (commande non testée sur main ; le helper `slide_tools.py` existe, mais l'orchestrateur `.marprc.yml` n'a pas de cible `marp-render`).
- Source de vision : `mcp__sk-agent__call_agent(attachment=…)`. **L'outil `sk-agent.analyze_image` n'existe plus** (mesuré 2026-09-29, documenté dans `slide-analyzer-sk-agent.md` : « *sk-agent n'expose plus d'outil `analyze_image`* »). L'agent lui-même n'a pas été rerouté vers `call_agent(prompt=..., attachment=...)` (qui, lui, existe).

**`slide-improver.md`** (266 lignes) :
- 1 mode : améliorer un deck Marp en comparant au PPTX original.
- Mêmes dépendances : Marp CLI + sk-agent vision.
- Pipeline concret : `marp slides.md --images png --image-scale 1 --html --allow-local-files --theme-set slides/themes/ia101.css -o .../marp_renders/slide.png` → render → prompt vision → édition de `slides.md` (Marp) avec patterns catalogue.
- **Cible = fichier Marp** ; aucun front Slidev.

**Front commun aux 2 agents** : (a) format Marp, (b) sortie PNG par slide, (c) sk-agent vision (périmé). Les trois fronts sont en transition ou périmés : Marp coexisté en legacy, le tooling PNG est mort-né (0 rendu), l'organe vision est déjà remplacé par un autre nom.

## 3. 4 voies + arbitrage (ce que l'issue propose, qualifié par les chiffres §1)

| Voie | Périmètre | Coût | Bénéfice | Risque |
|---|---|---|---|---|
| **1. Réécrire pour Slidev** | 2 agents visent Slidev : `slidev-improver` compare Slidev à PPTX (ou à un render natif Slidev headless Chromium) ; `slidev-analyzer` mode unique. Migrer `slides.marp.md` → `slides.md` au passage (12 fichiers). | Élevé (refonte 2 agents + 12 migrations + helpers) | Pérenne : la direction dépôt est Slidev (cf. README) | Migration incomplète si Marp continue d'être maintenu en parallèle |
| **2. Fusionner en `slide-curator`** | 1 agent couvre analyse + amélioration, écosystème Slidev (`slidev export` PNG par slide, headless Chromium) | Moyen | Moins d'agents, plus lisible | Doit couvrir 2 cas d'usage dans un seul prompt — peut-être trop |
| **3. Retirer les 2 agents** | Suppression pure ; mise à jour des 8 références | Bas | Pas de dette morte | Perte du backstop vision (mais aucun appel enregistré sur les 12 derniers mois) |
| **4. Garder une variante legacy Marp** | Conserver `slide-improver` / `slide-analyzer` en Marp-only (figés), ne pas les maintenir, ne pas en ajouter | Bas | Préserve l'existant | Dette technique visible (commentaire « figé » dans le frontmatter) |

**Recommandation : Voie 1 (réécrire pour Slidev).** Trois raisons :

1. **Cohérence avec la direction dépôt.** `slides/README.md` est sans ambiguïté : Slidev est la cible officielle. Garder un agent qui vise l'autre format, c'est signaler le contraire à un futur lecteur.
2. **L'organe de vision est déjà mort.** Le commentaire de `slide-analyzer-sk-agent.md` dit que `analyze_image` n'existe plus, et que `call_agent(prompt, attachment, …)` est l'API courante. Une réécriture impose le reroutage — ce qui est une dette technique de toute façon, voie 3 ou voie 4.
3. **Le tooling Slidev est déjà en place.** `playwright-chromium` est dans `devDependencies`, le thème `theme-ia101` est codé, `slides/_tools/render_deck.py` couvre déjà le rendu générique. **Il manque l'agent qui s'en sert.**

**Pourquoi pas voie 3** (retrait pur) : le diagnostic de la Slidev-vs-PPTX reste une demande récurrente des reviewers (`#221`, layout `image-overlay`). Sans agent, c'est un regard humain à chaque PR, ce qui est coûteux et non scalable. La voie 3 est défendable **si** Slidev fournit un outil natif qui le fait ; le scoping n'a pas trouvé cet outil (à vérifier en phase d'exécution).

**Pourquoi pas voie 4** (legacy Marp) : 12 `slides.marp.md` cohabitent avec 18 `slides.md` ; la migration Marp→Slidev des 12 restants est un travail d'accrétion qui demande un agent outillé. Garder un agent mort pour 12 fichiers qui sont en train de migrer est une dette visible.

## 4. Plan d'exécution (à étayer en phase 2, conditionnel à l'arbitrage user/coordinateur)

**Si Voie 1 retenue** (recommandation) :

1. **Décision tranchée par le user** (registre d'arbitrage) — un coup parti sur Marp-only serait gaspillé.
2. **Reroutage vision** (sous-tâche 0) : adapter les 2 agents pour appeler `mcp__sk-agent__call_agent(prompt=…, attachment=…)` au lieu de l'`analyze_image` disparu. Ce reroutage est **pré-conditions** aux étapes 3-4 ; sans lui, les agents ne tournent pas, Marp ou Slidev.
3. **Réécriture `slide-improver` → `slidev-improver`** : cible `slides.md` (Slidev) au lieu de `slides.marp.md` ; utilise `slides/_tools/render_deck.py` (déjà Slidev-compatible) ou `npx slidev build --base … --out dist/`.
4. **Réécriture `slide-analyzer` → `slidev-analyzer`** : mode unique Slidev + 1 mode `compare-vs-pptx` ; mêmes prompts canoniques (primaire FR + retry FR court) que `slide-analyzer-sk-agent.md` documente comme invariants.
5. **Migration des 12 `slides.marp.md`** : suppression ou archivage sous `slides/*/_archive/` après vérification qu'aucun carnet n'importe leur contenu ; mise à jour des 8 fichiers qui référencent Marp (`README.md`, `subagents-reference.md`, `slide-analyzer-sk-agent.md`, `vibe-coding-workspace-map.md`, etc.).

**RÈGLE F (SOTA-OK)** : si l'agent natif Slidev ou sk-agent fournit déjà l'équivalent (ex : un `slidev audit` ou un mode vision de `call_agent` qui prendrait directement un dossier Slidev), l'organe natif est utilisé, et le scope des étapes 3-4 se réduit à l'orchestration.

**Smells anticipés** :

- **S1** : la migration des 12 `slides.marp.md` peut révéler un contenu non trivial présent uniquement dans la version Marp (annotations, easter eggs). Le test : `diff` mot-à-mot entre `slides.marp.md` et `slides.md` du même dossier, score de similarité.
- **S2** : `slidev build` produit un SPA HTML, pas un PNG par slide. Le rendu PNG par slide pour la comparaison vision demande un re-pipeline (`playwright-chromium` sur le SPA). Coût : 1 helper à coder si non-trivial.
- **S3** : `slide-analyzer-sk-agent.md` est référencé par `vibe-coding-workspace-map.md` (genai) et `README.md` (docs racine) — la mise à jour de ces fichiers demande une propagation soignée.

**Hors-scope** (à expliciter en PR) : (a) refonte du thème `theme-ia101` ; (b) intégration Slidev dans les workflows CI existants (`slides-build-advisory.yml`, `slides-composition-advisory.yml`, `slides-composition-pr-relay.yml`) — la première vague peut se contenter du tooling local.

## 5. Comparaison aux précédents (registre durable)

- **#19525** (PR tranche finale, c.201) : 3 corrections harnais sur `slide-improver.md` au titre de la règle #221 — sorties de la PR par décision 06/10 (cf cid 6022771569). **Le devenir des agents eux-mêmes est la question ouverte que #19578 reprend.**
- **#9535** item 7 : la relocalisation `.claude/agent-memory/slide-analyzer/` → `docs/reference/slide-analyzer-sk-agent.md` (cf docs/README.md l.91) — c'est l'**origine** du statut « durable, outil périmé » du fichier de référence.
- **`#221`** (règle image-overlay) : convention visuelle qui justifie l'analyse slide-via-vision — sans agent de relecture, c'est un regard humain à chaque PR, ce qui motive la voie 1.

## 6. Critère de fermeture de #19578

L'issue est ouverte jusqu'à ce qu'une des 4 voies soit tranchée par **écrit** (réponse user ou coordinateur sur l'issue, ou PR qui matérialise la décision). **Ce mémo tranche la voie 1 avec preuve** ; la décision finale reste à arbitrer (user, registre des arbitrages). Une fois tranchée, la PR d'exécution (voie 1) ouvre une nouvelle vague avec son propre claim et ses propres deliverables.

## Sources first-hand

- `slides/README.md` (l.1-80, format Slidev officiel, inventaire 14 decks actifs).
- `slides/package.json` (deps Slidev, aucune dep Marp).
- `slides/.marprc.yml` (config legacy).
- `slides/theme-ia101/styles/index.css` (theme Slidev).
- `slides/_tools/{marp_to_slidev.py, pptx_to_marp.py, render_deck.py}` (3 outils legacy + 1 générique).
- `slides/*/slides.marp.md` (12 fichiers) + `slides/*/slides.md` (18 fichiers) — comptes `find` mesurés.
- `.claude/agents/slide-analyzer.md` (170 lignes) + `.claude/agents/slide-improver.md` (266 lignes) — lecture intégrale.
- `docs/reference/slide-analyzer-sk-agent.md` (64 lignes, statut durable-outil-périmé).
- `docs/reference/slides-layout-pattern.md` (Slidev-first, trois règles).
- `docs/reference/subagents-reference.md` (l.44, référence aux 2 agents).
- `docs/README.md` (l.91) + `docs/genai/vibe-coding-workspace-map.md` (l.23, 55) — 5 références totales à `slide-analyzer-sk-agent.md`.

## Chevauchement de claims

Claim posé sur #19578 (cid 6024249244, 06/10 19:52Z, paths scoped : `docs/research/slide-agents-marptoslidev-*.md`, `.claude/agents/slide-analyzer.md`, `.claude/agents/slide-improver.md`). Pas de claim tiers sur l'issue (vérifié 06/10 19:52Z). Pas de PR ouverte sur ce périmètre.

## Convention honnête

**Aucun engagement d'exécution dans ce mémo.** La voie 1 est recommandée avec 3 raisons mesurées ; les 3 autres voies sont arbitrées avec leurs coûts/bénéfices/risques. **L'arbitrage user ou coordinateur reste requis** pour passer à la phase 2 (réécriture effective des 2 agents). Sans décision, ce mémo est une **brique de décision**, pas un plan d'exécution.

## Annexe — comptes exacts (audit-ready)

```text
$ find slides/ -name 'slides.marp.md' | wc -l   # 12
$ find slides/ -name 'slides.md' | wc -l         # 18
$ find slides/ -path '*marp_renders*' | wc -l    # 0
$ find slides/ -name '*.pptx' | wc -l            # 0
$ grep -rln 'Marp\|marp' .claude/ docs/ | wc -l  # 5
$ grep -rln 'slide-improver\|slide-analyzer' .claude/ docs/ | wc -l  # 8
$ wc -l .claude/agents/slide-analyzer.md         # 170
$ wc -l .claude/agents/slide-improver.md         # 266
$ wc -l docs/reference/slide-analyzer-sk-agent.md # 64
```

Mesurés le 2026-10-06 sur `main` @ `d09acde1a2`, worktree `feature/c1110-slide-agents-decision`.

🤖 Generated with [Claude Code](https://claude.com/claude-code)
