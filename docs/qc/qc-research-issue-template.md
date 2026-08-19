# Template de sous-issue — Moissonnage quantconnect.com/research/

> **Epic parent** : [#11698](https://github.com/jsboige/CoursIA/issues/11698)
> **Label obligatoire** : `quantconnect-research`
> **Filtre de voisinage** : `docs/qc-strategies-status.md` (source de vérité 130 stratégies)

## Pourquoi ce template

Une sous-issue par article de recherche publié sur `quantconnect.com/research/`. Ce template garantit que **toute** évaluation suit la même grille :

1. **Tracabilité source** — l'article est référencé avec auteur(s) affiché(s) date URL.
2. **Lecture analytique** — pas une paraphrase, une **différenciation** vs bouquet.
3. **Verdict actionnable** — 4 catégories exclusives, dont une seule ouvre une PR.
4. **Acceptance vérifiable** — la case "sources primaires identifiées" est le **filet** contre la chaîne d'attribution rompue (cf EPIC #11168).

## Template

Copier-coller ce bloc dans le body de la sous-issue. Remplacer chaque `[…]` par le contenu réel.

```markdown
## Article source

- **URL** : [https://www.quantconnect.com/research/XXX]
- **Auteur(s)** : [auteur(s) affiché(s) sur l'article — ne jamais cru sans vérifier les sources primaires]
- **Catégorie putative** : [alpha / framework / ML / RL / factor / vol / risk / pedagogy / autre]
- **Date de publication** : [AAAA-MM-JJ]

## Lecture analytique

### Ce que l'article annonce

[paraphrase en 3-5 lignes de la proposition centrale de l'article]

### Sources primaires citées / à vérifier

- [papier arXiv / SSRN / DOI / manuel de référence — lister 1-N sources citées *dans* l'article]
- [variance entre l'article et la source : l'article dit-il la même chose que le papier ?]

### Différenciation vs bouquet existant

- **Filtre** : `docs/qc-strategies-status.md` (livré par #1621 phase 5)
- **Projets voisins** : [lister 1-3 projets existants qui touchent le même angle]
- **L'article est-il redondant ?** OUI / NON / PARTIELLEMENT [+ justification courte]

## Verdict

- [ ] **CONSOLIDATION** — un projet existant est enrichi ou remplacé. PR GitHub associée : [#XXX](url)
- [ ] **PÉDAGOGIQUE** — l'article documente un concept à intégrer dans un cours existant. Notebook à modifier : `[chemin]`. Pas de nouveau notebook.
- [ ] **NOUVEAU** — aucun équivalent valable, création justifiée. Justification détaillée obligatoire.
- [ ] **IGNORE** — l'article n'apporte rien de distinctif / qualité limitée. Justification explicite.

## Acceptance locale

- [ ] Article lu en entier (≥30 min de lecture effective)
- [ ] Voisinage `qc-strategies-status.md` re-vérifié
- [ ] Sources primaires identifiées (≥1) et tracées
- [ ] Verdict coché avec justification
- [ ] PR ou commentaire GH associé si verdict CONSOLIDATION / PÉDAGOGIQUE / NOUVEAU

## Liens

- **Epic parent** : [#11698](https://github.com/jsboige/CoursIA/issues/11698)
- **EPIC sibling** : [#1621](https://github.com/jsboige/CoursIA/issues/1621) (consolidation QC)
- **EPIC sibling** : [#11168](https://github.com/jsboige/CoursIA/issues/11168) (vérification citations arXiv)
- **Source de vérité voisinage** : [`docs/qc-strategies-status.md`](./qc-strategies-status.md)
- **Méthode audit-distillation** : `.claude/rules/audit-cross-source-distillation.md`
```

## Convention de titre

```
[QC-research] <titre court de l'article>
```

**Exemples** :
- `[QC-research] Regime-based crypto portfolio allocation`
- `[QC-research] Leveraged ETF momentum factor`
- `[QC-research] Reinforcement learning for portfolio rebalancing`

## Convention de labels

- `quantconnect-research` (obligatoire)
- `quantconnect` (héritage)
- `enhancement` si verdict NOUVEAU/CONSOLIDATION, `documentation` si verdict PÉDAGOGIQUE, `wontfix`/`discussion` si verdict IGNORE

## Convention de claim

```bash
gh issue comment <N> --body "[CLAIMED] lane <machine:workspace> — <article-title>"
```

Sans timestamp dans le corps (cf [lane-claim-protocol.md](../../claude/rules/lane-claim-protocol.md)) — le `createdAt` GitHub fait foi.

## Cap journalier

**Hard cap 2 articles/jour par lane.** Si une lane a déjà résolu 2 sous-issues le même jour, elle attend le lendemain. Pas de plafond — un plancher non plus. Le pool est infini, les workers sont bornés.

## Anti-patterns fondateurs

- **Verdict NOUVEAU** sans justification détaillée → **CHANGES_REQUESTED** au review.
- **Verdict CONSOLIDATION** projet inexistant → **CHANGES_REQUESTED**.
- **Sources primaires = 0** alors que l'article en mentionne → **CHANGES_REQUESTED** (anti-#11168).
- **PR ouverte sans verdict coché** → **CHANGES_REQUESTED**.
- **Verdict IGNORE** sans justification → **CHANGES_REQUESTED**.

## Exemples de bons verdicts

### Exemple 1 — Verdict CONSOLIDATION
- Article : « Momentum strategy on leveraged ETFs »
- Voisinage : `LeveragedETFMomentum` (tranche 6, PSR 79.8 %)
- Verdict : CONSOLIDATION
- Justification : « L'article propose un filtre de momentum sur leveraged ETFs. Notre projet `LeveragedETFMomentum` (PSR 79.8 %) couvre déjà cet angle. PR #XXX enrichit le notebook de recherche avec le filtre proposé. Pas de nouveau projet. »
- PR associée : oui.

### Exemple 2 — Verdict PÉDAGOGIQUE
- Article : « Understanding volatility regime shifts »
- Voisinage : `DynamicVIXSpyRegime-QC` (alive, 69.4 %)
- Verdict : PÉDAGOGIQUE
- Justification : « L'article propose un cadre pédagogique de détection de régimes de volatilité. Le projet `DynamicVIXSpyRegime-QC` couvre déjà la dimension algorithmique. Le notebook `QC-Py-12b-Vol-Regimes-CrossAsset` est enrichi d'une section pédagogique reprenant le cadre de l'article. Sources primaires : Hamilton (1989) déjà citées. »
- PR associée : oui (sur le notebook de cours).

### Exemple 3 — Verdict NOUVEAU
- Article : « Crowdsourced alpha extraction from SEC filings »
- Voisinage : aucun projet ne croise avec NLP/SEC filings en QC.
- Verdict : NOUVEAU
- Justification : « L'article propose un pipeline NLP→alpha sur les filings SEC, angle non couvert par les 130 projets existants (cf cartographie #1621). Le secteur fundamental US est stratégique pour le cours EPITA-IS. Création d'un notebook `research/research_nlp_sec_alpha.ipynb` standalone (pas un projet complet — un POC de recherche). »
- PR associée : oui.

### Exemple 4 — Verdict IGNORE
- Article : « Day trading penny stocks with Bollinger bands »
- Voisinage : EMA-Cross-Index, Bollinger-Bands (plusieurs).
- Verdict : IGNORE
- Justification : « L'article décrit une stratégie day-trading penny stocks peu robuste (n=20, frais non intégrés, surapprentissage visible). Sources primaires = 0. Notre projet `EMA-Cross-Index` couvre l'angle trend-following. Aucun gain pédagogique ou de performance attendu. Ne pas reproduire. »

## Pourquoi 4 verdicts et pas 2

Un verdict binaire « actionnable / non-actionnable » perd la nuance entre :

- **CONSOLIDATION** (actionnable, **PR ouvre**, enrichissement de l'existant)
- **PÉDAGOGIQUE** (actionnable, **PR ouvre**, enrichissement d'un cours)
- **NOUVEAU** (actionnable, **PR ouvre**, création justifiée)
- **IGNORE** (non-actionnable, **pas de PR**, verdict seul)

Les trois premiers convergent vers une PR, le quatrième est un verdict de clôture. Sans cette distinction, on perdrait la trace de **combien** d'articles ont effectivement amélioré le cours — métrique-clé de l'Epic acceptation Phase 4.

## Liens projet

- [`docs/qc-strategies-status.md`](./qc-strategies-status.md) — source de vérité 130 stratégies
- [`.claude/rules/audit-cross-source-distillation.md`](../../claude/rules/audit-cross-source-distillation.md) — méthode de distillation d'une source canonique
- [`.claude/rules/lane-claim-protocol.md`](../../claude/rules/lane-claim-protocol.md) — claim cross-lane
- [`.claude/rules/audit-reassessment.md`](../../claude/rules/audit-reassessment.md) — protocole 4 étapes de vérification
- [`.claude/rules/anti-regression.md`](../../claude/rules/anti-regression.md) — règle D.5 : ne pas stripper une cellule `# Solution`
- [`.claude/rules/pr-review-discipline.md`](../../claude/rules/pr-review-discipline.md) — critères CHANGES_REQUESTED
