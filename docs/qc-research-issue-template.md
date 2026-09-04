# Template de sous-issue QC-research (EPIC #11698)

Une sous-issue par article évalué. Titre : `[QC-research] <titre de l'article> (<#id article>)`.
Label : `quantconnect-research`. Copier le squelette ci-dessous dans le body.

Précédents d'usage : #13892 (dual VIX #21143, verdict CONSOLIDATION), #14091
(corrélation hedge #21050, verdict CONSOLIDATION).

```markdown
## Article source
- URL : https://www.quantconnect.com/research/<id>/<slug>/
- Auteur(s) : [auteur(s) affiché(s) — ne jamais cru sans vérifier]
- Catégorie putative : [alpha / framework / ML / RL / factor / vol / risk / pedagogy]
- Date de publication : [AAAA-MM-JJ]

## Lecture analytique

### Ce que l'article annonce
[paraphrase en 3-5 lignes]

### Sources primaires citées / à vérifier
- [papier arXiv / SSRN / manuel de référence]
- [variance entre l'article et la source]

### Différenciation vs bouquet existant
- Filtre : `docs/qc/qc-strategies-status.md` (livré #1621 phase 5)
- Projets voisins : [lister 1-3 projets existants qui touchent le même angle]
- **L'article est-il redondant ?** OUI / NON / PARTIELLEMENT [+ justification]

## Verdict

- [ ] **CONSOLIDATION** — un projet existant est enrichi/remplacé. PR GitHub associée.
- [ ] **PÉDAGOGIQUE** — l'article documente un concept à intégrer dans un cours existant. Notebook à modifier : [chemin]. Pas de nouveau notebook.
- [ ] **NOUVEAU** — aucun équivalent valable, création justifiée. Justification détaillée obligatoire.
- [ ] **IGNORE** — l'article n'apporte rien de distinctif/qualité limitée. Justification explicite.

## Acceptance locale
- [ ] Article lu en entier
- [ ] Voisinage `docs/qc/qc-strategies-status.md` re-vérifié
- [ ] Sources primaires identifiées (≥1)
- [ ] Verdict coché avec justification
- [ ] PR ou commentaire GH associé si verdict CONSOLIDATION/PÉDAGOGIQUE/NOUVEAU
```

Rappels de discipline (détaillés dans le body de l'EPIC #11698) :

- **Claim** : `[CLAIMED] lane <machine:workspace> — <article>` sur la sous-issue avant d'éditer.
- **Cap** : 2 articles/jour max par lane.
- **Grain** : première ligne `Grain: <TIER>/qc — lane <machine:workspace> — prev: <TIER>/<GENRE> #<PR>` (protocole de variation).
- **Backtest obligatoire** (règle G) pour toute PR issue d'un verdict CONSOLIDATION/NOUVEAU touchant `projects/` : Sharpe/CAGR/MaxDD dans le body, fenêtre OOS distincte du training.
- Un verdict IGNORE n'ouvre PAS de PR — verdict sur l'issue seulement.
