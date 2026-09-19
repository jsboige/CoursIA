# Protocole de veille — Trading algorithmique (socle RNCP41881)

[← QuantConnect](../README.md)

Cadre : certification **RNCP41881 — Expert en finance de marché**, compétence de veille portée par le syllabus TimeSpice 2026/2027 sous son **codage historique** `RNCP37437BC01C1.1` (veille scientifique, technologique, économique, réglementaire et environnementale — 3 h 30). RNCP37437 est inactive et remplacée par RNCP41881 ; les codes historiques sont conservés dans les supports sans normalisation silencieuse (cf issue #16239).

Référentiels : [RNCP41881](https://www.francecompetences.fr/recherche/rncp/41881/) · [RNCP37437 (inactive)](https://www.francecompetences.fr/recherche/rncp/37437/)

---

## 1. Objectif pédagogique

La veille n'est **pas une accumulation de liens** : c'est une discipline de décision. Chaque entrée du registre doit pouvoir, en principe, **changer une ligne du projet** — une hypothèse de marché, un paramètre d'allocation, une limite de risque, un choix de donnée. Une veille qui n'impacte rien n'est pas une veille, c'est une agrégation de flux.

La compétence évaluée n'est pas « savoir trouver de l'information » mais **maintenir un registre traçable dont le projet porte la trace** : chaque synthèse de veille se conclut par un impact explicite (intégré / surveillé / écarté, avec justification).

## 2. Typologie des sources — quatre familles

| Famille | Contenu attendu | Canaux typiques | Piège typique |
|---|---|---|---|
| **Scientifique & technologique** | Méthodes quantitatives, backtesting, microstructure, ML appliqué aux marchés ; évolutions de l'outil (LEAN, données QC) | arXiv `q-fin`/`cs.LG`, SSRN, revues (Journal of Portfolio Management...), changelogs LEAN et QuantConnect, repos GitHub | L'article non relu pris pour un résultat établi |
| **Économique & financière** | Cycle, inflation, taux, calendrier et comptes rendus de banques centrales, emploi, surprises de données | Fed (FOMC minutes, dot plot), BCE (projections), BLS, INSEE, calendriers économiques, notes de recherche broker | Le commentaire de marché daté du jour, périmé en une semaine |
| **Réglementaire** | Règles affectant exécution, reporting, données, produits (leviers, divulgation, short-selling) | ESMA, AMF, SEC (filings, rulemaking), MiFID II/MiFIR, consultations publiques | La consultation (brouillon) lue comme une règle acquise |
| **Environnementale & extra-financière** | Réglementation climatique/ESG, données carbone et contrastes, risques physiques et de transition | ISSB/IFRS S1-S2, TCFD, réglementation européenne (CSRD), publications de données ESG des providers | Le communiqué institutionnel pris pour une donnée mesurée |

## 3. Fréquence et périmètre

| Famille | Cadence minimale | Justification |
|---|---|---|
| Scientifique & technologique | Hebdomadaire | Les méthodes évoluent vite, pas au jour le jour |
| Économique & financière | Bi-hebdomadaire (autour des reunions de banques centrales et des releases majeures) | Le cycle est le régime de toute stratégie trend/macro |
| Réglementaire | Mensuelle + alerte sur consultations | Les règles changent lentement mais franchement |
| Environnementale | Mensuelle | Horizon long, revue périodique suffisante |

**Périmètre borné** : 8 à 12 sources **actives** maximum par groupe. Au-delà, la veille se dilue en consommation passive — la borne force la sélection par la qualité (§4), pas par le volume.

**Fenêtre dédiée** : deux créneaux de 30 minutes par semaine (ex. mardi/vendredi), plus une revue mensuelle de synthèse. La veille sans créneau réservé disparaît en deux semaines — constat récurrent des projets collectifs.

## 4. Critères de qualité et traçabilité

Chaque source candidate est notée **binairement** sur cinq critères (grille adaptée de CRAAP) ; **4/5 requis** pour entrer au registre :

| Critère | Question de contrôle | Refus si |
|---|---|---|
| **Autorité** | Qui signe ? L'institution/l'auteur est-il identifiable et compétent ? | Anonymat, autorité invérifiable |
| **Actualité** | La donnée est-elle datée, et la date est-elle pertinente pour la famille ? | Indatable, ou périmée pour sa famille (un calendrier de la semaine passée) |
| **Exactitude** | Le fait est-il sourcé, méthode ou chiffré — reproductible ou vérifiable auprès de la source primaire ? | Assertion non sourcée, reprise de seconde main exclusive |
| **Motivation** | Quel intérêt a l'émetteur ? (vente, régulation, réputation) | Conflit d'intérêts non déclaré dominant l'information |
| **Pertinence** | Ce fait peut-il changer une ligne du projet ? (cf §1) | Aucun canal d'impact identifiable |

**Traçabilité** : chaque entrée du registre conserve l'URL exacte, la **date de publication** ET la **date de consultation** (une page change ; la date de consultation fixe ce qui a été lu).

## 5. Registre de veille — modèle

Copier ce tableau dans le rapport du projet (section « Veille ») et le remplir au fil de l'eau :

```markdown
| Date consult. | Famille | Source (URL) | Qualité /5 | Fait observé | Impact projet | Statut |
|---|---|---|---|---|---|---|
| 2026-10-02 | Économique | federalreserve.gov/... (FOMC minutes, 2026-09-16) | 5 | Médiane des projections relèvement taux fin 2026 | Réduit l'exposition nette long du régime trend ES dans la sous-période simulée | Intégré |
| | | | | | | |
```

Colonnes obligatoires : les sept ci-dessus. Le **statut** prend trois valeurs — `Intégré` (une ligne précise du projet a changé), `Surveillé` (impact plausible mais différé), `Écarté` (impact testé et rejeté, justification en note). Un registre sans colonne *Statut* n'est pas évaluable.

## 6. Intégration au projet collectif

1. **Section « Veille » du rapport** : le registre (§5) + **au moins trois synthèses datées** sur la fenêtre du projet, chacune concluant sur un impact explicite.
2. **Traçabilité inverse** : chaque hypothèse de marché du projet (régime, direction, risque de liquidité) référence au moins une entrée du registre par sa date — un lecteur doit pouvoir remonter de l'hypothèse à la source.
3. **Soutenance** : chaque membre du groupe présente **au moins une veille qu'il a intégrée** et l'effet mesuré (avant/après sur le backtest ou l'allocation). C'est le critère individuel de la compétence (cf #16239 : vérifier la contribution et la compréhension individuelles).

## 7. Anti-patterns

- **Registre sans impact** : des dizaines d'entrées, zéro ligne de statut remplie — la veille décorative.
- **Source unique répétée** : tout le flux d'un seul émetteur ; la diversité de familles (§2) est un critère en soi.
- **Actualité indatable** : une « tendance de marché » sans date de publication ni de consultation.
- **Veille post-hoc** : le registre écrit la semaine de la soutenance ; les dates de consultation doivent s'étaler sur la fenêtre du projet.
- **Confusion consultation/publication** : citer la date où l'on a lu au lieu de celle du fait — les deux datent (§4).

## 8. Référentiel et périmètre

- Compétence : veille (RNCP37437BC01C1.1, codage historique TimeSpice conservé) → RNCP41881.
- Ce protocole couvre le **socle obligatoire** de la compétence veille ; les aspects marchés/règlement propres à une stratégie donnée restent à la charge du groupe dans son registre.
- Hors périmètre ici : LEAN CLI, optimiseur, paper trading, deep learning (cf #16239).

See #16239 (livrable 3 — protocole de veille ; les livrables 1, 2 et 4 suivent leur propre grain).
