# Pré-enregistrement — schéma attentionnel et contrôle : stabilité, correction d'erreur, adaptation (case 5ter)

**Issue :** #8182 (veille et distillation progressive, candidat Graziano 2017, versant contrôle)
**Lane :** `myia-po-2028:CoursIA`
**Scellé :** 2026-10-30, **avant** toute implémentation du module et avant toute exécution sur les graines d'étude.

Ce document fixe le terrain, les bras comparés, les métriques, les prédictions et leurs bandes **avant** de coder `ict/attention_schema_control.py`. Il est révisable une seule fois, par un commit distinct qui dit ce qui a changé et pourquoi (protocole de scellement v1 → v2 des tranches Schurger #13459 et Vervaeke) ; toute révision antérieure à l'évaluation held-out reste visible dans l'historique git.

---

## 1. Source, provenance et ce qui est attribué

**Référence lue :** Graziano MSA (2017), « The Attention Schema Theory: A Foundation for Engineering Artificial Consciousness », *Frontiers in Robotics and AI* 4:60, DOI `10.3389/frobt.2017.00060`, CC-BY (OA).

**Copie archivée :** `G:\Mon Drive\MyIA\IA\Bibliographie IA\Consciousness\2017 - Graziano - The Attention Schema Theory, A Foundation for Engineering Artificial Consciousness (Front Robot AI 4-60, DOI 10.3389_frobt.2017.00060, OA).pdf` — empreinte sha256 préfixe `58a1a461e5d6fc5a`, identité vérifiée sur la première page (titre, auteur, Princeton, DOI, licence, 14 nov. 2017). Les citations ci-dessous sont extraites du texte de **cette copie**.

**Distinct de la source des cases 5/5bis.** Ces cases créditent le livre de 2013 (*Consciousness and the Social Brain*). La présente tranche lit le **papier de 2017**, dont le cadre est explicitement l'ingénierie : ce que la théorie prédit pour une machine qu'on construit. Les passages sur lesquels elle repose :

1. « That control should benefit from an attention schema—a coherent set of information that represents basic stable properties of attention, reflects ongoing changes in the state of attention, makes predictions about where attention can be usefully directed, and anticipates consequences of attention. »
2. « However, in that case, visual attention suffers deficits in control. It behaves less stably over time and shows evidence of being less able to error-correct and less able to adapt to perturbations (McCormick, 1997; Lin and Murray, 2015; Webb and Graziano, 2015; Webb et al., 2016a). The evidence suggests that awareness is necessary for the good control of attention. »
3. « One group of researchers has presented a computational model of attention with and without an internal model and found that at least this simplified, artificial attention is better controlled with the internal model (van den Boogaard et al., 2017). »
4. « Once again, it is worth noting that the robot is not reporting on the actual state of its body, but rather reporting the contents of an internal model. If that internal model is in error, then the robot will provide an incorrect report. If you trick the body schema into representing the arm as more to the left than it actually is, or larger than it actually is, that distorted information will pass through cognition and linguistic processing and enter the verbal report. »
5. « It is also worth noting that even when the body schema is working correctly, it is always incomplete. » / « Its body schema contains only the information that the system needs to control the body. » — et, transposé à l'attention : « Consciousness is, in a sense, a cartoon sketch of attention. »
6. « The machine is captive to its own information. It knows only what it knows. »
7. (Anti-duplication, cf §2) « In effect, the global workspace theory is the same as the AST, if you took away the attention schema part, and had only the attention part—the ability of the brain to selectively enhance signals such that they have a global impact on many brain systems. »

**Ce que l'article soutient et que ce carnet ne teste pas.** (a) La constructibilité de la conscience (« if AST is correct, then consciousness is buildable with current technology ») : aucune expérience ci-dessous ne prétend construire ni mesurer de la conscience. (b) La phénoménologie — le papier dit lui-même que la théorie « emphatically does not explain how we have a subjective experience ». (c) Le versant neurobiologique (TPJ, cerveau social) et le versant social (attribution du schéma à autrui). Ce carnet teste la partie **opérationnelle** que le papier énonce pour l'ingénieur : les citations 1–3 (bénéfice de contrôle d'un modèle interne de l'attention) et 4–6 (le rapport lit le modèle, pas l'état — une distorsion du modèle passe dans le rapport).

**Grade de provenance.** Citations grade A (copie archivée, lue intégralement). L'**opérationnalisation** est de grade C : une traduction choisie par cette lane sur un substrat jouet, pas une mesure que l'article revendique. Aucune phrase du livrable ne présentera l'opérationnalisation comme un résultat de Graziano.

---

## 2. Positionnement contre les cases voisines (anti-duplication)

| Case | Ce qu'elle mesure | Verdict | Ce que 5ter n'en refait pas |
|---|---|---|---|
| **5** (PR #15547) | Readout : le workspace SAE discrimine-t-il `q̂(attention)` de `q̂(objet)` (`R_attn`) ? | INCONCLUSIF (propa saturé) | Aucune mesure de readout/workspace SAE, aucun LLM |
| **5bis** (#15798) | Causal : l'état de clause attentionnel est-il déplaçable (patch/interchange), la signature migre-t-elle, la verbalisation suit-elle ? | ÉTAT 6/6 · READOUT 6/6 · COMPORTEMENT 2/6 directionnel | Aucune intervention sur traces gelées |
| **15** (confabulation/broadcast) | La workspace **consacre** une représentation fausse (versant broadcast) | Ligne à deux opérationnalisations | Le broadcast n'est pas le contrôle ; ici la fausseté est dans le **modèle de contrôle**, pas dans le contenu diffusé |
| **ICT-24** WorkspaceIgnition (#5643) | GWT/ignition | — | La citation 7 du papier opère elle-même la séparation : GWT = AST **sans** la partie schéma. 5ter teste précisément la partie que GWT n'a pas |

L'axe de 5ter — le **contrôle** (principe de Conant-Ashby appliqué à l'attention, citations 1–3) et la **dissociation rapport/contrôle** (citations 4–6) — n'est couvert par aucune case existante (grep nul sur Conant / good regulator / van den Boogaard dans `ict/` et `docs/ict/` au scellement). Substrat : jouet CPU déterministe, sans LLM ni SAE — le papier cite van den Boogaard 2017 comme précédent computationnel exactement de cette nature (attention avec/sans modèle interne).

---

## 3. Surrogate déclaré

**Terrain.** Suivi attentionnel sur un anneau [0, 1) (distance circulaire). `n_items = 12` items mobiles, chacun avec vitesse persistante (processus OU discret sur la vitesse, θ = 0,05, σ_v = 0,002, σ_noise position = 0,002). Un item est la **cible** (désignée par un signal de saillance initial, jamais ré-annoncée) ; les 11 autres sont des distracteurs dont la saillance observée est bruitée. L'agent alloue un **foyer** attentionnel unique de **champ de largeur `w = 0,10`** : tout item à distance < w du foyer est capturé (reçoit du gain). `steps = 720`. La saillance observée de chaque item = saillance vraie + bruit gaussien (σ_s = 0,3, échelle relative) ; la compétition est biaisée : l'item capturé au foyer voit sa saillance effective multipliée par le gain (2,0), conformément au cadre biased competition que le papier emprunte.

**Bras comparés (mêmes graines, même terrain, mêmes entrées de saillance, même budget de calcul — seule l'organisation de l'état diffère) :**

| Bras | Règle d'allocation |
|---|---|
| `reactive` | Attention sans modèle interne : le foyer suit l'argmax d'une EMA courte (α = 0,3) de la saillance observée. Aucun état maintenu au-delà de l'EMA. |
| `schema` | Mêmes entrées. Le contrôleur maintient un **schéma attentionnel appauvri** : estimation de saillance (EMA α = 0,1 ; v2, cf §6), position du foyer quantifiée (grille 0,01), confiance, vitesse estimée du foyer — mis à jour lentement (EMA α = 0,1) **et** corrigé par la prédiction 1-pas (position + vitesse estimée). L'allocation lit le schéma ; l'observation de position qui alimente l'updater est l'argmax de l'estimation de saillance du schéma (jamais l'argmax brut). |
| `schema_shuffled` | Identique à `schema`, mais l'updater du schéma est alimenté par les saillances **permutées** entre items (null : un schéma mal informé ne doit rien apporter). |
| `schema_distorted` | Identique à `schema`, avec offset `d` injecté dans l'**encodage** de la position du schéma : position stockée = position réelle du foyer + d, pour d ∈ {0, w/4, w/2}. Le « rapport » = décodage de la position stockée ; le contrôle = allocation résultante. |

**Perturbations planifiées** (instants fixes, non annoncées à l'agent), 3 types × 3 occurrences : `jump` (t = 150, 390, 630 — la cible est téléportée de ±0,15), `gain_drop` (t = 210, 450, 690 — efficacité du gain à 40 % pendant 60 pas), `distractor` (t = 90, 330, 570 — un distracteur reçoit saillance × 4 pendant 60 pas).

**Métriques.** `e_t` = distance circulaire(foyer, cible). `stabilité` = std(e_t) sur les pas calmes (hors fenêtres [pert − 10, pert + 80]). `correction` = pas pour revenir à e_t < 0,15 pendant 5 pas consécutifs après une perturbation (censuré à 80), moyenné sur les 9. `adaptation` = ratio correction(3ᵉ occurrence) / correction(1ʳᵉ occurrence), moyenne géométrique sur les 3 types. `erreur_pred` = erreur absolue moyenne de la prédiction 1-pas du foyer. `erreur_rapport(d)` = moyenne |position décodée du schéma − position vraie du foyer|.

**Déterminisme.** `numpy.random.default_rng(seed + offset_bras)` ; terrain tiré une fois par graine puis **gelé**, les quatre bras le rejouent à l'identique. Dépendances : stdlib + numpy uniquement. CPU-only.

---

## 4. Prédictions pré-enregistrées

Toutes portent sur les graines d'étude `(0, 1, 7, 42, 99)` ; les bandes sont **fixées ici**, avant le pilote de calibration (graine `1000`, disjointe, hors étude, jamais comptée dans un verdict).

| # | Prédiction | Bande préfixée | Réfutation |
|---|---|---|---|
| **P1a** | Le schéma stabilise le contrôle | `stabilité(schema) ≤ 0,8 · stabilité(reactive)` sur ≥ 4/5 graines | 3 graines ou plus hors bande ⇒ réfutée |
| **P1b** | Le schéma corrige mieux après perturbation | `correction(schema) ≤ 0,75 · correction(reactive)` sur ≥ 4/5 graines | 3 graines ou plus hors bande ⇒ réfutée |
| **P1c** | Le schéma s'adapte mieux aux répétitions | `adaptation(schema) ≤ 0,9 · adaptation(reactive)` sur ≥ 3/5 graines | 3 graines ou plus hors bande ⇒ réfutée |
| **P2** | Le schéma porte une prédiction utilisable | `erreur_pred(schema) ≤ 0,9 · min(persistance, EMA-vitesse)` sur ≥ 4/5 graines | 3 graines ou plus hors bande ⇒ réfutée |
| **P3a** | La distorsion passe dans le rapport | pour chaque d ∈ {w/4, w/2} : `erreur_rapport(d) ≥ 0,8 · d` sur ≥ 4/5 graines | une valeur de d sous bande sur 3 graines ⇒ réfutée |
| **P3b** | … alors que le contrôle est préservé (d sous-clinique) | à d = w/4 : `Δstabilité ≤ 0,02` ET `Δcorrection ≤ +12 pas` vs d = 0, sur ≥ 4/5 graines | 3 graines ou plus hors bande ⇒ dissociation non démontrée |
| **P4** | Null : un schéma mal alimenté n'aide pas | `stabilité(shuffled) ≥ 0,95 · stabilité(reactive)` ET `correction(shuffled) ≥ 0,95 · correction(reactive)` sur ≥ 4/5 graines | battu par shuffled ⇒ l'avantage n'est pas le modèle |
| **P5** | Porte instrument | si `stabilité(reactive) ≤ 0,03` ET `correction(reactive) ≤ 10` sur ≥ 4/5 graines → **NON_CONCLUSIF_INSTRUMENT** (terrain trop facile : le cas dégénéré où tout contrôleur est optimal, celui-là même que le papier éviterait) | — |

**Verdict.** `SUPPORTED` si P1a ∧ P1b ∧ P1c ∧ P2 ∧ P3a ∧ P3b ∧ P4, P5 fermée. `PARTIAL` si P1a ∧ P1b ∧ P4 ∧ (P2 ∨ P3a ∧ P3b). `REFUTED` sinon. `NON_CONCLUSIF_INSTRUMENT` si P5 ouverte. Un verdict `PARTIAL` ou `REFUTED` se publie tel quel, avec la liste exacte des prédictions tombées.

**Contre-régime explicité d'avance.** (i) Si `schema_shuffled` bat `reactive` (P4 tombé), l'avantage mesuré vient de « plus d'état », pas d'un modèle de l'attention — publié comme réfutation de l'attribution, même si P1 passe. (ii) Si `erreur_rapport` ne suit pas d (P3a tombé), le rapport du jouet ne lit pas son modèle — la lecture « cartoon sketch » de la citation 5 n'est pas opérationnalisée ici, et la discussion devra dire pourquoi. (iii) Si les deux bras sont optimaux (P5), aucune conclusion n'est tirée sur AST à ce substrat.

---

## 5. Ce qui ne sera pas fait

- Aucun ajustement de bande après lecture des graines d'étude. Un ajustement post-pilote (graine 1000) est possible **avant** l'étude et se commet séparément (v2), en nommant la valeur v1 et la raison.
- Aucune généralisation à la constructibilité de la conscience ni à la phénoménologie (grade C, citation « emphatically does not explain »).
- Aucune prétention d'isomorphisme avec le TPJ ou le schéma attentionnel neurobiologique : le jouet teste le principe de contrôle (citations 1–3) et la lecture du modèle par le rapport (citations 4–6), rien d'autre.
- Le terrain, les bras, les perturbations et les seuils sont écrits avant le module et ne dépendent pas des résultats ; le module est l'exécutant, pas le designer.

---

## 6. Révision v2 (2026-10-30, post-pilote, pré-étude)

**Ce qui a changé.** Le bras `schema` porte désormais une **estimation de saillance EMA α = 0,1** dans son état, et l'observation de position alimentant son updater est l'argmax de cette estimation (et non l'argmax de la saillance brute). Le bras `schema_shuffled` reçoit la même révision : la permutation frappe l'entrée brute **avant** l'EMA de saillance du schéma (le null garde sa force — l'estimation devient une bouillie uniforme et son argmax erre). Tout le reste (terrain, perturbations, métriques, bandes P1a..P5, graines d'étude, verdict) est inchangé.

**Valeurs v1 et le constat du pilote (graine 1000, disjointe, jamais comptée).** Sous v1 (« la saillance brute ne sert qu'à la mise à jour du schéma », lue comme : argmax brut = observation de position) : `reactive` stabilité = 0,0055, correction = 5,8 ; `schema` stabilité = 0,1484, correction = 8,2 ; `erreur_pred(schema)` = 0,089 ≈ persistance = 0,073 — les deux dominés par les bascules d'argmax. Mécanisme : à σ_s = 0,3, l'argmax **brut** bascule entre items ~25–30 % des pas (cible capturée 2,0 ± 0,3 vs distracteur capturé 1,6 ± 0,3), alors que l'argmax de l'EMA du bras reactive bascule rarement (σ_effectif ≈ 0,3·√(α/(2−α)) ≈ 0,13). Les deux bras ne recevaient donc **pas des entrées comparables** — le reactive observait « position de la cible + jitter minuscule », le schema « position d'un item quasi aléatoire + jitter énorme » — en violation de la clause de contrôle du §3 (« même budget de calcul — **seule l'organisation de l'état diffère** »). Le pilote v1 est committé comme preuve (`ict/results/attention_schema_control_pilot_v1_seed1000.json`).

**Pourquoi cette révision plutôt qu'une autre.** La citation 1 du §1 définit le schéma comme « a coherent set of information that represents basic stable properties of attention, reflects ongoing changes in the state of attention, makes predictions about where attention can be usefully directed » — une estimation de saillance est littéralement une pièce de cet ensemble (« reflects ongoing changes »). L'EMA α = 0,1 la maintient **plus lente** que l'EMA α = 0,3 du bras reactive : le schéma reste l'organisation appauvrie/lente, le reactive le suiveur rapide — la comparaison teste toujours l'organisation de l'état, sur des entrées désormais de même nature. Aucune bande n'est retouchée : si le schéma v2 perd encore, le verdict REFUTED se publie tel quel.

**Protocole.** Une seule révision (celle-ci), avant l'étude held-out, en commit distinct nommant les valeurs v1 (fait ci-dessus) ; le texte v1 reste visible dans l'historique git. La graine 1000 reste disjointe ; son rejeu sous v2 est calibration, jamais preuve.
