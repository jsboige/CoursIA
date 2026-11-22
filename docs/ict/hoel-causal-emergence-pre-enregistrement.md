# Pré-enregistrement — Émergence causale (case 25 : l'information effective mesurée — le macro peut-il battre le micro ?)

> **Grade C explicite.** Ce document **scelle** le protocole de la tranche « émergence causale / information effective » de la veille [#8182](https://github.com/jsboige/CoursIA/issues/8182) **AVANT toute écriture du banc de mesure** — héritage direct des tranches Assembly Theory (case 20), Penrose Orch-OR (case 24) et sœurs : source primaire lue et archivée, pré-enregistrement commité avant l'implémentation et la mesure, verdict borné.
>
> **Cycle du 2026-11-21**, lane `myia-po-2024:CoursIA`. Claims : [c.7065272596](https://github.com/jsboige/CoursIA/issues/8182#issuecomment-7065272596) puis [CLAIMED-AMEND c.7065291344](https://github.com/jsboige/CoursIA/issues/8182#issuecomment-7065291344) (périmètre rétréint aux fichiers du case listés au CLAIMED-AMEND ; README série et matrice reportés après résolution des PRs ouvertes #27470/#26601). Correction de citation : [c.7065771004](https://github.com/jsboige/CoursIA/issues/8182#issuecomment-7065771004).

## 1. Source primaire et archivage

**Source primaire** : Erik P. Hoel, Larissa Albantakis, Giulio Tononi, « Quantifying causal emergence shows that macro can beat micro », *PNAS* **110**(49):19790–19795, 3 décembre 2013, DOI [10.1073/pnas.1314922110](https://doi.org/10.1073/pnas.1314922110). **Open access** (PMC3856819).

**Archivage gisement** ([bibliography-hygiene](../../.claude/rules/bibliography-hygiene.md)) : `G:\Mon Drive\MyIA\IA\Bibliographie IA\Probabilistic\2013 - Hoel - Quantifying Causal Emergence Shows That Macro Can Beat Micro (PNAS 110-49 19790-19795, DOI 10.1073_pnas.1314922110, OA PMC3856819).pdf` — 1 128 549 octets, sha1 `de27420b3599108bfebfd78a57fba25a5969ef57`, 6 pages, identité vérifiée sur la **première page** (titre + auteurs + affiliation). Recherche préalable par auteur ET titre (`hoel`, `albantakis`, `tononi`, `causal emergence`, `quantifying`) : **aucune copie préexistante du 2013** — le rayon `Probabilistic` portait déjà Comolatti & Hoel 2022 (*Causal emergence is widespread across measures of causation*) et Hoel 2025 (*Causal Emergence 2.0*) ; le primaire rejoint ce rayon, un seul dépôt.

**Mode de récupération** (traçabilité) : DOI vérifié sur Crossref après autodétection d'un rappel erroné (10.1371/journal.pcbi.1002596 = Tetzlaff, *Decorrelation of Neural-Network Activity by Inhibitory Feedback* — écarté à la vérification p.1) ; PDF obtenu via Wayback Machine (instantané 2022-03-03 de l'endpoint EuropePMC `ptpmcrender.fcgi`, drapeau `id_` = octets originaux), les accès directs (EuropePMC, PMC, PNAS) étant derrière protection anti-robot.

**Méthode de lecture** : texte intégral extrait (`pypdf`, 6 pages) puis **relecture firsthand** par la lane — théorie (p. 19791–19792), les quatre systèmes canoniques (p. 19792–19794), discussion et lignes directrices (p. 19794–19795). **Limite déclarée** : les schémas de câblage (Figs. 2A, 4A, 5A, 6A) sont vectoriels et **illisibles sur ce siège** (modèle sans entrée image) — le banc ne les devine pas : il les **reconstruit par calibrage** sur les valeurs imprimées dans le texte (§5, porte G3), et toute reconstruction non calibrée est exclue des hypothèses.

## 2. Le cadre en deux phrases

Pour un système discret à `n` états de matrice de transition `TPM` (obtenue en perturbant uniformément tous les états, Pearl), l'**information effective** `EI(S) = (1/n) Σ_{s0} DKL(SF|s0 ‖ UE)` — `UE` = distribution moyenne des effets — mesure à la fois la taille du répertoire (`≤ log2 n`) et l'efficacité des mécanismes ; l'**efficacité normalisée** se décompose en `Eff = ⟨déterminisme⟩ − ⟨dégénérescence⟩` (p. 19791). Le **regroupement** (exhaustif, disjonctif, perdant l'identité des micro-éléments — `[[00,01,10],[11]]` légal, `[[00,01],[10,11]]` illégal, p. 19792) définit un macro `SM` par perturbation macro = moyenne des micro-états groupés, et l'**émergence causale** est `CE = EI(SM) − EI(Sm) > 0` : le macro gagne en efficacité plus qu'il ne perd en taille (`ΔEI = ΔIEff + ΔISize`, `ΔISize ≤ 0` toujours, p. 19792).

**Le claim fort du papier** : « for certain causal architectures EI can peak at a macro level in space and/or time » (résumé) — le macro **supervient** sur le micro mais peut le **supplanter** causalement ; les systèmes canoniques imprimés : Fig. 2 (4 AND bruités, émergence spatiale contre le bruit, `CE = 0.40` bits, `EI 1.15 → 1.55`, `Eff 0.29 → 0.78`, déterminisme `0.34 → 0.78`, dégénérescence `0.05 → 0.006`) ; Fig. 4 (6 AND déterministes dégénérés → 3 COPY, `CE = 0.57`, `EI 2.43 → 3`, `Eff 0.4 → 1`, `ΔIEff = 1.79 > −ΔISize = 1.22`) ; Fig. 5 (temporel, mécanismes Markov d'ordre 2, `EI 0.16 (1 pas) → 1.38 (2 pas) → 2.0 (macro)`, `CE = 0.62`) ; Fig. 6 (spatiotemporel 9 neurones, `EI 0.59 → 3.51`, `CE = 2.92`).

**Point de contact avec la matrice de dissociations** : le case interroge le motif « fortement compressé non causalement utilisé » par son contrepoint exact — ici la compression (le regroupement est une **perte d'information** : l'identité des micro-éléments disparaît) **augmente** la puissance causale mesurée. La ligne matrice dira si la veille ICT peut héberger un tel renversement : un macro **plus** causal que le micro qui le porte.

## 3. Question falsifiable

**Le renversement EI-macro est-il reproductible par implémentation indépendante de la seule spécification textuelle, et borné par ses conditions d'impossibilité imprimées ?**

Quatre sous-questions, une par énoncé distinct :

- **H1 (spatial, contre le bruit)** : sur l'architecture Fig. 2 (AND bruités appariés, regroupement `[[00,01,10],[11]]`), `CE > 0` porté principalement par le gain de déterminisme (> 80 % du `ΔIEff`).
- **H2 (spatial, contre la dégénérescence)** : sur l'architecture Fig. 4 (cycle d'AND déterministes → COPY macro), `CE > 0` avec `Eff(SM) = 1` exactement — gain par élimination de dégénérescence seule (micro déjà déterministe).
- **H3 (temporel)** : sur l'architecture Fig. 5 (Markov ordre 2), l'EI **croît** dans l'ordre `EI(1 pas) < EI(2 pas) < EI(macro temporel)`.
- **H4 (réduction, témoin négatif)** : sur un système micro déjà quasi maximal en efficacité (AND/COPY bruités **indépendants**, sans structure de groupe), `CE ≤ 0` sur **tous** les regroupements légaux — la mesure ne crie pas « émergence » partout (lignes directrices (i)/(ii), p. 19795).

**Ce que ce banc n'est pas.** Il ne teste pas la Fig. 6 (9 éléments, spatiotemporel — reconstruire ses règles hétérogènes sans lire la figure sur-déterminerait le câblage par invention) ; il ne teste aucune conscience ni aucun cerveau ; il ne mesure pas la cause-information état-dépendante au-delà de ce qu'exigent les portes instrumentales.

## 4. Le substrat et l'instrument (scellés)

**Substrat** : systèmes finis discrets d'éléments binaires, mécanismes = portes logiques (AND, COPY) sur bruit intrinsèque de probabilité `p` (flip symétrique). TPM exacte par énumération des `2^k` micro-états — **instrument exact, pas de Monte-Carlo** : les graines 0/1/7/42/99 n'entrent que dans les tirages éventuels de membres de classe (déclarés par hypothèse), jamais dans la mesure EI elle-même.

**Instrument (deux implémentations, conforme [organ-first](../../.claude/rules/organ-first-implementation.md))** :
1. **L'organe natif de la série** : [`ict.causal_emergence`](../../MyIA.AI.Notebooks/IIT/ICT-Series/ict/causal_emergence.py) possède DÉJÀ la sémantique complète — `determinism`, `degeneracy`, `effectiveness`, `effective_information`, `causal_profile`, et surtout `partition_profile(groups)` (TPM macro par perturbation uniforme intra-groupe + sommation des colonnes : la construction canonique 2013, p. 19792). Le banc **invoque** cet organe pour toute mesure EI/Eff/det/deg et tout coarse-graining — il ne le réimplémente pas. C'est aussi la première couverture de test directe de cet organe (aucun `test_causal_emergence.py` n'existe).
2. **Contre-vérification indépendante** : `ei_mi(TPM)` dans le banc — forme mutuelle `EI = MI(UC; UE)` entre causes uniformes et effets induits (le papier : « EI is also the mutual information MI(UC;UE) », p. 19791), implémentée par compteurs indépendants de la forme de l'organe.

**Regroupement (implémentation scellée)** : mapping micro→macro **exhaustif, disjonctif par élément, perdant l'identité** ; garde de légalité rejetant `[[00,01],[10,11]]` (l'identité des éléments serait requise) ; perturbation macro = moyenne uniforme sur les micro-états groupés (« macro perturbation », p. 19792) ; TPM macro obtenue par sommation des blocs de la TPM micro sur les micro-états groupés.

**Reconstruction des systèmes (calibrage, pas invention)** : les textes imposent des classes, pas des câblages : Fig. 2 = 4 éléments, chacun AND de **2 entrées** dans l'autre groupe, bruit `p`, groupes {AB}→α, {CD}→β symétriques ; Fig. 4 = 6 AND déterministes en cycle (classe des cycles d'AND à 2 entrées), regroupement en 3 COPY adjacentes ; Fig. 5 = 2 éléments à mémoire d'ordre 2 (burst → burst), fenêtre 2 pas, regroupement temporel `[[00,01,10],[11]]`. Le banc **énumère les câblages et bruits de chaque classe bornée** et retient ceux qui reproduisent les valeurs imprimées (porte G3) ; tout le reste est exclu.

## 5. Prédictions scellées (aucune bande ne sera recalculée après mesure)

### Portes instrumentales (dormantes par construction, mesurées quand même)

| # | Porte | Critère | Si déclenchée |
|---|---|---|---|
| **G1** | accord des deux implémentations | `ei_dkl == ei_mi` à `1e-9` près sur **toutes** les TPM mesurées | `INSTRUMENT_INVALIDE`, aucune hypothèse évaluée |
| **G2** | cas analytiques | COPY parfait k éléments : `EI = log2(2^k)`, `Eff = 1`, `degeneracy = 0` ; bruit total (TPM uniforme) : `EI ≈ 0` ; dégénéré total (toutes lignes identiques ≠ uniformes) : `Eff ≈ 0` | `INSTRUMENT_INVALIDE` |
| **G3** | calibrage des reconstructions | chaque système (Figs. 2, 4, 5) : existence d'un câblage de la classe bornée reproduisant les valeurs imprimées à ±0.06 bit / ±0.03 près (`EI`, `Eff`, déterminisme, dégénérescence) | la figure correspondante est **exclue** de son hypothèse — verdict `NON_CONCLUSIF` pour elle seule, les autres hypothèses restent évaluées |
| **G4** | garde de légalité du regroupement | le mapping illégal `[[00,01],[10,11]]` est **rejeté** par la garde | `INSTRUMENT_INVALIDE` |

### H1 — émergence spatiale contre le bruit

Sur la reconstruction calibrée du système Fig. 2 : **`CE = EI(SM) − EI(Sm) > 0`**, bande scellée **[0.2, 0.6] bits** ; part du gain de déterminisme dans `ΔIEff` **≥ 80 %** (imprimé : 91 %). Verdict : `CONFIRMÉE` si CE > 0 ET bande ET part ≥ 80 % ; `FALSIFIÉE` si CE ≤ 0 ; sinon `PARTIEL`.

### H2 — émergence spatiale contre la dégénérescence

Sur la reconstruction calibrée du système Fig. 4 : **`CE > 0`**, bande **[0.3, 0.8] bits** ; `Eff(SM) = 1.0` exactement (macro COPY parfait) ; micro déterministe (`determinism(Sm) = 1`). Verdict : `CONFIRMÉE` / `FALSIFIÉE` / `PARTIEL` comme H1.

### H3 — émergence temporelle

Sur la reconstruction calibrée du système Fig. 5 : **`EI(1 pas) < EI(2 pas) < EI(SM)`** (imprimé : 0.16 < 1.38 < 2.0) et `CE = EI(SM) − EI(2 pas) > 0`, bande **[0.3, 0.9]**. Verdict comme H1.

### H4 — témoin négatif : la réduction

Système témoin scellé : 4 éléments **indépendants**, chacun COPY bruité de rien (autorégression `x ← x` avec bruit `p = 0.1`) — micro efficace, sans structure de groupe. Prédiction : **`CE ≤ 0` sur chacun des regroupements légaux non triviaux** énumérés (paires adjacentes, regroupement `[[00,01,10],[11]]` par élément). Verdict : `CONFIRMÉE` (la réduction tient) si aucun CE > 0 ; `FALSIFIÉE` si un regroupement légal donne CE > 0 — ce qui serait un contre-témoin sérieux contre la mesure.

### Graines et multi-seed

Instrument exact (TPM énumérées) : les EI ne dépendent d'aucune graine. Les 5 graines canoniques (0/1/7/42/99) servent **uniquement** si un tirage de membres de classe s'avère nécessaire (aucun prévu dans les hypothèses ci-dessus — déclaré). Le JSON de résultats porte le champ `stochastic: false`.

## 6. Verdict global et portée

Verdict global borné par les issues 1 à 4 (aucune agrégation au-delà) : la veille conclura **`SOUTENU`** (le renversement se reproduit sur les architectures calibrées et le témoin négatif tient), **`RÉFUTÉ`** (un CE ≤ 0 sur H1/H2/H3 calibrées, ou H4 livre un CE > 0), **`PARTIEL`**, ou **`NON_CONCLUSIF`** (portes G1/G2/G4, ou G3 pour toutes les figures). Portée écrite : ce verdict dit si **la construction EI/regroupement de Hoel 2013 survit à une réimplémentation indépendante depuis le seul texte** — il ne dit rien des mesures voisines (Comolatti 2022) ni d'aucun système biologique réel, et la ligne matrice de dissociations le formule ainsi.

See #8182
