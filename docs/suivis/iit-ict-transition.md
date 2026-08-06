# IIT → ICT — note de transition

> Note de transition durable de la série [`MyIA.AI.Notebooks/IIT/ICT-Series/`](../../MyIA.AI.Notebooks/IIT/ICT-Series/) (Epic [#4588](https://github.com/jsboige/CoursIA/issues/4588), plan de partition [#5081](https://github.com/jsboige/CoursIA/issues/5081)) — pivot narratif et architectural IIT → ICT. Posée initialement au cycle c.478 (po-2025 : `myia-po-2025:CoursIA-2`), tenue à jour au fil des livraisons.

Cette note **n'est pas** un substitut des documents fondateurs de la série — qui sont
déjà posés, conservés verbatim, et font foi :

- [`ICT-0-Framing.md`](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-0-Framing.md) — cadrage narratif (la méthode « Integrated Causal Trajectories », filiation Levin + Hoel + Thom).
- [`ICT-0-Annexe-IntegratedComplexityTheory.md`](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-0-Annexe-IntegratedComplexityTheory.md) — texte fondateur de la théorie « Integrated Complexity Theory » (discussion ChatGPT re-fournie par le user le 2026-07-03), préservé verbatim.
- [`README.md`](../../MyIA.AI.Notebooks/IIT/README.md) — fondations PyPhi et panorama IIT.

Cette note **trace** les fils qui se sont tissés entre la série IIT historique et la
série ICT, et **référence** les ancres existantes. Elle est exécutive : un lecteur
qui la lit doit savoir où se trouve quoi, et pourquoi la transition a eu lieu.

---

## 1. Pourquoi une transition ?

La série **IIT / PyPhi** apprend à mesurer l'organisation causale d'un système **à un
état donné** — matrice de transition (TPM), sous-système, $\Phi$, structure
cause-effet (CES), partitions, coarse-graining. C'est une **photographie** : une
forme causale figée à un instant.

La série **ICT** déplace la question vers le **film** :

```
C0 → C1 → C2 → ... → Cn
```

où chaque $C_t$ est une description causale intégrée — ou un résumé causal — du
système à l'instant $t$. Les questions deviennent dynamiques et multi-échelles :
comment une structure causale évolue-t-elle dans le temps ? Conserve-t-elle une
**identité** malgré les perturbations ? Quelles transformations sont locales,
globales, réversibles, irréversibles ? Existe-t-il une **macro-description** plus
lisible ou plus causale que la micro-description ?

ICT ne remplace pas IIT : ICT **consomme** IIT (PyPhi reste le calcul de référence
pour les petits systèmes, voir ICT-1 / ICT-5) et **ajoute** une couche `ict/`
chargée de la simulation, des trajectoires, des mesures dynamiques et des
primitives multi-échelles. C'est cette partition — couche `ict/` à côté de PyPhi —
qui est documentée dans [§ « Architecture » de ICT-0-Framing](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-0-Framing.md#architecture-une-couche-ict-à-côté-de-pyphi).

## 2. Double lecture du sigle ICT

Le sigle **ICT** porte deux lectures **qu'il faut tenir ensemble**, et qui ont
longtemps été confondues :

| Lecture | Sens | Source | État dans le dépôt |
|---|---|---|---|
| **Integrated Complexity Theory** | Théorie : un $\Phi_\text{dyn}$ qui répond aux critiques classiques d'IIT (intractabilité, caractère statique de $\Phi$, absence de dynamiques temporelles, explosion combinatoire, adéquation phénoménologique) | Discussion ChatGPT, re-fournie par le user 2026-07-03 | [`ICT-0-Annexe-IntegratedComplexityTheory.md`](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-0-Annexe-IntegratedComplexityTheory.md), préservation verbatim |
| **Integrated Causal Trajectories** | Méthode construite : partir d'un substrat minimal (le tri auto-organisé), y exhiber expérimentalement la robustesse, le délai de gratification, l'agrégation par affinité, l'émergence causale multi-échelles | Filiation Levin (tri-morphogenèse) + Hoel (émergence causale) + Thom (sémiophysique) | Série `ICT-Series/` ICT-1 à ICT-25 |

La réconciliation tient en **une phrase** (citée du cadrage, [ICT-0-Framing § « Double lecture »](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-0-Framing.md#double-lecture-du-sigle)) :

> *Les trajectoires causales intégrées sont la voie calculable vers la théorie de la complexité intégrée.*

- la **théorie** pose le langage unificateur (ce que $\Phi_\text{dyn}$, l'énergie
  libre, la compression cherchent à capturer) ;
- la **méthode** construit les cas calculables qui instancient ce langage et
  permettent de le mesurer *sans complaisance* ;
- la **strate 5** (ICT-14 → ICT-24) ferme la boucle : sur le banc cross-substrat,
  les trois scalaires fondateurs $\Phi / F / K$ se rencontrent ; l'identité MDL,
  l'$\epsilon$-machine et le LLM comme quatrième substrat réalisent littéralement
  la théorie fondatrice sur des substrats où le tri ne suffit plus.

## 3. Partition du travail — couche `ict/` à côté de PyPhi

L'inventaire à jour de la couche `ict/` est dans [ICT-0-Framing § « Architecture »](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-0-Framing.md#architecture-une-couche-ict-à-côté-de-pyphi). Les modules livrés incluent :

| Module | Rôle | Première livraison |
|---|---|---|
| `ict/self_sorting.py` | Modèle vue-cellule (Cell, SelfSortingArray, scheduler) | ICT-2 [#4588](https://github.com/jsboige/CoursIA/issues/4588) |
| `ict/kin_sorting.py` | Règles enrichies : réparation bidirectionnelle + affinité kin | ICT-4 |
| `ict/sorting_metrics.py` | Sortedness, monotonie, inversions, agrégation, recovery | ICT-2 / ICT-3 |
| `ict/trajectories.py` | Évolution d'états, attracteurs, trajectoire de $\Phi$, événements | ICT-1 / ICT-10 |
| `ict/causal_emergence.py` | CE 2.0 (Hoel 2025) : primitives causales, apportionnement, EC | ICT-5 / ICT-6 |
| `ict/tpm_estimation.py` | Pont simulation → chaîne de Markov → TPM | ICT-6 |
| `ict/scale_free.py` | Diagnostic scale-free (MLE de Hill, KS, choix de $x_{\min}$) | ICT-7 |
| `ict/bistable.py` | Modèle de pâturage de May, potentiel effectif, bifurcation pli | ICT-8 |
| `ict/early_warning.py` | Variance/AR1 roulantes, τ de Kendall, amincissement, détrendage | ICT-8 |
| `ict/reaction_diffusion.py` | Simulateur Gray-Scott (Laplacien périodique, contrôle) | ICT-9 |
| `ict/agency.py` | Ablation `do(·)`, structure, recovery_score, repair_gain, similarité spectrale | ICT-9 / ICT-11 |
| `ict/catastrophe.py` | Fronce (cusp), équilibres/plis, lacet d'hystérésis, `p̂` | ICT-10 |
| `ict/time_arrow.py` | TPM, inversion temporelle, réversibilisation, $\sigma$, detailed balance error | ICT-18 [#5279](https://github.com/jsboige/CoursIA/issues/5279) |
| `ict/workspace.py` | Axe Global Workspace (Dehaene, Baars) — module livré | ICT-24 [#5641](https://github.com/jsboige/CoursIA/issues/5641) |

PyPhi reste le calcul de référence pour $\Phi$ strict sur petits systèmes (ICT-1,
ICT-5). La couche `ict/` ne duplique pas PyPhi : elle l'appelle ponctuellement et
fait tout le reste (simulation, trajectoires, mesures multi-échelles, instruments
thermodynamiques).

## 4. Strates de la série ICT

| Strate | Notebooks | Substrat / instrument | Fil conducteur |
|---|---|---|---|
| **Strate 1** — tri transparent | ICT-1 à ICT-7 | Tri auto-organisé → TPM → émergence causale → signature scale-free | Le tri comme morphogenèse minimale (Zhang, Goldstein & Levin 2025) ; l'émergence causale multi-échelle (Jansma & Hoel 2025) |
| **Strate 2** — morphogenèse dynamique | ICT-8 à ICT-10 | Paysage d'attracteurs (May bistable), régénération (Gray-Scott), grammaire des catastrophes (Thom) | Le système **génère** son propre paysage de buts (et ne le reçoit plus) |
| **Strate 3** — agents | ICT-11 à ICT-13 | Profils d'agence causale, animats valence, Axelrod IPD | Trois « jouets » actantiels sur trois substrats différents |
| **Strate 4** — représentationnel | ICT-14 | Free energy / Friston | La jambe énergie-libre du représentationnel (substrat computationnel de l'anticipation) |
| **Strate 5** — convergence & capstone | ICT-15 à ICT-25 | Banc cross-substrat (tri, Gray-Scott, Axelrod, LLM) : convergence $\Phi / F / K$, MDL, $\epsilon$-machine, flèche du temps, batterie ENJEU, feature catastrophes, SAE, persona, Global Workspace | L'appareil unique sur plusieurs substrats, qui pousse ses mesures à leur frontière |

Le détail notebook par notebook est maintenu dans [ICT-0-Framing § « Feuille de route des notebooks »](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-0-Framing.md#feuille-de-route-des-notebooks) — la table de cette section est un index réduit.

## 5. Ancres théoriques et opérationnelles

| Concept | Source théorique | Implémentation ICT | Notebook |
|---|---|---|---|
| Compétence *for free* | Levin (Lex Fridman podcast, 2024-2025) | Tri biased bubble sort, réparation spontanée | ICT-2, ICT-3, ICT-4 |
| Cône de lumière cognitif | Levin, Frontiers Psychology 2019 | Non-mesurable directement (proxy : taille du but) | ICT-0 (cadre) |
| Émergence causale | Jansma & Hoel, *Engineering Emergence* 2025 ; Hoel, Albantakis & Tononi PNAS 2013 | `ict/causal_emergence.py` (CE 2.0) | ICT-5, ICT-6 |
| Signature scale-free | Clauset et al. 2009 (MLE Hill + KS) | `ict/scale_free.py` | ICT-7 |
| Bifurcation pli + EWS | May 1977, Scheffer 2009, Dakos 2012 | `ict/bistable.py` + `ict/early_warning.py` | ICT-8 |
| Agence régénérative | Gray-Scott (Pearson 1993), Levin *competency for free* | `ict/reaction_diffusion.py`, `ict/agency.py` | ICT-9, ICT-11 |
| Grammaire des catastrophes | Thom 1972 (sémiophysique), *sans complaisance* | `ict/catastrophe.py` | ICT-10 |
| Free energy principle | Friston 2010 | ICT-14 livré ([#5089](https://github.com/jsboige/CoursIA/issues/5089)) | ICT-14 |
| $\Phi_\text{dyn}$ | Discussion ChatGPT, ICT-0-Annexe | (instrument thermodynamique `ict/time_arrow.py`, mesure le **MOYEN** de la triade) | ICT-18, ICT-19 |
| MDL / deux-parts code | Grünwald 2007 | ICT-16 livré ([#5099](https://github.com/jsboige/CoursIA/issues/5099)) | ICT-16 |
| $\epsilon$-machine | Crutchfield 1994 | ICT-17 livré ([#5100](https://github.com/jsboige/CoursIA/issues/5100)) | ICT-17 |
| SAE features | Anthropic 2024 | `ict/sae.py` (à venir) | ICT-21 [#5101](https://github.com/jsboige/CoursIA/issues/5101), ICT-22 [#5102](https://github.com/jsboige/CoursIA/issues/5102) |
| Global Workspace | Dehaene, Baars | `ict/workspace.py` (livré #5641) | ICT-24 livré ([#5635](https://github.com/jsboige/CoursIA/issues/5635)) |

## 6. Triade *moyen / fin / enjeu* — l'enseignement propre à ICT-18

ICT-18 (Flèche du temps & réversibilisation, [#5279](https://github.com/jsboige/CoursIA/issues/5279)) a consolidé, au cycle c.477, un cadrage qui manquait à la série : **l'instrument thermodynamique `I_thermo` ne mesure qu'un seul pôle d'une triade**, pas l'agentivité globale.

| Pôle | Sens | Grandeur | ICT-18 le mesure ? |
|---|---|---|---|
| **ENJEU** | Résister à l'équilibration du soi (auto-maintien, clôture de contraintes, *stake*) | Homeostasie, F (Friston) | **NON** — instrument markovien-stationnaire aveugle à la mémoire |
| **MOYEN** | Dissiper, exporter l'entropie, brûlage de gradient | $\sigma$, distance L1/2 à la réversible | **OUI** — c'est exactement `I_thermo` |
| **FIN** | Garder le soi *réversiblement récupérable* (récupérabilité comportementale, Levin *competency for free*) | Accessibilité de l'espace d'états, hystérésis, réparation | **NON** — mesurée par ICT-2/3/9, ICT-15, ICT-17 |

**Bornes opérationnelles** :

- **Faux-NÉGATIF** : ICT-8 (May bistable, friction anisotrope) sort `I_thermo ≈ 0` parce que la distribution stationnaire $\pi$ s'adapte aux taux de bascule pour minimiser la detailed balance. Le système est *comportementalement* très structuré mais *thermodynamiquement* invisible à l'instrument markovien-stationnaire.
- **Faux-POSITIF** : un pur dissipateur sans enjeu (marche aléatoire biaisée, oscillateur chimique piloté) allume `I_thermo` autant que S1 ICT-2 ou S3 ICT-13 sans avoir d'enjeu à défendre.

**Implication épistémique** : `I_thermo` est **nécessaire** (un système à l'équilibre thermodynamique ne lutte pas, il subit) mais **pas suffisant** (une tornade dissipe autant qu'un agent sans être agent). Pour conclure l'agentivité, il faut **corroborer** avec d'autres instruments :

- **ICT-2/3/9** pour la **FIN** (récupérabilité comportementale) ;
- **ICT-14** (free energy / Friston) pour l'**ENJEU** (le *stake* de l'auto-maintien) ;
- **ICT-15 / 17** (complexité intégrée, $\epsilon$-machine) pour la **structure** sous-jacente.

ICT-19 / ICT-19b (cadrage B verrouillé par user 2026-07-06, [#5483](https://github.com/jsboige/CoursIA/issues/5483), implémentation [#5489](https://github.com/jsboige/CoursIA/issues/5489), raffinement [#5728](https://github.com/jsboige/CoursIA/issues/5728)) **fusionne** la batterie MOYEN d'ICT-18 (`I_thermo`) avec la batterie ENJEU (`I_stake` = gain de réparation après `do(·)`) sur le banc cross-substrat S1-S5, avec contrôle négatif obligatoire (S5 = pur dissipateur).

## 7. Lacunes restantes

Connu, planifié, à faire dans un cycle ultérieur :

| Lacune | Cycle attendu | Raison |
|---|---|---|
| **ICT-21 / ICT-22** (LLM comme substrat S4) | GPU-required (Qwen local, RTX 3090) | Non exécutable sur cette machine CPU/.NET |
| **ICT-25** (InoculationRL, capstone pont PostTraining ; phase GPU) | GPU-required | Planifié [#5105](https://github.com/jsboige/CoursIA/issues/5105) — réalignement 3 bras N/I/P avant phase GPU |
| **Catalogue** (`COURSE_CATALOG.generated.json`) | Régén par `catalog-cron.yml` sur `main` | **NE PAS** régénérer sur branche (cf `catalog-pr-hygiene` R1) — laisser le cron faire |

## 8. Ce que cette note livre (PR de transition fondatrice, c.478)

- **Un suivi de transition** (ce fichier) : fil conducteur IIT → ICT, double lecture du sigle, partition `ict/` ↔ PyPhi, strates, ancres théoriques, triade *moyen/fin/enjeu*, lacunes restantes.
- **Aucun notebook modifié** (ICT-18 et ICT-19 restent *tels quels*, dans la lignée « sans complaisance »).
- **Aucun module `ict/` modifié**.
- **Aucun catalogue régénéré** (laisser `catalog-cron.yml` faire sur `main`).

PR : *Part of [#5081](https://github.com/jsboige/CoursIA/issues/5081)* (plan de partition ICT-Series), *See [#4588](https://github.com/jsboige/CoursIA/issues/4588)* (Epic registre ICT), *Part of [#4208](https://github.com/jsboige/CoursIA/issues/4208)* (axe D finition publique).

## 9. Voir aussi

- [ICT-0-Framing.md](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-0-Framing.md) — cadrage narratif complet, feuille de route, principe méthodologique.
- [ICT-0-Annexe-IntegratedComplexityTheory.md](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-0-Annexe-IntegratedComplexityTheory.md) — théorie fondatrice (texte préservé verbatim).
- [README.md de IIT](../../MyIA.AI.Notebooks/IIT/README.md) — fondations PyPhi et panorama IIT.
- Epic [#4588](https://github.com/jsboige/CoursIA/issues/4588) — registre des livrables ICT.
- Plan de partition [#5081](https://github.com/jsboige/CoursIA/issues/5081) — Epic parente c.478.
- Issue [#5279](https://github.com/jsboige/CoursIA/issues/5279) — ICT-18 (flèche du temps), issue [#5483](https://github.com/jsboige/CoursIA/issues/5483) — cadrage B ICT-19 (ENJEU), [#5489](https://github.com/jsboige/CoursIA/issues/5489) — impl. ICT-19, [#5728](https://github.com/jsboige/CoursIA/issues/5728) — raffinement S4 en espace de champ.
- Issue [#5641](https://github.com/jsboige/CoursIA/issues/5641) — module `ict/workspace.py` livré (ICT-24).
- Issues [#5089](https://github.com/jsboige/CoursIA/issues/5089), [#5090](https://github.com/jsboige/CoursIA/issues/5090), [#5099](https://github.com/jsboige/CoursIA/issues/5099), [#5100](https://github.com/jsboige/CoursIA/issues/5100), [#5101](https://github.com/jsboige/CoursIA/issues/5101), [#5102](https://github.com/jsboige/CoursIA/issues/5102), [#5103](https://github.com/jsboige/CoursIA/issues/5103), [#5104](https://github.com/jsboige/CoursIA/issues/5104), [#5105](https://github.com/jsboige/CoursIA/issues/5105), [#5635](https://github.com/jsboige/CoursIA/issues/5635), [#5352](https://github.com/jsboige/CoursIA/issues/5352) — autres issues ICT.

---

*Suivi de cycle c.478, partition native `myia-po-2025:CoursIA-2` (worker ayant
construit ICT-1/2/3 [#5141](https://github.com/jsboige/CoursIA/issues/5141)/[#5145](https://github.com/jsboige/CoursIA/issues/5145)/[#5235](https://github.com/jsboige/CoursIA/issues/5235) — substance, pas sweep).*
