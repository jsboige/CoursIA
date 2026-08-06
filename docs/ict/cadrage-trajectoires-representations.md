# ICT — Cadrage « trajectoires de représentations » : le pivot états → représentations (N2)

> **Statut.** Document de cadrage, grade **C-documentaire** (positionnement, pas de nouveau
> dispatch ni de nouvelle dépendance expérimentale). Il réalise le livrable explicite de
> l'issue [#7396](https://github.com/jsboige/CoursIA/issues/7396) (N2) : **raccrocher la
> généalogie du représentant interne** — documentée backward (ICT-10 → ICT-17) par
> [`genealogy-representation-interne.md`](genealogy-representation-interne.md) — **aux jambes
> de la strate 5** (grokking, SAE, substrat LLM, persona, workspace, inoculation), et
> **positionner** la thèse normative qui en émerge, sans la démontrer.
>
> **Objet.** Décrire la **famille** des phénomènes où l'objet suivi n'est plus l'état du
> système mais sa *représentation* (interne, apprise), et marquer les **ponts qui résistent**
> à un transport formel — comme le fait la généalogie backward, mais en projetant vers
> l'échelle LLM et la dynamique d'entraînement.
>
> **Discipline (HARD, issue #7396).** *Pas d'unification prématurée.* On décrit la famille,
> on ne force pas une théorie unique. La thèse normative qui émerge du résultat Anthropic
> (cf. §3) est **positionnée comme une thèse à situer**, non assertée. Aucun nom décoré
> (lettre grecque, « structure ») sur un objet non encore constaté au-delà de l'échelle jouet.

Issue-source : [#7396](https://github.com/jsboige/CoursIA/issues/7396). See [#4588](https://github.com/jsboige/CoursIA/issues/4588).

## 1. Le pivot états → représentations

La généalogie backward ([`genealogy-representation-interne.md`](genealogy-representation-interne.md))
raconte comment un système qui extrapole ponctuellement un signal devient un système qui
*possède un état causal résumant son passé prédictif* (maillons 1–6, ICT-10 → ICT-17). Cette
généalogie s'arrête à l'**état causal** (ε-machine de Crutchfield) — le descendant formel le
plus naturel du scalaire `p̂` initial, mais mesuré sur des **signaux jouets** (prédation,
champ de valence, Gray-Scott).

Le pivot N2 pose la question suivante : **que devient le représentant interne quand le
substrat cesse d'être un signal jouet pour devenir un modèle entraîné à l'échelle du
milliard de paramètres ?** La strate 5 de la série ICT a instrumenté ce saut : le
représentant n'est plus extrapolé par un algorithme hand-crafted (EMA, Kalman), il est
**appris** par optimisation (features SAE, représentations latentes d'un transformer). Le
pivot états → représentations est donc, opérationnellement, le passage du **représentant
calculé** au **représentant appris**.

> **Honnêteté (G.1).** Ce passage n'est **pas** un transport formel démontré. La généalogie
> backward marque déjà (garde-fou 1) qu'aucun transport formel `p̂` → SAE / J-lens n'est
> établi. N2 **décrit la famille** que ce transport *relierait s'il existait* ; elle ne le
> postule pas. Chaque jambe ci-dessous est ancrée dans un notebook **livré et mesuré** ;
> les ponts entre jambes sont qualifiés *conceptuels*, pas *démontrés*.

## 2. La généalogie étendue : trois jambes au-delà d'ICT-17

À la suite des six maillons backward, trois jambes strate-5 projettent le représentant vers
l'échelle entraînée. Comme les maillons backward, chacune **répond à une insuffisance du
précédent** — mais cette fois l'insuffisance n'est plus *dans la forme du représentant*
(scalaire → distribution → code → état causal), elle est *dans la dynamique qui le produit*
(calculé → appris → régularisé → normé).

### Jambe A — ICT-17b : le représentant devient une *dynamique* (grokking)

[`ICT-17b-Grokking-CompressionProgress`](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-17b-Grokking-CompressionProgress.ipynb)
(strand Schmidhuber, #7258) confronte la **jambe K** (compression) à l'entraînement. La
synthèse cross-substrat avait *falsifié* l'hypothèse d'un scalaire universel Φ/F/K : Φ et F
covarient (τ ≈ +1.00), **K diverge** (τ ≈ +0.33), suggérant que la jambe K n'est pas un
niveau statique mais une **dynamique**. Le grokking (transition de phase représentationnelle
pendant l'entraînement, vérifié contre Power et al. 2022) est précisément le phénomène où le
représentant *change de régime* : mémorisation → généralisation. **Insuffisance levée** :
le représentant cesse d'être un instantané pour devenir une *trajectoire dans l'espace des
représentations*, indexée par le temps d'entraînement. C'est le pont vers la lecture Thom
du grokking (catastrophe de la représentation, #7259).

### Jambe B — ICT-21 / ICT-22 : le représentant à l'échelle LLM (SAE)

[`ICT-21-SAETrajectoires`](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-21-SAETrajectoires.ipynb)
(#5101) fait entrer le substrat S4 au banc, et [`ICT-22-LLMSubstrat`](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-22-LLMSubstrat.ipynb)
(#5102) pose le transformer comme **quatrième substrat** du banc cross-substrat. Le
représentant n'est plus lu sur la TPM d'un signal jouet : il est extrait comme **features
SAE** (sparse autoencoder) d'un LLM. L'objet mesuré change d'espèce : d'un scalaire ou d'un
état causal, on passe à un **dictionnaire de features** dont la structure (clustering,
rareté, couverture) est elle-même l'objet. **Insuffisance levée** : la représentation cesse
d'être ponctuelle pour devenir *structurée* — un dictionnaire, pas un nombre. Le panneau
cross-échelle (700M → 120B, rectification A4, PR #7889) est ouvert ici.

### Jambe C — ICT-24 : l'opérateur W (workspace), pas un `p̂` structuré

[`ICT-24-WorkspaceIgnition`](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-24-WorkspaceIgnition.ipynb)
(#5635) mesure l'**opérateur `W_t`** — ce qui rend des composantes disponibles à d'autres
mécanismes. Comme le souligne la garde-fou 2 de la généalogie backward, `W_t` n'est **pas**
`p̂` structuré : `p̂` est un *contenu*, `W_t` est une *organisation de l'accès*. La
dissociation `q_t` bon / `W_t` sélectif (ICT-24) est la **preuve par dissociation** que les
deux grandeurs ne se réduisent pas l'une à l'autre. **Insuffisance levée** : la
représentation, pour être *utilisée*, doit non seulement être bonne mais être *rendue
disponible* — l'opérateur W articule représentation et contrôle.

| Jambe | Notebook | Opération | Grandeur | Insuffisance levée |
|---|---|---|---|---|
| A | ICT-17b | Grokking (K dynamique) | Trajectoire du représentant | Représentant statique → dynamique |
| B | ICT-21/22 | SAE + substrat LLM | Dictionnaire de features | Représentant scalaire → structuré |
| C | ICT-24 | Workspace (W) | Organisation de l'accès | Représentation → disponible au contrôle |

## 3. Le chantier normativité : la jambe qui résiste (thèse à situer, non assertée)

[`ICT-23-PersonaCatastrophe`](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-23-PersonaCatastrophe.ipynb)
(#5104, capstone Partie 1 CPU-only) est le **micro-analogue** des phénomènes Anthropic
(*Inoculation Prompting*, novembre 2025, arXiv:2511.18397 — *rapporté* par le notebook,
vérifié firsthand dans son en-tête). [`ICT-25-InoculationRL`](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-25-InoculationRL.ipynb)
(#5105, capstone final) pousse l'inoculation jusqu'à GRPO à récompense *hackable* et au pont
ICT ↔ PostTraining.

De ces jambes **émerge** — sans être démontrée — une thèse positionnée par #7396 :

> **Thèse (à situer, non assertée).** Le résultat Anthropic (règles explicites ⇒ les personae
> pathologiques n'émergent pas) suggère que **le normatif fait partie du système, pas de son
> commentaire** : la norme est une composante de la dynamique représentationnelle
> (inoculation, régularisation par instruction), pas un méta-commentaire externe posé
> *après* l'apprentissage.

**Pourquoi c'est une thèse et pas un résultat.** Le micro-analogue ICT-23 (fronce de Thom
sur le désalignement émergent) et l'inoculation ICT-25 (GRPO hackable) **rendent le phénomène
mesurable à l'échelle jouet**, mais le pont vers la *thèse générale* « le normatif est
intrinsèque à la dynamique représentationnelle » reste **conceptuel**. Ce document la
**positionne** (il l'identifie comme le fil directeur des jambes Persona/Inoculation) sans la
**démontrer** ni la postuler comme établie. Sa falsifiabilité est claire : si l'inoculation
s'avère n'être qu'un *patch externe* sans effet sur la dynamique représentationnelle interne
apprise, la thèse meurt — et la jambe se replie sur un constat purement comportemental.

## 4. Garde-fous d'honnêteté

### Garde-fou 1 — Le saut d'échelle n'est pas un transport formel

Le passage représentant-jouet (`p̂`, ICT-10) → représentant-LLM (features SAE, ICT-21) n'est
**pas** démontré formellement. La généalogie backward le dit déjà (garde-fou 1) ; ce document
le réitère pour la projection forward. Ce qu'on a, c'est une **continuité conceptuelle**
(chaque jambe répond à une insuffisance) et une **continuité de l'objet étudié** (le
représentant interne, sous ses espèces successives). Le pont `p̂` → dictionnaire SAE est le
**chantier cross-échelle** (#5105 / rectification A4), pas un résultat.

### Garde-fou 2 — Le workspace (W) n'est pas `p̂` structuré (déjà établi)

Réitéré de la généalogie backward (garde-fou 2) : `W_t` (ICT-24) est une organisation de
l'accès, distincte du contenu représentationnel `q_t`. La jambe C **étend** la matrice de
dissociations ([`dissociations-matrix.md`](dissociations-matrix.md)), elle ne fusionne pas W
et q.

### Garde-fou 3 — La thèse normative n'est pas une inclusion dans la généalogie

La thèse du §3 **n'ajoute pas un maillon** à la généalogie représentationnelle : elle
identifie un **fil directeur transversal** aux jambes Persona/Inoculation. Présenter
l'inoculation comme « le maillon 7 de la généalogie de `p̂` » serait forcer une unification
que les données ne soutiennent pas. La thèse est *orthogonale* à la généalogie (elle porte
sur la *production* du représentant, non sur sa *forme*).

## Ce que ce document n'est pas

- **Pas une théorie unifiée.** N2 décrit une **famille** (les phénomènes où l'on suit une
  représentation apprise plutôt qu'un état calculé) et positionne une **thèse** (la
  normativité intrinsèque). Ni l'un ni l'autre ne subsume les jambes.
- **Pas une démonstration du transport cross-échelle.** Le saut signal-jouet → LLM est
  *ouvert*, pas *fermé*.
- **Pas une assertion de la thèse normative.** Elle est *située* (identifiée comme fil des
  jambes 23/25) et *falsifiable* (meurt si l'inoculation est un patch externe sans effet
  interne), pas *assertée*.
- **Pas un nouveau dispatch.** Aucune nouvelle dépendance expérimentale. Les notebooks
  ICT-17b/21/22/23/24/25 sont livrés et mesurés ; ce document les relie sous le parapluie
  « états → représentations » que #7396 ouvre.

## Repères vérifiables

- Généalogie backward (maillons 1–6, ICT-10 → ICT-17) : [`genealogy-representation-interne.md`](genealogy-representation-interne.md) (issue-source #7735).
- Grille 3-régimes (transversale, orthogonale au fil diachronique) : [`synthese-invariants-dissociations-obstructions.md`](synthese-invariants-dissociations-obstructions.md).
- Matrice de dissociations (colonne `q_t` indexée par la généalogie, `W_t` distinct) : [`dissociations-matrix.md`](dissociations-matrix.md).
- Jambes strate 5 : [ICT-17b](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-17b-Grokking-CompressionProgress.ipynb) (grokking, #7258) · [ICT-21](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-21-SAETrajectoires.ipynb) (SAE, #5101) · [ICT-22](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-22-LLMSubstrat.ipynb) (substrat LLM, #5102) · [ICT-23](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-23-PersonaCatastrophe.ipynb) (persona, #5104) · [ICT-24](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-24-WorkspaceIgnition.ipynb) (workspace, #5635) · [ICT-25](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-25-InoculationRL.ipynb) (inoculation, #5105).
- Cadrage `p̂`/`q_t` vs prégnance thomienne : [`docs/grothendieckian-lens.md`](../grothendieckian-lens.md) §3 (post-rectification A1, PR #7889).
- Issue-source : [#7396](https://github.com/jsboige/CoursIA/issues/7396) · Epic umbrella [#4588](https://github.com/jsboige/CoursIA/issues/4588).
