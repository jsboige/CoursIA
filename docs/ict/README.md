# ICT — Index de la documentation de cadrage et de synthèse

> **Portée.** Index thématique des 10 documents de cadrage et de synthèse de la série ICT (Integrated / Integrated-Coordination Theory de la strate 7). Tous sont au **grade C-documentaire** : positionnement, consolidation, cartographie — *aucun ne revendique un résultat démontré* ; ils nomment, articulent ou cartographient ce que les notebooks ICT expérimentent.
>
> **Épics de rattachement.** [#4588](https://github.com/jsboige/CoursIA/issues/4588) (Epic umbrella ICT) · [#7395](https://github.com/jsboige/CoursIA/issues/7395) (méta-proxy ICT). Les issues-sources de chaque jambe sont citées dans le document correspondant.

## Cartographie des 10 documents

Les documents se répartissent en **trois modes d'écriture** explicitement distingués dans [`d1-c4-rencontre-meta.md`](d1-c4-rencontre-meta.md) §0 — *vertical* (un fil de lecture), *horizontal* (une cartographie), *méta* (une articulation entre deux livrables).

### Mode vertical — les fils de lecture (synthèses transversales)

Chaque fil est un angle d'attaque distinct sur le même objet (la strate 7 / ICT) ; les fils ne se réduisent pas les uns aux autres.

| Document | Rôle |
|----------|------|
| [`synthese-invariants-dissociations-obstructions.md`](synthese-invariants-dissociations-obstructions.md) | **Fils 1–3** (Grothendieck / Schmidhuber / Thom + Grothendieck) : trois régimes de lecture d'une trajectoire — invariants, dissociations, obstructions. Point d'entrée des fils. |
| [`genealogy-representation-interne.md`](genealogy-representation-interne.md) | **4e fil** — le problème de la représentation interne : généalogie successive de `p̂` à travers les notebooks ICT-10 → ICT-17. |
| [`dissolution-scalaires.md`](dissolution-scalaires.md) | **5e fil** — la dissolution successive des scalaires : ce qui arrive à Φ, F, K quand on les pousse hors de leur substrat d'origine (ICT-1 → ICT-22). |
| [`strate7-boussole-myth.md`](strate7-boussole-myth.md) | **6e fil** — la boussole de la strate 7 : un mythe fondateur (auto-référence performative fractale) qui fixe la direction sans se déguiser en hypothèse scientifique. |

### Cadrages formels — les jambes (D1 / D3 / C4 / N2)

Les « jambes » sont des cadrages autonomes et complémentaires (pas redondants) : chacune porte une face que les autres ne portent pas.

| Document | Rôle |
|----------|------|
| [`strate7-cadres-libres.md`](strate7-cadres-libres.md) | **Jambe D1** — le formalisme : variables libres bien choisies, free coordinates de 2e ordre, jeu évolutif `G_t`, mécanisme `M`, 6 proxys, dette d'irréversibilité. Issue [#7745](https://github.com/jsboige/CoursIA/issues/7745). |
| [`jambe-c4-propagation.md`](jambe-c4-propagation.md) | **Jambe C4** — la grammaire de propagation & seuil de bascule `(π, W, causalité)` : quand une représentation locale transforme le tout. Jambe *inter-jambes* centrale (Thom / Grothendieck / Luhmann / Friston). Issue [#7743](https://github.com/jsboige/CoursIA/issues/7743). |
| [`cadrage-trajectoires-representations.md`](cadrage-trajectoires-representations.md) | **Pivot N2** — le pivot états → représentations : passage du « où est-on » au « comment est-ce représenté ». |

### Mode horizontal — cartographies

Lectures *horizontales* : où les fils se rejoignent, s'éloignent, se mélangent ou s'affrontent — et ce qui empêche de monter trop vite de dissociation à obstruction.

| Document | Rôle |
|----------|------|
| [`tresse-cartographie.md`](tresse-cartographie.md) | Cartographie de la **tresse** (Thom / Grothendieck / Schmidhuber / Friston) + hiérarchie de sobriété + deux ponts Conway. Issue [#7738](https://github.com/jsboige/CoursIA/issues/7738). |
| [`dissociations-matrix.md`](dissociations-matrix.md) | **Matrice de dissociations** (notebook × claim × proxy × contrôle × réplicats × type × verdict × portée) — ossaturée par la factorisation 4-objets `(s, q, π, W)` dégagée par l'audit #4. |

### Mode méta — articulation

| Document | Rôle |
|----------|------|
| [`d1-c4-rencontre-meta.md`](d1-c4-rencontre-meta.md) | **Méta-cadrage D1 ↔ C4** — la rencontre du formel et de l'opérationnel. Reformule l'isomorphisme `ρ_c = (π_c, W_c, P_c)` en termes symétriques (D1 *nomme*, C4 *mesure* — et réciproquement), borne ce que le pont permet et interdit. N'écrivable qu'après que D1 et C4 eurent chacun leur cadrage autonome. |

## Parcours suggéré

- **Entrée par les fils** (lecture verticale) : [`synthese-invariants-dissociations-obstructions.md`](synthese-invariants-dissociations-obstructions.md) → [`genealogy-representation-interne.md`](genealogy-representation-interne.md) → [`dissolution-scalaires.md`](dissolution-scalaires.md) → [`strate7-boussole-myth.md`](strate7-boussole-myth.md).
- **Entrée par les jambes** (cadrage formel) : [`strate7-cadres-libres.md`](strate7-cadres-libres.md) (D1) → [`jambe-c4-propagation.md`](jambe-c4-propagation.md) (C4) → [`d1-c4-rencontre-meta.md`](d1-c4-rencontre-meta.md) (leur articulation).
- **Entrée par la carte** (vue d'ensemble) : [`tresse-cartographie.md`](tresse-cartographie.md) (la tresse) + [`dissociations-matrix.md`](dissociations-matrix.md) (la matrice 4-objets).

## État et provenance

Tous les documents consolident un travail mené sur la série de notebooks ICT et les conversations de référence (cadrage stratégique 2026-07-19, tour 523 audit #4, tour 755 jambe C4 2026-07-20). Ils sont *postérieurs* aux livrables expérimentaux qu'ilscadrent — c'est ce timing (synthèse *après* les jambes) qui les rend lisibles. Aucun ne crée de nouvelle dépendance expérimentale ; ils ne dispatchent pas de nouveau notebook.
