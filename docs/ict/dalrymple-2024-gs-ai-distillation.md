# Distillation CB2 (#16761) — Dalrymple et al. 2024, "Towards Guaranteed Safe AI"

> **Statut.** Carte blanche **CB2** du tracker de distillation #16741 (corpus Tegmark + crew IAIFI/BAF, 16 publications). Distillation **grade C-documentaire** (cadrage + extraction verbatim, **pas** de cadrage opérationnel ni de false claim). Issue-source : [#16761](https://github.com/jsboige/CoursIA/issues/16761). Épisode du cadrage Epic : [#16741](https://github.com/jsboige/CoursIA/issues/16741). *Part of* [#7395](https://github.com/jsboige/CoursIA/issues/7395) (méta-proxy ICT).
>
> **Objet.** Distiller le cadre « guaranteed safe (GS) AI » — tel que défini par Dalrymple, Skalse, Bengio, Russell, Tegmark + 12 co-auteurs (cf. infra) — dans la perspective de **T15 (boussole : de l'interp à la preuve formelle, [#16756](https://github.com/jsboige/CoursIA/issues/16756))** et de **T17 (contrôle par interp : refusal, unlearning, finetuning shallow, [#16758](https://github.com/jsboige/CoursIA/issues/16758))**. Le GS fournit une **triade terminologique canonique** (world model, safety specification, verifier) qui pose la question de T15 (le « verifier » = notre « boussole ») à l'échelle d'un système AI complet.
>
> **Avertissement méthodologique.** (a) Le texte de cette distillation cite **verbatim** les énoncés de l'abstract et de la Definition 3.1 du papier, et **résume** (sans reformuler les formules) les sous-aires et challenges. (b) Les **claims croisés** (« cité par R10 §6 », « cité par R11 §2.3.2 » du corps de #16761) **sont faux** d'après l'extraction first-hand du PDF jointe ci-dessous : **R10 (Engels 2405.14860) n'est PAS dans les références du papier Dalrymple**, et **R11 (Singapore 2608.14611) est daté 2026 — postérieur au papier v3 (2024-07-08), donc R11 cite Dalrymple et non l'inverse**. La traçabilité est en [§Citations croisées](#citations-croisees--verification-first-hand).
>
> **Suite.** Le **scope** est **cells dans T15** ([#16756](https://github.com/jsboige/CoursIA/issues/16756)) : T15 est un grain non-claimé qui pourra absorber cette distillation comme **cas terminal** du programme (« le verifier de Dalrymple = notre boussole, mais au niveau du programme prouvé »). T17 consommera la triade au niveau contrôle (refusal/unlearning comme safety specifications partielles S1–S3 du spectre). Pas d'issue dédiée — la distillation vit dans ce fichier, point.

## Source et identification

| Métadonnée | Valeur | Source |
|---|---|---|
| **Référence arXiv** | 2405.06624v3 | `https://arxiv.org/abs/2405.06624` |
| **Date v3** | 8 juillet 2024 | arXiv page header |
| **Date v1** | 10 mai 2024 | arXiv page header |
| **Date v2** | 17 mai 2024 | arXiv page header |
| **Titre verbatim** | Towards Guaranteed Safe AI: A Framework for Ensuring Robust and Reliable AI Systems | arXiv page header |
| **Auteurs (17)** | David "davidad" Dalrymple, Joar Skalse, Yoshua Bengio, Stuart Russell, Max Tegmark, Sanjit Seshia, Steve Omohundro, Christian Szegedy, Ben Goldhaber, Nora Ammann, Alessandro Abate, Joseph Y. Halpern, Clark Barrett, Ding Zhao, Tan Zhi-Xuan, Jeannette Wing, Joshua B. Tenenbaum | arXiv page header |
| **Sujet** | cs.AI (Computer Science — Artificial Intelligence) | arXiv page header |
| **sha256 (4 premiers MiB)** | `134b9166470b3789bc85e4fc33edb075ad47e7ea64ae2d76b506b455e48c54dd` | `python hashlib`, première page vérifiée |
| **sha8** | `134B9166` | troncature |
| **Taille intégrale** | 2 086 079 octets (~30 pages) | confirmé contre arXiv PDF |
| **Gisement GDrive** | `G:\Mon Drive\MyIA\IA\Bibliographie IA\XAI\2024 - Dalrymple et al - Towards Guaranteed Safe AI.pdf` | vérifié post-téléchargement (c.754, 2026-09-21) |

## Résumé de l'argument (5 lignes, paraphrase de l'Intro §1)

1. Définit « guaranteed safe (GS) AI » comme une famille d'approches visant des garanties quantitatives à haute assurance sur le comportement d'un système AI.
2. Les trois piliers : *formal safety specification*, *world model*, *verifier* (cf. verbatim Definition 3.1, §[Definition GS AI](#definition-3.1--gs-ai-verbatim) ci-dessous).
3. Le cadre GS est à la fois *promising* et *underexplored* par rapport aux approches existantes (benchmarking, red-teaming, RLHF, etc.).
4. Identifie des avenues de recherche en cours, leurs difficultés centrales, et des approches pour les résoudre.
5. La motivation : les infrastructures critiques requièrent déjà une certification rigoureuse ; l'AI s'approche d'une criticité comparable — la charge de la preuve doit migrer du développeur vers une **évidence formelle**.

## Definition 3.1 — GS AI (verbatim)

> *"A Guaranteed Safe AI system is one that is equipped with a quantitative safety guarantee that is produced by a (single, set of, or distribution of) world model(s), a (single, set of, or distribution of) safety specification(s), and a verifier, satisfying the following criteria:*
>
> *1. The probabilistic specification encodes societal risk criteria, which should ideally be determined by collective deliberation.*
>
> *2. The verifier provides a quantitative guarantee (in the form of a proof certificate, probabilistic bound, asymptotic guarantee, or other comparable assurance) that the AI system satisfies the specification with respect to the world model.*
>
> *3. All potential future effects of the AI system and its environment relevant to the safety specification should be modelled (and – if feasible – conservatively over-approximated) by the world model."*

**Sens in-text des trois piliers** (Section 3 intro, paraphrase contrôlée) :

| Pilier | Sens |
|---|---|
| **World model** | « describes the dynamics of the AI system's environment » |
| **Safety specification** | « a property that we wish an AI system to satisfy » / « a mathematical description of what effects are acceptable » |
| **Verifier** | « produces quantitative assurances for a given AI system » / « in the most straightforward form … a formal proof that the AI system (or its output) satisfies the safety specification relative to the world model » |

## Les trois spectres — W0–W5, S0–S7, V0–V10

Le papier dote ses trois piliers d'**échelles de sophistication** numérotées, qui servent de *graded target* : à chaque niveau, ce qui est exigé du pilier **monte**. Cette structure en spectre est directement réutilisable par T15 (le *verifier* V10 = preuve concise lisible par humain = exactement la « boussole » du titre de strate 7 [strate7-boussole-myth.md](strate7-boussole-myth.md)).

### Spectre W (world model)

| Niveau | Description résumée | Approches citées par le papier |
|---|---|---|
| **W0** | No model (comportement empirique) | — |
| **W1** | Trained black-box simulator | generative AI entraînement classique |
| **W2** | ML generative causal model testé contre modèles humains | mechanistic interpretability, scénarios contrefactuels |
| **W3** | Audited probabilistic causal model | probabilistic programs audités |
| **W4** | Formally verified sound abstractions of physics | méthodes formelles + physique |
| **W5** | Universally quantified specification over all worlds | idéal limite, hors d'atteinte pratique |

### Spectre S (safety specification)

| Niveau | Description résumée | Approches citées |
|---|---|---|
| **S0** | No spec (test ad hoc) | — |
| **S1** | Human judges (annotation humaine) | RLHF, jury humain |
| **S2** | Natural-language spec interprétée par black-box AI | LLM-as-judge |
| **S3** | Hand-written limited formal specs | PCTL/PSL, hyperproperties partielles |
| **S4** | Top-level logic spec with neural components | reward machines, neural-symbolic |
| **S5** | Compositional AI-synthesised audited parts | Cooperative IRL (CIRL), reward learning |
| **S6** | Hand-written comprehensive formal specs | logiques temporelles, types |
| **S7** | Complete encoding of all human preferences | idéal limite |

### Spectre V (verifier)

| Niveau | Description résumée | Approches citées |
|---|---|---|
| **V0** | No guarantee | — |
| **V1** | Ad-hoc empirical testing | smoke tests |
| **V2** | Standardised tests | test suites |
| **V3** | Property-based avec domain randomisation | QuickCheck-style |
| **V4** | Black-box fuzzing | AFL |
| **V5** | White-box fuzzing | KLEE, symbolic exec |
| **V6** | Probabilistic inference avec convergence asymptotique | PAC-learning |
| **V7** | Asymptotic + white-box | PAC + symbolic |
| **V8** | Non-asymptotic convergence bounds | PAC-Bayes |
| **V9** | Sound probability bound | proof certificate formel |
| **V10** | Human-readable concise proof | preuve lisible, auditable |

**Convergence utile** : `T15` vise structurellement un **V9→V10** dans la nomenclature Dalrymple (preuve sound/auditable au-dessus de `world model` W2–W3 et `spec` S4–S5). C'est l'endroit où la « boussole » de la strate 7 touche l'AI safety comme discipline — pas comme métaphore.

## Challenges identifiés (par pilier, wording du papier)

### World model
- Trouver une solution satisfaisante à la **gestion simultanée des incertitudes bayésienne et knightienne**.
- Hypothèses qui ne valent que « *part of the time* ».
- Trade-off **interprétabilité vs. accuracy prédictive**.
- **Complexité computationnelle** (pour W4, modèles basés sur la physique).

### Safety specification
- Difficultés à formuler des specs adéquates.
- Les fonctions de récompense « *cannot typically express hyperproperties* ».
- « *Most data sources are insufficient for identifying the underlying reward function uniquely, even in the limit of infinite data* ».
- **Goodhart's law**.
- Reward model appris « *is itself typically not interpretable* ».
- « *Harm is a vague predicate* ».

### Verifier
- « *Traditional formal methods face unique challenges for AI systems* » (Seshia et al., 2016).
- « *Obtaining such guarantees currently imposes a very high burden* ».
- « *Not all AI components have formal specifications* » → compositional verification sans compositional specs.
- **Complexité computationnelle** (jambe partagée avec W).

## Section 4 — Examples of GS AI Solutions (résumé-index)

Le papier énumère **8 examples canoniques** où la triade se déploie. Ce sont des *applications types* qui valident que la triade **n'est pas jouet** :

1. **Code Translation** — spec sur préservation sémantique, world model = typings, verifier = equivalence checker.
2. **Autonomous Vehicle Safety** — spec sur zones de collision évitées, world model = dynamique véhicule + environnement, verifier = bounded model checking.
3. **Household Robots** — spec sur objets endommagés (hyperproperty).
4. **Medical Diagnosis Agent** — spec sur false positive/negative rate, world model = épidémiologie, verifier = conformal prediction.
5. **Compute Centre Management** — spec sur SLOs, verifier = monitoring.
6. **Re-implementation Bug-Free for Cyber Defence** — re-implémentation formellement vérifiée de logiciels/matériels.
7. **Safe Nucleic Acid Sequence Screening & Synthesis** — biocontrôle (risque ex classique de biosécurité).
8. **Stabilisation of the Climate System** — géo-ingénierie (?) — *à vérifier dans le texte intégral, il y a peut-être un jeu de mot absent*.

## Vers T15 — la boussole épouse la triade

Le cadrage strate 7 ([strate7-boussole-myth.md](strate7-boussole-myth.md)) fixe deux cascades non-récolées (descriptive vs performative). La triade Dalrymple **fonde un troisième statut** : le **statut certifié**. Sortir du non-recollement entre les deux cascades ne se fait pas en dialectique — il se fait en *garantie vérifiée*.

- **Cascade descriptive** ↔ **World model W (description du monde)**.
- **Cascade performative** ↔ **Safety specification S (effets à garantir)**.
- **Boussole** ↔ **Verifier V (preuve que S ⊨ W)**.

T15 ([#16756](https://github.com/jsboige/CoursIA/issues/16756)) pourra absorber cette carte en posant la question : **à quel niveau V (0..10) chacune de nos livraisons « prouvées » (Lean, vericoding, sandbox) se place-t-elle ?** Cette mesure replace la strate 7 dans un *graded objective*, pas dans une prose mystique.

## Vers T17 — la triade au niveau contrôle

T17 ([#16758](https://github.com/jsboige/CoursIA/issues/16758)) traite le **contrôle par interpretabilité** : refusal direction, ablation, steering, unlearning, finetuning shallow. Dans la nomenclature Dalrymple :

- Ces techniques sont des **safety specifications partielles** (S2–S3) — un *refusal direction* encode une direction latente, ce n'est pas une spec formelle.
- Elles s'appuient sur un **world model W1–W2** (modèle entraînable mais partiellement audité).
- Le **verifier** est V3–V4 (property-based testing, fuzzing white-box sur les activations) — pas de preuve formelle.

Pousser T17 vers W3 + S5 + V7 serait un **progrès substantiel et falsifiable**. Pousser T17 vers W5 + S7 + V10 serait le programme de T15 — *mais seulement après* que T17 ait livré ses *property-based tests* mesurés (T17 **ne peut pas sauter V3 pour aller à V10** sans saignée expérimentale).

## Citations croisées — vérification first-hand

Le corps de l'issue #16761 affirmait deux claims de citation croisée. **Tous deux sont faux** d'après l'extraction verbatim de l'agent lecteur du PDF (c.754, Run ab2afa4d3ae6fa72e + Run a29d75c0af0cb9164) :

| Claim (corps #16761) | Vérification first-hand | Verdict |
|---|---|---|
| « **cité par R10 §6** » (R10 = Engels et al., *Not All Language Model Features Are One-Dimensionally Linear*, arXiv:2405.14860) | Grep sur PDF intégral : **0 occurrence** de « Engels », « linear features », « 14860 » | **FAUX** |
| « **cité par R11 §2.3.2** » (R11 = Casper et al., *The 2026 Singapore Consensus*, arXiv:2608.14611) | R11 daté 2026 — **postérieur** au v3 (2024-07-08). Grep sur PDF Dalrymple : **0 occurrence** de « Singapore ». Donc le sens de la citation est inversé si elle existe : **R11 cite Dalrymple** (qui est cité comme exemple de programme GS), pas Dalrymple qui cite R11 | **INVERSION DE SENS** |

**Traçabilité de l'extraction first-hand** : deux runs agents lancés c.754 (2026-09-21) — `ab2afa4d3ae6fa72e` (PDF metadata + abstract + 2 premiers paragraphs) et `a29d75c0af0cb9164` (TOC + §1 + §3 Definition + §3 sous-aires + §3 challenges + §7 conclusion + grep R10/R11). Les deux runs affirment « R10 absent des références, R11 postérieur ».

**Correction recommandée dans #16741 (Epic)** : amender le cartouche « CB2 — cité par R11 §2.3.2 et R10 §6 » en « CB2 — *anti-cité* par R11 (Casper 2026 cite ce papier comme exemple canonique de programme GS ; Dalrymple ne cite pas Singapore Consensus puisque Singapore est postérieur). R10 (Engels) n'est PAS cité. ». Conserver la « matière première de T15 » qui est vraie. Le suivi est du ressort du coordinateur (ai-01) ou de la lane portera #16741.

## Conclusion §7 — verbatim

> *"Much work remains to fully develop the GS approach. But given its importance for avoiding AI risks, we argue that the GS agenda deserves substantially more attention and resources than it currently receives. With a concerted research effort on the core technical problems, significant progress could be made. We hope this paper provides a useful starting point and motivation for a wider pursuit of the GS program."*

**Lecture honnête** : le papier pose le programme mais ne prétend pas l'avoir résolu. Pour T15, cela signifie que le **graded target V0..V10** est un *graded aspirational scaffold*, pas un acquis — il invite à des **livraisons incrémentales vérifiées**, pas à un *grand* programme.

## Voir aussi

- [strate7-boussole-myth.md](strate7-boussole-myth.md) — cadrage strate 7 (la boussole, sans la triade)
- [dissociations-matrix.md](dissociations-matrix.md) — dissociations ICT
- [hoffman-interface-distillation.md](hoffman-interface-distillation.md) — pattern distillation grade C
- [#16741](https://github.com/jsboige/CoursIA/issues/16741) — Epic distillation corpus Tegmark
- [#16756](https://github.com/jsboige/CoursIA/issues/16756) — T15 : de l'interp à la preuve formelle
- [#16758](https://github.com/jsboige/CoursIA/issues/16758) — T17 : contrôle par interp
- [arxiv 2405.06624](https://arxiv.org/abs/2405.06624) — page originale
