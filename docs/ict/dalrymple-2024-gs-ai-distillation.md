# Distillation CB2 (#16761) — Dalrymple et al. 2024, "Towards Guaranteed Safe AI"

> **Statut.** Carte blanche **CB2** du tracker de distillation #16741 (corpus Tegmark + crew IAIFI/BAF, 16 publications). Distillation **grade C-documentaire** (cadrage + extraction verbatim, **pas** de cadrage opérationnel ni de false claim). Issue-source : [#16761](https://github.com/jsboige/CoursIA/issues/16761). Épisode du cadrage Epic : [#16741](https://github.com/jsboige/CoursIA/issues/16741). *Part of* [#7395](https://github.com/jsboige/CoursIA/issues/7395) (méta-proxy ICT).
>
> **Passe de vérification intégrale (2026-10-02, lane myia-po-2023).** Relecture des 30 pages du PDF du gisement contre ce fichier : le résumé-index §4 de la v1 comportait des détails non sourcés (verifiers nommés **absents du texte**) — corrigé ci-dessous ; ajout des sections §5 (route alternative interp→preuve), Appendix A (définition causale du harm) et Appendix B (Definition B.1 formelle, le tuple ⟨π, m, ψ, Vψ⟩).
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

## Section 4 — Examples of GS AI Solutions (les 8 exemples, vérifiés intégral)

Le papier énumère **8 exemples canoniques** où la triade se déploie — « from current- or near-term tractable and economically viable applications, to ones that have not yet been realised due to their more ambitious scope ». Chaque exemple suit le gabarit Problem / Specification / World Model / AI System (le **verifier n'est pas systématiquement nommé** par le papier dans chaque exemple) :

| # | Exemple | Specification | World Model | AI System |
|---|---|---|---|---|
| 4.1 | Code Translation (C → Rust) | Functional correctness (équivalence source/cible sur l'état de programme pertinent) + absence de classes de vulnérabilités ; specs parfois **partielles** | Contraintes sur les entrées (**pré-conditions**) + threat models de sécurité | LLMs de génération de code (GPT-4, Claude, modèles spécialisés) |
| 4.2 | Autonomous Vehicle Safety | « **Rulebook** » (Censi et al. 2019) : règles munies d'un pré-ordre — fonctions objectifs, logique temporelle, bornes probabilistes, automates — + spec core restreinte pour le(s) backup system(s) | Scénarios formalisés : composants de l'AV, agents et objets (avec modèles de comportement), environnement (contraintes spatiales, météo), modèles des humains et de leurs préférences — stochastiques ; programmation probabiliste (ex. Scenic) ; runtime monitors vérifiant l'*operational design domain* | Pipeline DNN (perception → prédiction → planning → contrôle), LLMs pour les interfaces humaines |
| 4.3 | Household Robots | Tâches ménagères diverses (nettoyage, rangement, apport d'objets) + navigation sûre autour des humains + adaptation aux besoins et environnements spécifiques | Diversité des foyers (layouts, tâches) + contraintes du robot (sécurité, efficacité) | VLMs multi-task + mécanismes de continuous learning |
| 4.4 | Medical Diagnosis Agent | Diagnostic précis à partir des symptômes + causes sous-jacentes + recommandations de traitement | Corps humain (physiologie et pathologie) + facteurs environnementaux | Système multi-média (notes diagnostiques, imagerie médicale) |
| 4.5 | Compute Centre Management | Allocation efficace selon les accords business + conformité légale (ex. compute caps) + sécurité (détection des breaches) | Écosystème de calcul partagé : isolation tenant, allocation de ressources, hardware cryptographiquement sécurisé | Modèle entraîné à l'allocation optimale sous contraintes économiques, légales et de sécurité |
| 4.6 | Formally Verified Re-Implementation (Cyber Defence) | Fonction intentionnelle du code legacy + absence de bugs/vulnérabilités | **Autoformalisation** : prendre le legacy et en **inférer sa fonction intentionnelle** | Agent « Software Engineer » : réimplémentation via autoformalisation + *interactive specification crafting* avec les stakeholders |
| 4.7 | Safe Nucleic Acid Screening & Synthesis | Rejet des séquences utilisables pour pathogènes/toxiques ; identification des séquences bénéfiques | Relation structures moléculaires ↔ pathologie | « Bioengineering agent » vérifiant qu'un risque de mésusage reste sous une borne conservatrice |
| 4.8 | Stabilisation of the Climate System | Stabilité du système climatique + santé de l'écosystème | Dynamique climatique complexe sous divers régimes d'intervention | « Climate agent » générant des solutions de **géo-ingénierie** qui *verifiably stabilise* le climat |

> **Correction vs la v1 de cette distillation** (passe intégrale du 2026-10-02). La première mouture du résumé-index citait des détails **absents du texte** : « equivalence checker » (4.1), « bounded model checking » (4.2), « objets endommagés / hyperproperty » (4.3), « false positive/negative rate + épidémiologie + conformal prediction » (4.4), « SLOs + monitoring » (4.5). « Conformal prediction » a **0 occurrence dans tout le papier**. La dette « géo-ingénierie (?) » de l'item 8 est levée : le texte dit bien *geoengineering*, sans jeu de mot.

**4.6 est la charnière T15** : le world model n'y est pas un simulateur entraîné mais **l'autoformalisation du code legacy** — l'inférence formelle de sa fonction intentionnelle. Le programme « interp → preuve » de T15 y trouve son cas d'usage industriel exact : extraire la sémantique du legacy, la faire valider par les stakeholders (interactive specification crafting), puis synthétiser une réimplémentation prouvée bug-free.

## Section 5 — Discussion : la route alternative interp→preuve

Le passage le plus directement utile à T15, absent des résumés usuels du papier : Dalrymple et al. reconnaissent que **GS AI n'est pas la seule route** vers des garanties quantitatives, et décrivent une alternative qui **n'utilise pas de world model séparé** :

> *"An alternative approach might be to extract interpretable policies from black-box algorithms via automated mechanistic interpretability and directly proving safety guarantees about these policies. This approach differs from GS AI in that it does not make use of a world model that is separate from the policy; instead, it requires that the policy can itself be made interpretable."* (§5, p. 16-17)

**Le trade-off est asymétrique, et le papier le dit par deux exemples** :

- Les **règles des échecs sont moins complexes** qu'une politique qui joue bien aux échecs ;
- Il est **plus facile de spécifier les axiomes de la géométrie euclidienne** qu'un programme bon en démonstration géométrique.

Autrement dit : « it may be much easier to create an interpretable world model than to create a performant interpretable policy » — mais « it is ultimately an empirical question whether it is easier to create interpretable world models or interpretable policies in a given domain of operation ».

**Lecture pour T15/T17** : c'est l'axe le long duquel la strate 7 doit se positionner. La triade ⟨W, S, V⟩ suppose le monde modélisé **séparément** de la politique ; la route interp→preuve suppose la politique **rendue interprétable** (par mech interp automatisée) puis prouvée directement. Les deux convergent vers un V9/V10 mais ne paient pas le même coût : la première paie en world model, la seconde en complexité de la politique extraite. T15 (autoformalisation Lean) est structurellement du **second** type — la « politique » qu'on formalise est le raisonnement lui-même. À noter aussi : le papier crédite le **GPS de Newell & Simon (1961)** du premier système à composantes séparées world-modelling/specification/verification — la triade est une convergence revendiquée, pas une nouveauté.

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

## Appendix A — une définition causale du harm

Le papier formalise « harm » — que la section challenges notait être « *a vague predicate* » — sur un **modèle causal étendu** :

1. **Base** : DAG causal classique — variables exogènes (déterminées hors du modèle) et endogènes (équations de leurs parents) ; une intervention crée un nouveau modèle ; contrefactuel « A plutôt que A′ est cause de B plutôt que B′ ».
2. **Extension 1 — utility on outcomes** : variable endogène spéciale « outcome », chaque valeur associée à une utilité normalisée dans [0,1] (sans perte de généralité : un ensemble d'outcomes se « package » en une seule variable).
3. **Extension 2 — default utility** : utilité de référence, **contextuelle**, qui représente l'attendu/le « normal » du scénario.

**Définition du harm (deux conditions conjointes)** : un événement X=x cause un harm s'il existe x′ et des outcomes o, o′ tels que (i) l'utilité de l'outcome réel o est **inférieure à la default utility**, et (ii) X=x plutôt que X=x′ cause o plutôt que o′, où l'utilité de o est inférieure à celle de o′.

Le papier qualifie cette définition d'« appealing starting point », immédiatement tempéré : *"implementing this in a complex world model to meaningfully cover the utilities, the downstream implications of an event, etc. are, to put it mildly, a challenge."*

## Appendix B — Definition B.1 : le tuple formel ⟨π, m, ψ, Vψ⟩

La Definition 3.1 verbatim (cf. supra) possède une version formelle, utile à toute implémentation du cadre :

| Composante | Type | Note |
|---|---|---|
| **Policy** π | (O×A)\* × O → ∆(A) — distribution d'actions pour chaque historique d'observations/actions | Π = ensemble de toutes les politiques |
| **World model** m | S×A → **P**(∆(O×S)) — un **ensemble** de distributions d'états/observations | note 15 : couvre le cas déterministe m : S×A → ∆(O×S) **et** le cas **credal set** |
| **Safety specification** ψ | ϕ : Π×M → [0,1] — une valeur par couple (policy, world model) | |
| **Verifier** Vψ | Π×M → P([0,1]) — calcule ou estime ψ(π, m) | note 16 : **anytime** — Vψ(π, m, t) ⊆ Vψ(π, m, t′) dès que t ≤ t′ (estimations de plus en plus précises) ; peut être probabiliste (vecteur aléatoire en entrée) |

> Un système GS AI est un **tuple ⟨π, m, ψ, Vψ⟩** où π est une politique telle que Vψ(π, m) tombe dans un ensemble admissible.

**Lecture T15** : la monotonie **anytime** du verifier (note 16) est la propriété qui rend le programme **incrémental** — un verifier conforme n'a pas à terminer, il doit resserrer ses estimations. C'est exactement la forme d'une boussole de strate 7 : une preuve qui se raffine, pas un certificat binaire.

## Voir aussi

- [strate7-boussole-myth.md](strate7-boussole-myth.md) — cadrage strate 7 (la boussole, sans la triade)
- [dissociations-matrix.md](dissociations-matrix.md) — dissociations ICT
- [hoffman-interface-distillation.md](hoffman-interface-distillation.md) — pattern distillation grade C
- [#16741](https://github.com/jsboige/CoursIA/issues/16741) — Epic distillation corpus Tegmark
- [#16756](https://github.com/jsboige/CoursIA/issues/16756) — T15 : de l'interp à la preuve formelle
- [#16758](https://github.com/jsboige/CoursIA/issues/16758) — T17 : contrôle par interp
- [arxiv 2405.06624](https://arxiv.org/abs/2405.06624) — page originale
