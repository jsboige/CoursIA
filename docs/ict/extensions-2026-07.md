# Extensions 2026-07 — la fin, la canonicité, l'identité et le discours

> **Provenance.** Détail déporté du cadrage [ICT-0-Framing.md](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-0-Framing.md) (§ *Extensions 2026-07*), à
> périmètre constant : le texte ci-dessous y était **verbatim** avant le déport ([#15470](https://github.com/jsboige/CoursIA/issues/15470)).
> Le cadrage conserve le cadre de lecture, la carte des strates et les décisions tranchées ; cette page
> porte le détail des quatre fronts ouverts en 2026-07 et la décision de numérotation.
>
> **Rattachement.** Epic [#4588](https://github.com/jsboige/CoursIA/issues/4588).

Le cadrage stratégique de 2026-07 (Epic #4588, section « Jambes 2026-07 ») étend la série sur
quatre fronts, chacun ancré dans un résultat déjà livré :

1. **La « fin » de la réversibilisation, mesurée** (#7287, slot ICT-18b) — **livré**. La troisième
   jambe de la triade moyen / fin / enjeu (#5352) : la réversibilisation comme **ressource** (un
   budget $B(t)$ qui s'épuise et se régénère), au-delà du *moyen* (production d'entropie $\sigma$,
   ICT-18) et de l'*enjeu* (batterie $I_\text{stake}$, ICT-19). Module
   `ict/reversibility_budget.py` + notebook [ICT-18b](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-18b-ReversibilityBudget.ipynb) — deux
   définitions comparées ($B_\text{state}$ Monte-Carlo primaire, $B_\text{work}$ témoin) et verdicts
   pré-enregistrés **P1 PASS / P2 DISSOCIATION / P3 PASS** (détail : feuille de route + notebook).
   La triade a désormais sa jambe mesurée.

2. **La canonicité des scalaires du zoo** (#7288, slot ICT-15b). La synthèse cross-substrat a
   falsifié le « scalaire universel » ($\Phi/F$ covarient, $K$ diverge) ; la question méta devient :
   *qu'est-ce qui rend un scalaire canonique ?* La sensibilité de Huang 2019 (cf.
   `SymbolicAI/Lean/Lean-12-Sensitivity-Theorem` / `Lean-12b`) fournit un candidat de **scalaire
   local** sur les graphes de transition, avec une conjecture de borne à construire puis tester.

3. **Le secret comme canal d'irréversibilisation de l'identité** (ICT-23 → ICT-25). Le résultat
   central de la littérature 2025 (Anthropic, *inoculation prompting*, arXiv:2511.18397 ; OpenAI,
   *persona features*, arXiv:2506.19823) : deux agents RL apprennent le **même** hack de
   récompense, mais seul celui qui triche **en secret** dérive vers une persona désalignée
   généralisée — celui à qui on a **explicitement permis** le raccourci apprend l'acte *sans*
   contamination d'identité. Dans la fronce d'ICT-23, la permission met la charge sémantique de
   l'acte à ~0, donc $a \geq 0$ : potentiel monostable, pas de catastrophe — l'inoculation est le
   **dual opérationnel de la réversibilisation** appliqué à la trajectoire de persona. ICT-25
   l'instancie en poids (protocole 3 bras N secret / I permission / P pénalité-contraste, #5105).

4. **Le discours comme substrat — graine de strate 6** (#7289, puis horizon #7291). Le même
   mécanisme, à l'échelle culturelle : les trajectoires de croyance sur graphes d'arguments
   (Tweety, `argumentation_analysis`, Axelrod augmenté), l'analyse spectrale des structures
   fallacieuses, et la prédiction pré-enregistrée d'une **dette d'irréversibilité du discours** —
   la dissociation $\sigma$ élevé / $K$ faible des régimes rhétoriques manipulatoires (bascules à
   sens unique + slogans compressibles) contre $\sigma$ faible / $K$ élevé des régimes délibératifs.
   L'horizon (collaboration agentique et altérité, #7291) est verrouillé par un **contrat de
   falsifiabilité** écrit avant tout run — la thèse unificatrice n'a pas le droit de
   s'auto-confirmer.

**Numérotation.** Les insertions se font par suffixe `b` — l'option **réversible** (précédent :
Lean-12b) ; la grande renumérotation linéaire (#5081) les absorbera en une PR atomique unique,
déclenchée par la livraison d'ICT-24b + ICT-24c + les verdicts de #7287/#7288. Décision complète :
[#7260](https://github.com/jsboige/CoursIA/issues/7260).
