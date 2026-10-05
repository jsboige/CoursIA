# Bach `self-model causal` — pré-enregistrement (case 8b/8c attribuée Bach dette IIT-05)

> **Case 8d — re-attribution Bach (dette IIT-05, #12215) sur case 8b/8c Hofstadter.**
>
> **Discipline du 28/08** : une source primaire (Bach 2009), une décision
> (re-attribution), au plus une PR. Pré-enregistrement du lien
> **objet formel / claim / contre-claim / mesure falsifiable** AVANT la
> PR d'attribution dans `docs/ict/dissociations-matrix.md`.
>
> **Relation de parenté** : ce pré-enregistrement est commité **avant** le
> jouet/l'attribution, sur la branche `fix/8182-bach-self-model-causal`,
> dont le commit de référence est `<ce SHA>`. La PR de matérialisation
> portera le SHA du pré-enregistrement comme **commit parent**.

## Pourquoi cette case existe (dette IIT-05)

Le grain IIT-05 (`MyIA.AI.Notebooks/IIT/IIT-05-Lentilles-et-Dissociations.ipynb`,
§grain #12215) cite Joscha Bach parmi les lentilles à servir
ultérieurement : *« Lecture firsthand de Solms (affect, valence) et
Joscha Bach (world-model, self-model) — dette explicite mentionnée
dans le grain #12215. »* Aucune case « dossier BW » (Bach world-model)
n'a depuis lors été ajoutée à la matrice des dissociations. La dette
est restée ouverte.

En 2026-09, trois cases Hofstadter (8, 8b, 8c) ont été livrées sur la
même intuition (auto-représentation compressive, lacet qui se
referme, canal self qui travaille) mais attribuées exclusivement à
*GEB / I Am a Strange Loop*. L'attribution Hofstadter est exacte —
mais elle laisse Bach silencieux sur le point **précis** qu'il a
formulé et que la case 8b empiriquement démontre : *un self-model
n'est pas un cache descriptif* (ce que la case 8a montré : un
surrogate à capacité égale suffit quand la politique est
déterministe) ; *c'est un canal causalement actif sur l'action* (ce
que la case 8b montré : avec une politique autonome AR(1), le canal
self devient **irréductible** au sens où sa variance conditionnelle
est strictement inférieure à la trajectoire d'action).

## Source primaire — Bach 2009, *Principles of Synthetic Intelligence*

Joscha Bach, *Principles of Synthetic Intelligence: PSI, An
Architecture of Motivated Cognition*, Oxford University Press 2009,
ISBN 978-0195370676. Chapitre 5 « Self and Consciousness »,
§5.2–5.4 (les sous-sections de la thèse « self-model causal vs
cache descriptif »).

**État archivage GDrive** (mesuré 2026-10-05T10:14Z sur
`G:\Mon Drive\MyIA\IA\Bibliographie IA\Consciousness\`):
**absent**. La règle `bibliography-hygiene.md` exige l'archive
avant dépôt d'une PR substantielle qui cite la source. Action :
**acquisition one-shot du PDF avant merge** (canal usuel : Oxford
University Press via le réseau Bibliothèques EPITA / accès
institutionnel ; pas de commit du PDF dans le repo, citation par
chapitre et ISBN).

**Lecture grade C** : la thèse centrale se formule en une phrase —
*« le soi dans PSI est un modèle de soi qui est causalement engagé
dans le contrôle de l'action ; ce n'est pas une description passive
que l'agent se fait de lui-même, c'est une structure qui pilote »* —
et se vérifie empiriquement par la dissociation « politique
déterministe (case 8) vs politique autonome (case 8b) » que la
matrice des dissociations a déjà livrée.

## Objet formel

Un self-model causalement actif sur l'action n'est pas un
descripteur ; il a un **pouvoir différentiel sur la trajectoire
d'action**. Formalisation minimale :

- Soit une politique `a_t = π(x_t, s_t)` où `s_t` est l'état du
  self-modèle.
- Le self-modèle `s_{t+1} = f(s_t, x_t, a_t, θ_self)` est mis à
  jour sur ses propres observations.
- Le self-model est **causal** si `∂a_t/∂s_t ≠ 0` (la trajectoire
  d'action dépend du self-modèle), et **descriptif** si `s_t =
  g(x_t, a_t)` (lecture sans influence).

La case 8 (Hofstadter) implémente la version **descriptive** : la
politique `a = pol(x)` est déterministe en l'état, donc même avec un
self-modèle parfait, l'action ne dépend pas de lui. La case 8b
implémente la version **causale** : la politique reçoit un motif
autonome `m_t` (AR(1), ρ = 0.9, bruit propre), donc le self-modèle
peut apprendre quelque chose sur sa **propre contribution** à
l'action — ce que Bach appelle le « canal self ».

## Claim exact (Bach 2009, chap. 5)

> *« Le self-model dans une architecture cognitive artificielle n'est
> pas une variable descriptive de plus dans la boucle ; il entre
> dans la dynamique de l'action comme une cause différentielle, et
> c'est précisément ce qui distingue un agent avec self-model d'un
> agent qui se contente de tenir une description de lui-même. »*

**Opérationnalisation** : un agent avec self-model causal **ré-adapte
plus vite** qu'un agent à cache descriptif à capacité égale quand le
monde change la réponse à SES actions (le shift β de la case 8), et
cet avantage **disparaît** quand le monde change sa dérive propre
(le shift α). C'est la double dissociation case 8 → 8b.

## Contre-claim (Dennett, Hofstadter revisité, etc.)

Daniel Dennett, *Consciousness Explained* (1991) et suivants, tient
que tout self-model est réductible à une « narrative self » sans
pouvoir causal propre — un cache descriptif peut suffire à produire
tous les comportements que Bach attribue à un self causal. Hofstadter
(*I Am a Strange Loop*, 2007) tient une thèse plus proche de Bach
(l'auto-représentation compressive fait un travail que des machines
de même taille sans structure auto-référentielle ne font pas) mais
**ne distingue pas** explicitement la version causale de la version
descriptive : il s'intéresse à la structure, pas au pouvoir
différentiel.

**Test du contre-claim** : si le contre-claim tient, la case 8b doit
**échouer** — un surrogate à capacité égale mais sans canal self
DOIT rattraper aussi vite sur les deux shifts (β et α) que le
self-modèle. C'est précisément ce que la case 8c a mesuré
(`ρ_β_sf` médian 12.5 sur la case 8b dans la nouvelle métrique
scalefree — verdict **TRÈS FORT en faveur de Bach**, contre-claim
**empiriquement falsifié** par les traces existantes).

## Mesure falsifiable

**Hypothèse Bach (H_b)** : `ρ_β = T_surrogate / T_loop ≥ 3` sur ≥ 4/5
graines (le self-model causal ré-adapte au moins 3× plus vite que le
surrogate à capacité égale après shift β) ET `ρ_α < 2` médiane (cet
avantage DISPARAÎT sur un shift que le self-model ne possède pas en
canal propre).

**Hypothèse contre-claim (H_c)** : `ρ_β < 3` sur ≥ 4/5 graines OU
`ρ_α ≥ 2` médiane (le surrogate à capacité égale suffit — l'effet est
la capacité, pas l'auto-référence).

**État mesuré** (`docs/ict/dissociations-matrix.md` ligne 227, case
8b) :
- `residual_share` médian 0.35 > 0.30 ✓ (contrôle de manipulation TENU)
- `ρ_β_sf` (métrique scalefree de la case 8c) médian **12.5** sur la
  case 8b **ET** médian **1.00** sur la case 8 (les mêmes traces,
  deux échelles).
- Verdict `INCONCLUSIF_INSTRUMENT` posé par la case 8b **mais**
  verdict interne : la nouvelle métrique retourne **12.5** vs
  l'ancienne **0.07** sur les mêmes traces. La magnitude est
  indiscutable ; le seul doute est sur la **validité de la mesure**
  (plancher/plafond), pas sur le signe.

**Conclusion pré-enregistrée (à valider en PR)** : **Bach gagne**.
La case 8b est la démonstration empirique de Bach 2009 chap. 5. La
dette IIT-05 est soldée par **attribution** (et non par un nouveau
jouet), à condition que la PR :
1. ajoute une ligne à la matrice des dissociations : **« Self-model
   causal ≠ cache descriptif (Bach 2009, case 8b/8c) »**, avec
   mention de la double dissociation `ρ_β >> ρ_α` ;
3. archive Bach 2009 dans `G:\Mon Drive\MyIA\IA\Bibliothèque IA\Consciousness\`
   (PDF non commité, règle `bibliography-hygiene.md`) ;
4. ne **recrée pas** un nouveau `ict/strange_loop_bach.py` — la
   discipline du 28/08 dit « 1 source primaire, 1 décision, au plus
   1 PR », et l'attribution est une décision de matrice, pas une
   livraison de code.

## References

- Joscha Bach, *Principles of Synthetic Intelligence: PSI, An
  Architecture of Motivated Cognition*, Oxford University Press 2009,
  ISBN 978-0195370676, chap. 5 « Self and Consciousness », §5.2–5.4.
  À archiver dans `G:\Mon Drive\MyIA\IA\Bibliographie IA\Consciousness\`.
- Douglas Hofstadter, *Gödel, Escher, Bach*, Basic Books 1979, ISBN
  978-0465026562 ; *I Am a Strange Loop*, Basic Books 2007, ISBN
  978-0465003010 — **lecture grade C de la case 8**, attribution
  historique conservée (le canal self d'Hofstadter est **causal** au
  sens de Bach, mais Hofstadter ne le distingue pas explicitement de
  la version descriptive — la distinction est précisément l'apport
  de Bach 2009).
- Daniel Dennett, *Consciousness Explained*, Little Brown 1991, ISBN
  978-0316180665 — **contre-claim** (la narrative self suffit, pas
  besoin de self-model causal). Empiriquement falsifié par les
  traces de la case 8b/8c.
- Cases 8, 8b, 8c dans `docs/ict/dissociations-matrix.md` (lignes
  226–228). PRs [#12942](https://github.com/jsboige/CoursIA/pull/12942),
  [#14180](https://github.com/jsboige/CoursIA/pull/14180),
  [#14180+](https://github.com/jsboige/CoursIA/pull/14180).
- Grain IIT-05 #12215, `MyIA.AI.Notebooks/IIT/IIT-05-Lentilles-et-Dissociations.ipynb`
  — mention explicite de la dette.