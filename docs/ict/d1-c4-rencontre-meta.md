# ICT — Méta-cadrage D1 ↔ C4 — la rencontre du formel et de l'opérationnel

> **Statut.** Document de cadrage **méta** (mode 3 d'articulation), grade **C-documentaire**. Ni vertical (par fil : Thom, Grothendieck, Schmidhuber, Friston), ni horizontal (cartographie de la tresse, [#7738](https://github.com/jsboige/CoursIA/issues/7738)) : ce document **articule** ce que le cadrage formel D1 ([#7745](https://github.com/jsboige/CoursIA/issues/7745), [`strate7-cadres-libres.md`](strate7-cadres-libres.md)) et la jauge opérationnelle C4 ([#7743](https://github.com/jsboige/CoursIA/issues/7743), [`jambe-c4-propagation.md`](jambe-c4-propagation.md)) *se doivent mutuellement*. Il ne refait ni l'un ni l'autre : il explicite le **seuil commun** (ρ_c ↔ (π_c, W_c, P_c)), montre **pourquoi** ce seuil est le même objet vu sous deux angles, et identifie **ce que cette articulation rend possible** (et ce qu'elle interdit). *See* [#4588](https://github.com/jsboige/CoursIA/issues/4588) (Epic umbrella ICT). *Part of* [#7395](https://github.com/jsboige/CoursIA/issues/7395) (méta-proxy ICT).
>
> **Objet.** (a) **Reformuler l'isomorphisme** ρ_c = (π_c, W_c, P_c) en termes symétriques (D1 *nomme*, C4 *mesure* — mais aussi C4 *contraint* D1, D1 *qualifie* C4) ; (b) **montrer** que cette articulation n'est ni redondante (chaque jambe fournit un contenu que l'autre ne porte pas) ni accidentelle (elle est *nécessaire* parce que la strate 7 a une face formelle et une face opérationnelle inséparables) ; (c) **borner** ce que le pont permet (passer d'une jambe à l'autre dans un raisonnement) et ce qu'il interdit (réduire l'une à l'autre, ou agréger les 3 dimensions en un scalaire — cf. dissolution Φ/F/K [#7736](https://github.com/jsboige/CoursIA/issues/7736)).
>
> **Discipline.** Cadrage grade C, **AUCUNE nouvelle dépendance expérimentale** n'est créée. Pas de notebook, pas de banc, pas de verdict. Le présent document *consolide* deux cadrages existants (D1 livré c.1246 PR [#9596](https://github.com/jsboige/CoursIA/pull/9596), C4 livré c.1247 PR [#9601](https://github.com/jsboige/CoursIA/pull/9601) OPEN), et explicite leur articulation *après* que les deux jambes aient été posées séparément. C'est précisément ce timing (méta-cadrage *après* les deux jambes) qui rend le pont lisible : on ne pouvait pas l'écrire avant d'avoir les deux faces.
>
> **Avertissement méthodologique.** Ce document **n'est pas** une promotion de la jauge `(π, W, causalité)` au rang de « vrai » seuil de la strate 7, ni une réduction du jeu évolutif `G_t` à la grammaire de propagation. La rencontre est *bidirectionnelle*, pas hiérarchique. D1 et C4 sont **complémentaires** au sens strict : chacune a la moitié d'un objet que l'autre moitié ne porte pas. Cf. [`strate7-cadres-libres.md`](strate7-cadres-libres.md) §0 et [`jambe-c4-propagation.md`](jambe-c4-propagation.md) §0 — les deux cadrages posent explicitement leur propre *avertissement méthodologique* ; le présent document assume les deux.

## 0. Pourquoi un troisième mode d'articulation

Les cadrages déjà livrés sur la strate 7 et la jambe C4 se répartissent en deux modes d'écriture :

1. **Mode vertical** — un *fil de lecture* (Thom : Sémiophysique [#7739](https://github.com/jsboige/CoursIA/issues/7739), Grothendieck : variables libres [lens](../grothendieckian-lens.md), Schmidhuber : compression-progress / beauty [#7258](https://github.com/jsboige/CoursIA/issues/7258), Friston : active inference [#7735](https://github.com/jsboige/CoursIA/issues/7735)). Chaque fil est *un* angle d'attaque sur le même objet (la strate 7 / C4) ; les fils ne se réduisent pas les uns aux autres (cf. cartographie de la tresse [#7738](https://github.com/jsboige/CoursIA/issues/7738), [`tresse-cartographie.md`](tresse-cartographie.md)).
2. **Mode horizontal** — une *cartographie* qui croise les fils et pose leur non-recollement. La cartographie ne dit pas *ce que disent les fils* : elle dit *comment ils se croisent sans se recoller*. C'est le mode du document [`tresse-cartographie.md`](tresse-cartographie.md) (c.1239, B4 non-recollement).

Le présent document introduit un **mode 3** — un mode *méta* :

3. **Mode méta** — une *articulation entre deux livrables* qui ne sont ni verticaux (ils ne sont pas un fil) ni horizontaux (ils ne sont pas une cartographie), mais qui sont **deux faces du même objet**. D1 et C4 sont deux faces du seuil de bascule / seuil de performativité de la strate 7. Ce mode n'était *pas* écrivable avant que D1 et C4 aient chacun leur cadrage autonome : un méta-cadrage *avant* les deux jambes aurait été un cadrage *supplémentaire* qui se serait substitué à l'une d'elles.

Ce timing *post*-D1-*post*-C4 est la raison pour laquelle ce document arrive en c.1248 (après c.1246 D1 et c.1247 C4), et **pas avant**.

## 1. L'isomorphisme reformulé en termes symétriques

### 1.1 D1 *nomme*, C4 *mesure* — et inversement

C4 §4.1 pose que « ρ_c dans D1 = (π_c, W_c, P_c) dans C4 ». Reformulons cette égalité en termes **symétriques** :

| Côté formel (D1) | Côté opérationnel (C4) |
|---|---|
| ρ_c = seuil de performativité du coup ontologique `η` | (π_c, W_c, P_c) = seuils simultanés sur la jauge de bascule |
| *Nomme* le seuil comme une condition sur la *forme* du coup (un `η` est performatif s'il franchit `ρ_c`) | *Mesure* le seuil comme une triple condition sur la *substance* du coup (prégnance de `r`, accessibilité via `W_t`, pouvoir causal do-calculus) |
| Pose la question : « *quelles institutions* permettent l'apparition de vocabulaires utiles sans capture ? » (D1 §2.4) | Pose la question : « *à quel moment* une représentation locale acquiert-elle assez de π / W / P(R) pour transformer le tout ? » (C4 §0, [#7743](https://github.com/jsboige/CoursIA/issues/7743) verbatim) |

Les deux questions sont **équivalentes** au sens où *la réponse à l'une est aussi la réponse à l'autre* — mais elles ne sont **pas** la même question. La question D1 est *institutionnelle* (« quelles règles du jeu ? ») ; la question C4 est *temporelle* (« à quel instant ? »). Une réponse D1 (un seuil *formel* posé pour un coup `η`) **gagne** à être lisible comme une réponse C4 (un triple seuil *opérationnel* sur la bascule) — et réciproquement.

### 1.2 Mais la symétrie n'est pas totale

La symétrie est *partielle*. D1 et C4 ne sont pas deux *vues* interchangeables du même objet : elles sont deux *côtés* du même objet, qui ne portent pas le même contenu.

Ce que **C4 porte en plus** (que D1 ne porte pas) :

- Le **cycle à quatre temps** (totalité → représentant local → énoncé condensé → action en retour) — c'est l'*histoire* d'une bascule, pas seulement sa condition. D1 pose le seuil, C4 raconte l'histoire qui le franchit.
- L'**hystérésis** et la **dette d'irréversibilité** `I(R) > 0` (C4 §2.4) — ce qui distingue un coup performatif d'un coup ornemental. D1 §3 inclut `I(R)` dans le 6-uplet, mais C4 *explique* pourquoi `I(R) > 0` est *nécessaire* (sans hystérésis, la bascule s'évapore).
- Le **do-calculus** appliqué *directement* au cycle : `P(R) = D(Pr(traj|do(R)) ∥ Pr(traj|do(¬R)))`. D1 §3 cite `P(R)` dans le 6-uplet, mais C4 *spécifie* le calcul.

Ce que **D1 porte en plus** (que C4 ne porte pas) :

- Le **jeu évolutif** `G_t = (N, L_t, S_t, A_t, U_t, P_t)` et son **mécanisme** `M` (D1 §2.2-2.4). C4 *assume* un mécanisme qui décide ce qui devient public (C4 §1.3, §4.1) mais ne le *formalise* pas comme un objet à 6 composantes.
- La **non-canonicité** `C_t = |Ext(G_t)|` (D1 §1.2) comme grandeur propre — la *mesure* du fait qu'il y a plusieurs extensions admissibles. C4 utilise l'idée (la grammaire de propagation est elle-même non-canonique) mais ne la *pose* pas comme grandeur mesurable.
- Les **6 proxys** comme **6-uplet** *simultané* (D1 §3) — pas une mesure séquentielle. C4 fait l'un après l'autre (π, puis W, puis P(R)), D1 les pose *ensemble* comme un test d'acceptation composite (sans agrégation en scalaire, cf. §3 ci-dessous).

L'isomorphisme est donc *réel* (le seuil est le même objet) mais *non réducteur* (les deux faces portent des contenus non-substituables).

## 2. Pourquoi cette articulation est *nécessaire* (pas accidentelle)

### 2.1 Le formel et l'opérationnel sont inséparables dans la strate 7

La strate 7 est, par construction, l'endroit où l'agent peut *modifier l'espace dans lequel il agit*. Cette propriété — *l'auto-modification de l'espace* — n'a de sens **que si elle est à la fois** :

- **Formellement** posable comme une condition sur le coup (`η : G_t → G_{t+1}` est performatif ssi `η` franchit ρ_c — D1).
- **Opérationnellement** mesurable comme une condition sur la bascule (le coup `η` *est* une bascule représentation-locale → action-sur-tout ssi π ≥ π_c, W ≥ W_c, P(R) ≥ P_c — C4).

**Sans la face formelle** (D1 sans C4), on aurait une condition *vide* : « un coup est performatif s'il franchit un seuil » — mais on ne saurait pas *lequel* ni *pourquoi*. Sans D1, le seuil ρ_c n'est pas *nommé* comme une condition *formelle* ; c'est juste un nombre magique.

**Sans la face opérationnelle** (C4 sans D1), on aurait une mesure *aveugle* : « on mesure π / W / P(R) » — mais on ne saurait pas *à quelle question* cette mesure répond, ni *pourquoi* ces trois dimensions et pas d'autres. Sans C4, le seuil ρ_c n'est pas *mesuré* ; c'est juste une déclaration non-testable.

L'articulation est donc *nécessaire* au sens où chacune des deux jambes *remplit un trou logique* que l'autre laisse ouvert. Ce n'est **pas** une coïncidence que D1 et C4 coïncident sur le seuil : c'est la *condition* pour que la strate 7 ait un sens falsifiable.

### 2.2 L'héritage de la dissolution des scalaires

[`dissolution-scalaires.md`](dissolution-scalaires.md) (c.1238, [#7736](https://github.com/jsboige/CoursIA/issues/7736)) a montré que Φ / F / K covarient (τ = +1.00) ou divergent (K bipolaire puis tri-polaire) : les trois candidats scalaires *ne se laissent pas réduire à un seul*. La leçon n'est pas « tout se vaut » : c'est **« le scalaire avait la mauvaise forme »**.

Cette leçon conditionne l'articulation D1 ↔ C4 :

- **D1 n'agrège pas** ses 6 proxys en un scalaire (D1 §3, *six grandeurs indépendantes*). Si D1 agrégeait, l'articulation avec C4 reviendrait à *réduire* les trois dimensions de C4 à un scalaire — ce que la dissolution a disqualifié.
- **C4 ne réduit pas** ses trois dimensions à un seuil unique (C4 §0, *jauge multi-composantes, pas un scalaire*). Si C4 agrégeait, l'articulation reviendrait à *réduire* les 6 grandeurs de D1 à une seule — symétriquement disqualifié.

L'articulation D1 ↔ C4 hérite donc de la dissolution : c'est une articulation entre **deux multi-composantes** (6 et 3), pas entre un scalaire et un scalaire. Le seuil **commun** ρ_c ↔ (π_c, W_c, P_c) n'est **pas** un scalaire, c'est un **uplet de conditions simultanées** (cf. §3 ci-dessous).

## 3. Ce que l'articulation rend possible

### 3.1 Passer d'une jambe à l'autre dans un raisonnement

L'articulation permet à un raisonnement sur la strate 7 de **basculeur** entre les deux faces sans perte :

- Un argument *formel* (« le coup `η` est non-canonique — il y a plusieurs extensions admissibles — donc `η` peut être performatif ») peut être **traduit** en argument *opérationnel* (« la représentation locale `r` a plusieurs prolongements possibles — donc elle est candidate à la bascule ») sans perte de substance. Le pont `C_t = |Ext(G_t)| ↔ C4 §1.3 « la grammaire est elle-même non-canonique » est *exactement* ce passage.
- Un argument *opérationnel* (« la bascule est mesurée par `P(R)` — la divergence KL entre les trajectoires sous `do(R)` et `do(¬R)` ») peut être **traduit** en argument *formel* (« le coup `η` est performatif ssi sa distribution d'effet est non confondable avec celle de `¬η` — c'est la définition do-calculus de la causalité »). Le pont `P(R)` (D1 §3) ↔ `P(R)` (C4 §2.3) est *exactement* ce passage.

Ces deux traductions sont **non triviales** : elles exigent que le lecteur saisisse pourquoi la *forme* du coup (D1) et la *substance* de la bascule (C4) sont interchangeables *ici*, alors qu'elles ne le seraient pas *ailleurs* (par exemple, pour décrire un phénomène physique sans agentivité).

### 3.2 Borner ce que le pont *ne* permet pas

L'articulation **ne permet pas** :

- **Réduire D1 à C4.** D1 a 6 grandeurs ; C4 en a 3. Les 3 grandeurs de D1 *non reprises* par C4 (`O_t`, `ΔA_t`, `institutionnalisation`) restent des grandeurs *propres* à la face formelle — l'expansion ontologique, l'ouverture politique, et l'institutionnalisation ne sont pas des grandeurs *opérationnelles* au sens C4.
- **Réduire C4 à D1.** C4 a un cycle à 4 temps ; D1 a un jeu à 6 composantes. Le temps 4 de C4 (« action en retour sur la totalité ») est *irréductible* à un coup `η : G_t → G_{t+1}` — c'est l'histoire de la bascule, pas sa condition formelle.
- **Agréger** les 3 dimensions de C4 en un scalaire. La dissolution l'a disqualifié.
- **Agréger** les 6 grandeurs de D1 en un scalaire. Symétriquement disqualifié.
- **Confondre** la *position* dans le 6-uplet D1 (par exemple, `P(R)` est la 4e grandeur, après `O_t`, `ΔA_t`, `C_t`) avec la *séquence* temporelle dans C4 (la séquence π → W → P(R) → I(R) est temporelle, pas ordinale).

## 4. Statut hiérarchique (mesuré / construit / nommé sans démonstration)

| Niveau | Élément |
|---|---|
| **Construit** (formalisé dans le présent cadrage) | L'articulation symétrique (D1 *nomme* et *est nommé par* C4) · la distinction « ce que C4 porte en plus » / « ce que D1 porte en plus » · la *nécessité* (pas l'accidentalité) de l'articulation · les bornes du pont (ce qu'il permet, ce qu'il interdit) · l'héritage de la dissolution Φ / F / K |
| **Nommé sans démonstration** (grade C, posé pour cadrage) | L'idée que *le formel et l'opérationnel sont inséparables dans la strate 7* (§2.1) · l'idée que *les traductions D1↔C4 sont non triviales* (§3.1) |
| **À vérifier** (par les bancs strate 7 futurs) | Que les 6 grandeurs D1 et les 3 grandeurs C4 *covarient* effectivement sur les bancs ICT-26 → ICT-30 (déjà MERGED, mais l'articulation n'a pas été testée comme telle) |

Le passage de « nommé sans démonstration » à « construit » ou « mesuré » reste un **livrable futur** :

- *Construire* = instancier la double face sur une jambe-sœur nouvelle (par exemple : inoculation RL [#5105](https://github.com/jsboige/CoursIA/issues/5105), argumentation [#7289](https://github.com/jsboige/CoursIA/issues/7289), animats ICT-15 [#7288](https://github.com/jsboige/CoursIA/issues/7288)) et vérifier que la *même bascule* est lisible formellement (D1) et opérationnellement (C4).
- *Mesurer* = faire covarier les 6 grandeurs D1 et les 3 grandeurs C4 sur les bancs ICT-26 → ICT-30 (cf. [#7746](https://github.com/jsboige/CoursIA/issues/7746) MERGED), et observer une structure *commune* — pas une agrégation en scalaire, mais une *compatibilité* des multi-composantes.

Ce passage **n'est pas** un claim actuel. Si l'articulation tient ce passage, ce sera une PR grade B à célébrer ; sinon, les éléments resteront au statut « nommé sans démonstration », et le cadrage restera cadrage.

## 5. Ce que ce document n'est pas

- **Ce n'est pas une promotion d'une jambe sur l'autre.** D1 et C4 sont *complémentaires*, pas hiérarchiques. Aucune des deux n'est « plus fondamentale » que l'autre.
- **Ce n'est pas une unification des deux jambes.** L'articulation *explicite* ce qui était implicite (le pont existait déjà en C4 §4, mais y était *à sens unique* : C4 vers D1). Le présent document rend le pont *bidirectionnel*, mais ne le *fond* pas en un objet unique.
- **Ce n'est pas une thèse sur la conscience.** Comme D1 et C4, le présent document décrit la *forme* de l'articulation, pas le *contenu* subjectif qu'elle pourrait avoir.
- **Ce n'est pas une PR de code ou de notebook.** C'est un **méta-cadrage**. Aucun notebook n'est créé ou modifié.
- **Ce n'est pas un déblocage de quoi que ce soit.** Les jambes gelées (C3 [#7742](https://github.com/jsboige/CoursIA/issues/7742), horizon strate 6 [#7291](https://github.com/jsboige/CoursIA/issues/7291)) restent gelées ; l'articulation D1 ↔ C4 n'est *pas* un chemin pour les dégelner — elle *explicite* la rencontre entre deux livrables déjà posés.
- **Ce n'est pas un matériau strate 6/7 sensible.** Cf. [#8182](https://github.com/jsboige/CoursIA/issues/8182) jalon 3 — la frontière privé → public est stricte. Le présent document reste au niveau de la *forme* de l'articulation, pas des cas qu'elle instancie.

## Voir aussi

- **Issue source implicite** : ce document n'ouvre pas d'issue dédiée ; il est *greffé* sur [#7745](https://github.com/jsboige/CoursIA/issues/7745) (D1) et [#7743](https://github.com/jsboige/CoursIA/issues/7743) (C4), qu'il *re-lit* ensemble. Cf. [#4588](https://github.com/jsboige/CoursIA/issues/4588) (Epic umbrella ICT).
- **Cadrage D1** : [`strate7-cadres-libres.md`](strate7-cadres-libres.md) — livré c.1246, PR [#9596](https://github.com/jsboige/CoursIA/pull/9596) MERGED. Le présent document *consolide* D1 en articulation avec C4.
- **Cadrage C4** : [`jambe-c4-propagation.md`](jambe-c4-propagation.md) — livré c.1247, PR [#9601](https://github.com/jsboige/CoursIA/pull/9601) OPEN. Le présent document *étend* C4 §4 (le pont à sens unique) en pont *bidirectionnel*.
- **Cartographie tresse (mode horizontal)** : [`tresse-cartographie.md`](tresse-cartographie.md) — livré c.1239, PR [#9551](https://github.com/jsboige/CoursIA/pull/9551) MERGED. La cartographie dit *comment les fils se croisent* ; le présent document dit *comment deux livrables coïncident sur un seuil*.
- **Dissolution des scalaires** : [`dissolution-scalaires.md`](dissolution-scalaires.md) — livré c.1238, PR [#9547](https://github.com/jsboige/CoursIA/pull/9547) MERGED. L'héritage de la dissolution est *transmis* à l'articulation D1 ↔ C4 (pas de scalaire unique, pas d'agrégation).
- **Boussole narrative D3** : [`strate7-boussole-myth.md`](strate7-boussole-myth.md) — livré c.1243, PR [#9579](https://github.com/jsboige/CoursIA/pull/9579) MERGED. D3 *raconte* la strate 7 ; D1 la *formalise* ; C4 l'*opérationnalise* ; le présent document *articule* D1 et C4. D3 reste complémentaire (mode narratif, pas mode méta).
- **Synthèse invariants/dissociations/obstructions** : [`synthese-invariants-dissociations-obstructions.md`](synthese-invariants-dissociations-obstructions.md) — [#7399](https://github.com/jsboige/CoursIA/issues/7399) MERGED. La grille 3-régimes *précède* l'articulation D1 ↔ C4 : les invariants/dissociations/obstructions sont *ce qui peut être formalisé* (D1) ou *opérationnalisé* (C4) sans perte.

— *CoursIA-2 — c.1248 (po-2025) — 2026-08-06*
