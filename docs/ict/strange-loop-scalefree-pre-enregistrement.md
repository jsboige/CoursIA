# Case 8c — une métrique de ré-adaptation *sans échelle* : pré-enregistrement

> **Statut.** Pré-enregistrement scellé **avant** l'écriture du jouet (ordre git vérifiable :
> ce fichier est committé dans un commit antérieur à `ict/strange_loop_scalefree.py`,
> comme `55d4aad9ef` → jouet sur la case 8 et `85dbca6364` → `fc99bdeed4` sur la case 8b).
> Veille [#8182](https://github.com/jsboige/CoursIA/issues/8182), iceberg L4 (Hofstadter),
> jalon 3. **Grade C documentaire.** CPU-only, numpy pur, 5 graines fixes.

## Pourquoi cette case existe

La **case 8b** (PR [#14180](https://github.com/jsboige/CoursIA/pull/14180), mergée
2026-09-02) a rendu `INCONCLUSIF_INSTRUMENT`. Elle avait réussi sa manipulation — le canal
*self* était bien devenu irréductible (`residual_share` médian **0.35**, contre **0.0000**
mesuré sur la politique déterministe de la case 8) — et c'est **la réussite de la
manipulation qui a cassé l'instrument** :

| | case 8 | case 8b |
|---|---|---|
| `pre_err_ratio` (surrogate / self) | **1.00** | **2.86** |
| surrogates au plancher d'horizon | **0/5** | **5/5** |
| verdict | `FALSIFIED` (vraie mesure) | `INCONCLUSIF_INSTRUMENT` |

Le corps de la PR #14180 nommait, comme la case 8 avant elle, sa propre condition de reprise :

> Elle motive une **case 8c** à métrique *sans échelle* (le défaut identifié est la
> normalisation par l'asymptote propre), à pré-enregistrer avant tout jouet.

Et la case 8b existait précisément parce qu'« une falsification qui nomme la condition de sa
reprise est indiscernable d'une excuse tant que cette condition n'est pas testée ». Laisser
la sienne non testée reproduirait mot pour mot le défaut qu'elle a corrigé sur la case 8.
**Une seule chose change ici : la métrique.** Dynamique, politiques, modèles, shift, graines
et seuils de décision sont importés tels quels des cases 8 et 8b.

## Le défaut, en une ligne de code

`adaptation_horizon` (case 8, ligne reprise telle quelle en 8b) déclare un bras rattrapé
quand son erreur glissante repasse sous `1.2 x` **sa propre** asymptote pré-shift :

```python
pre = median(errs[warmup:shift_step])          # asymptote PROPRE du bras
if mean(errs[t-50:t]) < catchup_factor * pre:  # seuil RELATIF À SOI
```

Tant que les asymptotes des bras sont à égalité (case 8 : ratio 1.00), le seuil est commun de
fait et la comparaison est licite. Dès qu'elles divergent (case 8b : 2.86), le bras le moins
précis reçoit un seuil **2.86× plus lâche** : il est déclaré rattrapé à la première occasion
mesurable — `adaptation_horizon = 50`, qui n'est pas « rapide » mais **le plus petit chiffre
exprimable**, la recherche démarrant à `shift_step + 50`. `rho_beta` et `kappa` ne comparent
alors plus des vitesses : ils comparent des **largeurs de seuil**.

## La métrique de remplacement

**Temps de relaxation.** On soustrait l'asymptote au lieu de la prendre pour seuil, et on
rapporte la décroissance à **son propre pic de perturbation** :

```
s(t)      = moyenne glissante de l'erreur sur [shift + t - win, shift + t]
excess(t) = s(t) - pre                       pre = médiane pré-shift du bras
peak      = max excess(t) sur la fenêtre de perturbation
T         = min { t : excess(t) < gamma . peak }        gamma = 0.5
```

**L'invariance d'échelle est une propriété démontrable, pas un réglage.** Sous
`errs -> c . errs` avec `c > 0` : `pre -> c.pre`, donc `excess -> c.excess`, donc
`peak -> c.peak`, donc la comparaison `excess(t) < gamma . peak` est **inchangée terme à
terme**. `T` est donc *exactement* invariant — pas approximativement. C'est ce que
`adaptation_horizon` n'est pas, et c'est le seul défaut que cette case corrige.

`gamma = 0.5` est la **demi-vie**, choix canonique scellé ici : aucune autre valeur n'a été
essayée avant ce scellement, et aucune ne le sera après.

**Deux axes que l'ancienne métrique confondait**, tous deux sans échelle :

| Quantité | Sens | Invariante sous `err -> c.err` |
|---|---|---|
| `T` — temps de relaxation | **combien de temps** le bras met à absorber le choc | oui (ratio d'excès) |
| `disruption = peak / pre` | **de combien** le choc l'a sorti de son régime | oui (ratio) |

Un bras structurellement moins précis a un `pre` plus haut *et* un `peak` plus haut : les deux
axes le neutralisent, là où l'ancien seuil le récompensait.

## Prédictions chiffrées (scellées)

- **P1 seconde — validité d'instrument (contrôle, non découverte).** Pour **tout** bras et
  **toute** graine, et pour `c` dans `{0.1, 10}` : `T(c . errs) == T(errs)` **exactement** ;
  et sur les mêmes traces, `adaptation_horizon(c . errs)` **change** pour au moins un bras.
  C'est un contrôle à deux faces — un positif *et* un négatif : sans la seconde moitié, une
  métrique qui rendrait une constante passerait le test. **Cette prédiction tient par
  construction** (cf. la démonstration ci-dessus) : elle ne découvre rien, elle atteste que
  l'instrument est bien celui qu'on décrit. Si elle échoue, l'implémentation trahit la
  définition et **rien d'autre dans cette case n'est lisible**.
- **P2 seconde — le lacet travaille (re-test de la case 8b).** `rho_beta_sf = T_surrogate /
  T_loop >= 3` sur **>= 4/5** graines. Seuil **identique** à P2 et P2 prime, pour que les trois
  cases soient enfin comparables sur une seule échelle.
- **P3 seconde — le canal doit être SIEN.** `kappa_sf = T_noise / T_surrogate` médian dans
  **[0.5, 2]**.
- **Porte de non-dégénérescence.** Aucun bras ne doit se poser au plancher (`T <= win`) ni au
  plafond (`T` = fenêtre entière) sur une majorité de graines, et `peak > 0` pour tous. Sinon
  le verdict est `INCONCLUSIF_INSTRUMENT` **de cause distincte**, à rapporter comme tel et
  jamais comme une confirmation.

## Ce que je sais déjà en scellant — et ce que je ne sais pas

La métrique est conçue **en connaissant** le mode d'échec de la case 8b. Le dire est la
condition pour que le reste soit lisible :

| Déjà mesuré (donc hors prédiction) | Valeur |
|---|---|
| case 8b — `pre_err_ratio` | 2.86 |
| case 8b — bras au plancher sous l'ANCIENNE métrique | surrogate 5/5, noise 5/5, self 0/5 |
| case 8b — `rho_beta` ancien, `kappa` ancien | 0.07 médian ; 1.00 exact |
| case 8 — `pre_err_ratio`, bras au plancher | 1.00 ; 0/5 |

**Ce que je ne sais pas** : aucune valeur de `T`, de `rho_beta_sf`, de `kappa_sf` ni de
`disruption` n'a été calculée avant ce scellement, sur aucune des trois cases. P2 seconde et
P3 seconde portent donc sur des quantités inconnues.

**Le garde-fou contre le sur-ajustement** n'est pas une promesse mais un montage : la même
métrique, avec le même `gamma`, est appliquée **aux trois cases dans le même run**. Elle ne
peut pas être accordée à l'une sans se voir sur les deux autres — et la case 8, dont le
verdict `FALSIFIED` est déjà publié, sert de témoin fixe.

## Nulls adversariaux — ce qui ferait échouer la case

| # | Condition | Lecture |
|---|---|---|
| (a) | P1 seconde échoue | l'implémentation ne réalise pas la définition : **instrument invalide**, aucune autre lecture n'est permise |
| (b) | `rho_beta_sf < 3` sur la case 8b | même avec un canal self irréductible **et** une métrique sans échelle, l'auto-connaissance n'achète aucune accélération : le diagnostic de la case 8 était faux, et la case 8b ne le sauvait pas — falsification la plus forte disponible |
| (c) | `kappa_sf < 0.5` | un canal exogène accélère lui aussi : c'est la largeur d'entrée, pas le soi |
| (d) | plancher/plafond sur une majorité de graines | nouvelle dégénérescence, de cause distincte : `INCONCLUSIF_INSTRUMENT`, à ne surtout pas lire comme un résultat |
| (e) | la case 8 re-mesurée rend un verdict **différent** de son `FALSIFIED` publié | alors la falsification de la case 8 était elle aussi un artefact d'échelle, et il faut le dire : cela invalide rétroactivement une conclusion déjà livrée par cette lane (PR #12942) |
| (f) | `T` identique sur les trois bras à toutes les graines | la métrique ne discrimine rien : elle est sans échelle **et** sans pouvoir de résolution |

Le null (e) est le plus coûteux pour cette lane, et c'est pourquoi il est scellé : la case 8
est **ma** livraison, son `FALSIFIED` est publié, et la métrique qui pourrait le renverser est
écrite par la même main. L'écrire d'avance est ce qui empêche de ne pas le regarder.

## Ce que cette case ne dit pas

Grade C : on corrige un **instrument** sur un substrat scalaire. Une métrique sans échelle ne
rend pas la mesure « vraie » — elle retire une confusion identifiée, et rien de plus. Aucune
phénoménologie n'est mesurée ; un `CONFIRMED` ne dirait rien de l'expérience vécue. La valeur
de Hofstadter reste **documentaire** : il fournit le vocabulaire (*tangled hierarchy*,
fermeture sans régression infinie), pas une prédiction quantitative.

## Crédit

*Douglas Hofstadter*, « Gödel, Escher, Bach », Basic Books 1979, ISBN 978-0465026562 ;
« I Am a Strange Loop », Basic Books 2007, ISBN 978-0465003010.
Carrefour : *Kurt Jaimungal — Theories of Everything*, iceberg L4 ([#8182](https://github.com/jsboige/CoursIA/issues/8182)).
