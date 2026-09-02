# Case 8b — le canal *self* irréductible : pré-enregistrement

> **Statut.** Pré-enregistrement scellé **avant** l'écriture du jouet (ordre git vérifiable :
> ce fichier est committé dans un commit antérieur à `ict/strange_loop_irreducible.py`,
> comme `55d4aad9ef` → `425ee656b2` sur la case 8).
> Veille [#8182](https://github.com/jsboige/CoursIA/issues/8182), iceberg L4 (Hofstadter),
> jalon 2. **Grade C documentaire.** CPU-only, numpy pur, 5 graines fixes.

## Pourquoi cette case existe

La **case 8** (« fermeture du lacet : auto-modèle ⟂ surrogate à capacité égale »,
livrée par la lane `myia-po-2024:CoursIA-2`, PR
[#12942](https://github.com/jsboige/CoursIA/pull/12942), 2026-08-25) a rendu un verdict
`P2 FALSIFIÉ` : `ρ_β` médian **1.0** au lieu du `≥ 3` pré-enregistré. Le self-modèle
structuré ne ré-adaptait pas plus vite qu'un surrogate à capacité égale.

Sa falsification est arrivée avec un **diagnostic qui nomme sa propre condition de reprise** :

> l'action `a = pol(x)` étant déterministe en l'état, le canal « self » ne porte AUCUNE
> information indépendante de `x` — l'auto-connaissance n'achète aucune accélération de
> ré-adaptation à ce régime. Le lacet ne « travaille » que si le canal self est
> **irréductible** à l'état (autonomie partielle du self-modèle).

C'est une conjecture, pas un résultat : elle explique l'échec *après coup*. Une falsification
qui nomme la condition sous laquelle la prédiction tiendrait n'a de valeur que si cette
condition est **testée** — sinon elle est indiscernable d'une excuse. Case 8b la teste.

**Une seule variable change** par rapport à la case 8 : la politique reçoit une composante
autonome non récupérable depuis l'état. Métrique, seuils, horizon, graines : identiques.

## Le montage

Dynamique inchangée : `x_{t+1} = a_t · x_t + b_t · action_t + w_t`, shift au pas 2000
(bras `beta` = le monde change la réponse à MES actions ; bras `alpha` = le monde change la
dérive de MON ÉTAT, canal que le modèle structuré ne possède pas davantage que le surrogate).

**Le seul changement — la politique devient partiellement autonome :**

```
action_t = omega . phi_pol(x_t) + m_t
m_{t+1}  = rho . m_t + eta_t ,  eta ~ N(0, sigma_m) ,  rho = 0.9
```

`m_t` est un « motif » interne de l'agent : l'agent **connaît** son action (il l'a émise),
mais `m_t` **n'est pas** une fonction de `x_t`. Le canal *self* porte donc, pour la première
fois dans cette lignée, de l'information que l'état ne contient pas.

**L'irréductibilité est MESURÉE, pas supposée.** On rapporte
`residual_share = 1 - R2(action ~ phi(x))`, part de la variance de l'action non explicable
par l'état. Sur la case 8 elle vaut ~0 *par construction*. Ici la manipulation n'est réputée
avoir pris que si `residual_share > 0.30` ; en dessous, le test ne mesure pas ce qu'il croit
mesurer et le verdict est `INCONCLUSIF_MANIPULATION` — jamais une confirmation.

**Trois modèles, tous à même largeur d'entrée et même pas d'apprentissage :**

| Modèle | Prédicteur | Ce qu'il incarne |
|---|---|---|
| `SelfLoopModel` | `w.phi(x) + c.action` (action réellement émise) | le lacet : « je sais quelle part de ça est moi » |
| `CompositeSurrogate` | `v.psi(x)` | capacité égale, aucun canal propre |
| `NoiseChannelSurrogate` **(nouveau)** | `u.[psi(x), z]`, `z` exogène de même variance | capacité égale **et un canal de plus** — mais ce canal n'est pas *lui* |

Le troisième est le null que la case 8 n'avait pas et ne pouvait pas avoir : tant que
l'action était réductible à l'état, « avoir le canal action » ne se distinguait pas de
« avoir une dimension d'entrée de plus ». Il le devient ici.

## Prédictions chiffrées (scellées)

- **P1 prime — fermeture.** `d*` médian **<= 12** itérations, **>= 4/5** graines.
  L'irréductibilité ne doit pas casser la fermeture : un lacet qui ne se referme plus n'est
  plus une *strange loop*, c'est une régression infinie.
- **P2 prime — le lacet travaille.** `rho_beta = T_surrogate / T_loop >= 3` sur **>= 4/5**
  graines, **ET** `rho_alpha < 2` (médiane). C'est exactement la double dissociation que la
  case 8 n'a pas su exhiber.
- **P3 prime — le canal doit être SIEN.** `kappa = T_noise / T_surrogate` médian dans
  **[0.5, 2]** : un canal exogène, de même dimension et même variance, n'achète **aucune**
  ré-adaptation. Conjoint à P2 prime, c'est ce qui isole l'*auto*-connaissance de la simple
  largeur d'entrée.

## Nulls adversariaux — ce qui ferait échouer la case

| # | Condition | Lecture |
|---|---|---|
| (a) | `rho_beta < 3` | même avec un canal self irréductible, l'auto-connaissance n'achète rien : **le diagnostic de la case 8 était faux**, la réductibilité n'était pas le verrou |
| (b) | `rho_alpha >= 2` | le modèle structuré rattrape aussi vite sur un canal qu'il ne possède pas : flexibilité générique, pas auto-connaissance |
| (c) | `kappa < 0.5` | un canal arbitraire accélère lui aussi : c'est la dimension d'entrée, pas le soi |
| (d) | verdict qui saute d'une graine à l'autre | mesure une instabilité, pas une structure |
| (e) | `d* > 12` sur >= 2/5 | l'irréductibilité aurait acheté la ré-adaptation **au prix de la fermeture** : verdict distinct (`CLOSURE_LOST`), à rapporter comme tel et **non** comme une confirmation |
| (f) | `residual_share <= 0.30` | la manipulation n'a pas pris : `INCONCLUSIF_MANIPULATION` |

## Un biais assumé, et il joue contre nous

L'horizon de rattrapage est mesuré **par rapport à l'asymptote pré-shift de chaque modèle**
(`< 1.2 x` son propre plateau). Or, avec un canal self irréductible, le surrogate a
structurellement une asymptote **plus haute** — donc un seuil de rattrapage **plus lâche**,
donc il est déclaré « rattrapé » plus facilement. Ce biais joue **contre P2 prime**. Le
rapporter n'est pas une précaution de style : si `rho_beta >= 3` sort malgré lui, l'effet est
plus net que le chiffre ne le dit ; s'il ne sort pas, on ne pourra pas l'attribuer à un seuil
trop sévère.

## Ce que cette case ne dit pas

Grade C : on teste une **classe de mécanisme** sur un substrat scalaire — un self-modèle dont
le canal propre est partiellement autonome ré-adapte-t-il plus vite quand le monde change la
réponse à ses propres actions. Ce n'est **pas** une validation de la thèse de Hofstadter sur
le cerveau (philosophique, sans protocole falsifiable au sens ICT), et aucune phénoménologie
n'est mesurée. La valeur de Hofstadter ici reste **documentaire** : il fournit le vocabulaire
(*tangled hierarchy*, fermeture sans régression infinie), pas une prédiction quantitative.

Contrainte héritée pour le mapping persona ICT-23/25 : si P2 prime tient, alors le lacet
persona `q(self)` ne « travaille » que dans la mesure où le self dispose d'une **autonomie
partielle** — un persona entièrement déductible de son contexte ne s'achète aucune
ré-adaptation.

## Crédit

*Douglas Hofstadter*, « Gödel, Escher, Bach », Basic Books 1979, ISBN 978-0465026562 ;
« I Am a Strange Loop », Basic Books 2007, ISBN 978-0465003010.
Carrefour : *Kurt Jaimungal — Theories of Everything*, iceberg L4 ([#8182](https://github.com/jsboige/CoursIA/issues/8182)).
