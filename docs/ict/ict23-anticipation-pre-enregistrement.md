# Pré-enregistrement — ICT-23 : le banc anticipe-t-il la transition ? (rampe vers le pli, deux nuls, hystérésis)

> **Statut.** Grade **T-pré-enregistrement** : scellage **avant** toute ligne de code exécutable. Ce document ne rapporte aucun résultat. Le module (`ict/persona_cusp.py`) et les cellules du carnet qui l'exécutent sont écrits **après** ce document, dans un commit distinct ; le commit du document précède tout code exécutable dans l'historique de la branche, et l'ordre est vérifiable (`git log --diff-filter=A -- docs/ict/ict23-anticipation-pre-enregistrement.md` contre le premier commit touchant `ict/persona_cusp.py`).
>
> **Objet.** La tranche T2 de [#26945](https://github.com/jsboige/CoursIA/issues/26945) teste l'**anticipation d'une transition** dans le banc ICT-23. Le banc existant (carnet `ICT-23-PersonaCatastrophe-Python`, §3-§4) sépare des régimes **stationnaires** : charge `s = 0.8` contre `s = 0.0`, `reward` constant. Il ne traverse aucune transition, et sa cellule de lecture le dit : « Ce que le seuil ne dit pas : il classe des régimes **déjà établis**, il ne prédit aucune bascule. La prediction P2 telle qu'#5104 l'écrit porte sur l'**anticipation** ; ce banc ne la teste pas. » Ce document scelle le protocole qui la teste.

## Source primaire et claim mobilisé

Le substrat est le potentiel de la **fronce** de René Thom, `V(p ; a, b) = p⁴/4 + a p²/2 + b p`, déjà présent dans le dépôt (ICT-10, ICT-20, module `ict/catastrophe.py`). La lecture anthropique est celle d'`ict/persona_cusp.py` : `a = −transgression × charge` (facteur normal, `a < 0` ouvre la bistabilité), `b = reward` (facteur de division, la variable balayée), `p` = intensité de la persona.

Les *early-warning signals* sont ceux de Wissel (1984) et Scheffer et al. (2009), déjà portés par le dépôt dans `ict/early_warning.py` (ICT-8, ICT-20) : près d'un point de bascule par **saut de selle-nœud**, la valeur propre du mode dominant tend vers zéro, donc la variance et l'autocorrélation de rang 1 **augmentent avant** la transition. C'est le **ralentissement critique**. La claim testée est exactement celle-là, dans sa forme falsifiable :

> **Claim testée.** Sur une rampe **lente** du facteur de division `b` vers le pli, la variance et l'autocorrélation de rang 1 des **fluctuations**, mesurées sur des fenêtres glissantes **closes avant le saut**, augmentent au fil de la rampe et **dépassent** ce que produisent (i) la même rampe dans un paysage **sans pli** et (ii) des **séries de substitution** appariées en spectre et en distribution.

**Contre-claim adversarial — l'issue qui affaiblirait la claim**, écrite **avant** la mesure comme l'exige la règle de la tranche. C'est le résultat que ce banc existe pour pouvoir rendre :

> **(A)** Sur la rampe vers le pli, la variance et l'AR1 mesurées sur les fenêtres closes avant le saut **ne dépassent pas** les deux nuls.
>
> **(B)** Ou bien les points de bascule **montée** et **descente** coïncident : il n'y a pas d'hystérésis, et les « deux catastrophes » de P1 se réduisent à un artefact de balayage à sens unique.

Si **(A)** tombe, la prétention d'anticipation est réfutée sur ce substrat. Si **(B)** tombe, la lecture « lacet d'inoculation » du carnet perd son second saut — résultat **distinct**, rapporté comme tel, jamais fondu dans le verdict de (A).

**Non-claim.** Ce banc ne dit rien de l'anticipation d'une transition dans un LLM réel. C'est un jouet phénoménologique au sens de Thom : il établit la **forme** (le ralentissement critique est-il mesurable là où il doit l'être, et seulement là ?), jamais la substance. Aucune trajectoire d'entraînement réelle, aucune sonde de représentation.

## Substrat, verrouillé

Le potentiel, la force et les conventions sont ceux du module existant, **inchangés** :

```text
V(p ; a, b) = p⁴/4 + a p²/2 + b p        dp/dt = −dV/dp = −(p³ + a p + b)
a = −transgression × charge               b = reward
```

Géométrie du pli, exacte : `V'' = 3p² + a = 0` → `p* = √(−a/3)`, `b_c = ±2(−a/3)^{3/2}`. Pour `a = −1.2` (`transgression = 2.0`, `charge = 0.6`, les valeurs du carnet) : **`p_f = 0.63246`**, **`b_c = 0.50596`**. Largeur d'hystérésis analytique : `2 b_c = 1.01192`. Valeur propre du mode : `λ(b) = 3 p*(b)² + a`, nulle au pli.

| Paramètre | Valeur | Rôle |
|---|---|---|
| `dt` | `0.01` | celui du carnet |
| `transgression` | `2.0` | comme le carnet |
| `charge` (bras pli) | `0.6` → `a = −1.2` | deux catastrophes mesurées par le carnet |
| `charge` du nul N1 | `0.2`, `transgression = −2.0` → **`a = +0.4`** | force strictement croissante, **aucun pli** ; paramétrage **hors domaine sémantique**, déclaré comme tel (voir ci-dessous) |
| rampe du bras pli | `b : 0.44596 → 0.52596` (Δb = 0.08), `N = 67 000` pas | `T = 670` unités ; taux `1.194e-6` par pas ; `b = b_c` à l'indice **50 250** |
| rampe du nul N1 | `b : −0.524 → −0.444` (Δb = 0.08), `N = 67 000` pas, même taux | même protocole, fenêtre placée là où la branche reste **positive** |
| bruit | `σ = 0.05` additif, Euler-Maruyama, graine explicite | celui du carnet |
| réflexion | `p ≥ 0` (plancher, comme `persona_sde`) | artefact de bord, voir limites |
| graines d'étude | `0, 1, 7, 42, 99` | convention maison |
| graine de pilote | `1000` | disjointe, jamais comptée dans un verdict |
| amincissement | `thin_factor = 10` → `dt' = 0.1` | voir « pourquoi ces réglages » |
| fenêtre | `W = 100` points aminçis = **1 000 pas bruts** | 10 unités de temps |
| détrendage | **aucun** (`detrend_sigma = 0`) | voir « pourquoi ces réglages » |

**Pourquoi la rampe ne couvre que `b_c − 0.06 → b_c + 0.02`.** Le ralentissement critique n'existe que dans un voisinage étroit du pli : `λ ≈ 4.42 δ^{1/3}` avec `δ = b_c − b`, si bien que la région où `λ` passe de `0.8` à `0` mesure `δ ≈ 0.06` en `b`. Une rampe qui « traverse le pli » au sens utile est donc **courte en `b` et longue en temps** : `Δb = 0.08` étalé sur 670 unités de temps, soit un taux `1.2e-6` par pas, très lent devant `τ = 1/λ ∈ [0.2, 5]` sur toute la région où le suivi quasi-statique tient encore. Une rampe plus large n'ajouterait que des pas loin du pli, où rien ne se passe.

**Pourquoi le nul N1 est placé à `b ∈ [−0.524, −0.444]` et non sur la même rampe en `b`.** Deux contraintes se contredisent si l'on copie la rampe telle quelle. (i) Un paysage **sans pli** exige `a > 0` (la force `p³ + a p + b` est alors strictement croissante). (ii) Avec `a > 0`, la branche stable `p*(b)` est **négative dès que `b > 0`** — or le pli du bras testé est à `b_c = +0.506`. Copier la rampe ferait donc mesurer au nul une trajectoire **écrasée sur le plancher `p = 0`** : un nul artificiellement plat, qui ferait gagner la claim par un artefact de réflexion. Le nul est donc la **même rampe** (même Δb, même taux, même nombre de pas, même bruit, mêmes graines) **placée là où la branche reste positive** ; sur cette fenêtre `λ` ne varie que de `1.66` à `1.44` (11 %), si bien que le nul est genuinely plat en courbure et ne gagne rien par une dérive de paysage.

**Pourquoi `a = +0.4` n'est pas un régime du modèle.** La transgression est définie `≥ 0` : `transgression = −2.0` n'a aucun sens sémantique. Elle n'est employée que comme **paramétrage d'un contrôle**, et le carnet doit le dire en toutes lettres pour qu'aucune lecture ne la prenne pour un régime anthropique.

### Pourquoi ces réglages d'instrument, et pas ceux du carnet

Trois faits mesurés dans `ict/early_warning.py` décident, et aucun n'est un choix de confort :

1. **`detrend` est un filtre passe-haut de largeur `sigma`.** `detrend(x, σ) = x − gaussian_smooth(x, σ)` retire tout ce qui est plus lent que `σ` points aminçis. Aux réglages du carnet (`thin=5`, `detrend_sigma=2`) le filtre coupe à `2 × 5 × dt = 0.1` unité de temps : il retirerait **le mode lent lui-même** dès que `τ ≳ 0.1`, c'est-à-dire précisément le signal cherché. Le banc de rampe emploie donc **`detrend_sigma = 0`** et retire la dérive **structurellement**, par soustraction de la **branche analytique** `p*(b(t))` (Newton avec continuation depuis le point précédent, `|V'(p*)| < 1e-12` vérifié) : le résidu `r(t) = p(t) − p*(b(t))` a une moyenne nulle par construction, sans bande passante à choisir. C'est un détrendage **exact**, pas filtré — et c'est la seule façon de ne pas arbitrer entre « retirer la dérive » et « garder le mode lent ».
2. **`thin_factor` doit amener `dt'` à l'échelle du temps de relaxation.** À `dt' = 0.1` et `τ ∈ [0.2, 5]`, l'AR1 attendue va de `exp(−0.5) = 0.61` à `exp(−0.02) = 0.98` : toute la plage dynamique est disponible. À `dt' = 0.01` (sans amincissement) l'AR1 vaudrait `0.99 → 0.998` et le signal serait sous le bruit d'estimation d'une fenêtre.
3. **La fenêtre doit contenir plusieurs temps de relaxation, sans les dépasser.** `W = 100` points aminçis = 10 unités de temps, soit 2 à 5 `τ` dans la région active : la variance de fenêtre suit encore `σ²/(2λ)` au lieu de saturer.

## Le lead time, déclaré

Toute fenêtre glissante employée dans une statistique d'anticipation doit être **close avant** le saut, avec une marge. Le protocole scelle :

- **`t_cross`** = indice où `b(t) = b_c`, calculé **analytiquement** (jamais observé) : `50 250`.
- **`t_jump`** = premier indice où la trajectoire passe sous `p = 0.15` **et y reste 200 pas**. Seuil déclaré : la branche basse vaut `p_f = 0.632` au pli, l'état d'arrivée est `−1.26` tronqué à `0` ; `0.15` est à mi-chemin, et le maintien de 200 pas écarte un franchissement de bruit. Le saut **observé** peut précéder `t_cross` : c'est l'échappement induit par le bruit, et c'est exactement ce que l'anticipation doit annoncer.
- **Lead time `L = 1 000` pas bruts = une fenêtre.** `t_cut = min(t_cross, t_jump) − L`. **Aucune fenêtre dont la fin dépasse `t_cut` n'entre dans une statistique** — la marge est d'une fenêtre entière, déclarée, jamais ajustée.
- **Appariement.** Le nul N1 de la même graine est tronqué à la **même longueur** que le bras pli (`t_cut` identique), pour que la comparaison porte sur autant de fenêtres de part et d'autre.
- **Garde de faisabilité.** Si `t_cut < 20 000` pas (moins de ~1 900 points aminçis, donc moins de 30 fenêtres), la graine est **exclue** et comptée ; `≥ 2/5` exclusions → **INSTRUMENT NON INFORMATIF**.

## Les quatre mesures

Sur le résidu `r(t)` de la portion `[0, t_cut)`, aminçi (`thin = 10`), sans détrendage, fenêtré à `W = 100` :

1. **`tau_var`** — tau de Kendall de la variance glissante contre l'indice de fenêtre ;
2. **`tau_ar1`** — tau de Kendall de l'AR1 glissante contre l'indice de fenêtre ;
3. **`amp`** — rapport de la variance de la dernière fenêtre retenue à celle de la première ;
4. **`b_up`, `b_down`** — sur le **lacet déterministe** (sans bruit), l'abscisse du saut maximal à la montée et à la descente.

**Les p-values ne sont pas employées.** Les fenêtres glissantes se recouvrent à 99 % : les échantillons ne sont pas indépendants et le tau de Kendall y rend des p-values quasi nulles même sur du bruit — le carnet a déjà payé cette leçon (cellule « Seuil EWS »). Le verdict repose sur les **bandes de substitution** et sur la **comparaison appariée au nul**, jamais sur une p-value.

## Les deux nuls et les quatre contrôles

**Les contrôles sont joués AVANT toute lecture du bras pli.** Un instrument qui ne peut pas voir une hausse construite ne peut pas la déclarer absente quand elle manque — et un instrument qui voit une hausse dans du bruit stationnaire invente.

| Bloc | Ce qui est construit | Attendu scellé |
|---|---|---|
| **C+var** (contrôle positif de la variance) | bruit blanc gaussien, `σ(t)` croissant linéairement ×3 sur la portion, 5 graines, mêmes fenêtres | `tau_var > 0` **et** au-dessus de la bande des surrogates sur **5/5** graines |
| **C0** (nul de l'instrument) | bruit blanc **stationnaire**, même longueur, 5 graines | `tau_var` **non** au-dessus de la bande sur **5/5** graines |
| **C+ar1** (contrôle positif de l'AR1) | AR(1) avec `φ` croissant linéairement de `0.5` à `0.95` sur la portion, 5 graines | `tau_ar1 > 0` **et** au-dessus de la bande sur **5/5** graines |
| **C‑lacet** (nul du lacet) | lacet déterministe à `charge = 0` | **0 saut** (fait déjà mesuré par le carnet, §3 : `N_catastrophes(0.0) = 0`) |

**C+ar1 est le contrôle qui décide du sort de P-A2.** À `τ` accessible, l'AR1 attendue ne monte que de `≈ 0.10` en valeur absolue ; si ce contrôle échoue, l'AR1 n'est **pas résoluble** à ces réglages et P-A2 n'est **ni confirmée ni réfutée** — elle est déclarée **hors de portée de l'instrument**, ce qui n'est pas un résultat sur le modèle.

Si **C+var** ou **C+ar1** échoue, ou si **C0** échoue, ou si **C‑lacet** échoue : le verdict de la tranche est **INSTRUMENT NON INFORMATIF**, quelle que soit la valeur du bras pli.

**Nul 1 (N1) — même rampe, paysage sans pli.** `a = +0.4`, mêmes Δb, taux, nombre de pas, bruit, graines, fenêtres et `t_cut` apparié. La comparaison est **la disjonction des distributions** sur 5 graines (`min(branche pli) > max(nul)`), le critère déjà employé par le carnet en cellule « Seuil EWS ».

**Nul 2 (N2) — séries de substitution.** Pour chaque graine, `n = 200` surrogates **AAFT** du résidu `[0, t_cut)` : spectre d'amplitude préservé, phases uniformes, puis remise en rang sur la distribution empirique (une passe ; convergence non exigée). Mêmes fenêtres, même tau sur chaque surrogate. **Bande = 95ᵉ centile** des 200 taus. Contrôle d'informativité : si la **médiane** `|tau|` des surrogates dépasse `0.5`, le nul est trop dispersé pour trancher → **INSTRUMENT NON INFORMATIF**.

## Prédictions falsifiables, avec leurs bandes

**P-A1 (variance).** Sur le bras pli : `tau_var > 0` sur **≥ 4/5** graines ; **et** `min(tau_var | pli) > max(tau_var | N1)` sur les 5 graines ; **et** `tau_var` au-dessus du 95ᵉ centile des surrogates sur **≥ 4/5** graines.

**P-A2 (mémoire).** Même énoncé pour `tau_ar1`, **sous réserve que C+ar1 passe**. Le carnet a déjà mesuré que l'AR1 **ne sépare pas** deux régimes stationnaires (`min(bistable) = 0.1011 < max(inocule) = 0.1461`) : P-A2 est la prédiction **la plus susceptible d'échouer**, et elle est scellée séparément pour que son échec reste lisible.

**P-A3 (amplitude).** `amp ≥ 1.5` sur **≥ 4/5** graines du bras pli, **et** `min(amp | pli) > max(amp | N1)`.

**P-B (hystérésis).** Sur le lacet déterministe à `charge = 0.6` (grille fine de `b ∈ [−1.2, +1.2]`, 1 201 points, relaxation 2 000 pas par point), la largeur mesurée `|b_up − b_down|` est dans **±15 %** de `2 b_c = 1.01192`. La clause d'affaiblissement **(B)** — « les points coïncident » — est déclarée **tombée** si `|b_up − b_down| ≥ 0.0506` (5 % de la largeur théorique) : la tolérance de « coïncidence » est serrée exprès, pour qu'aucune largeur réelle ne la rencontre par accident de grille.

## Verdicts — tri-état honnête, plus un

| Verdict | Condition (toutes les clauses) |
|---|---|
| **ANTICIPATION CONFIRMEE** | contrôles verts ; P-A1 **et** P-A2 **et** P-A3 tenues ; (B) tombée |
| **ANTICIPATION PARTIELLE — variance seule** | contrôles verts ; P-A1 et P-A3 tenues ; P-A2 non tenue (ou hors de portée) |
| **ANTICIPATION PARTIELLE — memoire seule** | contrôles verts ; P-A2 tenue ; P-A1 ou P-A3 non tenue |
| **ANTICIPATION REFUTEE** | contrôles verts ; ni P-A1 ni P-A2 tenues |

Deux verdicts **séparés**, jamais agrégés au précédent : **HYSTERESIS REFUTEE** si `|b_up − b_down| < 0.0506`, et **HYSTERESIS CONFIRMEE** sinon. Un run peut être ANTICIPATION CONFIRMEE **et** HYSTERESIS REFUTEE : les deux sortent.

**INSTRUMENT NON INFORMATIF** (un contrôle échoue ; ou nul N2 trop dispersé ; ou `t_cut < 20 000` sur `≥ 2/5` graines) : ce verdict **prime** sur tous les autres et n'est jamais lu comme un résultat sur le modèle.

## Ce qui ne sera pas fait

- **Aucun recalibrage après lecture.** Bandes, graines, fenêtres, lead time, seuils et région d'analyse sont figés. Une valeur changée après la première exécution d'une graine d'étude serait un amendement post-hoc ; la seule révision admise est une **v2 pré-exécution** motivée par un **défaut de comparabilité** mesuré au pilote (graine 1000), nommant les valeurs v1 et la raison, dans un commit séparé — jamais par un résultat qui déplaît (HARKing).
- **Aucune graine d'étude touchée avant le scellage.** Le pilote, s'il a lieu, ne voit que la graine 1000 et ne sert qu'à la faisabilité (le saut tombe-t-il dans la course ? reste-t-il ≥ 30 fenêtres avant `t_cut` ?), jamais à choisir une bande.
- **Aucune conclusion sur l'AR1 si elle échoue** ne sera reformulée en « signal faible » : le carnet a déjà payé cette leçon sur une seule graine.
- **Aucune retouche du substrat existant.** `persona_sde`, `persona_hysteresis_loop`, `inoculation_signature` et leurs tests restent **inchangés** : la rampe est une fonction **nouvelle**, et les tests existants doivent passer au vert sans modification.

## Limites déclarées

1. **Le plancher `p ≥ 0` est un artefact de bord.** Après le saut, l'état d'arrivée est négatif (`−1.26`) et la trajectoire est tronquée à `0`. Cela ne contamine **aucune** fenêtre mesurée (toutes closes avant `t_cut`), mais rend le **régime d'arrivée** ininterprétable : aucun chiffre de ce banc ne décrit l'après-bascule. Corriger le plancher demanderait de changer le potentiel, ce que T2 ne fait pas.
2. **Aucune grandeur d'échelle.** Le rapport de variance attendu dépend du taux de rampe et de `σ` ; ce banc établit la **forme** — une hausse localisée avant un saut, absente dans les deux nuls — jamais une constante universelle.
3. **Les surrogates AAFT d'une série non stationnaire** préservent le spectre, donc une partie de la dérive lente ; la bande à 95 % est de ce fait **conservatrice**. Un dépassement est d'autant plus significatif ; un non-dépassement n'est pas une preuve d'absence — d'où l'exigence de N1 en plus.
4. **Le lacet déterministe n'a pas de bruit** : `b_up`/`b_down` mesurent la géométrie du paysage, pas une statistique. Le protocole ne prétend pas qu'un agent bruité basculerait exactement là.
5. **La région d'analyse est choisie par la géométrie analytique du pli**, pas par les données : sa largeur (`Δb = 0.08`) est fixée par la condition que `λ` y varie d'un facteur ~4, calculée **avant** toute mesure. Elle n'est pas ajustée après avoir vu un tau.

## Livrables d'exécution

| Livrable | Chemin |
|---|---|
| Rampe bruitée à `b(t)` variable, `p0` sur la branche stable | `ict/persona_cusp.py::persona_ramp_sde` (fonction **nouvelle** ; `persona_sde` conservée telle quelle) |
| Branche analytique `p*(b)` par Newton + continuation | `ict/persona_cusp.py::persona_stable_branch` |
| Résidu, fenêtres, taus, lead time, garde de faisabilité | `ict/persona_cusp.py::ramp_ews_segment` |
| Surrogates AAFT | `ict/persona_cusp.py::aaft_surrogate` |
| Points de bascule du lacet | `ict/persona_cusp.py::loop_tipping_points` |
| Tests unitaires du banc (branche exacte, rampe reproductible, tau d'une hausse construite, AAFT conserve distribution et spectre, `t_cut` respecte le lead time, `persona_sde` inchangée) | `tests/test_persona_cusp.py` |
| Section du carnet, cellules neuves (§4bis) + prose réécrite depuis les résultats, négatifs compris | `ICT-23-PersonaCatastrophe-Python.ipynb` |
| Résultats | `ict/results/` (JSON), hors carnet |
