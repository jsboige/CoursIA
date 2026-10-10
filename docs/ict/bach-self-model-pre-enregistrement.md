# Self-model causal vs cache descriptif (H_b) — pré-enregistrement de la lane

**Statut** : hypothèse de la lane, **non adossée à un passage identifié**. La distinction « self-model causalement actif sur l'action » vs « cache descriptif sans pouvoir différentiel » est une **reformulation de la lane**, inspirée par la tradition PSI (Principles of Synthetic Intelligence) au sens large, et **non** une citation de Bach 2009 ni d'un autre auteur précis. **Dette IIT-05 #12215** : reste **OUVERTE** tant qu'aucun passage identifié ne porte la thèse — l'attribution de la case 8d est une décision de matrice, pas une livraison de source.

## État archivage GDrive (mesure 2026-10-06T01:40Z)

`G:\Mon Drive\MyIA\IA\Bibliographie IA\Consciousness\` — **absent** pour toute publication attribuable à cette thèse précise. La règle `bibliography-hygiene.md` exige l'archive avant dépôt d'une PR substantielle qui cite la source. Conséquence : la dette IIT-05 reste **OUVERTE** ; cette PR documente la reformulation en hypothèse de la lane, mais ne **clôt pas** la dette. **Critère de mort** de la dette : (i) un passage identifié qui porte la distinction causal ↔ descriptif (vérifié par lecture + page), (ii) PDF archivé dans la bibliothèque partagée GDrive. Tant que l'un manque, la dette survit aux cycles (rappelé au cycle suivant par `MEMORY.md`).

## Objet formel

Un self-model causalement actif sur l'action n'est pas un descripteur ; il a un **pouvoir différentiel sur la trajectoire d'action**. Formalisation minimale :

- Soit une politique `a_t = π(x_t, s_t)` où `s_t` est l'état du self-modèle.
- Le self-modèle `s_{t+1} = f(s_t, x_t, a_t, θ_self)` est mis à jour sur ses propres observations.
- Le self-model est **causal** si `∂a_t/∂s_t ≠ 0` (la trajectoire d'action dépend du self-modèle), et **descriptif** si `s_t = g(x_t, a_t)` (lecture sans influence).

**Ce formalisme est de la lane.** Il n'est pas paraphrasé d'un auteur, et aucun passage archivé n'est invoqué pour le fonder. Il sert d'**énoncé opératoire** d'une hypothèse H_b dont la falsifiabilité est testable par dissociation 8/8b/8c.

## Hypothèse de la lane (H_b)

> **H_b** : un agent dont le self-modèle entre dans la dynamique de l'action (politique conditionnée par `s_t`, dérivée `∂a_t/∂s_t ≠ 0`) **ré-adapte plus vite** qu'un agent à cache descriptif à capacité égale quand le monde change la réponse à SES actions (le shift β de la case 8), et cet avantage **disparaît** quand le monde change sa dérive propre (le shift α). C'est la double dissociation case 8 → 8b.

**Statut épistémique** : H_b est une **hypothèse de travail** de la lane, à pré-enregistrer avant toute mesure. Elle n'engage aucun auteur tiers : le passage présumé n'est pas identifié, et la dette IIT-05 le restera tant qu'il ne l'est pas.

## Contre-hypothèse (H_c)

Un cache descriptif à capacité égale **suffit** à reproduire les comportements qu'un self causal prétend expliquer. Formellement : `∂a_t/∂s_t = 0` pour tout `t` — la politique ne reçoit pas d'entrée du self-modèle, et l'avantage mesuré sur 8/8b est entièrement absorbé par la capacité de modélisation générique.

**Sources du contre-claim** : la lecture canonique de Dennett (*Consciousness Explained* 1991) tient cette position, mais **Dennett n'est pas archivé non plus** (mesure 2026-10-06T01:40Z). H_c est ici énoncé comme position théorique générale, non comme citation textuelle.

**Test conjoint H_b vs H_c** : si H_c tient, la case 8b doit **échouer** — un surrogate à capacité égale mais sans canal self DOIT rattraper aussi vite sur les deux shifts (β et α) que le self-modèle. C'est précisément ce que la case 8c a mesuré.

## Mesure falsifiable

**H_b** : `ρ_β = T_surrogate / T_loop ≥ 3` sur ≥ 4/5 graines (le self-model causal ré-adapte au moins 3× plus vite que le surrogate à capacité égale après shift β) ET `ρ_α < 2` médiane (cet avantage DISPARAÎT sur un shift que le self-model ne possède pas en canal propre).

**H_c** : `ρ_β < 3` sur ≥ 4/5 graines OU `ρ_α ≥ 2` médiane (le surrogate à capacité égale suffit — l'effet est la capacité, pas l'auto-référence).

**État mesuré** (`docs/ict/dissociations-matrix.md` ligne 227, case 8b) :

- `residual_share` médian 0.35 > 0.30 ✓ (contrôle de manipulation TENU)
- `ρ_β_sf` (métrique scalefree de la case 8c) médian **12.5** sur la case 8b **ET** médian **1.00** sur la case 8 (les mêmes traces, deux échelles).
- Verdict `INCONCLUSIF_INSTRUMENT` posé par la case 8b **mais** verdict interne : la nouvelle métrique retourne **12.5** vs l'ancienne **0.07** sur les mêmes traces. La magnitude va dans le sens attendu par **H_b** (12.5 ≫ 1), mais le tableau qualifie lui-même la valeur de « plafond artefact » (signe retourné, magnitude non bornée) — la mesure ne tranche pas l'origine de l'écart.

**Conclusion pré-enregistrée (à valider en PR)** : la case 8b est **compatible avec H_b** au sens où l'écart mesuré va dans le sens attendu. La dette IIT-05 est **non soldée** par cette PR (l'archive d'un passage identifié reste la condition). La PR :

1. ajoute une ligne à la matrice des dissociations : **« Self-model causal vs cache descriptif (H_b, hypothèse de la lane — case 8b/8c) — compatible, non démontré »**, avec mention de la double dissociation `ρ_β_sf >> ρ_α_sf` et de l'avertissement artefact ;
2. **ne marque pas** la dette IIT-05 comme soldée tant qu'aucun passage identifié n'est archivé. La dette reste **documentée et ouverte** ;
3. ne **recrée pas** un nouveau `ict/strange_loop_bach.py` — la discipline du 28/08 dit « 1 source primaire, 1 décision, au plus 1 PR », et l'attribution est une décision de matrice, pas une livraison de code.

## References

Cette section ne contient **aucune attribution d'auteur** à la distinction causal↔descriptif. Les références ci-dessous sont les **sources premières** du dossier (Hofstadter sur la structure, Dennett sur le contre-claim) — la **distinction** elle-même n'est attribuée à personne tant qu'un passage précis n'est pas identifié.

- **Hofstadter** sur la structure du lacet (L4 iceberg) — `Gödel, Escher, Bach` Basic Books 1979, ISBN 978-0465026562 ; `I Am a Strange Loop` Basic Books 2007, ISBN 978-0465003010. *Hypothèse d'archive GDrive* : à vérifier en mesure `find G:\Mon Drive\MyIA\IA\Bibliographie IA\Consciousness -iname "*hofstadter*"`. *Note* : la distinction **causal ↔ descriptif** n'est pas une formulation de Hofstadter, qui tient la structure sans distinguer les deux versions — l'**énoncé opératoire** de la lane (§Objet formel) comble ce trou.
- **Dennett** sur le contre-claim — `Consciousness Explained` Little Brown 1991, ISBN 978-0316180665. *Hypothèse d'archive GDrive* : à vérifier. La position de Dennett (« narrative self suffit, pas besoin de self-model causal ») est **l'antithèse** de H_b, mais l'attribution de la position reste **non textuelle** tant que l'archive n'est pas en place.
- Cases 8, 8b, 8c dans `docs/ict/dissociations-matrix.md` (lignes 226–228). PRs [#12942](https://github.com/jsboige/CoursIA/pull/12942), [#14180](https://github.com/jsboige/CoursIA/pull/14180).
- Grain IIT-05 #12215, `MyIA.AI.Notebooks/IIT/IIT-05-Lentilles-et-Dissociations.ipynb`.

## Dette IIT-05 — récapitulatif

| Condition | État au 2026-10-06 | Source |
|---|---|---|
| (i) un passage identifié qui porte la distinction causal ↔ descriptif | **NON** | mesure `bach passage` 2026-10-06 (recherche table des matières de Bach 2009 chap. 5, **4 sous-sections** : 5.1 Language comprehension, 5.2 Problem solving with language, 5.3 Language and consciousness, 5.4 Directions for future development — **aucune ne porte la thèse** ; mesure étendue à la thèse de 2007, 0 occurrence de « self-model ») |
| (ii) PDF archivé dans `G:\Mon Drive\MyIA\IA\Bibliographie IA\Consciousness\` | **NON** | mesure 2026-10-06T01:40Z, dossier `Consciousness/` vide ou sans Bach 2009 |

**Conclusion** : la dette IIT-05 #12215 **reste ouverte** après ce cycle. Elle ne se solde **ni** par ré-attribution (option rejetée par la coordonnateur ai-01 c.46 : « la source ne dit pas ce que le document lui fait dire »), **ni** par reformulation en hypothèse de la lane (cette PR, qui documente la H_b sans l'adosser à un passage). La dette survivra aux reprises de cron tant que les deux conditions (i) et (ii) ne sont pas satisfaites — son **critère de mort** est l'archive vérifiable, pas l'attribution ou la paraphrase.
