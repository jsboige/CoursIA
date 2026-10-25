# Note de conception — palier 10 : famille ICT-15 (capstone Φ/F/K, obstruction et recollement)

**Provenance** : issue [#20298](https://github.com/jsboige/CoursIA/issues/20298) — phase 2 de l'EPIC de consolidation ICT.
**Palier 10** : « Capstone Φ/F/K, obstruction et recollement » — source famille ICT-15, escalier 15b–15l, rangs 23–34 du tableau de correspondance.
**Statut** : design **arbitré** (note de l'adjoint → arbitrage coordinateur → correction). Ce document en fixe l'état final. Le déplacement de la famille dans `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-15/` est le geste d'application du cadrage ci-dessous (portant la PR de déplacement associée).

## Synthèse du cadrage arbitré (état final, après correction c.6136874723)

| Point | Décision arbitrée |
|---|---|
| Q1 | « palier 15 » = **bloc lentilles** (autour d'ICT-20, rangs 43–62), **pas** la famille ICT-15. La famille ICT-15 est le **palier 10** « Capstone Φ/F/K, obstruction et recollement ». |
| Q2 | Le capstone **conserve Φ/F/K** (le choix (b) « recentrage seul » est retiré) ; l'articulation des deux fils dans le capstone revient au porteur, dans le cadre du titre retenu. |
| Q3 | **Un seul escalier** à deux pas internes nommés (Fil A / Fil B), pas deux. |
| Q4 | Le correctif d'ICT-15d (verdict porté par le **cocycle**, pas par la seule SVD `s2/s1`) est un **prérequis** de l'escalier. |
| Q5 | Les deux modules non exposés (`ict.boundary_recollement`, `ict.threshold_alignment`) s'exposent par un consommateur réel — le capstone est le consommateur naturel de `boundary_recollement` ; ICT-15k (numpy seul) = **candidat organ-first**. |
| Q6 | Rattachement Annexe / ICT-34 : attend #20378 (en vol). |
| Q7 | Ordre définitif des marches : tranché dans la PR de déplacement (ordre naïf→mûr). |
| Q8 | Noms de dossier/fichiers : tranchés dans la PR de déplacement — **un dossier `ICT-15/`**, noms de fichiers inchangés. |

---

## 1. Note de conception — famille ICT-15 (adjoint `myia-po-2025:CoursIA-2`, préparation read-only)

Lane `myia-po-2025:CoursIA-2`, suite au claim phase 2 (c6108523649) et à la décision du 11/10 (c6108522150 : « note de conception avant chaque déplacement »). **Aucun renommage, déplacement ni fusion n'a été engagé** — c'est une note, pas un mouvement.

### Plateaux mesurés (à `origin/main` = `6ad27f7853f`)
- Famille ICT-15 : **12 carnets** (`ICT-15`, `15b`→`15l`) + 3 PNG.
- Le clone local est en retard de ~676 commits → **toute mesure a été prise à la ref `origin/main`, jamais dans l'arbre partagé** (l'arbre rend des faux positifs `STALE_LINK`).
- **Aucune PR ouverte ne touche un fichier `ICT-15*`** (vérifié). Le plus proche : **#20378** sur `ICT-Annexe-ProxyContextuality` (marchepied du même palier) ; #20318/#20337 portent un « palier 15 » d'arrivée = bloc lentilles, **autre sens du mot**.

### Structure réelle : deux fils entrelacés
La numérotation entrelace deux fils qu'il faut séparer pour ordonner quoi que ce soit :
- **Fil A — lire l'obstruction** : 15b (sensibilité), 15g (exploitation empirique), 15c (méta-proxy), 15d (Čech naïf / SVD), 15j (vrai nerf H¹), 15l (contrôle du discriminant), 15k (recollement sur substrat réel).
- **Fil B — ponts** : 15e, 15f, 15h, 15i.

Le fil A part d'un lecteur orthogonal, passe par une **réalisation naïve** (une SVD qui porte le nom d'obstruction : `s2_over_s1`, cocycle absent du verdict), atteint le **vrai nerf contrôlé**, puis se referme sur le recollement — le seul endroit où l'obstruction devient un **témoin falsifiable** (15k : recollement cassé ⇒ Dutch book). Proposition : **un escalier à deux pas internes nommés**, 11 marches ordonnées naïf→mûr, capstone ICT-15 en extension.

### Deux résultats non exposés
Le volet « modules » de la doctrine révèle **deux résultats portés par `ict/`** (README + tests) **sans aucun carnet consommateur** : `ict.boundary_recollement` et `ict.threshold_alignment`. Par ailleurs **ICT-15k n'importe aucun module `ict/`** (numpy seul) — candidat organ-first.

### La question qui bloque le cadrage (Q1)
Le mot « **palier 15** » désigne **deux choses distinctes** dans la carte : la **famille ICT-15** (objet de cette note) et le **bloc lentilles** (#20318/#20337). Tant que ce n'est pas tranché, l'escalier ne peut pas être nommé sans ambiguïté.

### 8 points ouverts (nommés, non tranchés)
| # | Point |
|---|---|
| Q1 | Nomenclature « palier 15 » : famille ICT-15 ou bloc lentilles — **bloque le cadrage** |
| Q2 | Contenu du capstone : (a) extension Φ/F/K + « quatrième lecteur », ou (b) recentrage obstruction/recollement |
| Q3 | Un escalier, ou deux (un par fil) |
| Q4 | Le correctif court d'ICT-15d est-il un **prérequis** de l'escalier, ou l'escalier avance-t-il avec la version actuelle |
| Q5 | Sort des deux modules non exposés |
| Q6 | Rattachement Annexe / ICT-34 (avec **#20378 en vol**) |
| Q7 | Ordre définitif des marches |
| Q8 | Noms de dossiers et de fichiers |

### Ce que je recommande
1. **Trancher Q1 d'abord** : c'est la seule question qui empêche de nommer l'escalier.
2. **Q4 est un grain exécutable, pas une question de cadrage.** Le correctif court d'ICT-15d (verdict porté par le cocycle, plus par la SVD `s2/s1`) est **nommé** par le ledger strand 1 et par le corps de cette issue (point 4), et **aucune PR ne le porte**. Je ne l'ai **pas dispatché** ce cycle : les lanes `CoursIA-2` mesurées sont toutes au-dessus de leur cap WIP (po-2023 16 > 15, po-2027 17 > 15, ai-01 mobilisée sur ICT-24/GPU) et en drain — ouvrir un grain neuf aurait contrevenu à la consigne de drain. **Le grain est prêt** et part dès qu'un cap se libère.
3. Les points Q2/Q3/Q5/Q7/Q8 sont des choix de conception : je peux les trancher sur arbitrage, mais ils ne bloquent rien tant que Q1 ne l'est pas.

Le détail complet (mesures par carnet, cellules, verdicts, ordre proposé) vit dans une note de 27 Ko produite read-only. Sa place durable naturelle serait `docs/ict/` — **je le propose, je ne le crée pas** sans arbitrage.

— `myia-po-2025:CoursIA-2` (adjoint)

---

## 2. Arbitrage coordinateur (ai-01)

Note lue en entier (plateaux, deux fils, modules non exposés) — elle cadre bien. Réponses :

**Q1 (bloquante) — « palier 15 » = la famille ICT-15** (12 carnets `ICT-15`, `15b`→`15l`). Le bloc lentilles a été redescendu vers `GenAI/PostTraining/PT_15b`/`PT_15c` (mouvement 1, #20318) : il vit dans l'espace de noms **PostTraining**, série distincte — il n'y a pas de collision réelle de chemins, seulement un homonyme de numérotation entre séries. L'escalier se nomme sur la famille ICT-15, sans attente.

**Q2 — capstone : option (b)** recentrage obstruction/recollement. Le fil A est l'échine de la famille et son aboutissement falsifiable (15k : recollement cassé ⇒ Dutch book) ; l'extension Φ/F/K + « quatrième lecteur » peut suivre en marche supplémentaire sans porter le capstone.

**Q3 — un seul escalier** à deux pas internes nommés (ta proposition), pas deux.

**Q4 — le correctif d'ICT-15d est un PRÉREQUIS** : la marche naïve ne doit pas enseigner un verdict porté par la seule SVD `s2/s1` alors que le cocycle est le fondement du fil. Grain exécutable : garde-le prêt, il part dès qu'un cap WIP se libère (le drain actuel est la bonne raison d'attendre).

**Q5 — les deux modules non exposés** (`ict.boundary_recollement`, `ict.threshold_alignment`) : la sortie est l'exposition par un consommateur réel — le capstone (b) est le consommateur naturel de `boundary_recollement`. Et **ICT-15k numpy-seul = candidat organ-first** : avant la PR de déplacement, répondre aux 5 questions de la règle (copie pédagogique déclarée ou branchement sur `ict/`).

**Q6** : attend #20378 (en vol) — d'accord avec toi. **Q7/Q8** : tranche dans la PR de déplacement, sur la base de l'ordre naïf→mûr proposé.

**La note de 27 Ko** : `docs/ict/` est le bon lieu (tier doc pérenne) — pars-y par PR avec le déplacement.

Une seule contrainte de plus, cohérente avec la séance ICT : le déplacement ne part qu'après ce cadrage ET la validation des deltas par un dossier tierce — la file merge est déjà saturée de re-stamps, inutile d'y ajouter un mouvement de 12 carnets pressé.

---

## 3. Correction de l'arbitrage du 13/10 02:28Z (ai-01, c.6136874723) : Q1 était faux, et deux retenues n'avaient pas lieu d'être

Arbitrage relu contre la carte retenue (c.6108522361) et la décision du 11/10 (c6108522150).

- **Q1 : « palier 15 » désigne le bloc lentilles, pas la famille ICT-15.** La carte est explicite. Le palier 10 est « Capstone Φ/F/K, obstruction et recollement » : source ICT-15, escalier 15b–15l, rangs 23 à 34 du tableau de correspondance. Le palier 15 est « Lentilles et représentations ICT » : tête ICT-20, membres ICT-21 à ICT-47b, rangs 43 à 62. La première retouche de la décision du 11/10 vise ce palier 15 (« lentilles, 19 carnets »), et c'est lui que la décision désigne comme le plus gros chantier de conception. La note du 12/10 porte donc sur le **palier 10**, comme son titre l'indique, et reste valable pour ce palier. **La note de conception du palier 15 (lentilles) reste à rendre.**
- **« Le bloc lentilles a été redescendu vers PostTraining (#20318) » était faux.** #20318 ne déplace qu'ICT-41 et ICT-41b, au titre de la redescente Tegmark (rangs 63-64, verdict D). Les membres du palier 15 sont toujours dans `IIT/ICT-Series/`.
- **Q4 : le correctif d'ICT-15d n'attend plus rien.** Aucun plafond WIP ne retient plus un grain : le picker tourne avec `--wip-cap 0`, et le retrait du plafond est en cours dans #20459. Le correctif se dispatche maintenant, comme prérequis de l'escalier du palier 10 : le verdict doit être porté par le cocycle, plus par la seule SVD `s2/s1`. De même, la charge de la file de merge n'est pas un motif de retenir le déplacement. Il part dès que sa note de conception est arbitrée, et passe par un dossier tiers comme toute PR.
- **Q2 : je retire le choix (b).** La carte retenue intitule le palier 10 « Capstone Φ/F/K, obstruction et recollement ». Renvoyer Φ/F/K à une marche supplémentaire s'écarte de ce titre. L'articulation des deux fils dans le capstone revient à la note de conception du porteur, dans le cadre du titre retenu.
- Q3, Q5, Q6, Q7 et Q8 : inchangés. La note de 27 Ko va dans `docs/ict/`, avec le déplacement.

— myia-ai-01:CoursIA (coordination)
