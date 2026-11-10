# Relecture de la banque QCM — septembre 2026

Tranche 4/4 du grain [#18223](https://github.com/jsboige/CoursIA/issues/18223) : relecture
des questions publiées dans cette banque. Conformément au garde-fou de l'issue, un constat
est **signalé, jamais réécrit en silence** — la banque reste l'import fidèle des exports
Moodle du Drive, et le présent document est le registre des défauts constatés.

## Méthode

Deux passes :

1. **Lecture intégrale déléguée** (sous-agent lecture seule) : chaque question lue, chaque
   clé mathématique rejouée. Les constats issus de cette passe sont notés **R** (rapportés).
2. **Re-vérification par la lane** des constats décisifs : les deux questions à options
   dupliquées contradictoires (attribution à la source par probe des XML, ci-dessous) et
   quatre constats de clés mathématiques (recalculs). Ces constats sont notés **V** (vérifiés
   firsthand).

| Répartition des constats | nombre |
|---|---:|
| datés (référence obsolète) | 1 |
| coquilles (typographie, orthographe) | 23 |
| contestables (clé discutable ou indrivable) | 10 |

Les coquilles vivent dans la source Moodle : la banque les reproduit fidèlement et ne les
corrige pas. Les contestables sont les seuls à affecter l'usage pédagogique de la banque.

## Liaison des figures — défaut corrigé (review NanoClaw du 28/09)

La review structurelle de #18263 a relevé que les figures extraites étaient **orphelines** :
le convertisseur réécrivait le chemin (`@@PLUGINFILE@@/…` → `images/<id>.<ext>`) dans le HTML
brut, puis le nettoyage des balises supprimait le `<img>` qui portait cette référence — les
quatre questions concernées annonçaient « la figure suivante » sans aucun lien.

Corrigé dans la même PR : `html_to_text` conserve désormais la référence en texte
(`[figure: images/<id>.<ext>]`) avant le nettoyage, `check` détecte le sens inverse (tout
fichier de `images/` non référencé est une erreur ; toute figure annoncée sans référence
embarquée est une attention), et les tests couvrent les deux sens.

## Publication des figures — décision ai-01 du 28/09

La review ai-01 de #18263 a relevé que trois figures ne peuvent pas entrer dans un dépôt
public en l'état, et que le convertisseur les y **ramènerait** à la prochaine conversion
(la source XML vit hors dépôt). La décision est donc portée par le convertisseur lui-même,
dans une `PUBLICATION_POLICY` keyée par identifiant — le produit reste reproductible :

| Question | Figure d'origine | Traitement retenu |
|---|---|---|
| ia4-004 | photographie d'une page du manuel Russell & Norvig (fig. 14.23) | **redessinée** à partir de ses seules valeurs (`redraw_qcm_figures.py`, mention de source incluse), `images/ia4-004.png` |
| ia4-006, ia4-007 | capture d'écran de la table du dentiste du même manuel | **tableau markdown** dans l'énoncé (les huit nombres, mention de source) |
| ia2-010 | URL Dropbox personnelle (jeton de partage) | **marqueur neutre** `[figure externe non disponible]` |

Les trois fichiers d'origine (`ia4-004.jpg`, `ia4-006.png`, `ia4-007.png`) sont retirés du
dépôt ; `images/` ne contient plus que `ia2-027.png` et `ia4-004.png`. Les deux tableaux du
dentiste restituent les mêmes valeurs que la capture — contrôlées sur les clés des questions :
P(carie | mal aux dents) = 0.12/0.2 = 0.6 et P(non carie | pas mal aux dents) = 0.72/0.8 =
0.9, soit les deux clés correctes. La figure redessinée restitue de même la chaîne de
ia4-004 (P(C|T,I,P) = 0.9 puis P(E|C) = 0.9 → P(¬E) = 0.19, la clé de la question).

**ia2-027 relue en vision (28/09)** : graphe d'exploration S→G, coûts sur les arêtes et
valeurs heuristiques en rouge — une figure de cours (graphe propre à l'exercice, pas une page
d'ouvrage ni une capture), qui reste donc légitimement dans `images/`. Reste ouverte la
question du doublon ia2-010 ↔ ia2-027 ci-dessous.

**ia2-010 précisé** : sa figure est une **URL Dropbox externe** (le `<img>` de l'export 2018
pointe un lien `photos-5.dropbox.com`, vignette 32×32 — probablement expiré), pas un fichier
embarqué. Depuis le 28/09 elle est publiée sous **marqueur neutre** (`[figure externe non
disponible]`) — le jeton de partage personnel ne peut pas rester dans un dépôt public ; elle
reste signalée en `ATTENTION` par `check` (« figure annoncée sans référence embarquée »), ce
qui est le signal voulu : l'énoncé annonce une figure absente de la banque. Sa quasi-jumelle **ia2-027** (même question, export 2020, mêmes options) porte
la figure embarquée — la clé de dédoublonnage sha1 ne les a pas fusionnées (ponctuation
différente : « par une » vs « par : une »). **Double arbitrage mainteneur** : rapatrier ou
accepter l'URL externe pour ia2-010, et statuer sur le doublon ia2-010 ↔ ia2-027.

## Les deux défauts structurants — attribution à la source

**ia2-008** (complexité mémoire d'IDS) et **ia5-002** (longueur de description minimale)
portent chacun une option en double exemplaire avec clés contradictoires (marquée correcte
puis fausse). Probe des exports XML bruts (Drive `Rattrapages/`) :

- `quiz-MSMEM4EN08-Questions 2018-20180319-1846.xml` contient exactement les onze réponses
  de ia2-008, avec `O(db)` à `fraction="0"` puis `O(db)` à `fraction="100"`, et `O(bm)`
  deux fois à `fraction="0"` — le convertisseur a fidèlement reproduit la source ;
- la question de ia5-002 apparaît à l'identique dans plusieurs exports (elle y figure neuf
  fois sur quatre fichiers), toujours avec l'option dupliquée (`fraction="100"` puis
  `fraction="0"`).

Ces doublons sont donc des **défauts de la source Moodle**, pas du convertisseur. En usage,
l'option dupliquée se comporte comme un piège (un exemplaire est « correct », l'autre non) :
à arbitrer par le mainteneur avant toute utilisation en évaluation.

Depuis cette relecture, `moodle_bank.py check` signale ces doublons en `ATTENTION` (sans
faire échouer la validation — la banque reste fidèle à la source) :
`test_check_flags_duplicate_options_as_attention` couvre la détection.

**Rectification du 6 octobre 2026 — ia2-008 n'était pas un défaut de la source.** La sonde
ci-dessus comparait le texte des réponses sans leur mise en forme. Or l'export porte les
puissances dans des `<span style="…vertical-align:super">` : les deux `O(db)` sont en réalité
`O(d^b)` (faux) et `O(db)` (juste), les deux `O(bm)` sont `O(b^m)` et `O(bm)`. C'est le
convertisseur qui aplatissait les exposants, et fabriquait ainsi le doublon. Il les rend
désormais en notation `^` (`O(b^d)`, `O(b^(d/2))`), ce qui rétablit aussi les options de la
question sur l'exploration bidirectionnelle (deux occurrences dans ia-2). La clé d'origine de
ia2-008, `O(db)`, est la bonne. ia5-002, lui, est bien un doublon de la source.

## Clés mathématiques recalculées

Les quatre constats suivants ont été recalculés firsthand par la lane (V) :

- **ia3-015 / ia3-019** (équivalents de p⇒q) : `¬(¬p∧¬q) ≡ p∨q`, qui n'est **pas** équivalent
  à `p⇒q ≡ ¬p∨q` (contre-exemple : p vrai, q faux). La paire de questions propage la même
  erreur dans les deux sens (ia3-015 marque l'option correcte, ia3-019 la marque non
  équivalente).
- **ia4-011** (machine à sous) : avec la définition donnée (« ? désigne n'importe lequel des
  autres symboles »), l'espérance vaut `(20+16+5+3)/64 + 2×(3/64) + 1×(9/64) = 59/64`. La
  clé `62/64` n'est dérivable d'aucune lecture naturelle de la table, et `59/64` figure
  parmi les options, marquée fausse.
- **ia4-018** (voiture d'occasion, Bayes) : `P(bon | test+) = 0.56/0.665 = 0.8421` ;
  `EU = 0.8421×500 + 0.1579×(−200) = 389.47 €`. La clé `378.92 €` ne correspond à aucun
  calcul cohérent, et `389.47 €` est absente des options.

Deux autres clés sont indérivables selon la passe déléguée (R, recalcul du sous-agent) :
**ia2-018** (clé 3.2 alors que l'arbre donne E=2.4 à la racine Max et 1.4 à l'option
marquée fausse) et **ia2-019** (clé 4.7 alors que l'arbre donne 4.8 et 7.7).

## Registre complet des constats

Colonne **vér.** : V = re-vérifié firsthand par la lane ; R = rapporté par la passe de
lecture déléguée (extrait et argument verbatim de cette passe).

| id | vér. | classe | extrait verbatim | constat |
|---|---|---|---|---|
| ia1-001 | R | coquille | `Très difficile - probablement loin dêtre résolu` | apostrophe manquante — « d'être ». |
| ia1-001 | R | contestable | `Jeu de Go → Très difficile - probablement loin d'être résolu` | AlphaGo (2016) puis AlphaGo Zero ont dépassé les champions du monde deux ans avant la source 2018 ; l'appariement Go est faux dans le référentiel de la question (AIMA 4e éd. : Go « 2016 »). |
| ia1-005 | R | coquille | `Quelque soit l'environnement de tâche` | graphie correcte : « Quelle que soit ». |
| ia1-007 | R | coquille | `Serveur téléphonique à commande vocal` | accord de genre : « commande vocale ». |
| ia2-002 | R | coquille | `A≠1B≠2D≥3D<B\|C-B\|≠1C≠5` | séparateurs manquants entre les contraintes, énoncé inanalysable tel quel. |
| ia2-005 | R | coquille | `Recombinaison des génômes` | graphie correcte : « génomes ». |
| ia2-008 | V | contestable | `O(db)` (correcte puis incorrecte) | option en double à clés contradictoires, et `O(bd)` marquée fausse est identique à la clé par commutativité — défaut de la source (probe ci-dessus) ; la clé O(bd) est elle-même la complexité mémoire standard d'IDS. |
| ia2-014 | R | coquille | `les coûts suivants { 2,1,1,0,3}` | cinq valeurs pour six volumes (0 à 5 L) ; la jumelle ia2-026 en porte six : `{2,1,1,1,0,3}` — valeur manquante. |
| ia2-014 | R | coquille | `Vous êtes John McClain` | le personnage s'appelle John McClane. |
| ia2-014 | R | coquille | `les volumes d'eaux de 0 à 5L` | « volumes d'eau » (erreur aussi présente dans ia2-026). |
| ia2-018 | R | contestable | clé `3.2` | indrivable : l'arbre donne E=2.4 (racine Max) et 1.4 (option marquée fausse). |
| ia2-019 | R | contestable | clé `4.7` | indrivable : l'arbre donne 4.8 (option marquée fausse) et 7.7 (clé attendue). |
| ia2-022 | R | coquille | `A≠1B≠2D≥3D<B\|C-B\|≠1C≠5` | mêmes séparateurs manquants que ia2-002. |
| ia2-026 | R | coquille | `Vous êtes John McClain` | « John McClane » (cf ia2-014). |
| ia3-015 | V | contestable | `¬(¬p∧¬q)` marquée équivalente | `¬(¬p∧¬q) ≡ p∨q` n'est pas équivalent à `p⇒q` (contre-exemple p=V, q=F). |
| ia3-019 | V | contestable | `¬(¬p∧¬q)` marquée non équivalente | même erreur que ia3-015 vue par l'autre bout : l'option (non équivalente) devrait être correcte. |
| ia4-005 | R | coquille | `la couverture de Markov d'un nœud est données par` | accord : « est donnée par ». |
| ia4-008 | R | coquille | `une mauvaise et une bonne nouvelles` | accord : « une mauvaise et une bonne nouvelle ». |
| ia4-011 | V | contestable | clé `62/64` | l'espérance calculée est `59/64` (option présente, marquée fausse) — cf section recalculs. |
| ia4-017 | R | coquille | `Qu'elle est la probabilité que le taxi était vert?` | « Quelle » (homophone). |
| ia4-017 | R | coquille | `9 taxis sur 10 y sont vert` | accord : « verts ». |
| ia4-018 | V | contestable | clé `378.92€` | le calcul de Bayes donne `389.47 €`, absent des options — cf section recalculs. |
| ia4-022 | R | coquille | `-5,5` (case Cinq,Cinq) | duopole à coûts identiques → gains symétriques, matrice en miroir : « -5,-5 » attendu (frappe probable). |
| ia5-002 | V | contestable | `La longueur de description minimale` (correcte puis incorrecte) | option en double à clés contradictoires — défaut présent dans tous les exports source (probe ci-dessus). |
| ia5-005 | R | coquille | `l'agent aprenant` | « apprenant » (et « des technique » → « des techniques »). |
| ia5-007 | R | contestable | `Arbres de décision` marqués paramétriques | les références standard (AIMA, Murphy, scikit-learn) classent les arbres de décision parmi les modèles non paramétriques. |
| ia5-009 | R | coquille | `Elle garantie l'inversibilité` | verbe conjugué : « garantit » (et « bloquer » → « bloqué »). |
| ia5-013 | R | coquille | `Ils peuvent fournissent des résultats` | « peuvent fournir » (double verbe). |
| ia5-014 | R | coquille | `sur une ordinateur conventionnel` | « un ordinateur ». |
| ia5-021 | R | coquille | `une opération binaire complexz` | « complexe ». |
| dl-001 | R | daté | `Une compétition annuelle d'intelligence artificielle` | ILSVRC n'a plus été organisée depuis 2017 — « annuelle » au présent est une référence datée. |
| dl-001 | R | coquille | `Qu'est ce que ILSRVC ?` | acronyme correct : ILSVRC (épelé correctement dans dl-005 et dl-010). |
| dl-011 | R | coquille | `crée par le français Yan LeCun` | « créé » et « Yann LeCun ». |
| dl-029 | R | coquille | `En utilisant TensorFlox et Keras` | « TensorFlow ». |

## Portée — ce qui n'a pas été vérifié

- **Questions à figure** : la lecture de figure était hors capacité de la passe déléguée.
  Elle a été faite depuis, en vision, sur les quatre figures concernées : ia4-006 et ia4-007
  sont validées numériquement (table conjointe dentiste 0.6/0.9), ia4-004 est redessinée et
  sa chaîne recalculée (P(¬E) = 0.19, la clé de la question), ia2-027 est une figure de
  cours (cf « Publication des figures »). ia2-010 ne porte **pas** de figure embarquée : sa
  seule référence était l'URL externe, publiée depuis sous marqueur neutre — le lien vers sa
  figure reste à trancher par le mainteneur, comme le doublon ia2-010 ↔ ia2-027.
- **Calculs rejoués concordants** (aucun constat émis) : minimax et alpha-bêta
  (ia2-016/017/030/031/032), expectiminimax (ia2-033/034), Bayes (ia4-003/008/015),
  partage des pirates (=97), stratégie mixte (1/6–1/3), arbre (=2 feuilles), LeNet-5,
  ResNet (3.57 %).

## Arbitrage du mainteneur — 6 octobre 2026

Le mainteneur a tranché (#18285) : les clés prouvées fausses sont corrigées **dans la
banque**, chacune avec une note dans son `explication`, et l'occurrence 2020 du doublon est
gardée. Les décisions vivent dans le convertisseur (`RETIRED`, `KEY_CORRECTIONS`), comme la
politique de publication des figures : une ré-conversion les réapplique, et une correction
qui ne trouve plus son option fait échouer la conversion au lieu de passer en silence.

| id | décision | avant → après |
|---|---|---|
| ia2-008 | défaut du convertisseur (exposants), cf rectification ci-dessus | options rétablies, clé `O(db)` inchangée |
| ia2-010 | retirée, doublon de ia2-027 (export 2020, figure embarquée) | la figure Dropbox expirée sort avec elle |
| ia2-018 | clé corrigée | `2.4` et `3.2` cochées → `2.4` seule |
| ia2-019 | clé corrigée | `4.7` et `7.7` cochées → `7.7` seule |
| ia3-015 | clé corrigée | `¬(¬p∧¬q)` cochée équivalente → non cochée |
| ia3-019 | clé corrigée | `¬(¬p∧¬q)` non cochée → cochée (non équivalente) |
| ia4-011 | clé corrigée | `62/64` → `59/64` |
| ia4-018 | option et clé corrigées (la bonne valeur était absente) | `378.92€` → `389.47€` |
| ia5-002 | second exemplaire de l'option retiré | 8 → 7 options |
| ia5-007 | clé corrigée | « Arbres de décision » paramétriques → non |

Les identifiants ne sont pas réattribués : ia2-011 et les suivantes gardent le leur, ia2-010
reste un trou dans la séquence. La banque compte 146 questions.

**Non tranché** : ia1-001 (le jeu de Go « loin d'être résolu », daté dès 2016) et les 23
coquilles, reproduites fidèlement depuis la source.
