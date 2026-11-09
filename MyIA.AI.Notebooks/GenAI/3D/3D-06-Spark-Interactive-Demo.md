# 3D-06 — Annexe : la démo interactive *spark-physics*, lecture annotée

[← Tradeoffs d'optimisation (3D-05)](3D-05-3DGS-Optimization-Tradeoffs.ipynb) | [← Série GenAI/3D](README.md)

> **Ce que fait ce document** : notre série a construit les gaussiens splatting *de l'intérieur* — compositing et tri en [3D-03](3D-03-Gaussian-Splats-Concepts.ipynb), moteur CUDA et conventions en [3D-04](3D-04-3DGS-From-Scratch-with-gsplat.ipynb), leviers d'entraînement en [3D-05](3D-05-3DGS-Optimization-Tradeoffs.ipynb). Cette annexe lit *de l'extérieur* une application grand public de cette technologie : [`bmild/spark-physics`](https://github.com/bmild/spark-physics), une taverne interactive où l'on marche, tire des projectiles et fait tomber une tour de Jenga **dans une scène faite de gaussiens splats**. Ce n'est pas un livrable d'exécution : c'est une lecture guidée du code réel, écrite pour reconnaître dans du JavaScript de production les concepts que nos carnets ont mesuré à la main.

**Note de lecture** : dépôt lu au commit `308fbf8` (2025-09-17, PR #2 « Stitched »), MIT, 62 étoiles. La démo vit en ligne sur `spark-physics.netlify.app`. Toute citation ci-dessous vient de `src/main.js` — fichier unique de 35 Ko qui contient toute l'application.

## 1. Les trois briques

| Brique | Rôle dans la démo |
|---|---|
| **Spark** ([sparkjs.dev](https://sparkjs.dev), dépôt `sparkjsdev/spark`, projet World Labs) | Rendu des gaussiens dans une scène Three.js : `SparkRenderer`, `SplatMesh`. Formats d'entrée : `ply`, `sogs`, `spz`, `splat`, `ksplat`, plus des splats procéduraux. LOD et effets dynamiques (« Dyno »). |
| **Rapier** (`@dimforge/rapier3d-compat`) | Moteur physique : monde, corps rigides, colliders, raycasts. |
| **Three.js** | Orchestration : caméra, lumières, loaders FBX/GLTF, `PointerLockControls`, la boucle d'animation. |

L'import qui résume la démo : `import { SparkRenderer, SplatMesh } from '@sparkjsdev/spark'` — le splat devient un *type de mesh parmi d'autres* dans la scène. C'est la promesse de Spark : les gaussiens cohabitent avec les meshes ordinaires, chacun rendu par son pipeline.

## 2. Lecture guidée de `src/main.js`

### 2.1 La scène : un splat décoratif, une géométrie invisible

L'environnement est chargé **deux fois**, sous deux formes :

```js
// le visible : un nuage de gaussiens (fichier .spz)
const splat = new SplatMesh({ url: 'hobbit_stitched.spz' });
splat.scale.set(3, -3, 3);   // notez le -3
splat.defaultView.sort32 = true;
splat.defaultView.sortRadial = true;

// l'invisible : le même environnement en GLB, maillé pour la physique
// chaque mesh devient un ColliderDesc.trimesh(vertices, indices) sur un corps fixe
```

Trois choses à lire dans ces lignes, trois ponts directs vers nos carnets :

- **`scale.set(3, -3, 3)`** — le flip d'axe Y. [3D-04](3D-04-3DGS-From-Scratch-with-gsplat.ipynb) a mesuré le même piège : nos caméras OpenGL (−z devant, y haut) et la convention OpenCV du moteur (+z devant, y bas) ne diffèrent que d'un retournement — là où nous construisions `diag(1,-1,-1,1)` autour de la world-to-camera, la démo l'absorbe dans le scale du mesh. Même maladie, deux pansements.
- **`sort32` et `sortRadial`** — le tri par profondeur. [3D-03](3D-03-Gaussian-Splats-Concepts.ipynb) l'a construit à la main (trier les splats arrière-avant à chaque frame, sinon l'alpha-blending superpose dans le mauvais ordre) ; Spark l'expose comme deux drapeaux : un compteur de tri 32 bits (précision de profondeur pour les grosses scènes) et un tri radial (regrouper par direction caméra plutôt que trier globalement, meilleur cache). Le concept que nous avons payé en Python pur est ici une option de configuration — parce qu'il vit côté GPU.
- **Deux fichiers pour une scène** : l'image (splats) et la collision (trimesh GLB) sont **deux représentations séparées du même lieu**. Le splat ne « collisionne » pas : c'est de la lumière. La physique vit dans un maillage invisible préparé séparément. La touche `Space` de la démo le prouve : le mode debug échange le splat contre le `MeshNormalMaterial` du maillage de collision — on voit alors la taverne *réelle* de la physique, en fils de fer.

### 2.2 Le joueur : une capsule, des raycasts, un pas fixe

```js
// le joueur : corps dynamique capsule, rotations verrouillées
// radius 0.07, half-height 0.35, amortissement linéaire 4.0, CCD activé
GRAVITY = { y: -9.81 * 0.7 }   // GLOBAL_SCALE 0.7 déteint même sur la gravité
FIXED_TIME_STEP = 1/60, MAX_SUBSTEPS = 5
```

`isPlayerGrounded()` tire un raycast vers le bas (`world.castRayAndGetNormal`) : au sol si le hit tombe sous `footOffset + 0.12` avec une normale y > 0.3 et une vitesse verticale ≤ 0.6. Le mouvement (`updateMovement`) est caméra-relatif (WASD, R/F pour voler), et `adjustVelocityForWalls` fait du *wall-sliding* : un raycast d'anticipation à `PLAYER_RADIUS + 0.1` projette la vitesse sur le plan du mur touché.

Le pas de temps mérite une note : la boucle `requestAnimationFrame` est variable, mais la physique avance à **1/60 fixe, au plus 5 sous-pas par frame** — le pattern canonique de tout moteur physique déterministe (accumuler le temps réel, consommer par quanta fixes). Notre optimisation en [3D-05](3D-05-3DGS-Optimization-Tradeoffs.ipynb) faisait l'inverse (des itérations discrètes sans temps simulé) parce qu'il n'y avait pas de dynamique ; dès qu'il y en a une, le pas fixe n'est pas négociable.

### 2.3 Les projectiles : dynamique, CCD et son réactif

`shootProjectile()` crée une sphère rouge (`0xff4444`), corps dynamique avec **CCD** (détection de collision continue — un projectile à 10.5 unités/s ne doit pas tunneler à travers un mur mince entre deux frames), collider boule de rayon 0.14, restitution 0.9 (rebond vif) contre 0.0 pour l'environnement. La détection de rebond vit dans la boucle physique : si le delta de vitesse d'un projectile dépasse `BOUNCE_DETECTION_THRESHOLD = 2.0` entre deux sous-pas, c'est un impact — `playBounceSound()` rend le volume selon la distance (falloff linéaire sur 10 unités) et la hauteur selon la vitesse (pitch 0.9–1.1, avec ±3 % de gigue pour éviter l'effet mitraillette).

### 2.4 La tour de Jenga et les personnages

`buildJengaTower` empile 16 couches de 3 briques (`BoxGeometry` + corps dynamiques, friction 0.8, restitution 0.05, amortissements 0.1/0.2) — assez pour qu'un projectile bien placé la décime. Les personnages (un orc GLB, un barman FBX) reçoivent des **colliders par os** : `createBoneColliders` attache à chaque os une boule `ColliderDesc.ball(0.3)` sur un corps `kinematicPositionBased()` — cinématique parce que l'os *dirige* la collision (il suit l'animation), il ne la subit pas. Un projectile qui touche la zone d'un os (à `CHARACTER_HIT_DISTANCE = 0.8`) déclenche une réplique vocale.

### 2.5 La boucle d'animation

Dans l'ordre : mouvement du joueur → refroidissements → physique en sous-pas fixes (avec, par sous-pas : synchronisation des projectiles, détection de rebonds, tour de Jenga, objet saisi maintenu à 1.2 unité devant la caméra) → caméra recalée sur les pieds + hauteur d'œil 0.7 → **`sparkRenderer.update({ scene })`** → surbrillance de l'objet visé (`updateHover`, raycast écran-centre à 3.0 unités, émissif jaune `0xffff00`) → mixers d'animation → rendu Three.js. Le renderer Spark a sa propre passe d'update dans la frame : c'est lui qui retrie les splats pour la nouvelle caméra.

## 3. Ce que cette démo enseigne par-dessus nos carnets

1. **L'image n'est pas la géométrie.** Nous optimisions des splats pour *reproduire* des images ; la démo les utilise comme *décor* au-dessus d'une géométrie de collision préparée séparément. Deux métiers, deux artefacts, un même lieu.
2. **Le tri par profondeur ne disparaît pas, il déménage.** Du tri Python par profondeur de 3D-03 (`sorted` à chaque rendu) aux drapeaux `sort32`/`sortRadial` côté GPU : le concept est permanent, seule la facture change.
3. **Les conventions d'axes sont une taxe permanente.** La démo la paie dans un scale, nous dans une matrice de vue (3D-04) — chaque nouveau consommateur du format la repaie à sa façon.
4. **Une app « temps réel » est une chaîne de responsabilités à pas fixe** : physique 1/60 bornée en sous-pas, rendu à la cadence du navigateur, audio réactif aux événements physiques. Nos carnets isolaient chaque maillon ; ici on voit la chaîne entière tenue dans une seule fonction `animate`.

## 4. Verdict SOTA — annexe descriptive, pourquoi

La démo est une application navigateur (Vite + Three.js + Rapier, interaction `PointerLock`) : son exécution **est** l'interactivité dans un navigateur, il n'existe pas de forme locale consommable par un carnet qui préserve ce qu'elle démontre. Le verdict `INTRINSIC` (au sens de la règle SOTA du dépôt) et sa checklist 6 axes — binding NuGet, `P/Invoke`, CLI `Process.Start`, pont IKVM, pont PythonNet, bibliothèque équivalente — sont répondus nominativement dans le corps de la PR qui porte ce document ; l'annexe descriptive est la forme que l'arbitrage de l'issue (#20390) a retenue pour ce livrable.

---

*Annexe de la série GenAI/3D, Pli 3 R-gsplat (Epic #18605). Lecture au commit `308fbf8` du 2025-09-17 ; la démo : `spark-physics.netlify.app` (MIT).*
