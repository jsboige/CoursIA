# Manifeste des figures — GenAI/Image/05-History/assets/clipasso

Provenance des images cibles du notebook `05-2-CLIPasso-Semantic-Sketching.ipynb`.

> **QA visuelle déléguée (merge-gate)** : ce MANIFEST est rédigé sur la lane `myia-po-2023:CoursIA` (GLM, sans vision). Les champs mécaniques (dimensions PIL, poids octets, provenance git/livre) sont vérifiés par outil ; les champs descriptifs (`Contenu réel vérifié`, alt-text) sont des descriptions de provenance — **la vérification visuelle firsthand est déléguée au merge-gate** (ai-01 ou lane CoursIA-2 MiniMax, doctrine vision des figures).

## target_camel.png

- **Source** : `target_images/camel.png` du dépôt officiel CLIPasso (`github.com/yael-vinker/CLIPasso`, MIT) — démo canonique de la Figure 1 du papier Vinker et al. 2022.
- **Description visuelle** : photographie d'un chameau de profil sur fond uni, cadrage carré.
- **Contenu réel vérifié** : PNG 248×248 RGB (dimensions PIL vérifiées). Contenu décrit par la provenance officielle (Fig. 1 du papier) ; vérification visuelle déléguée merge-gate.
- **Alt-text (FR)** : Photographie d'un chameau de profil sur fond uni — cible canonique des esquisses CLIPasso du papier (Fig. 1).
- **Poids** : 34 205 octets
- **Provenance** : copie byte-identique (pas de retouche) — `D:/Dev/clipasso-run/repo/target_images/camel.png`.

## target_robot.png

- **Source** : image de référence robot du notebook `03-4` (workflow VLM in-graph, série GenAI/Image) — `assets/krea2-character/reference_robot.png`, copiée localement pour rendre ce rayon autoportant (indépendant de l'ordre de merge de la PR krea2).
- **Description visuelle** : personnage robot en vignette générée, fond neutre.
- **Contenu réel vérifié** : PNG 591×591 RGB (dimensions PIL vérifiées). Contenu décrit par la provenance ; vérification visuelle déléguée merge-gate.
- **Alt-text (FR)** : Portrait de personnage robot — seconde cible des esquisses CLIPasso (grille de l'exercice 2).
- **Poids** : 309 749 octets
- **Provenance** : copie locale depuis le worktree krea2 (source : sortie ComfyUI du cours).

## grid_abstraction.png

- **Source** : sortie de la cellule « Lecture de la grille » du notebook `05-2` (rendu côte à côte matplotlib) — **extraction directe de l'output d'exécution**, pas un montage.
- **Description visuelle** : bande de 4 panneaux — photo cible chameau puis esquisses officielles CLIPasso 32/16/8/ traits (SVG rendus en PNG), abstraction croissante de gauche à droite.
- **Contenu réel vérifié** : PNG 1589×344 RGBA (dimensions PIL vérifiées, 122 880 octets). Les 4 SVG sources sont les `_best.svg` produits par les runs officiels GPU du 17-18/09/2026 (logs de provenance dans les outputs du notebook). Vérification visuelle déléguée merge-gate.
- **Alt-text (FR)** : Grille d'abstraction CLIPasso — la cible chameau et ses esquisses à 32, 16, 8 puis 4 traits de Bézier.
- **Poids** : 122 880 octets
- **Provenance** : `base64` du `image/png` de l'output de la cellule grille de l'exécution finale (papermill, kernel python3).
