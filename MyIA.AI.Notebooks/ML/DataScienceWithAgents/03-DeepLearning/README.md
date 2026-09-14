# 03-DeepLearning — Le deep learning from scratch : ouvrir la boîte noire couche par couche

[← DataScienceWithAgents (série parente)](../README.md) | [02-ML-Cours (prérequis)](../02-ML-Cours/README.md)

**Kernel** : Python 3 (`coursia-ml-training` pour 3.4c et 3.7) · **Bibliothèques** : NumPy (implémentations from scratch), matplotlib, torch (3.4c, 3.7, 3.9a) · **Niveau** : intermédiaire (post socle ML) · **CPU** : oui (exception 3.9a : entraînement ResNet-20 sur GPU, ~8 min)

## Pourquoi cette série

Le socle [`02-ML-Cours`](../02-ML-Cours/README.md) laisse un chaînon ouvert. La descente de
gradient y est ouverte à la main ([2.2](../02-ML-Cours/2.2-Descente-de-gradient.ipynb)) — mais
sur **une droite** ; le premier réseau de neurones de la formation
([2.9](../02-ML-Cours/2.9-Grokking-Generalisation.ipynb)) est entraîné en PyTorch **boîte
noire** : `loss.backward()` et tout suit. Entre les deux, personne n'a écrit la
**rétropropagation** à la main — l'étape où l'on comprend réellement *pourquoi* un réseau apprend.

Cette série ouvre cette mécanique, un concept par notebook, avec une discipline constante :
**from scratch PUIS framework**. Chaque mécanisme est d'abord implémenté en NumPy pur (sans
autograd), **vérifié** (gradient numérique par différence finie, parité pas-à-pas avec
l'équivalent PyTorch), et seulement ensuite relié à l'API PyTorch que consomment nos autres
séries (RL, PostTraining, ML-Training-Pipeline). L'entraînement final du 2.9 et les
`optimizer = Adam(...)` des séries appliquées deviennent lisibles par construction.

## Vue d'ensemble

| Notebook | Sujet | Concept-phare | Validation |
|----------|-------|---------------|------------|
| [3.0-Theorie-Information](3.0-Theorie-Information.ipynb) | Entropie, cross-entropy et KL construites from scratch sur un texte français, puis MSE vs cross-entropy sur un classifieur (le piège du gradient saturé), température (softmax) et pont vers DPO/GRPO | **La loss qui fait apprendre** : pourquoi la cross-entropy (et pas la MSE) est la bonne loss d'un classifieur, et la KL comme mesure de décalage entre deux distributions de modèle | entropie du français ~4,4 bits (redondance ~10-15 %, borne ≤ log₂K vérifiée) ; identité H(p,q)=H(p)+D_KL vérifiée, KL>0 sur tout le balayage (Gibbs) ; init saturée et fausse : la CE s'échappe (0,88) quand la MSE reste bloquée (0,39), gradient CE/MSE ~51× ; log 0 maîtrisé par lissage ε ; KL minimale en T=1 |
| [3.1-Retropropagation](3.1-Retropropagation.ipynb) | Le MLP et la rétropropagation à la main (NumPy pur, sans autograd) | **Le gradient vérifié** : différence finie vs analytique, parité exacte avec PyTorch | écart 1,3e-11 (seuil 1e-6) ; loss initiale, premier pas et trajectoire 3000 iters identiques à 1,1e-16 près ; init nulle = gradient nul (0,500 figé) |
| [3.2-Optimisateurs](3.2-Optimisateurs.ipynb) | Momentum, Adagrad, RMSProp, Adam et schedules, écrits en NumPy pur puis validés pas à pas contre `torch.optim` | **La parité exacte** : les 5 mises à jour sont celles de torch | GD/momentum/Adam à 1,11e-16, Adagrad bit-à-bit (0,00e+00), RMSProp à 2,22e-16 (float64, 1 pas) ; Beale : 5 trajectoires superposées (facteur 200 entre lr utilisables) ; MLP du 3.1 : 5 optimisateurs × 3 graines (RMSProp 0,059 < Adam 0,061 < … < GD 0,070) ; schedules : coût en full-batch déterministe, gain sous le plancher de bruit en mini-batch |
| [3.3-Regularisation](3.3-Regularisation.ipynb) | Dropout, weight decay et early stopping écrits à la main sur un MLP construit pour surapprendre (17 000 paramètres, 100 points d'entraînement, 12 étiquettes fausses) | **Corriger la variance sans changer le modèle** : trois remèdes appliqués au même surapprentissage fabriqué | sans régularisation : val acc 84,0 % (les 12 erreurs mémorisées) ; dropout p=0,3 : 89,0 % ; early stopping : +4,5 % ; gradient check du dropout (masque gelé) et invariants du dropout inverse (p=0,4, 2000×50) |
| [3.4-Attention-Transformer-From-Scratch](3.4-Attention-Transformer-From-Scratch.ipynb) | De l'attention mono-tête lisible sur l'inversion de séquence au mini-GPT de 1,25 M entraîné dans le notebook | **L'attention jusqu'au bout, sur CPU** : attention + masque causal + multi-têtes + bloc pré-norme, équivalence numérique avec `torch.nn`, mini-GPT char-level entraîné (117 s) sur le *Horla* (Maupassant, domaine public, 59 k caractères) | sac de mots A = B pour phrases opposées (1-9) ; inversion : poids requete 0 = `[0,007 0,007 0,007 0,007 0,007 0,967]` ; multi-têtes maison vs `torch.nn.MultiheadAttention` à 2,38e-07 (assert allclose 1e-5) ; mini-GPT 1 251 040 paramètres : perte ln(85)=4,44 → train 2,46 / val 2,45 en 800 étapes (117 s), perplexité val 11,5 ; 4 têtes spécialisées post-entraînement (diagonale 0,110 / 0,172 / 0,133 / 0,102) |
| [3.4c-MoE-from-scratch](3.4c-MoE-from-scratch.ipynb) | La couche Mixture of Experts écrite à la main (routeur top-k, capacité par expert avec jetons jetés, loss d'équilibrage `E·Σ f_i·P_i`), son coût mesuré en millisecondes contre deux FFN denses d'équivalence (iso-calcul, iso-paramètres) puis son entraînement dense contre MoE sur la tâche jouet du 3.4b | **Découpler paramètres et calcul** : E experts dont seuls k travaillent par jeton — le banc entrelacé mesure ce que la promesse vaut réellement, routage compris | routeur vérifié sur cas contrôlés (entropie uniforme 2,0794 = ln 8, tie-break de `topk` exposé) ; banc de coût : MoE E=8 k=2 (1 054 720 params) 17,46 ms/jeton contre dense-32d iso-paramètres 24,97 ms (0,70×) mais 2,41× le dense-8d iso-calcul — le routage top-k a un coût propre qui mange une partie de l'économie théorique ; qualité : la tâche jouet ne discrimine pas (acc 1,000 partout, dit comme tel) — l'information est dans les routeurs : sans loss d'équilibrage, parts 0,284…0,000 ; avec α=0,01, parts 0,121–0,134 quasi uniformes (L_aux 1,29 → 1,00) ; 3 exercices |
| [3.5-Phenomenes-de-Generalisation](3.5-Phenomenes-de-Generalisation.ipynb) | Grokking et double descente reproduits en NumPy pur (MLP à embeddings + Adam à la main), confrontés à la borne PAC du 2.8 | **Le phénomène sans la boîte noire** : mémorisation → transition abrupte, et le W de la double descente | garde gradient ≤ 1e-6 (embeddings inclus) ; grok mesuré : train saturé ~500 pas, test 100 % des dizaines de milliers de pas plus tard (wd = 1) ; contre-témoin wd = 0 ; double descente : pic au seuil M ≈ n (×5 le creux), asymptote moderne sous le creux classique, 20 graines |
| [3.6-Modeles-Generatifs](3.6-Modeles-Generatifs.ipynb) | VAE, GAN et diffusion (DDPM) écrits en NumPy pur, même cible (huit modes sur un cercle), même budget (6 000 pas, batch 256, largeur 64), face à une baseline GMM ajustée par EM | **Trois objectifs, trois échecs** : le VAE couvre mais moyenne, le GAN s'effondre, la diffusion raffine au prix de 100 passes par échantillon | garde gradient 1,4e-08 (ELBO + reparamétrisation) et 3,2e-10 (eps-net) ; multi-4-graines : GMM 8/8 disp 0,99 (2,2 s) ; VAE 8/8 disp 6,0 ; GAN 1,5 ± 0,5 modes ; DDPM 8/8 disp 1,51 ; trajectoire de denoising en 5 instantanés (t = 99 → 0) |
| [3.6b-Modeles-Generatifs-PyTorch](3.6b-Modeles-Generatifs-PyTorch.ipynb) | Versant **framework** du 3.6 : VAE, GAN et DDPM (diffusion) entraînés sur une même cible 2D à 4 modes (mélange de Gaussiennes, PyTorch CPU) puis comparés — ELBO vs adversarial vs débruitage | **Le compromis qualité/diversité** : 4 mécanismes génératifs sur les mêmes métriques (couverture de modes, entropie effective), le GMM empirique en référence « modèle exact » | médiane sur 3 graines (budget de pas commun) : GMM cov 4/4 ESS 3,96 · VAE cov 4/4 ESS 3,95 · GAN cov 3/4 ESS 2,99 (perte de diversité, un mode jamais couvert) · Diff cov 4/4 ESS 1,62 (couvre mais sous-échantillonne le mode le plus faible) — verdict nuancé, pas de « gagnant » unique |
| [3.7-Distillation-Maitre-Eleve](3.7-Distillation-Maitre-Eleve.ipynb) | Distillation teacher/student : un maître entraîné distille son savoir (dark knowledge) vers un élève ~9× plus petit | **Le facteur T² vérifié** : la KL brute chute en ~1/T², la KL scalée reste constante ; verdict INCONCLUSIVE au seuil strict — gain par exemple net (DM p < 0.001, CE 0.63 → 0.58) mais edge 0.6σ/1.4σ sous 5 folds × 4 graines | maître 0.8906 / distillé 0.8145 vs baseline 0.8029 ; ECE 0.0458 vs 0.0684 ; ratio params 8.9× ; 5 folds × 4 graines (20 paires), entrainement deterministe |
| [3.8-Representations-Contrastives](3.8-Representations-Contrastives.ipynb) | Pré-entraînement contrastif moderne sur vues continues : augmentations contrôlées du sac-de-mots (mask/swap/identité), encodeur MLP et loss InfoNCE écrits from scratch sans autograd, pont explicite vers le skip-gram (cooccurrence discrète vs vue continue) | **Apprendre des représentations sans étiquettes** : deux vues d'une même phrase attirent leurs embeddings, les autres phrases les repoussent | sonde linéaire 0,432 (chance 1/7 = 0,143 ; aléatoire gelé 0,161 ; skip-gram BoW 0,154 ; supervisé from scratch 0,368) ; contre-témoin de collapse mesuré (verdict NON) ; ablations température × augmentations × graines avec écart-type inter-graines ; 3 exercices |
| [3.9a-Compression-Quantization-INT8](3.9a-Compression-Quantization-INT8.ipynb) | La quantification INT8 construite à la main (mapping affine, fake-quant per-tensor/per-channel, activations dynamiques par hooks, calibrations statiques min/max et KL — port fidèle TensorRT) sur ResNet-20/CIFAR-10 entraîné dans le notebook, puis la falaise INT4 | **Le déjeuner gratuit et sa limite** : INT8 égale le FP32 à ±0,001 près pour 4× moins de mémoire ; la discrimination vit dans l'erreur de poids et la falaise INT4 | FP32 0,9019 ; w8 per-tensor 0,9024 / per-channel 0,9020 (erreur s3.1.conv1 : 1,05e-2 vs 7,72e-3) ; dynamique w-channel 0,9018 ; statique min/max 0,9017 ; statique KL 0,9012 (seuils 60-100 % du range, masse coupée ≤ 0,005 %) ; INT4 0,8778 (−2,4 pts, erreur ×18) ; 270 906 poids : 1,08 Mo → 0,27 Mo (4,0×) |


## Feuille de route

Les deux chantiers annoncés par cette feuille de route sont livrés : théorie de l'information
appliquée — entropie, KL, cross-entropy (#12420, livrée par #12640 → notebook
[3.0](3.0-Theorie-Information.ipynb)) ; régularisation — dropout, weight decay, early stopping
(#12409, livrée par #12527 → notebook [3.3](3.3-Regularisation.ipynb)). Le fil directeur n'a
pas changé et vaut pour la suite : chaque mécanisme écrit à la main, vérifié contre torch,
puis consommé via l'API officielle.

## Prérequis

- [02-ML-Cours](../02-ML-Cours/README.md) en entier — en particulier [2.2 (descente de
  gradient)](../02-ML-Cours/2.2-Descente-de-gradient.ipynb), [2.8 (théorie PAC, la borne que
  ce notebook confronte)](../02-ML-Cours/2.8-Theorie-PAC.ipynb) et
  [2.9 (le grokking boîte noire que le 3.5 rouvre à la main)](../02-ML-Cours/2.9-Grokking-Generalisation.ipynb)
- NumPy niveau [1.2](../01-PythonForDataScience/notebooks/1.2-Manipulation_de_Donnees_avec_NumPy.ipynb)
  (produits matriciels, broadcast)

## Environnement

```bash
pip install numpy matplotlib
# notebooks 3.7 et 3.9a (torch + torchvision, kernel coursia-ml-training pour 3.7) :
pip install torch torchvision
```

Tous les notebooks tournent sur CPU en moins de dix minutes — exception [3.9a](3.9a-Compression-Quantization-INT8.ipynb) : l'entraînement complet de ResNet-20 sur CIFAR-10 (~8 min sur RTX 3090) exige un GPU ; sur CPU le notebook bascule sur une recette réduite de 6 époques.
