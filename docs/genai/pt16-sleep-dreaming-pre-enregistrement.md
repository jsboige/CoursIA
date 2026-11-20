# Pré-enregistrement — Sleep et Dreaming : ce qui change dans un petit modèle quand les mémoires se consolident (PT-16)

> **Statut.** Scellage v1 **avant l'écriture du module exécutant** (recette scellée du dépôt). Ce document ne rapporte aucun résultat. Les **bandes numériques** des gates G1–G4 seront posées par **re-verrouillage v2** après un pilote exploratoire limité à la graine 1000 (disjointe des graines d'étude) et **avant toute évaluation des gates** — précédent : [threshold-alignment-pre-enregistrement.md](../ict/threshold-alignment-pre-enregistrement.md). Le v1 verrouille : le sujet, la lentille, les stades, les contrôles, la forme directionnelle des prédictions et les sondes. Aucun recalibrage après l'évaluation held-out.
>
> **Objet formel.** Un modèle de langage de 1,7 milliard de paramètres apprend un petit corpus de faits fictifs (phase wake), puis subit deux phases « sommeil » adaptées à échelle fixe — consolidation par replay (NREM) et dreaming par curriculum auto-généré (REM) — pendant qu'un SAE officiel, **fixe et apparié par repo-id**, sert de microscope sur un jeu held-out constant. La question : quelles quantités mesurables du dictionnaire SAE changent entre les stades, et l'ordre consolidation→dreaming (contre ses contrôles randomisés) fait-il une différence que l'on peut voir de l'intérieur et perturber causalement ?
>
> **Portée pédagogique.** Issue #27376, volet A. Complément user 2026-11-19 13:53Z : petits modèles ; jamais supposer un SAE transférable d'un autre modèle/couche ; vérifier les APIs exactes avant de sélectionner ; captures sur held-out aux 4 stades ; interventions causales avec témoins négatifs ; comparabilité des sondes à travers les changements de poids ; « voir de l'intérieur ce qui change et mettre les hypothèses en défaut ».

## Source primaire

Ali Behrouz, Farnoosh Hashemi, Adel Javanmard, Vahab Mirrokni, « Language Models Need Sleep: Learning to Self-Modify and Consolidate Memories », arXiv:2606.03979v2 (10 juillet 2026). **Lecture firsthand depuis la copie archivée** (`G:\Mon Drive\MyIA\IA\Bibliographie IA\MachineLearning\Transformers and Large Language Models\2026 - Behrouz et al - Language Models Need Sleep - 2606.03979.pdf`, 26 pages, archivée 2026-11-19). Claims mobilisés : (1) un apprenant continual n'a pas de temps d'entraînement/test mais deux états — **wake** (reçoit des données, les traite) et **sleep** (reçoit peu ou pas de données, traite les connaissances existantes) ; (2) la consolidation offline humaine (NREM) transforme des mémoires fragiles récentes en connaissances stables par un dialogue hippocampe→néocortex **perte-par-perte**, sans rejeu brut — elle ré-architecte ; (3) le dreaming (REM) renforce sélectivement les synapses nouvelles et intègre l'information neuve aux réseaux sémantiques préexistants ; (4) leur opérationnalisation : consolidation = Knowledge Seeding (distillation **ascendante** vers un réseau plus grand), dreaming = curriculum synthétique généré par RL. **Écarts déclarés** : nous restons à échelle et capacité **fixes** (pas de distillation ascendante — la consolidation est un replay within-model) et le dreaming est un rehearsal sur curriculum auto-généré **sans RL** (échantillonnage + filtrage par exactitude). Ces écarts sont des adaptations à l'échelle pédagogique, pas des reproductions partielles déguisées.

## Claim, contre-claim et périmètre

- **Hypothèse H1 (consolidation stabilise).** Après consolidation par replay, les features SAE portant les faits appris sont **plus stables** (split-half, voisinage) et **plus fidèles** (reconstruction locale) qu'après la seule acquisition rapide — à budget d'optimisation égal.
- **Hypothèse H2 (l'ordre compte).** La séquence consolidation→dreaming diffère mesurablement (au sens des sondes P1–P5 ci-dessous) du dreaming direct sans consolidation (bras C-nc) et du wake prolongé à budget égal (bras C-wake).
- **Hypothèse H3 (causalité lisible).** Le clamp des features identifiées comme porteuses des faits (par le stade le plus consolidé) dégrade le rappel des faits **plus** qu'un clamp témoin de features aléatoires appariées en activité (panel du harnais, `--matched-panel`) — l'effet est directionnel et spécifique.
- **Contre-claim adversarial.** Tout changement observé entre stades est un artefact du déplacement des poids sous un SAE **fixe** (le microscope se désaligne à mesure que le modèle bouge), pas une propriété de la consolidation. Le banc doit la mettre en défaut par des sondes qui ne dépendent pas de l'alignement SAE seul (P4 : rétention comportementale des faits ; mesure de dérive de reconstruction sur corpus **neutre** — des faits jamais appris).
- **Non-claim.** Ni une reproduction du paradigme Sleep complet (pas de croissance de réseau, pas de RL), ni une claim neurophysiologique sur le sommeil humain, ni une claim de transférabilité du SAE (le SAE reste sur **son** modèle de base — appariement par repo-id, cf. « Sujet et lentille »). Échelle pédagogique : les effets mesurés caractérisent ce couple modèle×corpus, pas « les LLM ».

## Sujet et lentille (verrouillés v1)

| Élément | Valeur scellée | Preuve (mesurée, tranche 2a c.7011507423) |
|---|---|---|
| Modèle | `Qwen/Qwen3-1.7B-Base`, sha `ea980cb0` | config mesurée : d_model 2048, 28 couches, bf16, 1 720 574 976 paramètres |
| SAE | `Qwen/SAE-Res-Qwen3-1.7B-Base-W32K-L0_50`, sha `ce1a79d9` | config mesurée : topk_sae, d_sae 32 768, k=50, layers 0–27, `resid_post`, float32 |
| Appariement | **par repo-id exact** — la garde `check_sae_model_match` est dimensionnelle (le SAE du 2B, d_model 2048 aussi, passerait) : le scellé interdit tout SAE autre que celui ci-dessus sur ce modèle | angle mort mesuré tranche 2a |
| Encodage | convention app.py officielle via le harnais : `pre = h @ W_enc.T + b_enc ; relu ; top-k(50)`, sans soustraction b_dec ni normalisation du hidden | `scripts/extract_sae_traces.py:574-604` |
| Profondeurs de capture | `--layer-frac 0.5` (couche 14) **principale** ; `--layer-frac 0.25` (couche 7) **robustesse** | `resolve_capture_layer(28, frac)` — couches distinctes, jamais `--layer` brut |
| Régime de précision | dissocié : QLoRA (base gelée 4-bit + adapters bf16) pour **toutes** les boucles d'entraînement ; rechargement **bf16 base+adapters fusionnés** pour **chaque** capture SAE — garde `assert_bf16_readout` | garde-fou n°3 du harnais |
| Variantes de trace | chaque capture existe en `trained` et `control` (SAE non entraîné / permutation seedée, convention harnais) | série ict21 existante |

## Corpus de faits et stades (verrouillés v1)

**Corpus.** 60 faits fictifs « sujet → attribut » (noms inventés, jamais vus en pré-entraînement — vérification par probabilité de base du modèle au stade S0, à documenter au pilote) : 40 train, 20 held-out (jamais entraînés, jamais rejoués). Held-out de capture : prompts fixes, ordre fixe, graines d'étude 0/1/7/42/99.

**Stades** — chaque capture SAE (held-out, bf16, deux profondeurs, trained+control) a lieu **après** la phase correspondante :

| Stade | Phase | Contenu | Budget |
|---|---|---|---|
| S0 | initial | modèle base, rien appris | — |
| S1 | wake (acquisition rapide) | fine-tuning QLoRA sur les 40 faits train, format question→réponse | B pas d'optimisation (verrouillé au pilote) |
| S2 | sleep-NREM (consolidation) | replay : ré-entraînement sur les **mêmes** 40 faits mélangés à un corpus neutre de régularisation (texte générique sans lien aux faits), **aucune donnée nouvelle** | B |
| S3 | sleep-REM (dreaming) | curriculum **auto-généré** : le modèle courant génère des paraphrases/rappels des faits train, filtrées par exactitude de réponse (rappel exact de l'attribut), fine-tuning léger dessus | B |

**Bras contrôles randomisés** (mêmes graines, mêmes budgets totaux) :

- **C-nc** (no-consolidation) : S0 → S1 → dreaming **direct** (S3 sans S2) — teste l'ordre.
- **C-wake** (compute-matched) : S0 → S1 → ré-entraînement sur données **neutres seules** à budget 2B — teste que l'effet vient du replay des faits, pas du compute.
- **C-shuffle** (replay négatif) : S0 → S1 → replay sur les 40 faits **d'un autre lot fictif disjoint** (jamais appris) — teste la spécificité du contenu consolidé.

## Sondes (famille PT-15b, sur traces held-out)

- **P1 — Spectre galaxy CSN** (Hill + KS + logLR) par stade, features actives.
- **P2 — Séparabilité split-half** (Fisher diagonal) des features-faits vs features neutres.
- **P3 — Position-tracking** (Spearman) : rang des features porteuses des faits à travers les stades.
- **P4 — Rétention comportementale** : exactitude de rappel des 40 faits train + 20 held-out par stade (probe generation court) — **sonde hors-SAE**, le contre-poison de la contre-claim.
- **P5 — Dérive du microscope** : fidélité de reconstruction + dead features mesurées sur corpus **neutre** (faits jamais appris) à chaque stade — quantifie la désalignement du SAE fixe indépendamment des faits.

## Prédictions falsifiables (direction verrouillée v1 ; bandes au v2 post-pilote)

| Gate | Prédiction (direction) | Échec |
|---|---|---|
| **G1** | stabilité split-half (P2) des features-faits : S2 > S1, et S2 ≥ C-wake au même point de budget | si S2 ≤ S1 |
| **G2** | l'ordre compte : au moins une sonde P1–P5 sépare {S2→S3} de {C-nc} au-delà de la bande v2 | si aucune sonde ne sépare |
| **G3** | spécificité : le replay de faits étrangers (C-shuffle) ne stabilise **pas** les features-faits au-delà de C-wake | si C-shuffle ≈ S2 |
| **G4** | causalité : clamp des top-features-faits dégrade P4 plus que le panel apparié en activité (H3) | si Δclamp-faits ≤ Δclamp-témoin |
| **G5** (validité) | P5 (dérive du microscope sur neutre) reste sous bande v2 — sinon les gates G1–G4 sont **non interprétables** et le verdict le dit | — |

Verdict **tri-état** par gate : CONFIRMÉ / INFIRMÉ / NON-INTERPRÉTABLE (si G5 échoue ou si P4 montre que le modèle n'a pas appris les faits au stade S1 — pilote de faisabilité d'abord).

## Contrôles instrumentaux

- Gardes du harnais systématiques : `resolve_capture_layer` (frac, jamais layer brut), `check_sae_model_match` + vérification repo-id **dans le module**, `assert_bf16_readout`, `trace_filename` (slug d'échelle — noms distincts par stade/bras/graine, aucun écrasement silencieux).
- Graines : étude 0/1/7/42/99 ; pilote v2 sur graine 1000 seule (disjointe).
- GPU : RTX 3070 Ti 8 Gio — 1.7B bf16 ≈ 3,5–4 Gio + SAE float32 par couche (~537 Mo au readout) : tient une fois le GPU libéré ; annonce de run sur le dashboard avant occupation (gouvernance GPU held/released).
- Téléchargements planifiés : modèle ~3,3 Go + 2 couches SAE ~1,1 Go (le harnais télécharge par couche — jamais le dépôt entier de 15 Go).

## Livrables d'exécution (module séparé, APRÈS ce scellage)

1. Notebook exécutant `MyIA.AI.Notebooks/GenAI/PostTraining/PT_16_*.ipynb` (série existante PostTraining, là où vivent PT-15/15b/15c) + traces npz committées (format compact du harnais).
2. Table stades × sondes × graines, verdicts tri-état, **publiés tels quels** (l'étude scellée se publie avec ses résultats quels qu'ils soient — cas 5ter #23570).
3. L'écart SAE-officiel vs `TopKSae` maison (repli 0.8B de la tranche 1) reste **hors périmètre** de ce scellage : il ferait l'objet d'un document séparé si le 1.7B s'avérait infaisable — auquel cas ce scellage est **fermé et documenté** comme chemin mort-né (précédent Čech), pas amendé en silence.

## Suivi

Issue #27376 (volet A). Tranches : inventaire c.7011354853, contrat API c.7011507423, ce scellage. Le pilote v2 (graine 1000, calibrage des bandes) et l'exécution held-out (graines d'étude) sont les tranches suivantes sous claims séparés.
