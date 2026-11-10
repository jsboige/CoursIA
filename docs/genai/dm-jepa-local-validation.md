> REFERENCE — vivante — dernière révision 2026-10-31

# DM-JEPA 1.7 — validation locale du moteur de décision

Issue de grain : #21997. Page sœur pour l'index de modèles de décision : [decision-models-local-verification.md](decision-models-local-verification.md).

Cette page rend compte d'une **mesure locale** du moteur [DangerLabs/dm-jepa-1.7](https://huggingface.co/DangerLabs/dm-jepa-1.7), un moteur de décision non-autorégressif : il lit un état et des questions typées (`choice`) et rend une probabilité par option, sans générer de texte. Elle applique le plan de validation de l'issue #21997 et ne valide **aucun** chiffre de la fiche Hugging Face au-delà de ce qui est mesuré ici.

## Verdict en une phrase

Le scoring **fonctionne et discrimine** — le rang moyen de l'option correcte est de **1,27** à 4 options et **1,72** à 6 options, contre **2,5** et **3,5** pour un tri aléatoire — mais **la latence revendiquée n'est pas reproduite** (56,7 à 89,7 ms mesurés contre 34,3 ms annoncés) et **l'artefact publié ne se charge pas tel quel** depuis le Hub, faute de publier le paquet `dm_bert` que ses propres modules importent.

## 1. Ce qui est mesuré, et ce qui ne l'est pas

**Mesuré**, avec le moteur officiel du dépôt (`dm_jepa_1_7_engine.py`, classe `DMJEPA17Engine`) et ses poids réels :

- le nombre de paramètres chargés et la couverture des clés du fichier `model.safetensors` ;
- la latence médiane et p90, sur CPU et sur GPU, et le pic de mémoire GPU ;
- le rang de l'option correcte sur un jeu de décisions construit ici, confronté à la baseline triviale du tri aléatoire ;
- la stabilité sur cinq familles d'entrées adverses.

**Non mesuré**, et pourquoi : les benchmarks revendiqués par la fiche (GSM8K et consorts) ne sont pas rejoués, car les charges utiles de la suite Decision Index 0.3 (`multimodalart/decision-index-suite-0.3`) ne sont pas publiées — 401 / `RepositoryNotFoundError`, mesure du 2026-10-21 documentée dans la [page sœur](decision-models-local-verification.md) §1. Les scores de la fiche ne sont donc ni confirmés ni infirmés ici : seul ce qui est reproductible localement est mesuré.

## 2. Méthode

### Artefact et environnement

| Élément | Valeur |
|---|---|
| Dépôt | `DangerLabs/dm-jepa-1.7` |
| Révision (snapshot) | `9f2f6f85a2923c0f2307cc966b7ead36723e96dc` (`main` ; le dépôt n'a **aucun tag**) |
| Version de configuration | `1.7` (`config.json:version`) |
| Architecture déclarée | `DMBertJEPA17` |
| Poids servis | `model.safetensors` (1 597,5 Mo) |
| Python / torch | 3.13.3 / 2.8.0+cu126 |
| GPU | NVIDIA GeForce RTX 3090, 24 Gio — **partagée**, 16,7 Gio déjà occupés par une autre charge au moment des mesures |
| Kit requis par l'engine | `apolinario/decision-index` (`decision_index.engines.base`) |

### Jeu de décisions

Soixante problèmes, graine **42**, construits par le harnais (`build_problem`) : cinq ancres (`chien`, `chat`, `oiseau`, `tracteur`, `klaxon`), une option correcte du type « On entend un {ancre} provenant de la cour », trois familles adverses systématiques, et `K-3` distracteurs neutres tirés sans remise dans une liste fixe de sept phrases sans rapport. L'ordre des options est mélangé de façon déterministe.

Les trois familles adverses :

| Famille | Exemple | Ce qu'elle teste |
|---|---|---|
| Négation | « On n'entend aucun {ancre} dans la cour » | La contradiction est-elle pénalisée, ou le mot de l'ancre suffit-il ? |
| Distracteur partageant l'ancre | « Le {ancre} du voisin est visible depuis la fenêtre » | Le modèle apparie-t-il le mot, ou le sens de la phrase ? |
| Neutres | « Le bilan trimestriel est positif », « xyz plt qrs tuv » | Référence de plancher |

**Baseline triviale** : tri aléatoire, rang attendu de l'option correcte `(K+1)/2`, soit 2,5 à 4 options et 3,5 à 6 options. Aucune heuristique plus fine n'est revendiquée : c'est le plancher que toute mesure doit dépasser.

Le harnais est `scripts/genai-stack/dm_jepa_local_check.py` ; il écrit un rapport JSON complet et n'appelle le hub que si aucun snapshot local n'est fourni.

## 3. Résultats mesurés

### 3.1 Rang de l'option correcte

| Mesure | K=4 | K=6 |
|---|---:|---:|
| Rang moyen, option correcte | **1,267** | **1,717** |
| Exactitude (rang 1) | **73,3 %** (44/60) | **33,3 %** (20/60) |
| Probabilité moyenne de l'option correcte | 0,353 | 0,231 |
| Rang aléatoire attendu | 2,5 | 3,5 |
| Rang moyen, **négation** | 2,650 | 3,750 |
| Rang moyen, **distracteur partageant l'ancre** | 3,883 | 5,700 |

Lecture honnête de ces trois lignes :

- l'option correcte est **nettement mieux classée qu'au hasard**, et l'écart se creuse quand le nombre d'options augmente (1,27 contre 2,5 ; 1,72 contre 3,5) ;
- le **distracteur partageant l'ancre tombe en bas du classement** (3,88 sur 4 ; 5,70 sur 6, dernière place dans 43 cas sur 60 à K=6) : le modèle ne se contente donc pas d'apparier le mot de l'ancre, il distingue « on entend X depuis la cour » de « X est visible depuis la fenêtre » ;
- la **négation n'est pas pénalisée** : son rang moyen est celui du hasard (2,65 contre 2,5 ; 3,75 contre 3,5). Autrement dit, « on n'entend aucun chien » n'est pas traité comme contredisant la question plus qu'une phrase neutre. C'est une limite mesurée, pas une inférence : elle interdit de présenter le moteur comme sensible à la polarité d'une phrase.

### 3.2 Robustesse

| Famille adverse | Mesure | K=4 | K=6 |
|---|---|---:|---:|
| Permutation de position (50 appels) | rang moyen de l'option correcte | 1,200 | 1,600 |
| | écart-type | 0,400 | 0,663 |
| | exactitude (rang 1) | 80 % | 50 % |
| | rang par position 0 → K-1 | 1,23 · 1,11 · 1,15 · 1,27 | 1,50 · 1,71 · 1,78 · 1,57 · 1,70 · 1,33 |
| Duplication d'option (10 cas) | écart de probabilité entre les deux jumeaux | **0,0** | **0,0** |
| | rang de la clé dupliquée / rang agrégé du couple | 1,3 / **1** | 2,0 / **1** |
| Lot de deux questions (10 cas) | écart max avec l'appel mono-question | **0,0** | **0,0** |

Trois conséquences pratiques :

1. **Pas de biais de position** : le rang par position ne suit aucune pente (1,11 à 1,27 à K=4), et la permutation laisse le rang moyen à 1,2.
2. **La duplication d'option n'est pas neutre** : les deux clés de texte identique reçoivent exactement la même probabilité (écart 0,0), donc dupliquer une option **double la masse** de ce concept et le fait passer au rang 1. Un appelant ne doit jamais répéter une option dans les `criteria` — ce n'est pas un bug du moteur, c'est un piège d'usage à documenter.
3. **Le lot est sûr** : deux questions dans un même appel rendent exactement les mêmes probabilités que deux appels séparés (écart 0,0), donc le regroupement ne contamine pas les réponses.

### 3.3 Latence et empreinte mémoire

| Mesure | Valeur |
|---|---|
| Latence revendiquée par la fiche | 34,3 ms |
| Latence médiane GPU, K=4 (p90) | **56,7 ms** (75,5) |
| Latence médiane GPU, K=6 (p90) | **68,1 ms** (93,4) |
| Latence GPU observée sur trois blocs consécutifs, K=6 | 84,9 · 73,5 · 80,6 ms (médianes) |
| Latence GPU, même harnais, mesure antérieure K=6 | 89,7 ms |
| Latence médiane CPU, K=6 (p90) | **168,3 ms** (183,1) |
| Pic VRAM GPU, inférence seule | **1,81 Gio** |
| Pic VRAM GPU, chargement des poids compris | **2,79 Gio** sur 24 Gio |
| Paramètres chargés | **349 030 286** |

La latence mesurée se situe entre **56,7 et 89,7 ms**, soit **1,65× à 2,6×** la valeur revendiquée, et **jamais** la valeur revendiquée. La dispersion s'explique par l'état de la carte : la RTX 3090 utilisée est **partagée**, avec 16,7 Gio occupés par une autre charge pendant les mesures. Le chiffre à retenir pour un dimensionnement est donc une fourchette, pas une valeur unique — et la fiche annonce une valeur unique, plus basse que le meilleur cas observé.

## 4. Findings sur l'artefact publié

1. **Non auto-contenu.** L'engine tente `from dm_bert.src.jepa_1_7 import DMBertJEPA17` puis retombe sur `from src.jepa_1_7 import …` (`dm_jepa_1_7_engine.py`, lignes 233-236). Or `src/jepa_1_7.py` importe lui-même le layout privé (`from dm_bert.src.backbone import …`, lignes 19-26), et le paquet `dm_bert` n'est pas publié. Tous les modules requis sont pourtant livrés dans le snapshot sous `src/` : un alias `sys.modules` (`dm_bert.src` → `src/`) suffit, **sans copier de code ni modifier de poids**. C'est ce que fait le harnais ; un appelant qui charge l'artefact naïvement échoue.
2. **Latence revendiquée non reproduite** : 34,3 ms annoncés, 56,7 ms au meilleur cas mesuré (§3.3).
3. **Compte de paramètres divergent** : la docstring de l'engine annonce 320,39 M, la mesure en donne **349,03 M** (+8,9 %). La fiche parle de « 0,3 Md », ce qui reste vrai à l'ordre de grandeur, mais le chiffre précis de la docstring n'est pas celui des poids publiés.
4. **Charges utiles de l'index non publiées** : `multimodalart/decision-index-suite-0.3` renvoie 401 / `RepositoryNotFoundError`, ce qui rend les scores de la fiche non reproductibles par un tiers (détail : [page sœur](decision-models-local-verification.md) §1).

## 5. Reproduire

Prérequis : Python 3.10+, `torch`, `tokenizers`, `safetensors`, `huggingface_hub`, et un clone du kit `apolinario/decision-index`.

```bash
git clone https://github.com/apolinario/decision-index /chemin/vers/decision-index

# 6 options, jeu de 60 problèmes, graine 42
python scripts/genai-stack/dm_jepa_local_check.py \
    --kit-path /chemin/vers/decision-index \
    --revision 9f2f6f85a2923c0f2307cc966b7ead36723e96dc \
    --k-options 6 --n-problems 60 --seed 42 \
    --json scripts/results/dm_jepa_local_k6.json

# 4 options, même jeu
python scripts/genai-stack/dm_jepa_local_check.py \
    --kit-path /chemin/vers/decision-index \
    --revision 9f2f6f85a2923c0f2307cc966b7ead36723e96dc \
    --k-options 4 \
    --json scripts/results/dm_jepa_local_k4.json
```

Un snapshot déjà téléchargé se sert sans réseau avec `--snapshot <chemin>` ; le harnais épingle alors ce répertoire et n'appelle pas le hub. Durée observée : environ une minute sur la configuration du tableau §2, dont deux chargements du modèle (CPU puis GPU).

## 6. Portée

Cette mesure **ne lève pas le HOLD opérationnel** posé par l'issue #21997 : elle établit qu'un scoring déterministe et meilleur qu'un tri aléatoire tourne en local, elle n'établit rien sur les benchmarks revendiqués. L'endpoint dédié et la démonstration pédagogique dans `07-élargissements` restent à arbitrer côté lane `ai-01` (port, service, cohabitation avec la pile vLLM), conformément au cadre d'intégration de l'issue.

Deux points à retenir pour l'usage pédagogique : le moteur **distingue le sens d'une phrase** sur le distracteur partagé, mais **ne traite pas la négation** ; et il ne faut **jamais dupliquer une option** dans les `criteria`.
