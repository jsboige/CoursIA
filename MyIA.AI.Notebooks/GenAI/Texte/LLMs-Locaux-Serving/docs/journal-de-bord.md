# Journal de bord — un fork vLLM en production

[← LLMs Locaux en Production](../README.md)

> Quatorze mois (mai 2025 → juin 2026), 110 commits, un serveur d'inférence qui a hébergé une demi-douzaine de modèles successifs sur 3 cartes RTX 4090. Voici son histoire — racontée par l'agent qui en a la responsabilité, en croisant l'archéologie git, les benchmarks, et les configurations qu'il a fallu jeter.

L'idée directrice : **un endpoint LLM de production auto-hébergé est un arbitrage permanent entre quatre grandeurs en tension — débit, longueur de contexte, qualité, et VRAM.** On ne maximise jamais les quatre à la fois. Tout le métier consiste à choisir, mesurer, et documenter le compromis.

---

## 1. Le décor

Le matériel tient en une ligne : **3× RTX 4090, soit 72 Go de VRAM** (3 × 24 Go). Pas de A100, pas de H100 — du grand public Ada Lovelace (architecture `SM89`). Cette contrainte façonne *toutes* les décisions qui suivent : un modèle de 46 Go ne rentre pas dans 48 Go de VRAM utile, les noyaux FP4 Blackwell n'existent pas sur cette génération, et certaines optimisations « évidentes » du datacenter ne s'appliquent simplement pas.

L'objectif : exposer des **endpoints compatibles OpenAI** auto-hébergés, accessibles via un reverse proxy interne. Un endpoint OpenAI-compatible sert le modèle principal — le même que les notebooks Texte utilisent pour démontrer un LLM local, et que l'on branche dans un assistant de code via `ANTHROPIC_BASE_URL`.

Les GPU ne sont pas équivalents : deux d'entre eux sont sur le bus PCIe rapide (ils portent le modèle principal en *tensor parallelism*), tandis que le troisième a longtemps porté un second modèle, avant d'être **entièrement libéré** (mai 2026) pour les entraînements du cours. Cette réallocation est elle-même un personnage de l'histoire.

**Leçon 1 — Le matériel n'est pas un détail.** Sur du grand public, la VRAM est la ressource rare et la génération de la carte (Ada vs Blackwell) décide de ce qui est *possible*, pas seulement de ce qui est *rapide*.

---

## 2. Origines, et un incident

Le fork démarre en **mai 2025** sur une base vLLM amont. Les premiers mois sont une succession de « missions » de mise en place : intégration de Qwen3, recherche sur les modèles de vision, réorganisation de la structure du projet.

Puis, **septembre 2025, un incident de sécurité.** L'historique git porte la cicatrice : un commit *« Post-APT consolidation — Complete security recovery and architecture cleanup »*. Une intrusion (APT, *advanced persistent threat*) a forcé une récupération complète — nettoyage, rotation des secrets, durcissement. Ce n'est pas une anecdote : un serveur d'inférence exposé sur Internet est une cible, et la sécurité (authentification par clé API par service, secrets jamais commités, reverse proxy) fait partie intégrante de « servir un modèle en production ».

La même période voit le premier vrai gain de performance : une **recherche en grille** (*grid search*) sur les paramètres de configuration aboutit à un réglage qui multiplie par **3,22 la taille du cache KV**. C'est la première fois que le projet mesure systématiquement au lieu de deviner — un réflexe qui ne le quittera plus.

**Leçon 2 — Sécurité et mesure d'abord.** Avant d'optimiser le débit, il faut un serveur qu'on ne se fait pas voler, et un protocole de mesure reproductible. Tout le reste s'appuie dessus.

---

## 3. La valse des modèles

C'est le cœur de l'histoire, et sa partie la plus humaine : le projet a essayé *beaucoup* de modèles, et en a rejeté beaucoup. Chaque essai répond à la même question — « ce modèle tient-il dans 48 Go de VRAM utile en gardant un débit, un contexte et une qualité utilisables ? »

**Qwen3-Coder-Next (février 2026)** — le premier candidat sérieux, et un échec instructif. Le modèle fait 46 Go : trop gros pour le *tensor parallelism* sur deux cartes (il déborde de 48 Go). Le découpage sur trois cartes est mathématiquement impossible (une dimension interne de 8192 n'est pas divisible par 3). Reste le *pipeline parallelism* sur trois cartes — qui fonctionne, mais souffre de **bulles de pipeline** : environ deux tiers du temps GPU est inactif, plombant le débit à **5-6 tokens/s**. Inutilisable. Rejeté.

**GLM-4.7-Flash (février 2026)** — le remplaçant qui débloque tout. 31 milliards de paramètres en mélange d'experts (MoE), 3 milliards actifs par token, attention MLA. Le débit décolle : **56 tokens/s** en décodage, un **gain de 3,3×** sur la configuration précédente. Pas de vision, mais un vrai pas en avant. Il faudra un conteneur Docker sur mesure (bibliothèque `transformers` plus récente) — détail qui reviendra souvent : les modèles récents ont besoin de bibliothèques plus récentes que celles embarquées dans l'image officielle.

**Qwen3.5-35B-A3B (février 2026)** puis **Qwen3.6-35B-A3B (avril 2026)** — la lignée qui s'installe durablement. Architecture MoE *hybride* : 35 milliards de paramètres mais seulement **3 milliards actifs par token** (256 experts, 9 actifs), et surtout une attention hybride mêlant des couches *GatedDeltaNet* (état linéaire, peu de cache) et des couches d'attention classique. Vision native, mode « raisonnement » (`<think>...</think>`), et avec la version 3.6, la préservation du raisonnement entre les tours de conversation. Les chiffres parlent : **107 tokens/s** en décodage, **369 tokens/s** en charge concurrente, appel d'outil en moins d'une demi-seconde.

En parallèle, sur le GPU dédié à la vision : **ZwZ-8B** (février 2026), puis **OmniCoder-9B** (mars 2026) — un modèle spécialisé pour le codage agentique, OCR à 97,5 %. Jusqu'à ce que ce GPU soit libéré pour les entraînements du cours.

**Le cimetière des rejetés** mérite son paragraphe, car c'est là que la connaissance s'accumule :

| Modèle / format | Pourquoi rejeté |
|-----------------|-----------------|
| Qwen3.5-27B *dense* | Trop lent (33-43 tokens/s : 27 milliards de paramètres *tous* actifs) |
| GPTQ-Int4 | Autotuning des noyaux triton manquant pour RTX 4090 : −98,5 % en charge concurrente |
| BitsAndBytes NF4 | Incompatible avec les noyaux Marlin MoE de vLLM |
| Distillé « Opus » v2 | Appel d'outil cassé, −53 % en concurrent |
| NVFP4 | Nécessite les tensor cores Blackwell ; sur Ada, le format est *déquantifié* → aucun gain |

**Leçon 3 — Rejeter, c'est apprendre.** Chaque modèle écarté a documenté une limite réelle (VRAM, divisibilité du découpage, noyaux manquants, génération de GPU). Ce journal des échecs évite de refaire dix fois la même expérience — il vaut autant que la documentation de la configuration gagnante.

---

## 4. Les batailles d'ingénierie

Au-delà du *quel modèle*, il y a le *comment le servir*. Quatre fronts reviennent à chaque déploiement.

**La quantification.** Les poids tournent en **AWQ 4-bit** avec les noyaux Marlin MoE — c'est ce qui fait rentrer un modèle de 35 milliards de paramètres dans 48 Go de VRAM utile. Mais quantifier le *cache KV* est une décision distincte : en FP8, on double la capacité du cache au prix d'environ 15 % de débit ; on y reviendra avec TurboQuant.

**Les graphes CUDA.** Verdict tranché et définitif : **ne jamais utiliser le mode `enforce-eager`** — c'est 3 à 4× plus lent sur toutes les métriques (12 tokens/s au lieu de 45). Les *piecewise CUDA graphs* à un taux d'occupation mémoire de 0,85 sont le bon réglage. Ce 0,85 (et non 0,92) n'est pas arbitraire : les noyaux Marlin MoE réclament de 850 Mo à 1 Go d'allocations temporaires variables, et viser plus haut provoque des saturations mémoire (bug suivi en amont, RFC vLLM [#27951](https://github.com/vllm-project/vllm/issues/27951)).

**L'échantillonnage (*sampling*).** Découverte contre-intuitive de mars 2026 : une pénalité de présence (`presence_penalty`) de 1,5 réduit la répétition d'un facteur **2 à 3**, *sans aucun impact sur le débit*. Huit profils ont été calibrés spécifiquement pour la quantification AWQ 4-bit, en ajustant les recommandations officielles (qui visent le format BF16) sur la base de benchmarks locaux.

**La stabilité.** Un serveur qui décode vite mais tombe toutes les six heures ne sert à rien. Une longue traque (avril 2026) a remonté une corruption de descripteur Python (`PyCFunction` sans le flag attendu) dans la couche de diffusion en mémoire partagée, sous charge — d'abord contournée par un changement de backend, puis corrigée par un **patch maison**, remonté en amont via les issues du projet. Un *watchdog* en side-car (double-ping, redémarrage automatique) garde le filet.

**Leçon 4 — Le débit n'est qu'une des quatre grandeurs.** Quantification, graphes CUDA, échantillonnage, stabilité : chacun est un curseur, et les régler suppose de *mesurer* l'effet réel sur le matériel réel, pas de copier une recette de datacenter.

---

## 5. La saga TurboQuant → Genesis

C'est l'arc le plus dramatique, et le plus représentatif du métier.

**Le constat (mai 2026).** Le workload réel n'est pas « un utilisateur qui décode vite » mais « beaucoup d'utilisateurs, en contexte long » — la classe, plus l'orchestrateur multi-agents, plus le routage des assistants de code. Pour ce profil, le goulot d'étranglement n'est pas le débit en mono-utilisateur : c'est la **capacité du cache KV**. Le bon levier est donc **TurboQuant k8v4**, une quantification du cache qui multiplie sa capacité par plus de six (le cache passe d'environ 322 000 à près de 2 millions de tokens). Sauf que ça ne marche pas du premier coup.

**La voie amont, bloquée.** Une *pull request* amont (mai 2026) débloque TurboQuant pour les modèles hybrides — mais expose un crash sur la première continuation de *chunked-prefill* ([vllm#41726](https://github.com/vllm-project/vllm/issues/41726)). Le correctif candidat reste **ouvert et bloqué**, sans date. Impasse.

**La voie aval, actionnable.** Un mainteneur tiers, **Sandermage**, publie un arbre de patches downstream : [`Sandermage/genesis-vllm-patches`](https://github.com/Sandermage/genesis-vllm-patches) (*Genesis*, v7.72.x), qui cible explicitement notre modèle hybride + TurboQuant k8v4 + un contexte de 256 K. Ses patches **P22 et P38** corrigent exactement notre crash — confirmé publiquement par un autre utilisateur (`xyehya`) dans la même issue. *Quand l'amont est bloqué, un arbre de patches downstream crédité peut être la seule voie praticable.*

**La nuit de la promotion.** Construire l'image Genesis et la valider a pris une nuit d'itérations serrées : une version validait toutes les charges actives… puis **régressait au repos** (un *deadlock* réapparaissait après 55 minutes d'inactivité). Retour automatique à la baseline, conformément à la règle « un soak au repos qui régresse annule la promotion ». La version suivante ajoutait une variable d'environnement désactivant un échantillonneur dont le chemin d'autotuning corrompait un verrou Python sous charge. Cette version a tenu **35 heures de soak propre** → promue baseline de production.

**Le résultat.** Cache KV multiplié par 6,3 (près de 2 millions de tokens), contexte de 262 K préservé, et surtout **environ 829 tokens/s agrégés à 16 utilisateurs concurrents** (la baseline précédente saturait vers 5). Exactement le levier qu'il fallait pour un workload multi-utilisateurs.

**Leçon 5 — Connaître son workload décide du levier.** TurboQuant (capacité du cache) battait les alternatives de décodage spéculatif (vitesse en mono-utilisateur) *pour nous*, parce que notre charge est multi-utilisateurs en contexte long. Le même arbitrage, sur un workload mono-utilisateur, aurait donné la réponse inverse.

---

## 6. Les impasses documentées

Toutes les pistes n'aboutissent pas, et les noter proprement est un livrable à part entière.

**Le décodage spéculatif — quatre tentatives, quatre crashes.** Deux approches (DFlash puis MTP), sur le modèle quantifié AWQ : deux bugs distincts traçables en amont. Deux *datapoints* ont été remontés sur les issues du projet. Conclusion : **rester sur la baseline** — 829 tokens/s agrégés suffisent largement pour notre charge. Les configurations sont conservées sur disque, en documentation, pour re-test quand les correctifs amont atterriront.

**Le plafond de batch.** Le *batch* d'exécution est plafonné à 4096 tokens. Une tentative de le passer à 8192 (juin 2026) a **planté la production** environ 1h25 après déploiement : un buffer pré-alloué (couche GatedDeltaNet) était dimensionné à 4096, et un *forward* combiné de 5536 tokens l'a fait déborder. Diagnostic initial : « c'était le cap de profilage » — **faux**, et confirmé faux par l'auteur des patches lui-même : le vrai coupable était un *autre* buffer, dont le résolveur de budget retombait silencieusement sur sa valeur par défaut. Un correctif candidat (une variable d'environnement qui dimensionne le buffer sur le batch demandé) est identifié, mais reste **non validé en production** : le test qui forcerait un *forward* combiné dans l'intervalle critique n'a jamais été lancé. Tant qu'il ne l'est pas, **4096 reste le plafond effectif**.

**Leçon 6 — `vérifié` n'est pas `supposé`.** Dans l'épisode du plafond de batch, l'arithmétique du crash était juste, mais l'*attribution causale* était fausse jusqu'à ce qu'on inspecte le conteneur en détail. La discipline « ne pas propager une affirmation sans un test qui la force » s'est imposée comme règle, après s'être trompé plus d'une fois. C'est peut-être la leçon la plus transférable de tout ce journal.

---

## 7. Ce que ça enseigne

Si l'on ne devait retenir que quelques idées de ce journal :

1. **Quatre grandeurs en tension.** Débit, contexte, qualité, VRAM. On choisit, on ne maximise pas tout. Le bon choix dépend du *workload réel*, pas d'un benchmark abstrait.
2. **Le matériel décide du possible.** Sur du grand public Ada, la VRAM et la génération de GPU ferment des portes (FP4, gros modèles, découpage non divisible) avant même la question de la vitesse.
3. **Mesurer, toujours.** Grid search, benchmarks de répétition, soaks de 35 heures : chaque décision majeure s'appuie sur un chiffre reproductible, pas sur une intuition.
4. **Documenter les échecs.** Le cimetière des modèles rejetés et les impasses de décodage spéculatif valent autant que la configuration gagnante — ils empêchent de refaire les mêmes expériences.
5. **Amont *et* aval.** Contribuer les bugs en amont (issues, *pull requests*) *et* adopter un arbre de patches downstream crédité quand l'amont est bloqué : les deux, pas l'un ou l'autre.
6. **`vérifié` ≠ `supposé`.** Avant de déclarer une cause, un test qui la force. Avant de propager un fait, une vérification.

Le serveur qui tourne aujourd'hui — modèle MoE Qwen3.6-35B-A3B, cache TurboQuant patché Genesis, près de 2 millions de tokens de contexte, fenêtre de 262 K, vision et raisonnement — n'est pas un point d'arrivée. C'est l'état courant d'un arbitrage qui a déjà changé dix fois et changera encore. C'est ça, servir un LLM en production : non pas trouver *la* configuration, mais entretenir un compromis vivant, mesuré, et honnêtement documenté.

---

*Sources : archéologie git du fork (110 commits, mai 2025 → juin 2026), documentation interne de déploiement. Patches Genesis : [Sandermage/genesis-vllm-patches](https://github.com/Sandermage/genesis-vllm-patches) (auteur Sandermage, v7.72.x, mai 2026). Issues amont vLLM citées : [#27951](https://github.com/vllm-project/vllm/issues/27951), [#41726](https://github.com/vllm-project/vllm/issues/41726). Aucun secret, clé, ni coordonnée interne joignable n'apparaît dans ce document.*
