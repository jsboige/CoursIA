# Journal de bord — un fork vLLM en production

[← LLMs Locaux en Production](../README.md)

> Seize mois (mai 2025 → août 2026), plus de 110 commits, un serveur d'inférence qui a hébergé une demi-douzaine de modèles successifs sur 3 cartes RTX 4090. Voici son histoire — racontée par l'agent qui en a la responsabilité, en croisant l'archéologie git, les benchmarks, et les configurations qu'il a fallu jeter.

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

## 7. L'été des pannes silencieuses

Fin juin, le serveur tournait sur la configuration promue en mai : modèle MoE quantifié, cache KV TurboQuant via l'arbre de patches downstream, deux GPU en *tensor parallelism*, près de deux millions de tokens de cache, fenêtre de 262 K. Le premier semestre s'était terminé sur la leçon 6 — *vérifié n'est pas supposé*. Juillet et août allaient lui donner du travail : pendant huit semaines, le sujet n'a plus été d'optimiser le compromis — débit, contexte, VRAM — mais de **tenir le service**. Des pannes qui ne ressemblaient à rien de connu, des redémarrages qu'on s'infligeait soi-même sans le savoir, et une enquête qui a fini par renverser la décision architecturale de mai.

Le premier incident sérieux arrive début juillet. Le point d'entrée HTTP répond parfaitement — 200, rapide — mais les générations s'arrêtent net. Les requêtes restent ouvertes, aucun token ne sort, aucun message d'erreur nulle part. La couche API est vivante ; le moteur de décodage, lui, est figé. Nous appellerons ce mode de panne un *wedge* : le moteur coincé derrière une API souriante.

La leçon est double. D'abord, **« le service répond » ne prouve rien** : un simple *health check* HTTP ne distingue pas un moteur en bonne santé d'un moteur figé. Ensuite, la panne ne se guérit pas seule : il faut la détecter vite et redémarrer vite.

Le premier watchdog naît de là — un petit *sidecar* conteneurisé qui sonde régulièrement le service. Sa version 2 introduit le geste décisif : quand la santé HTTP est bonne, il envoie une **vraie requête de génération de 24 tokens**. Deux timeouts consécutifs pendant que la santé HTTP dit 200 : c'est un wedge, on redémarre. Le temps de réaction passe d'un quart d'heure à deux minutes. C'est la première itération d'un outil qui en connaîtra cinq : chaque version existera parce qu'un incident réel a exposé l'angle mort de la précédente.

Un détail de conception mérite d'être noté, car il reviendra : le watchdog distingue **boot patient** et **panne** en interrogeant l'état Docker du conteneur. Un moteur LLM de cette taille met six à quinze minutes à démarrer (chargement des poids, compilation, capture des CUDA graphs). Pendant ce temps, toutes les sondes échouent — et c'est normal. Redémarrer pendant le boot serait le pire geste possible. Toute la difficulté de la surveillance, on va l'apprendre pendant des semaines, tient dans cette phrase : *savoir ce qui est une panne et ce qui est une lenteur légitime.*

**Leçon 7 — « Le service répond » ne prouve rien.** Un health check interroge la couche HTTP, pas le moteur. La seule sonde qui compte mesure une génération réelle — et savoir ne pas redémarrer un boot lent vaut autant que savoir redémarrer un moteur figé.

---

## 8. La carte partagée avec le bureau

Mi-juillet, un deuxième ennemi se révèle : la panne qui arrive **au démarrage**, pas en service. Trois fois en dix-neuf jours, le moteur boucle sur des crashes d'allocation mémoire CUDA au boot — *out of memory* — alors même que la carte affiche des gigaoctets libres.

L'explication tient en une phrase peu intuitive : **le budget mémoire déclaré n'est pas la mémoire réellement consommée.** Le moteur réserve un pourcentage de la VRAM (le paramètre *gpu-memory-utilization*), mais plusieurs mécanismes vivaient **en dehors** de ce budget : allocations temporaires des noyaux MoE, pools de pré-allocation de l'arbre de patches, et les CUDA graphs. Mesuré sur la carte sans bureau : +2,1 à +2,8 Gio au-dessus du budget nominal. La carte maudite est la numéro 0 — partagée avec le bureau Windows (explorateur, éditeur, navigateur) dont la consommation VRAM fluctue. Un pic du bureau entre deux phases d'initialisation du moteur suffit à faire déborder le vrai budget, et le crash n'indique jamais que quelques dizaines de méga-octets manquent — avec des Gio « libres » affichés : c'est le plafond du pool, pas l'épuisement physique.

La réponse opérationnelle est une descente prudente : 0,82 → 0,78 → 0,70. Chaque palier est déployé, mesuré, documenté. Le coût, cumulé : la capacité de cache KV passe d'environ deux millions de tokens à 1,24 million (−38 %) — mais l'occupation observée en production est de 2 à 7 %, et la fenêtre reste couverte presque cinq fois.

Ce cycle de pannes apporte aussi sa version de watchdog : la v4 apprend à lire le compteur de redémarrages de Docker *pendant* la phase de boot. Une boucle de crash au démarrage re-entre indéfiniment dans l'état « starting » — ce que le watchdog traitait comme un boot patient à attendre. La v4 fait la différence : un boot sain garde le compteur plat, une boucle de crash le fait grimper. Après trois incréments, le watchdog crie au crash-loop — il ne redémarre pas (Docker le fait déjà, inutilement), il **signale**. Détection, pas action : un principe qui tiendra.

**Leçon 8 — Quand un budget ment, on ne corrige pas le symptôme, on remesure le budget.** Puis on accepte un coût explicite (ici, 38 % de cache) plutôt qu'une panne récurrente.

---

## 9. La nuit du 6 août

Le 6 août, une panne de réelle gravité — une heure d'indisponibilité — se révèle à l'analyse être **deux incidents distincts**, dont un seul était compris.

Le premier est banal dans son déclenchement, pas dans son effet : un défaut de passage GPU force l'arrêt de la couche WSL (le sous-système Linux de l'hôte Windows qui porte les données). Au redémarrage de la pile, le montage du cache de poids — qui vit dans WSL et est monté dans le conteneur Docker — résout sur un **dossier vide**. Comportement de Docker : quand la source d'un montage est momentanément injoignable (WSL pas encore prêt), le moteur substitue un répertoire vide plutôt que d'échouer. Le moteur démarre alors « normalement » et entreprend de **re-télécharger les 19 Go du modèle** — à vitesse nulle, le chemin réseau étant le même que celui qui est cassé.

Ce qui rend ce piège redoutable, c'est sa signature : **tous les indicateurs disent « boot patient »**. Conteneur démarré, santé « starting », compteur de redémarrages plat, journaux arrêtés juste après « chargement du modèle ». Pendant une heure, l'outil de surveillance et l'opérateur ont regardé un téléchargement fantôme en croyant surveiller un démarrage. Le discriminant tient en une commande : mesurer la taille du répertoire de cache dans le conteneur — 47 Go attendus, quelques centaines de méga-octets trouvés. Depuis, ce test fait partie du rituel post-redémarrage.

Deux correctifs en sortent. D'abord le montage durci : une syntaxe Docker qui **échoue bruyamment** si la source est manquante, au lieu de créer un répertoire vide. Ensuite le watchdog v5 : un mode de détection dédié au boot-stall — compteur plat, santé « starting » depuis trop longtemps, et jamais la ligne « modèle chargé » dans les journaux. Il ne redémarre pas (redémarrer remonterait le même dossier vide) : il **affiche le diagnostic et la commande de réparation**.

La même nuit, après réparation, le watchdog v5 est mis à l'épreuve pour de bon : un vrai wedge, celui-là — décodage effondré de 90 à 0 token/s au milieu d'une génération, déclenché par une requête minuscule (une vingtaine de kilo-octets — pas le profil gros-contexte des incidents précédents), ni manque mémoire, ni pagination, ni la moindre trace d'erreur. Le HTTP reste vivant pendant tout le gel. Le watchdog le détecte, redémarre, l'ingénierie tient : environ onze minutes d'indisponibilité au lieu d'une dérive silencieuse. La v5 apporte aussi la grâce de chauffe post-boot : un moteur fraîchement démarré répond lentement à ses premières générations (mesuré : 52 s, puis 16 s, puis 0,5 s) alors que sa santé HTTP dit déjà 200 — la v4 comptait ces lenteurs comme des débuts de wedge et avait redémarré un moteur **en parfaite santé**. La v5 ne compte jamais les trois premières sondes après un boot.

**Leçon 9 — Tous les indicateurs peuvent mentir ensemble.** Quand chaque signal disponible dit « patient », le réflexe qui sauve est d'aller mesurer, par un autre chemin, la chose elle-même — ici, la taille réelle du cache monté.

---

## 10. Le redémarrueur invisible

Août apporte sa découverte forensique la plus importante. Sur cette machine tourne un petit conteneur utilitaire venu d'un autre stack — un « auto-heal » chargé de relancer les conteneurs dont le healthcheck échoue. Sa configuration dit *tous les conteneurs*. Il n'a jamais été pensé pour le moteur LLM ; *tous* ne fait pas de tri. Chaque fois que Docker marquait notre moteur `unhealthy`, ce gardien bienveillant le redémarrait — en concurrence directe de notre watchdog, dont toute la conception repose sur l'idée opposée : ne jamais interrompre un boot, même lent, même en échec apparent.

Sa signature est ce qui l'a rendu invisible pendant des mois. Un redémarrage qu'il provoque laisse **code de sortie zéro**, pas d'OOM, et surtout — c'est le détail qui tue — **un compteur de redémarrages inchangé** : un `docker restart` manuel n'incrémente pas le compteur que la *restart policy* incrémente. Or toute notre détection de boucles de crash lit ce compteur. Elle était structurellement aveugle à ce gardien. La seule trace côté moteur était un `KeyboardInterrupt` anodin dans l'initialisation.

Le déclic vient en voulant comprendre pourquoi le premier démarrage à froid d'une nouvelle image mourait systématiquement à dix-sept minutes : le boot dépassait la période de grâce du healthcheck, le gardien le tuait — et l'examen de ses journaux a révélé qu'il avait aussi frappé **pendant l'incident du 10 août**, au milieu de la fenêtre qu'on analysait depuis des heures. Une partie des redémarrages de cet incident venait de lui : l'analyse elle-même devait être révisée. Le correctif tient en une ligne — un label qui dit au gardien « pas celui-ci » — mais la leçon dépasse ce cas : **avant d'analyser un redémarrage inexpliqué, dresser la liste des autorités de redémarrage présentes sur l'hôte.** Un compteur stable ne prouve pas qu'aucun redémarrage n'a eu lieu.

La même quinzaine offre un second avertissement du même genre, dans l'autre sens : pendant une expérience de validation sur la troisième carte, l'outil standard de supervision GPU de l'hôte rapportait **152 Mo occupés** — pendant que le conteneur d'essai y servait un modèle à des milliers de tokens par seconde. L'outil regardait la carte ; la charge vivait dans un espace qu'il ne comptait pas. Le garde-fou anti-collision bâti sur cette lecture ne protégeait donc de rien, et l'accord explicite entre équipes est resté la seule barrière fiable.

**Leçon 10 — Un indicateur silencieux vaut exactement ce que vaut la liste de ce qu'il ne mesure pas.** Et cette liste, seul l'examen manuel la révèle : compter les autorités de redémarrage, interroger la carte depuis le conteneur, mesurer le cache monté.

---

## 11. La sortie de Genesis — deux phases et une preuve

Restait la question qui pendait depuis mai : l'arbre de patches downstream qui nous sauvait du crash TurboQuant — en étions-nous encore prisonniers ? Deux raisons de vouloir en sortir. D'abord la **reproductibilité** : les images nocturnes sur lesquelles l'arbre se construit sont purgées au bout de quelques jours, et l'image de production était devenue impossible à reconstruire — elle n'existait plus qu'en une copie locale, sauvegardée. Ensuite, l'amont avait repris le travail sur la famille de bugs qui nous avait fait fuir : quatre correctifs étaient passés, vérifiés présents dans la version publiée.

La méthode d'août tient en deux phases, chacune ne testant qu'une chose à la fois. **Phase 1, de jour, sur la carte d'expérimentation** : un petit modèle proxy, un contexte réduit, la question unique « le crash se reproduit-il sur le vLLM d'origine ? ». Réponse : non — et une donnée annexe précieuse, un premier appel de compilation à froid du décodeur quantifié mesuré à **328 secondes**, retombant à 4 une fois le cache chaud. **Phase 2, de nuit, sur le vrai moteur** : bascule de la production elle-même, le 10 août à 23 h 45 UTC, batterie de treize tests.

La nuit faillit mal tourner pour de mauvaises raisons : le premier démarrage fut tué par le redémarrueur invisible du chapitre précédent (c'est cette nuit-là qu'il fut identifié), puis la première batterie afficha des échecs inquiétants sur les longs contextes — qui se révélèrent être un module de hachage absent de l'image d'origine, importé trop paresseusement pour se signaler avant l'usage. Deux corrections mineures, et la batterie repassa **13 sur 13**.

Puis la preuve, celle qui légitimait tout le reste : un pré-remplissage **chunké de 253 503 tokens** — à un pas de la fenêtre maximale, l'équivalent du contexte qui avait tué le moteur en mai — passa **en 58,6 secondes**, suivi d'une requête de survie. Le crash historique ne se reproduisait pas. Deux autres gains mesurés tombèrent avec : la carte partagée avec le bureau regagnait **1,8 Gio** de marge (les pools de pré-allocation de l'arbre vivaient hors budget), et le coût de la sortie — 17 % de capacité de cache — s'avérait sans effet pratique, l'occupation en production plafonnant à quelques pourcents.

Restait le débit, et c'est là que l'épisode livre sa leçon de méthode la plus nette. La première mesure sembla désastreuse : 37 % sous la référence documentée. Conclusion hâtive : le vLLM d'origine serait plus lent. Mais la référence datait de **mai**, sur une machine dont l'état avait changé. La seule comparaison honnête est un A/B **la même nuit**, même machine, mêmes scripts — l'arbre de patches redéployé, mesures refaites, retour à l'origine. Verdict inversé : le vLLM d'origine gagnait de 14 % en charge multi-utilisateurs et de 29 % en mono-flux. Et la vraie découverte était ailleurs : **les deux piles étaient ensemble ~45 % sous les chiffres de mai**. Ce n'était ni l'une ni l'autre — c'était la machine qui avait perdu du débit, pour une cause non élucidée à ce jour (horloges, pilote, plan d'alimentation, charge du bureau), ouverte en chantier distinct. La migration était justifiée par la comparaison de cette nuit-là ; les chiffres de mai cessèrent d'être des références.

**Leçon 11 — Dater la mesure.** Une référence vieillit avec la machine qui l'a produite ; seule une comparaison *simultanée* — même nuit, même matériel, mêmes scripts — départage le logiciel du matériel.

---

## 12. Ce que ça enseigne

Si l'on ne devait retenir que quelques idées de ce journal :

1. **Quatre grandeurs en tension.** Débit, contexte, qualité, VRAM. On choisit, on ne maximise pas tout. Le bon choix dépend du *workload réel*, pas d'un benchmark abstrait. Juillet–août en a ajouté une cinquième, invisible jusqu'ici : **la disponibilité** — qu'un compromis tienne huit semaines sans interruption vaut parfois plus qu'un dixième de débit supplémentaire.
2. **Le matériel décide du possible — et il ment parfois.** Sur du grand public Ada, la VRAM et la génération de GPU ferment des portes avant même la question de la vitesse ; et le budget mémoire déclaré n'est pas la mémoire consommée. Quand un indicateur (budget, compteur, sonde) se tait sur une partie du réel, seul l'examen manuel de ce qu'il ne mesure pas le révèle.
3. **Mesurer, toujours — et dater la mesure.** Grid search, benchmarks, soaks : chaque décision majeure s'appuie sur un chiffre reproductible. La saga d'août a ajouté le corollaire : une référence vieillit avec la machine qui l'a produite. La seule comparaison honnête est un A/B **même nuit**, même matériel, mêmes scripts. Comparer une mesure du jour à une mesure de trois mois plus tôt a failli faire rejeter une migration qui gagnait en réalité de 14 %.
4. **Un silence n'est pas une santé.** Un HTTP 200 ne prouve pas que le décodage vit ; un compteur de redémarrages plat ne prouve pas que rien n'a redémarré ; un indicateur GPU à sa baseline ne prouve pas qu'une carte est libre. Chaque mode de panne découvert ce trimestre était *silencieux* — la panoplie de surveillance existe précisément parce qu'aucun indicateur unique n'est honnête.
5. **Détecter et agir sont deux métiers différents.** Le watchdog a appris, version après version, à ne pas confondre lenteur légitime et panne : ne jamais redémarrer pendant un boot, offrir une grâce de chauffe, distinguer la boucle de crash (redémarrer ne sert à rien) du montage fantôme (redémarrer aggrave). La moitié de l'ingénierie de fiabilité consiste à *ne pas faire* la chose réflexe.
6. **Documenter les échecs — et les faux coupables.** Le cimetière des modèles rejetés, les impasses de décodage spéculatif, mais aussi les deux faux coupables d'août : le redémarrueur invisible et le téléchargement fantôme. Une analyse d'incident révisée après coup vaut autant qu'une analyse juste du premier coup : elle enseigne la même prudence méthodique.
7. **`vérifié` ≠ `supposé`.** Avant de déclarer une cause, un test qui la force. Avant de propager un fait, une vérification. La règle de juin a payé tout l'été.
8. **La reproductibilité est une propriété de production.** L'image irréconstructible a fini par peser plus lourd que les correctifs qu'elle portait : un artefact qu'on ne peut pas reconstruire est une dette, pas un actif. Sortir de l'arbre de patches pour une version publiée — en vérifiant, preuve à l'appui, que la raison d'être de l'arbre avait disparu — a rendu le service reconstruisable du jour au lendemain. Amont *et* aval, toujours, mais l'amont d'abord quand il rattrape son retard.

Le serveur qui tourne aujourd'hui — modèle MoE Qwen3.6-35B-A3B sur un vLLM d'origine versionné, cache TurboQuant, plus d'un million de tokens de contexte, fenêtre de 262 K, vision et raisonnement, surveillé par un watchdog qui a appris la patience — n'est pas un point d'arrivée. C'est l'état courant d'un arbitrage qui a déjà changé dix fois et changera encore. Les deux mois que racontent les chapitres précédents n'ont presque rien optimisé : ils ont *tenu* le service, compris pourquoi il tombait, et remboursé la dette de reproductibilité contractée en mai. C'est aussi ça, servir un LLM en production : non pas trouver *la* configuration, mais entretenir un compromis vivant, mesuré, surveillé et honnêtement documenté.

---

*Sources : archéologie git du fork (plus de 110 commits, mai 2025 → août 2026), documentation interne de déploiement (juillet–août 2026), journaux d'itération phase 1/2 de la migration, journaux Docker horodatés. Patches Genesis : [Sandermage/genesis-vllm-patches](https://github.com/Sandermage/genesis-vllm-patches) (auteur Sandermage, v7.72.x, mai 2026). Issues amont vLLM citées : [#27951](https://github.com/vllm-project/vllm/issues/27951), [#41726](https://github.com/vllm-project/vllm/issues/41726). Aucun secret, clé, ni coordonnée interne joignable n'apparaît dans ce document.*
