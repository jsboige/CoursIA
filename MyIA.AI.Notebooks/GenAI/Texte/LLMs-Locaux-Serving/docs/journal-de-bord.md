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

## 12. Trois tokens, une pile disparue

La fin août ouvre la saison des incidents qui ne ressemblent à rien de connu. Le 27, un audit de sécurité découvre un **token Hugging Face vivant exposé en clair** sur le fork public — dans d'anciens fichiers compose d'une branche de travail. Révocation le jour même, vérifiée. Mais l'histoire ne s'arrête pas là : trois jours plus tard, un recomptage méthodique établit qu'il circulait **trois** tokens, pas deux — le mort, le neuf posé dans le `.env`… et celui que le conteneur de production **servait encore**, parce que l'environnement d'un conteneur est **figé à sa création** : un `docker restart` ne relit jamais le `.env`, seul un `--force-recreate` le fait. La rotation n'était finie que le 31, empreinte du secret servi vérifiée depuis l'intérieur du conteneur — et la discipline s'écrit : on ne prouve une rotation qu'en hashant les octets exacts du secret que le service utilise, jamais en regardant le fichier censé le porter.

Le 31, pendant le recreate justement, la couche GPU de WSL2 lâche : d'abord les montages de fichiers (le conteneur ne voit plus ses poids), puis, une fois les montages réparés, **le passthrough GPU lui-même** — `libnvidia-ml.so` introuvable dans le conteneur, cartes à 0 Mo. Un `--force-recreate` de plus n'aurait rien réparé : la cause était la couche pilote de l'hôte, et la sortie, une **mise à jour NVIDIA + redémarrage complet**. Le 2 septembre enfin, la pirouette : entre deux sightings, **les trois conteneurs disparaissent de `docker ps -a`** — pas arrêtés, *supprimés* — pendant une maintenance compose d'une autre pile qui ne cible à aucun moment vLLM. Trente-quatre minutes d'indisponibilité muette, cause exacte jamais établie. La leçon est structurelle : `restart: unless-stopped` et un watchdog *dans* la pile ne peuvent pas relever des conteneurs **détruits** — le down emporte le watcher avec le moteur. Naissance d'un **watcher côté hôte**, hors Docker, alerte seule, cadence 5 minutes, qui distingue l'absence de pile (suppression ou swap pendu) du simple redémarrage.

Et le 8 septembre, encore : une clé d'API d'embeddings exposée dans un dépôt public git. Rotation, fil de consumers 401 refermé. En douze jours, deux secrets différents, deux vecteurs distincts, même conclusion — le périmètre public d'un dépôt est une surface d'attaque du service de production, et la seule preuve de rotation est l'empreinte du secret servi.

> **Leçon 12.** Une rotation de secret n'est finie que quand le service qui la porte est *prouvé* servir le nouveau — l'environnement d'un conteneur est figé à sa création. Et la surveillance qui compte vit hors de la pile qu'elle surveille : ce qui peut être supprimé avec elle la sera.

## 13. Le banc d'essai de la carte 3

Pendant ce temps, la troisième carte — libérée en mai pour les entraînements — attire toutes les curiosités, et septembre en fait le banc d'essai des lignes candidates. D'abord **K2-Horizon**, un MoE à attention *Mixture-of-Values* tout juste publié : benches agentiques écrasants, pas de vision — l'utilisateur tranche : la vision est sacrifiable sur le moteur principal, un 8B spécialisé la fournira à la demande, et l'assistant du cluster la propose « en service ». Le support vLLM vient d'être fusionné en amont… mais **aucun tag release ne le contient encore**. La fenêtre d'évaluation croise un hôte qui gèle : **mort silencieuse, ni écran bleu, ni dump** — l'un de ces arrêts brutaux que la machine inflige environ toutes les deux semaines depuis des mois, sans aucune trace logicielle. Le job de quantisation de 5 h à 100 % GPU tombait pile dessus ; la question « est-ce sa faute ? » a reçu une réponse de taux de base : cinq des six gels des 90 derniers jours précèdent tout job de quant. Faux coupable, encore — mais la ligne est reportée quand même, et une discipline s'écrit : après un crash machine, collecter d'abord les enregistreurs (événements noyau, dumps, télémétrie interne), puis comparer au taux de base avant d'incriminer le job en cours. Puis, mi-septembre, le retour d'expérience de la carte seule : servir le dense 27B sur **une** carte à travers WSL2 se heurte à une taxe de **2,02 GiB** de paravirtualisation avant le premier poids, à des drapeaux d'allocation qui cassent les kernels Marlin, à un cache HF monté un niveau trop profond, et à une empreinte fixe de 2,37 GiB pour la tête de brouillon MTP — douze boots, sept modes d'échec, meilleur cas : **150 Mo de cache KV**. Structuralement impossible, ligne close et documentée.

La ligne K2 reparaît le 22 pour une dernière fenêtre : l'overlay amont s'avère **XPU-only**, mort sur CUDA ; le fork communautaire démarre enfin… à **6–8 tok/s** en flux simple, là où la production sert 120 — un ordre de grandeur manque, la cause tient au mode eager imposé par le fork. Ligne garée, à rouvrir quand l'amont saura quantifier les valeurs MoVA. Au passage, deux disciplines s'écrivent pour toujours : une **batterie appariée** (mêmes questions, indice par indice, test de McNemar) pour rejeter un challenger qualité sans bruit statistique — c'est elle qui a enterré Ornith-1.5 ; et la règle née d'un réquisitoire utilisateur après l'arrêt manuel d'un run de quantisation de 10 h : **tout job long embarque un checkpoint et une reprise prouvée** — le harnais a été validé en vol, et l'on a appris au passage que le critère « bit-exact » est le mauvais : deux exécutions fraîches d'une quantisation GPU diffèrent déjà ; une reprise honnête s'inscrit dans ce bruit-là.

> **Leçon 13.** Une carte « libre » n'est pas une carte « utilisable » : les taxes de paravirtualisation, les montages imbriqués et les empreintes fixes se prélevant avant le premier token, seul le compte complet décide. Un gel dur d'hôte vaut interdiction définitive des jobs longs sans checkpoint — et une reprise se prouve dans le bruit intrinsèque du calcul, pas contre lui.

## 14. Le cache préfixe mort-né

Le 11 septembre, un constat glacial : **520 101 requêtes de hachage de cache préfixe depuis la mise en service, zéro hit.** Pas une baisse de performance — zéro. Le cache préfixe, activé depuis toujours, censé accélérer chaque conversation multi-tours en réutilisant le contexte déjà calculé, n'avait jamais servi une seule requête. Et rien ne l'avait signalé : les métriques de succès étaient vertes, le service répondait, personne n'avait pensé à lire un compteur qui restait à zéro.

La cause est structurelle, pas accidentelle. Le modèle est hybride — réseaux Delta gating *et* attention classique — et sur ces architectures, l'alignement des états linéaires sur les blocs de cache force une granularité de correspondance égale à la taille du bloc : **2 768 tokens**. Or une clé de cache se calcule par bloc complet : tout ce qui est plus court qu'un bloc entier ne peut jamais correspondre. Un prompt système de 3 000 tokens, la signature des charges agentiques, restait lettre morte.

Le correctif tient en deux drapeaux — une unité de correspondance fine (16 tokens ; la divisibilité 2 768 = 16 × 173 le permet) et un état linéaire en float16 — et s'accompagne d'un bonus inattendu : la taille de bloc se redérive à 1 424 et le pool de cache **grossit** de 1,1 %. Les sondes jumelées parlent d'elles-mêmes : un prompt de 403 tokens passe de **0 à 400 hits** ; un prompt de 7 699 tokens rejoué en 0,412 s puis **0,078 s** ; seize requêtes concurrentes partageant un même prompt système passent de 527 à **1 008 tok/s** agrégés. Dix fois le temps de premier token, récupéré d'un coup, sur une machine qui tournait « bien » depuis des mois.

> **Leçon 14.** Un compteur de succès ne mesure pas la mort. Zéro hit sur 520 101 requêtes vivait tranquillement à côté de taux de réponse parfaits. Il faut lire les compteurs d'*échec* — et surtout se demander, pour chaque optimisation déclarée « active », ce qui prouve qu'elle a déjà servi ne serait-ce qu'une fois.

## 15. Le mur qui n'en était pas un

Septembre est aussi le mois des montées de version en série — v0.28.0 le 1ᵉʳ, v0.30.0 le 22 — et d'une histoire de mur qui mérite le détour. Au passage de v0.28.0, une vieille contrainte tombe : le plafond de batch à 4 096 tokens, qui avait coûté un crash en juin, était un **artefact de l'arbre de patches** (un tampon préalloué dimensionné par défaut), pas une limite du moteur — le stock tolère 8 192 d'origine, validé par un test de forçage : six préfills concurrents de ~2 700 tokens, somme délibérément dans la zone interdite (4 096–8 192], moteur au complet. Ça passe.

Puis v0.29.0, le 9 septembre : **rejet net.** Les deux processus de parallélisme meurent avant même le chargement du modèle — `UvaBuffer`, « UVA is not available ». La traduction semble claire : mémoire virtuelle unifiée indisponible sous la passe GPU de WSL2, frontière matérielle, on connaît déjà cette famille (un décodeur spéculatif était mort sur le même mur huit jours plus tôt). Retour arrière, incident documenté, affaire classée « limite environnementale ».

Deux jours plus tard, la même image, le même digest, **une seule ligne d'environnement** — et les deux workers chargent leurs 11,5 GiB chacun. Le « mur UVA » se révèle être une porte fermée sans étiquette : l'utilitaire qui lève l'exception est littéralement « la mémoire épinglée est-elle disponible — *ou* sommes-nous sur CPU », et sous WSL2 cette disponibilité se lit dans une variable d'environnement, désactivée par défaut. Treize gates sur treize, et un débit à seize concurrents de **869,5 tok/s** — record absolu de la machine, toutes époques confondues. v0.30.0 le 22 confirmera la tendance : +23 à 25 % à chaud contre la version précédente, mesurés la même soirée.

> **Leçon 15.** Un mur « environnemental » peut être un simple interrupteur éteint. Avant d'enterrer une version sur un diagnostic de frontière matérielle, suivre la chaîne d'appels jusqu'à la fonction qui décide — et se demander quelle configuration, plutôt que quelle architecture, la fait répondre non. Et toujours la comparaison même-soirée : le record de septembre n'a de sens que contre un témoin chauffé la même nuit.

## 16. Le pivot qualité

Le 24 septembre au soir, une décision d'arbitrage — la première de l'année qui ne porte pas sur le *débit* : changer de modèle non pour aller plus vite, mais pour écrire mieux. La ligne MoE 35B, splendide sur le papier, n'a pas de successeur annoncé ; la lignée dense de 27B, elle, est celle où l'écosystème itère — affinages communautaires, génération suivante annoncée. Le service bascule sur **Swift-1.5-Qwen3.8-27B**, quantifié W4A16, cache KV en FP8.

L'arbitrage est assumé et documenté : préfill **3 à 4 fois plus lent** (1 812 tok/s sur un prompt de 101 K contre 5 448–8 316 pour le MoE), décodage à 0,5–0,6×. En échange, le tier qualité — et une fenêtre de 262 K conservée avec 465 423 tokens de pool (1,78× la fenêtre). Le basculement se fait sans coupure pour les consommateurs : le serveur répond aux **deux noms** — l'ancien alias d'abord, pour que rien ne casse, le nom honnête ensuite.

Mais la batterie de gates de promotion échoue quatre tests sur treize — et l'analyse révèle un mécanisme plus intéressant qu'un échec : les quatre échecs **cascadent d'un seul événement**. Une requête ≥ ~100 K tokens monopolise l'ordonnanceur 130 à 170 secondes ; les nouvelles arrivées affament les sondes du watchdog ; le watchdog, voyant santé verte mais décodage coincé, redémarre le moteur — **tuant la requête géante**. Le moteur est sain ; c'est le garde-fou, calibré pour des tours courts, qui exécute les tours longs légitimes.

La résolution tient en un chiffre, côté sonde uniquement : le délai d'attente de génération passe de 40 à **90 secondes** — le moteur reste byte-identique. La validation est à l'échelle du problème : un prompt de **253 502 tokens** traité en 180,4 s, **zéro** événement wedge. Au passage, un batch à 16 K est testé et rejeté (−17 % de pool, aucun soulagement de la starvation). Reste une porte fermée : le décodage spéculatif MTP se heurte à un bogue du chargeur amont — le point de contrôle embarque sa tête MTP en BF16 dense, mais vLLM construit les couches du brouillon depuis la configuration de quantification *compressée* du modèle cible. Le bogue est remonté en amont ([vllm#58807](https://github.com/vllm-project/vllm/issues/58807)).

> **Leçon 16.** Un alias de service vaut une migration sans coupure — basculer un modèle sans en changer le nom exposé, c'est migrer un fournisseur sans toucher un client. Et un garde-fou doit suivre le workload qu'il protège : calibré sur des tours courts, il devient le tueur des tours longs légitimes. La patience fait partie des paramètres de production.

## 17. La machine reprend du service

Septembre commence par un double mandat : surveiller l'écosystème, et **mesurer** le soupçon de sous-utilisation de la machine la plus chère du cluster. La mesure tombe le 18 : sur sept jours, **aucune requête en vol 78 à 92 % des minutes** ; occupation du cache KV **sous 1 %**. Le moteur pouvait donc être emprunté — à condition de lui trouver du travail réel, pas de benchmark de complaisance.

Premier chantier : l'**audit de notebooks** du cours. Le pilote dégrossit une vérité inconfortable : le modèle local, livré à lui-même, *ne vérifie pas* — une trace d'appel d'outil sur neuf notebooks, des « exact » affirmés sans rien exécuter. La solution n'est pas un meilleur prompt mais un **harnais qui exécute** : trois étages déterministes — le modèle lit et propose des scripts de vérification, *le harnais les exécute*, le modèle juge sur les sorties réelles. Résultat : ~50 notebooks/heure en concurrence 6, contre 2/heure pour les deux agents dédiés. Le service tourne depuis le 23 septembre, toutes les heures à :05, avec l'accord explicite des trois consommateurs et des règles de livraison (ne jamais devancer ce que le bot a déjà audité entre-temps).

Deuxième chantier : la **preuve formelle Lean**. Le corpus de nœuds de théorie porte des théorèmes encore ouverts ; le harnais de preuve — coordinateur, tacticien, chercheur, critique — tourne entièrement sur le modèle local. Dix passes encadrées sur les barreaux 42 à 52 de l'échelle de difficulté : **huit succès, deux échecs honnêtes, zéro faux succès.** La première preuve « qualité » du nouveau modèle tombe au barreau 49 en 267 s. Et la discipline d'échec vaut le détour : une passe qui n'aboutit pas **restore le fichier**, mais l'échafaudage partiel est préservé dans la trace ; un temps de vérification dépassé est *INCONNU*, pas *CASSÉ* ; un début de preuve qui compile peut se conserver, le coordinateur en attestant. Le corpus lui-même enseigne l'humilité : 45 des 52 théorèmes ciblés s'avèrent déjà prouvés par une autre lane — vérifier l'état de la cible *avant* de tirer.

Troisième chantier, plus discret : la **condensation des tableaux de bord** multi-agents passe sur le modèle local — résumer l'historique de coordination, c'est précisément un travail de citation — avec un repli cloud validé en production pour les fenêtres de maintenance.

> **Leçon 17.** La sous-utilisation est une ressource mesurable — mais la charge réelle ne se *précise* pas, elle se **génère**. Les premières exécutions planifiées tombaient sur des files vides : annoncer « le vrai feu commence à 13:05 » sans vérifier l'état de la file, c'est prévoir la météo par le calendrier. Et déléguer du travail réel à un modèle local exige un harnais qui exécute : sans exécution déterministe entre les propositions et le jugement, l'agent affirme, il ne vérifie pas.

## 18. La chasse aux tokens spéculatifs

La veille prospective du mandat porte ses fruits le 29 septembre : un projet open source partage notre système d'exploitation opérationnel *au complet* — même version de vLLM épinglée, mêmes cartes 24 Go, même drapeau de mémoire épinglée WSL2, mêmes chausse-trapes. Leur thèse : le décodage spéculatif perd à haute concurrence mais **gagne massivement là où la réponse cite le prompt** — exactement le profil d'une charge agentique. Leur chiffre étendard : 381 tok/s en citation, contre ~50 en production pour nous.

Fenêtre 1, une heure, accord utilisateur. La base est saine — remplacement à l'identique, même pool de cache. Le mode « C+ » (brouillon DFlash2 + recherche n-gram + activations INT8) : **+59 % à 2 requêtes, +41 % à 4, +24 % à 8**, effondrement attendu à 16 — et surtout la **citation à 374 tok/s, 7,4 fois** le témoin, copie exacte. Mais la fenêtre de contexte tombe à 64 K : inutilisable pour nos charges longues. Rejet documenté.

Fenêtre 2, le soir même : la variante « contexte long » — cache KV en INT8 par tête de token, attention Triton. La fenêtre pleine de **262 144 tokens** revient, avec un pool de 297 748 tokens (1,14× la fenêtre, contre 1,78× en production — le prix du brouillon). L'échelle tient : **+51 % à 2, +60 % à 4, +16 % en solo**, citation à 270,7 tok/s (**5,4×**). Un prompt de 189 081 tokens est accepté et traité correctement ; le cache préfixe fonctionne sur KV INT8 (rejeu : 202 s puis **4,7 s**) ; et le watchdog ne bronche pas pendant un préfill de 205 s — les sondes courtes s'intercalent, là où le moteur de production affame les arrivées.

Puis le **soak nocturne** — la nuit entière en conditions réelles, l'utilisateur présent par choix. La charge est *générée* selon la leçon du chapitre précédent : une passe de preuve de 63 minutes, des conversations agentiques, le trafic ambiant. ~3,2 millions de tokens de prompt en 4 h 30. **Zéro événement watchdog, zéro signature d'erreur.** Et une découverte que les gates n'avaient pas vue : **la VRAM croît de ~4 GiB sous charge soutenue** — l'index n-gram du brouillon grandit avec le contexte servi, *en dehors* du budget mémoire déclaré (GPU 0 à 23,88 GiB). Une dégradation transitoire de citation (60 tok/s) se récupère à l'échantillon suivant — pagination du bureau, pas une panne. Réponse : le budget passe de 0,70 à 0,68, le pool est rogné mais la garde (pool > fenêtre) tient.

L'épisode s'achève sur une correction de méthode : les médianes de contexte (121 K, 103 K) qui avaient motivé le rejet de la fenêtre 1 venaient d'un **proxy cloud** — elles mesuraient le trafic routé vers un autre modèle, pas notre consommation locale. Les vrais consommateurs du moteur sont l'audit, la preuve, la condensation, les assistants — et leurs besoins, pas ceux d'un miroir de trafic, doivent arbitrer.

> **Leçon 18.** Le décodage spéculatif gagne exactement là où la charge cite le contexte — condensation, preuve, audit — mais il paie une **mémoire dynamique que le budget déclaré ne couvre pas** : c'est le soak, pas la batterie de gates, qui révèle la croissance. Et un argument de capacité construit sur les métriques d'un autre système est un faux ami : avant de rejeter pour cause de fenêtre étroite, vérifier qui consomme *réellement*.

## 19. Ce que ça enseigne

Si l'on ne devait retenir que quelques idées de ce journal :

1. **Quatre grandeurs en tension.** Débit, contexte, qualité, VRAM. On choisit, on ne maximise pas tout. Le bon choix dépend du *workload réel*, pas d'un benchmark abstrait. L'été en a ajouté une cinquième — **la disponibilité** — et l'automne une sixième, révélée par le pivot qualité : **le niveau de sortie**, qu'un service pédagogique finit toujours par réclamer.
2. **Le matériel décide du possible — et il ment parfois.** Sur du grand public Ada, la VRAM et la génération de GPU ferment des portes avant même la question de la vitesse ; le budget mémoire déclaré n'est pas la mémoire consommée — ni même une limite *fixe* : elle peut croître avec la charge servie ; et une carte « libre » porte des taxes invisibles qui se prélèvent avant le premier token.
3. **Mesurer, toujours — et dater la mesure.** Chaque décision majeure s'appuie sur un chiffre reproductible, et la seule comparaison honnête est un A/B **même nuit**. Comparer une mesure du jour à une mesure de trois mois plus tôt a failli faire rejeter une migration qui gagnait en réalité.
4. **Un silence n'est pas une santé.** Un HTTP 200 ne prouve pas que le décodage vit ; un compteur de redémarrages plat ne prouve pas que rien n'a redémarré ; un cache « activé » qui n'a jamais servi une requête reste invisible tant qu'on ne lit pas ses zéros ; et une rotation de secret n'existe pas tant que l'empreinte servie n'est pas vérifiée.
5. **Détecter et agir sont deux métiers différents.** Le watchdog a appris, version après version, à ne pas confondre lenteur légitime et panne — jusqu'à apprendre en septembre que « légitime » inclut les tours longs : sa patience est un paramètre de production, recalibré quand le workload change. Et ce qui peut être supprimé avec la pile surveillée doit être surveillé depuis l'extérieur.
6. **Documenter les échecs — et les faux coupables.** Le cimetière des modèles rejetés, les impasses de décodage spéculatif, le redémarreur invisible, le téléchargement fantôme — et l'automne ajoute le mur UVA qui n'en était pas un et les médianes de trafic qui n'étaient pas les nôtres. Une analyse révisée après coup vaut autant qu'une analyse juste du premier coup.
7. **`vérifié` ≠ `supposé`.** Avant de déclarer une cause, un test qui la force. Avant de propager un fait, une vérification — y compris sur soi-même : une prévision de charge non vérifiée contre l'état de sa source est une hallucination de planification.
8. **La reproductibilité est une propriété de production.** Un artefact qu'on ne peut pas reconstruire est une dette, pas un actif. Amont *et* aval, toujours — mais l'amont d'abord quand il rattrape son retard.
9. **Les compteurs de succès ne mesurent pas la mort.** Un an de cache préfixe à zéro hit à côté d'indicateurs verts : pour chaque optimisation déclarée active, exiger la preuve qu'elle a déjà servi.
10. **Un mur environnemental peut être un interrupteur éteint.** Suivre la chaîne d'appels jusqu'à la fonction qui décide avant d'enterrer une version sur un diagnostic de frontière matérielle.
11. **La sous-utilisation est une ressource — la charge se génère, elle ne se prévoit pas.** Mesurer l'inactivité (78–92 % des minutes à vide), puis déléguer du travail réel via des harnais qui exécutent : le modèle propose, la machine tranche.
12. **Le spéculatif paie en mémoire cachée.** Là où la charge cite le contexte, les gains sont massifs (5–7×) — mais la mémoire qui pousse avec le contexte servi vit hors du budget déclaré, et seule une nuit en conditions réelles la révèle.

Le serveur qui tourne aujourd'hui — un dense de 27B quantifié W4A16 sur un vLLM d'origine versionné, cache FP8, fenêtre 262 K servie sous double nom, watchdog patient, watcher externe, et *du travail réel* : des notebooks audités à l'heure, des théorèmes prouvés, des tableaux de bord condensés — n'est pas un point d'arrivée. C'est l'état courant d'un arbitrage qui a déjà changé onze fois et changera encore. L'automne n'a presque rien optimisé : il a *débouché* ce que l'été avait bouché (un cache, une version, une patience), refermé proprement des lignes mortes, changé de tier sur décision d'arbitrage, et surtout rendu à la machine sa raison d'être — servir. Dix-sept mois après le premier déploiement, c'est peut-être ça, la maturité d'un service : non pas trouver *la* configuration, mais entretenir un compromis vivant, mesuré, surveillé, honnêtement documenté — et occupé.

---

*Sources : archéologie git du fork (plus de 130 commits, mai 2025 → septembre 2026), journaux d'itération (rotation des secrets, incidents Docker, K2-Horizon, Qwen3.8-27B GPU-2, prefix-granularity, v0280/v0290/v0300-bump, swift15_promotion, nb_audit_pilot, hyperqwen_eval), journaux Docker horodatés, métriques /metrics du moteur. Issues amont vLLM citées : [#27951](https://github.com/vllm-project/vllm/issues/27951), [#41726](https://github.com/vllm-project/vllm/issues/41726), [#58807](https://github.com/vllm-project/vllm/issues/58807). Patches Genesis : [Sandermage/genesis-vllm-patches](https://github.com/Sandermage/genesis-vllm-patches) (auteur Sandermage, v7.72.x, mai 2026). Série de patches de référence septembre : [syv-ai/HyperQwen](https://github.com/syv-ai/HyperQwen) (vLLM 0.30.0, cartes 24 Go). Aucun secret, clé, ni coordonnée interne joignable n'apparaît dans ce document.*
