# Tutoriel GitHub — soumettre une correction d'exercice pas à pas

Ce tutoriel s'adresse à ceux qui n'ont **jamais utilisé GitHub** et doivent rendre une correction d'exercice d'un notebook de ce dépôt ([CoursIA](https://github.com/jsboige/CoursIA)). Il couvre tout le parcours : créer un compte, récupérer le notebook, le travailler, et ouvrir la Pull Request. Suivez les étapes dans l'ordre ; chacune prend quelques minutes. Le parcours de base est **100 % navigateur** : aucune ligne de commande, aucune installation de Git — seulement l'outil que vous utilisez déjà pour les notebooks (Jupyter ou Google Colab). Ceux qui préfèrent travailler dans **VS Code** (extensions Jupyter ou Polyglot Notebooks) trouveront en fin de page la [variante locale](#variante-vs-code--travailler-localement-avec-les-extensions-jupyter-ou-polyglot), elle aussi sans ligne de commande.

Le flux général et les conventions du dépôt sont décrits dans [CONTRIBUTING.md](../CONTRIBUTING.md) ; ce tutoriel en est la version « clic par clic » pour débutants. Votre cours peut préciser des consignes supplémentaires (notebooks autorisés, échéance, travail en groupe) : suivez-les en priorité.

Si une étape bloque, ne restez pas seuls : [ouvrez une issue](https://github.com/jsboige/CoursIA/issues/new?template=content-feedback.yml) en décrivant où vous bloquez (écran, message d'erreur), une réponse vous aidera à reprendre.

## Trois notions, deux minutes

- Un **dépôt** est un dossier de fichiers partagé, avec l'historique de toutes ses modifications.
- Un **fork** est votre copie personnelle d'un dépôt : vous y travaillez sans risque pour l'original.
- Une **Pull Request** (PR) est votre demande officielle : « voici mes modifications, merci de les intégrer au dépôt d'origine ». C'est elle qui est évaluée, et c'est sur elle qu'on vous répond.

Le parcours se déroule en un aller-retour : vous **téléchargez** le notebook depuis votre copie, vous le **travaillez** dans Jupyter ou Colab, vous le **renvoyez** sur votre copie, puis vous ouvrez la **PR** vers le dépôt d'origine `jsboige/CoursIA`.

## Étape 0 — Créer un compte GitHub (une fois, 2 minutes)

1. Allez sur [github.com/signup](https://github.com/signup).
2. Choisissez un identifiant professionnel (il sera visible sur votre contribution).
3. Validez l'e-mail de confirmation.

Un seul compte par personne suffit. En travail de groupe, le groupe désigne **un membre** dont le compte hébergera la copie de travail (étape 1) — les autres y sont invités (étape 2). En travail seul, ignorez l'étape 2.

## Étape 1 — Forker le dépôt CoursIA (une fois)

1. Connectez-vous, puis ouvrez [`github.com/jsboige/CoursIA`](https://github.com/jsboige/CoursIA).
2. Cliquez sur le bouton **Fork** en haut à droite de la page.
3. Laissez les options par défaut et cliquez sur **Create fork**.

GitHub crée `votre-compte/CoursIA` : c'est votre copie de travail. Le dépôt est volumineux, la création peut prendre une dizaine de secondes.

## Étape 2 — Inviter vos coéquipiers sur le fork (travail de groupe)

Pour que plusieurs membres puissent déposer des fichiers sur la copie :

1. Sur la page de `votre-compte/CoursIA`, allez dans l'onglet **Settings** du dépôt.
2. Dans le menu de gauche, **Collaborators** (GitHub peut demander de confirmer un code : suivez l'invite).
3. **Add people** : saisir l'identifiant GitHub de chaque coéquipier, puis **Add to this repository**.
4. Chaque invité accepte l'invitation reçue par e-mail ou dans ses notifications.

## Étape 3 — Synchroniser votre fork (avant chaque nouveau TP)

Votre copie a pu prendre du retard sur le dépôt d'origine depuis votre dernier TP. Une branche créée sur une copie en retard fait apparaître dans la Pull Request des centaines de fichiers sans rapport avec votre correction, et l'intégration doit alors d'abord fusionner `main`. Refaites donc cette synchronisation **avant chaque nouveau TP**, avant de créer la branche :

1. Sur la page de `votre-compte/CoursIA`, vérifiez que le sélecteur de branche affiche **main**.
2. Cliquez sur le bouton **Sync fork**, en haut de la page.
3. Si GitHub indique que la copie est en retard, cliquez sur **Update branch**. Si elle est déjà à jour, il n'y a rien à faire. Si GitHub propose un autre bouton, ne cliquez pas au hasard : ouvrez une issue (voir [En cas de blocage](#en-cas-de-blocage)).

En travail de groupe, c'est le compte qui héberge la copie (étape 0) qui fait cette synchronisation.

## Étape 4 — Créer une branche de travail

Une **branche** est une version parallèle où vos modifications restent isolées, sans toucher au reste.

1. Sur `votre-compte/CoursIA`, cliquez sur le sélecteur de branche (il affiche **main**) en haut à gauche de la liste de fichiers.
2. Tapez le nom de la nouvelle branche, par exemple `tp2-<notebook>` (le numéro du TP, puis le notebook) ou `<groupe>-<notebook>`. Ne mettez pas votre nom personnel : le nom de branche est public et apparaît sur la Pull Request.
3. Cliquez sur **Create branch ... from main** : la branche part de la `main` que vous venez de synchroniser (étape 3).

Le sélecteur affiche désormais votre branche. **Vérifiez-le avant chaque dépôt de fichier** : c'est l'erreur la plus fréquente.

## Étape 5 — Télécharger le notebook

1. Naviguez dans votre fork jusqu'au notebook visé (même chemin que dans le dépôt d'origine, par exemple `MyIA.AI.Notebooks/GenAI/...`).
2. GitHub affiche un aperçu du notebook. Cliquez sur le bouton **Raw** (à droite, au-dessus du contenu).
3. Le fichier brut s'affiche : enregistrez-le avec **Ctrl+S** (ou clic droit, *Enregistrer sous*), en gardant **exactement le même nom de fichier**.

## Étape 6 — Travailler le notebook dans Jupyter ou Colab

Ouvrez le fichier `.ipynb` téléchargé dans votre outil habituel :

- **Jupyter** (Anaconda...) : ouvrez le fichier directement ;
- **Google Colab** : *Fichier > Importer un notebook*, puis travaillez directement ;
- **VS Code** (extensions Jupyter ou Polyglot Notebooks) : voir la [variante VS Code](#variante-vs-code--travailler-localement-avec-les-extensions-jupyter-ou-polyglot) en fin de page.

Puis :

1. Corrigez l'exercice visé. Dans CoursIA, un exercice ouvert se présente comme une cellule à compléter (`pass`, `return None`, marqueur `TODO` ou équivalent) : écrivez une solution fonctionnelle et lisible — une solution qui calcule le résultat, pas une valeur codée en dur — avec une courte explication quand le raisonnement n'est pas évident.
2. **Exécutez tout le notebook depuis le début** (dans Colab : *Exécution > Tout exécuter*). Les sorties des cellules font partie du rendu : elles prouvent que votre correction tourne. Aucune cellule ne doit rester en erreur.
3. Vérifiez les cas nominaux et au moins un cas limite pertinent.
4. Enregistrez : *Fichier > Télécharger > Télécharger le .ipynb* (Colab), ou simple sauvegarde (Jupyter). Le fichier garde le même nom.

**Ne modifiez jamais le contenu du fichier `.ipynb` à la main dans GitHub** (l'éditeur web de GitHub y montrerait du JSON illisible) : passez toujours par Jupyter ou Colab, puis déposez le fichier obtenu à l'étape suivante.

Après validation d'une correction, les mainteneurs transforment la solution en **exemple guidé** crédité et ajoutent un nouvel exercice non résolu à la place — vous n'avez pas à fabriquer vous-même l'exercice de remplacement (détail dans [CONTRIBUTING.md](../CONTRIBUTING.md)).

## Étape 7 — Déposer le notebook sur votre branche

Une Pull Request ne porte qu'**un seul notebook** : chaque PR est relue et intégrée seule. Ne déposez donc sur cette branche que le notebook de votre correction ; pour un second notebook, reprenez l'étape 4 et créez une nouvelle branche.

1. Revenez sur `votre-compte/CoursIA` dans le navigateur, **sur votre branche de travail** (étape 4).
2. Naviguez jusqu'au **dossier exact** contenant le notebook d'origine (même chemin qu'à l'étape 5).
3. Cliquez sur **Add file > Upload files**.
4. Glissez le fichier `.ipynb` travaillé (même nom : GitHub propose de l'écraser, c'est bien ce qu'on veut).
5. En bas de page, sous *Commit changes*, remplacez le message par quelque chose d'explicite, par exemple : `Correction de l'exercice 2 de <nom du notebook>`.
6. Vérifiez que **Commit directly to the `<votre-branche>` branch** est sélectionné, puis cliquez sur **Commit changes**.

Pour une modification après review, refaites simplement cette étape : la Pull Request se met à jour toute seule.

## Étape 8 — Ouvrir la Pull Request vers CoursIA

1. Dans `votre-compte/CoursIA`, un bandeau jaune **Compare & pull request** apparaît après votre premier dépôt. Cliquez dessus. (Sinon : onglet **Pull requests > New pull request > compare across forks**.)
2. Vérifiez la direction en haut du formulaire — c'est la ligne qui décide de tout :
   - **base repository** : `jsboige/CoursIA`, base `main` (le dépôt d'origine) ;
   - **head repository** : `votre-compte/CoursIA`, compare `votre-branche`.
3. Le bouton **Create pull request** doit être vert (il indique *Able to merge*). S'il parle de conflit, ne forcez rien : ouvrez une issue en décrivant le message.
4. Remplissez le titre et la description, en précisant :
   - le notebook corrigé (son chemin) ;
   - l'exercice corrigé ;
   - comment vous avez vérifié (exécution complète, cas limites testés).
5. **Create pull request.** Sans PR ouverte, le travail ne peut pas être évalué.

## Étape 9 — Suivre la review

Votre PR est relue ; des ajustements peuvent être demandés — c'est normal, cela fait partie du processus, et les reviews de ce dépôt sont bienveillantes (une partie des réponses peut être rédigée par un agent IA, sous supervision humaine).

- Les remarques apparaissent dans l'onglet **Conversation** (commentaires généraux) et **Files changed** (commentaires ligne à ligne).
- Pour répondre : cliquez sur **Reply** sous la remarque, écrivez, puis **Comment**.
- Pour corriger : refaites les étapes 6 et 7 (travail dans Jupyter/Colab, dépôt sur la même branche). La PR et les discussions se mettent à jour automatiquement — inutile d'en ouvrir une nouvelle.
- Le dépôt lance des contrôles automatiques sur la PR. S'ils passent au rouge pour une raison d'environnement qui vous dépasse, signalez-le simplement dans la conversation ; concentrez-vous sur les remarques humaines.
- Une fois la remarque traitée, le relecteur clôt le fil lui-même : pas d'inquiétude si un fil reste ouvert quelques jours.

## Variante VS Code — travailler localement avec les extensions Jupyter ou Polyglot

Le parcours ci-dessus vit entièrement dans le navigateur. Si vous préférez travailler dans **VS Code**, les mêmes étapes se font localement, toujours sans ligne de commande. Deux usages, du plus simple au plus confortable.

### VS Code comme éditeur de notebook (remplace l'étape 6)

1. Installez [VS Code](https://code.visualstudio.com/), puis l'extension adaptée au notebook visé (onglet Extensions dans la barre de gauche, recherchez, installez) :
   - **Jupyter** — pour les notebooks Python du dépôt ;
   - **Polyglot Notebooks** — pour les notebooks .NET Interactive (C#, F#) du dépôt.
2. Ouvrez le fichier `.ipynb` téléchargé à l'étape 5 : *Fichier > Ouvrir le fichier...*.
3. Cliquez sur **Select Kernel** en haut à droite du notebook :
   - notebook Python : choisissez un des interpréteurs Python proposés. Si la liste est vide, installez Python depuis [python.org](https://www.python.org/downloads/), puis rouvrez VS Code ;
   - notebook .NET : choisissez le kernel C# (ou F#) proposé par Polyglot. S'il n'apparaît pas, installez le [SDK .NET](https://dotnet.microsoft.com/download), puis rouvrez VS Code.
4. Exécutez tout le notebook avec le bouton **Run All** en haut de la liste de cellules. Les sorties s'affichent sous chaque cellule ; aucune ne doit rester en erreur.
5. Enregistrez avec **Ctrl+S** : le fichier `.ipynb` conserve les sorties — c'est la preuve que votre correction tourne.

Le dépôt sur votre branche reste celui de l'étape 7 (*Add file > Upload files* dans le navigateur).

### VS Code avec le Git intégré (remplace aussi les étapes 5 et 7)

Pour éviter l'aller-retour téléchargement/dépôt à chaque review :

1. Dans VS Code, ouvrez la vue **Source Control** (icône de la barre de gauche) et cliquez **Clone Repository** : collez l'URL de **votre fork**, `https://github.com/votre-compte/CoursIA`, choisissez un dossier local et rouvrez ce dossier quand VS Code le propose. Si VS Code signale que Git est absent, suivez son invite d'installation.
2. Créez votre branche : synchronisez d'abord le fork (étape 3). Si vous avez déjà un clone local d'un TP précédent, mettez aussi votre `main` local à jour (commande *Pull* du menu `…` de la vue Source Control), sans quoi la branche partirait de l'ancienne version. Cliquez ensuite sur le nom de branche dans la barre de statut (en bas à gauche, il affiche `main`), puis *+ Create new branch...*, avec le même genre de nom qu'à l'étape 4 (par exemple `tp2-<notebook>`).
3. Ouvrez le notebook depuis l'explorateur de VS Code, travaillez-le et exécutez-le comme ci-dessus, puis **Ctrl+S**.
4. De retour dans la vue **Source Control** : le notebook modifié apparaît dans *Changes*. Cliquez le bouton **+** qui apparaît au survol du fichier, écrivez un message explicite (par exemple `Correction de l'exercice 2 de <notebook>`), puis **Commit** et **Sync Changes** — c'est l'équivalent de l'étape 7, directement depuis VS Code.
5. L'ouverture de la Pull Request (étape 8) se fait toujours dans le navigateur : le bandeau *Compare & pull request* apparaît après votre premier envoi.

À la première synchronisation, VS Code demande de vous identifier : suivez l'invite *Sign in with GitHub* (un clic).

## Pièges classiques

| Symptôme | Cause probable | Que faire |
|---|---|---|
| Le bouton **Fork** semble ne rien faire | Dépôt volumineux | Patienter puis rafraîchir ; le fork n'est à faire qu'une fois |
| Le dépôt s'est fait sur **main** au lieu de la branche de travail | Sélecteur de branche non vérifié (étape 7.1) | Ouvrir une issue plutôt que d'improviser |
| GitHub affiche du JSON illisible | Édition web du `.ipynb` | Ne jamais éditer le JSON : reprendre à l'étape 6 |
| *This branch has no changes* à l'ouverture de la PR | Dépôt sur une autre branche que celle comparée | Vérifier le sélecteur **compare** à l'étape 8.2 |
| Conflits signalés | Le dépôt d'origine a bougé sur le même fichier | Ouvrir une issue — ne pas cliquer sur *Resolve conflicts* en aveugle |
| Deux contributions sur le même exercice | PRs ouvertes non vérifiées | Vérifier les PR ouvertes avant de choisir l'exercice |
| *Select Kernel* ne propose rien (VS Code) | Interpréteur ou kernel non installé | Installer Python ou le SDK .NET, rouvrir VS Code (variante ci-dessus, point 3) |
| Sorties absentes du fichier déposé | Notebook exécuté mais non sauvegardé | *Run All* puis **Ctrl+S** avant le dépôt |

## Rappel sécurité

Ne déposez **jamais** de clé API, de fichier `.env`, de mot de passe ou de donnée personnelle dans un commit — tout ce qui est déposé est public. En cas d'erreur, prévenez immédiatement par issue. Les conventions complètes du dépôt (exécution des notebooks, secrets, style) sont dans [CONTRIBUTING.md](../CONTRIBUTING.md).

## En cas de blocage

[Ouvrez une issue](https://github.com/jsboige/CoursIA/issues/new?template=content-feedback.yml) décrivant l'écran et le message où vous bloquez — mieux vaut une question tôt qu'un blocage la veille de l'échéance.
