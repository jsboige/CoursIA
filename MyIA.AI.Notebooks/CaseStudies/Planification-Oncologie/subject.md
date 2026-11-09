# CC2 : OncoPlan - Le Protocole Oncologique Adaptatif

**Cours :** IA101 - Intelligence Artificielle (EPF 2026)
**Durée estimée :** 8h - 12h
**Type :** Devoir Maison (Binôme autorisé)
**Livrables :** Notebook Jupyter complété (`.ipynb`) + Rapport PDF succinct (optionnel si le notebook est bien commenté).

---

## 1. Contexte Médical : L'Oncologie de Précision

Vous êtes Data Scientist au sein de l'équipe R&D de l'hôpital "Saint-Louis IA". Votre mission est de développer **OncoPlan**, un assistant décisionnel pour les oncologues.

Le traitement du cancer repose sur des protocoles de chimiothérapie complexes (ex: FOLFOX, FOLFIRI) qui sont toxiques pour l'organisme. Le défi majeur est de trouver l'équilibre entre :
1.  **Efficacité** : Administrer une dose suffisante pour détruire la tumeur.
2.  **Toxicité** : Limiter les effets secondaires (baisse des globules blancs, neuropathie) pour ne pas mettre le patient en danger.

Chaque patient réagit différemment. Certains métabolisent le médicament rapidement ("Répondeurs Rapides"), d'autres accumulent la toxicité ("Répondeurs Lents").

Votre système devra :
*   **Partie 1 (Symbolique)** : Vérifier la validité des prescriptions par rapport aux règles médicales strictes (incompatibilités, délais).
*   **Partie 2 (Planification)** : Générer un calendrier de cures optimal respectant les contraintes de ressources de l'hôpital.
*   **Partie 3 (Probabiliste)** : Modéliser la réponse individuelle du patient pour adapter les doses dynamiquement.

---

## 2. Objectifs Techniques

Ce devoir mobilise les compétences suivantes :
*   **Représentation des Connaissances** : Modélisation d'une ontologie simple (Classes, Relations).
*   **Satisfaction de Contraintes (CSP)** : Utilisation de `OR-Tools` ou `Z3` pour la planification.
*   **Programmation Probabiliste** : Utilisation de `Pyro` pour l'inférence bayésienne sur variables latentes.

---

## 3. Partie 1 : Le Pharmacien Symbolique (Ontologie & Planification)

### 3.1. Modélisation des Connaissances (Ontologie)
Vous devez définir une structure de données (classes Python ou graphe RDF avec `rdflib`) représentant les concepts suivants :
*   **Médicaments** : `Cisplatine`, `5-FU`, `Docetaxel`, etc.
*   **Propriétés** :
    *   `toxicite_renale` (Booléen)
    *   `toxicite_neurologique` (Booléen)
    *   `incompatible_avec` (Liste de médicaments)
*   **Protocoles** : Un protocole est une liste de médicaments administrés à des jours précis (J1, J8, J21...).

**Tâche :** Implémentez une fonction `verifier_prescription(protocole, patient)` qui lève une alerte si :
1.  Deux médicaments incompatibles sont prescrits simultanément.
2.  Un médicament néphrotoxique (toxique pour les reins) est prescrit à un patient ayant une insuffisance rénale (donnée dans le profil patient).

### 3.2. Planification des Cures (CSP)
L'hôpital dispose de ressources limitées. Vous devez planifier 4 cycles de chimiothérapie pour un patient.

**Contraintes :**
1.  **Cycle** : Un cycle dure 21 jours.
2.  **Administration** : Le médicament est administré à J1 et J8 de chaque cycle.
3.  **Repos** : Aucun traitement entre J9 et J21 (période de récupération).
4.  **Ressources** :
    *   L'hôpital a 3 "Fauteuils de Chimio" disponibles par jour.
    *   Le service est fermé le Dimanche.
5.  **Continuité** : L'écart entre deux cycles doit être exactement de 21 jours (sauf report médical).

**Tâche :** Utilisez `OR-Tools` (module `cp_model`) ou `Z3` pour générer un calendrier valide (dates précises) pour 4 cycles, sachant que d'autres patients occupent déjà certains créneaux (fournis dans le squelette).

**Indice Technique (OR-Tools) :**
Pour interdire les dimanches, vous pouvez utiliser la contrainte `AddModuloEquality`. Si J1 est un Lundi (jour 1), alors les dimanches sont les jours 7, 14, 21... (multiples de 7).
Vous cherchez donc à imposer que `jour % 7 != 0`.
En CP-SAT, cela se traduit par :
1.  Créer une variable intermédiaire `reste` (domaine 0-6).
2.  Poser `AddModuloEquality(reste, jour_variable, 7)`.
3.  Poser `Add(reste != 0)`.

---

## 4. Partie 2 : Le Médecin Probabiliste (Modélisation Pyro)

C'est le cœur du sujet. Nous ne connaissons pas à l'avance la tolérance du patient à la chimio. Nous allons l'inférer à partir de ses prises de sang.

### 4.1. Le Modèle Génératif (Bayésien)
Nous modélisons la santé du patient avec les variables suivantes :

*   **Variables Latentes (Cachées)** :
    *   `ProfilToxicite` : Variable catégorielle (0: Résistant, 1: Normal, 2: Sensible).
    *   `ToxiciteCumulee(t)` : Variable continue évoluant dans le temps. Augmente avec la dose, diminue avec le temps (récupération).
*   **Variables Observées (Mesurées)** :
    *   `TauxGlobulesBlancs(t)` : Dépend de la `ToxiciteCumulee`. Plus la toxicité est haute, plus les globules blancs chutent.

**Tâche :** Implémentez ce modèle avec `Pyro`.
*   Définissez les *Priors* sur le `ProfilToxicite`.
*   Définissez la fonction de transition pour `ToxiciteCumulee`.
*   Définissez la loi d'observation pour `TauxGlobulesBlancs` (ex: distribution Normale centrée sur une valeur dépendant de la toxicité).

### 4.2. Inférence et Adaptation
Le patient "M. Dupont" a reçu sa première dose à J1. À J8, sa prise de sang révèle un taux de globules blancs anormalement bas (Neutropénie).

**Tâche :**
1.  Utilisez l'inférence (SVI ou MCMC/NUTS) pour estimer la distribution a posteriori de son `ProfilToxicite`. Est-il "Sensible" ?
2.  **Prédiction** : Si on administre la dose prévue à J21, quelle est la probabilité que ses globules blancs chutent sous le seuil critique (Danger de mort) ?
3.  **Décision** : Proposez une nouvelle dose (réduite) ou un report de date pour maintenir le risque < 5%.

**Indice Technique (Pyro) :**
Lors de l'inférence SVI, assurez-vous que les données d'entrée (doses) sont alignées avec les observations.
Si vous passez au modèle des doses futures pour lesquelles vous n'avez pas encore d'observation (ex: dose prévue à J21 mais observation seulement jusqu'à J8), Pyro va considérer les observations manquantes comme des variables latentes à inférer.
Comme votre `guide` ne couvre probablement pas ces variables (il ne couvre que le `profil`), cela provoquera une erreur.
**Solution :** Tronquez le tenseur des doses pour ne garder que l'historique correspondant aux observations réelles lors de l'étape `svi.step`.

---

## 5. Bonus : Traçabilité (Smart Contract)

Pour garantir que le protocole n'a pas été modifié à l'insu du patient, nous voulons "signer" numériquement la décision.

**Tâche :** Créez une classe `OncoContract` qui :
1.  Prend en entrée le plan de traitement final (dates + doses).
2.  Génère un Hash unique (SHA-256) de ce plan.
3.  Simule une "Signature" (ajout d'une clé privée médecin).
4.  Permet de vérifier si un plan donné correspond bien au Hash enregistré.

---

## 6. Consignes de Rendu

1.  **Notebook** : Renommez le squelette en `Nom1_Nom2_CC2_OncoPlan.ipynb`.
2.  **Code** : Le code doit être exécutable séquentiellement sans erreur. Commentez vos choix de modélisation (surtout les *priors* dans Pyro).
3.  **Analyse** : Répondez aux questions posées dans les cellules Markdown prévues à cet effet.

**Barème Indicatif (sur 20) :**
*   Ontologie & Vérification : 4 pts
*   Planification CSP (OR-Tools/Z3) : 6 pts
*   Modèle Pyro (Définition) : 4 pts
*   Inférence & Décision : 4 pts
*   Qualité du code & Bonus : 2 pts

Bon courage !