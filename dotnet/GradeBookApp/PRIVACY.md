# Politique de confidentialité — GradeBookApp

> Notice RGPD du **moteur de notation** `GradeBookApp/`. Générique et agnostique de
> l'établissement : aucun nom d'étudiant, aucune adresse e-mail, aucune note réelle ne
> figure dans ce document. Les exemples sont fictifs.
>
> Cette notice décrit la **politique de traitement des données à caractère personnel**
> que le moteur met en œuvre, et les **obligations d'usage** qui incombent à l'enseignant
> qui l'exécute. Elle complète [`README.md`](README.md) (architecture) et
> [`configs/README.md`](configs/README.md) (modèle GDrive).

## 1. Périmètre

`GradeBookApp` est un moteur de calcul et de gestion de notes. Il **lit** des évaluations
collectées (Google Forms/Sheets) et des listes d'étudiants, **calcule** des moyennes par
évaluation par les pairs et **produit** un rapport de notes (fichier `.xlsx`).

Cette notice couvre les données personnelles **étudiantes** traitées par le moteur. Elle ne
couvre pas les données que l'établissement traiterait par ailleurs dans ses propres systèmes
(SCOLA, apogée, ENT) — seul l'usage fait par `GradeBookApp` est décrit ici.

## 2. Responsable du traitement, base légale, finalité

- **Responsable du traitement** : l'enseignant qui exécute le moteur sur ses propres données
  de cours. Le moteur n'est qu'un outil ; la responsabilité du traitement demeure à
  l'enseignant.
- **Base légale** (RGPD art. 6) : **mission d'intérêt public** (art. 6 § 1 e) dans le cadre
  de l'évaluation pédagogique, ou, le cas échéant, l'**obligation légale** de notation. La
  finalité est strictement **pédagogique** : calcul de notes, évaluation par les pairs,
  production du rapport de semestre.
- **Finalité unique** : notation et pilotage pédagogique du cours concerné. **Aucune
  finalité commerciale, profilage ou publicitaire**.

## 3. Données traitées

Le moteur traite, sur les étudiants évalués :

| Catégorie | Exemples (fictifs) | Origine |
|-----------|--------------------|---------|
| **Identité** | prénom, nom | Liste d'étudiants (roster) |
| **Coordonnées** | adresse e-mail (collectée via le formulaire d'évaluation) | Google Forms |
| **Contexte pédagogique** | groupe, sujet de projet libre | Formulaire / roster |
| **Évaluation par les pairs** | notes par critère, points positifs, points négatifs, recommandations | Google Forms |
| **Métadonnées** | horodatage de la réponse | Google Forms |

**Aucune donnée sensible** (santé, opinions, origine, etc.) n'est collectée par le moteur.
Si un champ libre d'évaluation en contenait par accident, il doit être supprimé à la lecture.

## 4. Architecture et localisation

- **Le moteur est public** (ce dépôt) mais **ne contient aucune donnée étudiante**.
- **Les configurations et les données par cohorte sont privées** et vivent sur Google Drive,
  hors dépôt : `…\Formation\<établissement>\<année>\grading\`. Le moteur résout ces chemins
  via `COURSIA_ROOT` (cf. [`configs/README.md`](configs/README.md)).
- **Aucune transmission réseau vers un service externe n'est effectuée par le moteur** : le
  moteur ne fait aucun appel HTTP, aucune intégration OpenAI/Anthropic, aucune télémétrie.
  Vérifiable dans le code : aucune dépendance `requests`/`httpx`/`openai`/`anthropic`. Les
  données lues (CSV GDrive) et écrites (`.xlsx` local) restent sur le poste de l'enseignant.

## 5. Minimisation et pseudonymisation

- **Minimisation** : les champs chargés sont limités à ce que le calcul exige (cf.
  `EvaluationRecord`, `StudentRecord` : identité, contexte, notes, commentaires
  d'évaluation). Les colonnes non utilisées par une épreuve ne sont pas chargées.
- **Pseudonymisation recommandée** : remplacer l'**e-mail** par un **identifiant
  pseudonymisé** (ex. hash du couple `nom+date-de-naissance`, ou identifiant pédagogique de
  l'établissement) **dès que possible** dans le pipeline. Tant que l'e-mail est nécessaire au
  rapprochement d'identité (§ 6), il est conservé ; il doit être **supprimé du rapport final**
  sauf besoin documenté.

## 6. Fuzzy matching d'identité — gate et validation humaine

Le rapprochement entre une évaluation (saisie libre d'un nom/groupe) et un étudiant connu
utilise une **correspondance floue** (`rapidfuzz`). Deux seuils sont en vigueur dans le code :

| Seuil | Rôle | Valeur par défaut |
|-------|------|-------------------|
| `SIMILARITY_THRESHOLD` | identification du professeur parmi les évaluateurs | `80` |
| `group_match_threshold` | rattachement d'une évaluation à un groupe/projet étudiant | `90` (surchargeable par épreuve) |

**Règles de gouvernance (politique, à respecter par l'enseignant) :**

1. **Au-dessus du seuil** : correspondance acceptée automatiquement.
2. **Dans la bande d'ambiguïté** — score dans `[seuil - AMBIGUITY_MARGIN, seuil[`,
   soit 80–90 % aux valeurs par défaut : **validation humaine obligatoire**. Le
   rapprochement n'est **pas** crédité, il est consigné, et le run est déclaré
   **non final** tant que l'enseignant n'a pas arbitré.
3. **Journalisation** : les rapprochements de cette bande sont écrits automatiquement
   dans un journal structuré JSON (`ambiguites_rapprochement.json` par défaut),
   **sans donnée nominative** — condensé SHA-256 tronqué des deux libellés comparés,
   score, seuil et marge applicables (cf §5).
4. **Procédure en cas de confusion entre deux étudiants** : ni l'un ni l'autre n'est
   crédité automatiquement ; l'enseignant tranche, et l'incident est tracé.

> **État d'implémentation.** L'enforcement est en place (issue #8606).
>
> | Mécanisme | Emplacement |
> |---|---|
> | Bande d'ambiguïté nommée et configurable | `gradebook.py` : `AMBIGUITY_MARGIN` (défaut `10`) |
> | Journal structuré pseudonymisé | `gradebook.py` : `AmbiguityJournal`, actif par défaut |
> | Gate de sortie | `run_grading.py` : code de retour `2` (`EXIT_AMBIGUITIES_PENDING`) tant que des ambiguïtés subsistent ; `--allow-ambiguous` requis pour produire le rapport malgré tout |
> | Couverture de test | `test_fuzzy_match_group.py` (dont la confusion entre deux patronymes proches, règle 4) |
>
> **Décision de conception.** Le gate ne change **aucune décision de rapprochement** :
> un score sous le seuil reste un refus. Ce qui change est que le run en porte la trace
> et ne peut plus produire un rapport présenté comme final sans arbitrage — un
> avertissement dans les logs pouvait n'être jamais lu.
>
> **Défaut corrigé au passage.** Le cas d'inclusion simple (`fuzzy_match_group`, Cas 4)
> court-circuitait le seuil : un libellé inclus dans un autre était accepté même à
> `threshold=100`. Sur des patronymes proches (`… - dupont` inclus dans `… - dupontt`),
> l'un des deux étudiants était donc crédité automatiquement, en violation de la règle 4
> ci-dessus. L'inclusion exige désormais que le reliquat commence sur une frontière de
> token (séparateur), ce qui préserve le cas visé (« projet alpha » ⊂ « projet alpha -
> groupe 3 ») et ferme la confusion de noms.

## 7. Conservation et suppression en fin de semestre

- **Durée de conservation** : les données sont conservées **le temps du semestre** et de la
  période de **réclamation des notes** (typiquement jusqu'à la fin de la session de rattrapage
  / délai légal de contestation de l'établissement).
- **Suppression** : à la clôture du semestre, les **fichiers nominatifs intermédiaires**
  (CSV d'évaluations bruts contenant e-mails + commentaires, rapports de notes détaillés)
  sont **supprimés**. Ne sont conservés, si l'établissement l'exige, que les **résultats
  agrégés strictement nécessaires** à l'archive pédagogique (note finale, sans commentaire
  libre nominatif).
- **Procédure** : l'enseignantarchive la promotion `…\<année>\` de GDrive une fois le délai
  écoulé, puis supprime les fichiers sources.

## 8. Destinataires et séparation des rôles

- **Destinataires** : le rapport final est destiné à l'enseignant et, le cas échéant, au
  secrétariat pédagogique de l'établissement pour saisie officielle. Les **commentaires
  libres d'évaluation par les pairs ne sont jamais communiqués aux étudiants évalués** (règle
  de confiance du grading collégial).
- **Séparation des rôles** :
  - **Enseignant** : exécute le moteur, valide les correspondances ambiguës, produit et
    signe le rapport.
  - **Administrateur (secrétariat)** : reçoit le rapport final agrégé, n'a pas accès aux
    commentaires libres ni aux fichiers sources bruts.

## 9. LLM externes — interdiction de PII nominative

Le moteur **n'envoie aucune donnée à un LLM externe** (aucune intégration ; cf. § 4).
Toutefois, l'enseignant peut être amené à solliciter un LLM (assistant IA, service tiers)
pour **analyser** un rapport ou des commentaires. Règle absolue :

> **Il est interdit d'envoyer à un LLM externe des données nominatives**
> (noms, e-mails, identifiants étudiants, ou commentaires libellés permettant de
> réidentifier un étudiant).

Tout envoi à un LLM doit être **préalablement pseudonymisé** (§ 5) et limité à des
**agrégats ou motifs génériques** (« tendance des retours sur le critère X »).

## 10. Droits des personnes concernées

Conformément aux articles 15 à 20 du RGPD, un étudiant peut exercer, auprès de
l'enseignant responsable :

- un **droit d'accès** aux données le concernant traitées par le moteur,
- un **droit de rectification** (identité, note en cas d'erreur),
- un **droit à l'effacement** à l'issue du délai de conservation (§ 7),
- un **droit d'opposition** pour motif légitime.

Les demandes sont traitées par l'enseignant responsable du cours. Le moteur ne gère pas de
compte utilisateur : il n'y a pas de profil à « fermer ».

## 11. Mesures techniques

- **Stockage** : données sur Google Drive privé de l'enseignant (accès limité au compte de
  l'enseignant).
- **Pas d'exfiltration réseau** : aucune dépendance d'appel sortant dans le moteur.
- **Pas de données dans le dépôt public** : le moteur et les configs modèles sont publics ;
  les données réelles ne transitent jamais par le dépôt (cf. [`configs/README.md`](configs/README.md)).
- **Réversibilité** : le moteur lit/écrit des fichiers (`CSV` → `XLSX`) ; suppression = suppression
  des fichiers. Aucune base de données persistante à purger.

---

**Statut** : politique de référence (issue #8054). Ajournez ce document si le moteur évolue
(fuzzy-match enforced, nouvelles sources de données, intégration réseau). Voir aussi le
contexte PII historique et la couche policy manquante référencée dans l'issue.
