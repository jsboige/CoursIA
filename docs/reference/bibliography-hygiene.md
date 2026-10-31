# Bibliographie IA partagée

## Source canonique

Le gisement documentaire partagé du cluster est :

`G:\Mon Drive\MyIA\IA\Bibliographie IA`

Son fichier `README.md` est l'autorité opérationnelle pour la nomenclature, les rayons et la procédure d'ajout. Cette documentation du dépôt fixe l'obligation ; elle ne duplique pas un inventaire qui évolue sur GDrive.

## Quand archiver

Un agent archive une publication dès qu'il la récupère pour une lecture substantielle, l'utilise comme source ou la cite dans un notebook, une issue, une PR ou un dispatch. Une publication ne doit pas rester uniquement dans Downloads, un scratchpad ou le cache d'un outil.

Si la récupération échoue ou si l'accès est payant, l'agent le dit explicitement et indique le titre exact ainsi que le rayon de destination. Il ne fabrique ni présence locale ni preuve de lecture. Ce qu'il attribuerait à la publication ne s'écrit pas tant qu'elle n'a pas été lue : voir la clause « Lire avant d'attribuer » de la règle [bibliography-hygiene.md](../../.claude/rules/bibliography-hygiene.md).

## Procédure minimale

1. Chercher l'existant par nom d'auteur **et** mots du titre.
2. Vérifier l'identité du document sur sa première page, par exemple avec `pdftotext -f 1 -l 1`.
3. Conserver une seule copie dans le domaine principal par lequel elle sera recherchée.
4. Appliquer la nomenclature du README GDrive : `YYYY - Auteur(s) - Titre.pdf`.
5. Citer le chemin GDrive complet dans le livrable qui utilise la source.
6. Ne jamais ajouter le PDF au dépôt Git public.

Le chemin cité rend la source retrouvable par les autres machines, mais ne remplace pas une citation bibliographique dans le contenu pédagogique.

## Chemin du gisement dans une source de carnet

Un carnet donne deux choses pour une même publication : son **identifiant durable** (auteurs, année, titre, lien arXiv ou DOI) et, quand le cluster doit pouvoir rouvrir la copie sans la retélécharger, le **chemin** de cette copie dans le gisement partagé. Forme canonique, telle qu'elle s'écrit dans une cellule markdown :

`G:\Mon Drive\MyIA\IA\Bibliographie IA\<Rayon>\<YYYY - Auteur(s) - Sujet.ext>`

**Le chemin est un localisateur, pas une source.** L'identifiant durable porte l'information bibliographique et survit à un renommage ou à un déplacement du fichier ; le chemin ne vaut que tant que le gisement n'a pas bougé. Les deux se citent ensemble, jamais le chemin seul.

**Pourquoi aucun organe ne mesure ces chemins.** `scripts/notebook_tools/scan_machine_path_outputs.py` lit les **sorties** des carnets, jamais leurs sources : un chemin dans une source est un choix d'auteur, dans une sortie c'est un résidu d'exécution. Une citation de source ne déclenche donc aucun rouge — et c'est aussi pourquoi sa mise à jour, après un renommage du gisement, reste à la charge de l'auteur du carnet. Chaque rayon qui en use renvoie ici depuis son `README.md`, pour que le carnet suivant retrouve la convention au lieu de la réinventer.

## Publications, code et données

Une page d'article, un preprint et sa version publiée doivent être dédupliqués en privilégiant la version effectivement lue et citée. Les suppléments et le code accompagnant un article restent distingués de la publication.

Un dataset n'entre pas automatiquement dans le rayon des publications. Avant toute copie ou redistribution, vérifier et consigner :

- provenance et producteur ;
- licence et conditions d'utilisation ;
- droit de redistribution ;
- obligations de suppression ou de mise à jour ;
- données personnelles ou contenu sensible ;
- version et checksum.

Lorsque ces points sont indéterminés, conserver seulement la référence vers la source officielle et bloquer la redistribution. Les corpus privés, les données étudiantes et les secrets ne vont jamais dans le dépôt public ni dans la bibliographie partagée sans autorisation adaptée.

## Responsabilités dans les livrables

- **Notebook ou documentation** : citation bibliographique normale et, lorsque le travail doit être repris par le cluster, chemin canonique GDrive.
- **Issue ou PR** : nommer les sources réellement consultées et citer leur chemin complet ; qualifier preprint, manuscrit, papier évalué par les pairs ou source secondaire.
- **Audit** : vérifier la source firsthand ; la présence d'un PDF ne prouve ni sa lecture ni le claim attribué.
- **Dispatch** : fournir le chemin exact afin d'éviter un nouveau téléchargement, un doublon ou une confusion de version.

## Voir aussi

- [audit-cross-source-distillation.md](../../.claude/rules/audit-cross-source-distillation.md) — comparaison firsthand et sortie d'audit.
- [verify-before-claiming.md](../../.claude/rules/verify-before-claiming.md) — vérification avant affirmation.
- [secrets-hygiene.md](../../.claude/rules/secrets-hygiene.md) — données privées et secrets.
