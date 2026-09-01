# Bibliographie IA partagée

## Source canonique

Le gisement documentaire partagé du cluster est :

`G:\Mon Drive\MyIA\IA\Bibliographie IA`

Son fichier `README.md` est l'autorité opérationnelle pour la nomenclature, les rayons et la procédure d'ajout. Cette documentation du dépôt fixe l'obligation ; elle ne duplique pas un inventaire qui évolue sur GDrive.

## Quand archiver

Un agent archive une publication dès qu'il la récupère pour une lecture substantielle, l'utilise comme source ou la cite dans un notebook, une issue, une PR ou un dispatch. Une publication ne doit pas rester uniquement dans Downloads, un scratchpad ou le cache d'un outil.

Si la récupération échoue ou si l'accès est payant, l'agent le dit explicitement et indique le titre exact ainsi que le rayon de destination. Il ne fabrique ni présence locale ni preuve de lecture.

## Procédure minimale

1. Chercher l'existant par nom d'auteur **et** mots du titre.
2. Vérifier l'identité du document sur sa première page, par exemple avec `pdftotext -f 1 -l 1`.
3. Conserver une seule copie dans le domaine principal par lequel elle sera recherchée.
4. Appliquer la nomenclature du README GDrive : `YYYY - Auteur(s) - Titre.pdf`.
5. Citer le chemin GDrive complet dans le livrable qui utilise la source.
6. Ne jamais ajouter le PDF au dépôt Git public.

Le chemin cité rend la source retrouvable par les autres machines, mais ne remplace pas une citation bibliographique dans le contenu pédagogique.

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
