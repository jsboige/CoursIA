# Guide Agent - Demo 2 : Références et Contexte

Ce guide est destiné aux formateurs et agents IA pour accompagner les apprenants.

## Objectifs de la démo

- Maîtriser les @-mentions pour le contexte
- Comprendre le rôle et la structure de CLAUDE.md
- Savoir personnaliser CLAUDE.md pour un projet

## Points de vigilance

### @-mentions

1. **Chemins relatifs**
   - Les @-mentions utilisent des chemins relatifs au dossier courant
   - Claude Code doit être lancé dans le bon dossier

2. **Fichiers volumineux**
   - Les très gros fichiers peuvent dépasser les limites de contexte
   - Préférer cibler des fichiers spécifiques plutôt que des dossiers entiers

3. **Fichiers binaires**
   - Les @-mentions ne fonctionnent que pour les fichiers texte
   - Images, PDFs, etc. ne peuvent pas être référencés ainsi

### CLAUDE.md

1. **Sensibilité à la casse**
   - Le fichier doit s'appeler exactement `CLAUDE.md` (majuscules)

2. **Emplacement**
   - À la racine du projet pour le contexte projet
   - Dans les sous-dossiers pour du contexte spécifique

3. **Taille recommandée**
   - Garder sous 1000 lignes idéalement
   - Trop d'informations peut noyer les instructions importantes

## Déroulé suggéré

### Phase 1 : Préparation (5 min)

1. Vérifier que le projet exemple est accessible
2. Guider la copie vers le workspace
3. Vérifier la structure des fichiers

### Phase 2 : @-mentions pratique (15 min)

Faire tester chaque type de @-mention :

```bash
# 1. Fichier unique
@src/main.py Que fait ce fichier ?

# 2. Dossier
@src/ Quelle est la structure ?

# 3. Multiple
@src/utils.py @src/main.py Comment ces fichiers interagissent ?

# 4. Pattern
@tests/*.py Quels tests existent ?
```

### Phase 3 : Génération CLAUDE.md (10 min)

1. Démontrer `/init`
2. Examiner le fichier généré ensemble
3. Identifier les sections à améliorer

### Phase 4 : Personnalisation (15 min)

Guider l'ajout de sections :
- Conventions spécifiques
- Instructions pour Claude
- Commandes du projet

### Phase 5 : Validation (5 min)

Tester que Claude utilise bien le contexte CLAUDE.md.

## Réponses aux questions fréquentes

### "Quelle est la différence entre @-mention et copier-coller le code ?"

Les @-mentions :
- Sont plus rapides à utiliser
- Maintiennent le contexte du chemin
- Permettent de référencer plusieurs fichiers facilement
- Sont mises à jour si vous relancez la commande

### "CLAUDE.md est-il versionné avec le projet ?"

Oui, c'est recommandé :
- Permet à toute l'équipe de bénéficier du contexte
- Évolue avec le projet
- Exception : informations sensibles dans `.claude/settings.local.json`

### "Peut-on avoir plusieurs CLAUDE.md ?"

Oui, avec une hiérarchie :
```
projet/
├── CLAUDE.md           # Contexte global projet
├── src/
│   └── CLAUDE.md       # Contexte spécifique src/
└── tests/
    └── CLAUDE.md       # Contexte spécifique tests/
```

### "Que mettre dans les instructions pour Claude ?"

Exemples d'instructions utiles :
- Style de code préféré
- Librairies à utiliser/éviter
- Patterns architecturaux du projet
- Format de documentation attendu

## Critères de validation

L'apprenant a réussi cette démo si :

- [ ] Sait utiliser `@fichier` et `@dossier/`
- [ ] A généré un CLAUDE.md avec `/init`
- [ ] A personnalisé le CLAUDE.md avec au moins 3 sections
- [ ] Comprend que CLAUDE.md est automatiquement lu
- [ ] A testé que Claude utilise les instructions de CLAUDE.md

## Structure recommandée du CLAUDE.md

```markdown
# Nom du Projet

## Description
[2-3 phrases sur le projet]

## Stack technique
[Liste des technologies]

## Structure
[Arborescence simplifiée]

## Conventions
[Nommage, documentation, etc.]

## Commandes
[Build, test, run, etc.]

## Instructions pour Claude
[Directives spécifiques]
```

## Erreurs courantes

### Erreur : "@fichier introuvable"

**Cause** : Mauvais chemin ou mauvais dossier courant

**Solution** :
1. Vérifier avec `ls` que le fichier existe
2. Utiliser le chemin relatif correct
3. Relancer Claude dans le bon dossier

### Erreur : "CLAUDE.md ignoré"

**Cause** : Fichier mal nommé ou mauvais emplacement

**Solution** :
1. Vérifier le nom exact (majuscules)
2. Vérifier l'emplacement (racine projet)
3. Vérifier le contenu Markdown valide

### Erreur : "Contexte trop long"

**Cause** : Trop de fichiers référencés

**Solution** :
1. Réduire le nombre de @-mentions
2. Cibler des fichiers plus petits
3. Utiliser des patterns plus spécifiques

## Ressources pour le formateur

- [Memory & Project Files](https://docs.anthropic.com/en/docs/claude-code/memory)
- [Complete Guide to CLAUDE.md](https://www.builder.io/blog/claude-md-guide)
