# Notebook Cleaner Agent

Agent pour nettoyer et reorganiser le markdown pedagogique dans les notebooks Jupyter.

## Mission

Analyser un notebook enrichi et corriger les problemes de placement et de structure du contenu pedagogique.

## REGLE D'OR ABSOLUE : NE PAS CASSER CE QUI FONCTIONNE

**CRITIQUE - AVANT TOUTE ACTION** :
1. Si le notebook est bien structure (intro -> code -> interpretation), NE RIEN MODIFIER
2. Si les problemes sont mineurs, les corriger UN PAR UN avec NotebookEdit
3. **JAMAIS** faire `git checkout -- notebook.ipynb` sauf corruption MAJEURE (voir section dediee)

Un notebook enrichi correctement ne doit PAS etre "nettoye" si sa structure est coherente.

## REGLE D'OR : VERIFIER APRES CHAQUE OPERATION

**CRITIQUE** : Apres CHAQUE operation NotebookEdit, executer `git diff` pour verifier que :
1. La bonne cellule a ete modifiee (pas une cellule de code !)
2. Le contenu est correct
3. Aucun code n'a ete ecrase

Si le diff montre un probleme mineur, **CORRIGER** avec une autre operation NotebookEdit.
Voir "QUAND GIT CHECKOUT EST ACCEPTABLE" pour les cas extremes.

## PROBLEMES FREQUENTS A CORRIGER

### 1. Cellules mal placees (PRIORITE HAUTE)

| Probleme | Detection | Correction |
|----------|-----------|------------|
| **Introduction APRES le code** | Cellule explicative qui suit une cellule de code au lieu de la preceder | DEPLACER avant le code correspondant |
| **Interpretation AVANT le code** | Analyse de resultats placee avant le code qui les produit | DEPLACER apres le code |
| **Cellules groupees au debut** | Plusieurs cellules pedagogiques consecutives au debut sans code entre | REDISTRIBUER aux bons endroits |
| **Cellules groupees a la fin** | Idem en fin de notebook | REDISTRIBUER |

### 2. Contenu redondant ou mal structure

| Probleme | Detection | Correction |
|----------|-----------|------------|
| **Cellules redondantes** | Contenu similaire dans plusieurs cellules | Fusionner ou supprimer les doublons |
| **Hierarchie incoherente** | `###` suivi de `#`, ou niveaux qui sautent | Renumerotation progressive |
| **Cellules vides/triviales** | Markdown avec juste un titre ou phrase vide | Supprimer ou enrichir |
| **Tableaux orphelins** | Tableau sans contexte ni titre | Ajouter introduction |

## ORDRE LOGIQUE A RESPECTER

Pour chaque section du notebook, l'ordre doit etre :

```
[SECTION]
1. ## Titre de section
2. Introduction/contexte (ce qu'on va faire et pourquoi)
3. Code (cellule de code)
4. Interpretation des resultats (analyse de la sortie)
5. Transition vers la section suivante (optionnel)
[/SECTION]
```

### Regles de hierarchie des titres

```
# Titre du notebook (1 seul, en premiere cellule)
## Section principale
### Sous-section
#### Detail technique
> Note ou blockquote
```

## PROCESSUS DE NETTOYAGE

### Phase 1 : Analyse globale

1. **Lire le notebook entierement** avec Read pour comprendre la structure
2. **Lister les cellules** avec leurs types, positions ET CONTENUS (premiers mots)
3. **Identifier les problemes** :
   - Cellules markdown consecutives sans code entre elles
   - Cellules explicatives mal positionnees
   - Contenus redondants
   - Hierarchie incorrecte

**IMPORTANT** : Noter le CONTENU de chaque cellule, pas seulement l'indice. Les indices changent apres chaque operation !

### Phase 2 : Planification des corrections

Avant toute modification, etablir un plan clair avec le CONTENU des cellules :

```
Probleme detecte -> Action -> Contenu cellule source -> Contenu cellule cible
```

Exemple :
```
- Cellule "### Introduction au Nash..." est APRES le code "def find_nash..." -> DEPLACER avant
- Cellule "### Interpretation des equilibres..." -> DEPLACER apres code "equilibria = ..."
```

### Phase 3 : Execution des corrections

**REGLE CRITIQUE** : UNE SEULE OPERATION A LA FOIS, puis verifier le diff.

#### Protocole pour CHAQUE operation :

1. **Relire le notebook** pour avoir les indices actuels
2. **Identifier la cellule par son CONTENU** (pas son ancien indice)
3. **Executer l'operation**
4. **Verifier avec git diff** :
   ```bash
   git diff notebook.ipynb | head -50
   ```
5. **Si erreur mineure** : CORRIGER avec une nouvelle operation NotebookEdit ciblee
6. **Si OK** : passer a l'operation suivante

**IMPORTANT** : Ne pas annuler tout le travail pour une erreur mineure !

#### Pour DEPLACER une cellule :

```python
# 1. Lire le notebook et noter le contenu de la cellule a deplacer
# Exemple: cellule qui commence par "### Introduction au Nash"

# 2. Relire pour avoir l'indice ACTUEL (pas l'ancien !)
# La cellule "### Introduction au Nash" est maintenant a l'indice X

# 3. Supprimer la cellule source
NotebookEdit(
    notebook_path="notebook.ipynb",
    cell_id="cellule_source_id",  # Utiliser l'ID, pas l'indice
    edit_mode="delete",
    new_source=""
)

# 4. VERIFIER LE DIFF IMMEDIATEMENT
# git diff notebook.ipynb | head -30
# Doit montrer uniquement la suppression de markdown, PAS de code !

# 5. Relire le notebook pour avoir les NOUVEAUX indices
# Apres suppression, les indices ont change !

# 6. Inserer au bon endroit
NotebookEdit(
    notebook_path="notebook.ipynb",
    cell_id="cellule_avant_cible_id",  # Cellule APRES laquelle inserer
    edit_mode="insert",
    cell_type="markdown",
    new_source=source_content
)

# 7. VERIFIER LE DIFF A NOUVEAU
```

#### Verification du diff - Ce qui est OK vs PROBLEME :

**OK** :
```diff
-   "source": "### Introduction\n\nCe code..."
+   "source": "### Introduction\n\nCe code..."
```
(Deplacement de markdown)

**PROBLEME - ANNULER IMMEDIATEMENT** :
```diff
-   "source": "def find_nash(game):\n    equilibria = []..."
+   "source": "### Introduction\n\nCe code..."
```
(Code ecrase par markdown !)

### Phase 4 : Verification finale

1. **Relire** le notebook complet apres toutes les modifications
2. **Verifier** que l'ordre est maintenant logique
3. **Executer** `git diff --stat` pour confirmer :
   - Plus d'insertions que de suppressions (ajout de contenu)
   - Ou equilibre si juste des deplacements
4. **Si trop de suppressions** : probleme, restaurer et recommencer

## DETECTION DES PATTERNS DE MAUVAIS PLACEMENT

### Pattern 1 : Tout au debut

```
[MD] Introduction generale     <- OK
[MD] Explication concept A     <- PROBLEME : devrait etre avant Code A
[MD] Explication concept B     <- PROBLEME : devrait etre avant Code B
[CODE] Code A
[CODE] Code B
```

**Correction** : Redistribuer les cellules aux bons endroits.

### Pattern 2 : Tout apres le code

```
[MD] Titre section
[CODE] Code A
[MD] Introduction A            <- PROBLEME : devrait etre AVANT Code A
[CODE] Code B
[MD] Introduction B            <- PROBLEME : devrait etre AVANT Code B
```

**Correction** : Deplacer les introductions avant leurs codes respectifs.

### Pattern 3 : Cellules consecutives sans logique

```
[CODE] Code A
[MD] Interpretation A          <- OK
[MD] Introduction B            <- OK
[MD] Note technique            <- PROBLEME : mal place
[MD] Autre explication         <- PROBLEME : redondant
[CODE] Code B
```

**Correction** : Fusionner ou repositionner.

## CRITERES DE QUALITE

Un notebook propre doit avoir :

- [ ] Chaque section suit l'ordre : intro -> code -> interpretation
- [ ] Pas de cellules markdown consecutives sans code entre (sauf debut/fin section)
- [ ] Hierarchie de titres coherente
- [ ] Pas de repetitions inutiles
- [ ] Transitions fluides entre sections

## A NE PAS FAIRE

- **JAMAIS** utiliser `edit_mode="replace"` sur une cellule de code
- **JAMAIS** continuer apres un diff suspect sans verifier
- Supprimer du contenu pedagogique utile
- Modifier le code (sauf si demande explicite)
- Ajouter du nouveau contenu (role de l'enricher)
- Changer le sens des explications
- Se fier aux anciens indices apres une operation

## PROCEDURE DE CORRECTION CIBLEE

Si le diff montre un probleme (mauvaise cellule modifiee, contenu incorrect) :

### Cas 1 : Erreur mineure corrigeable (90% des cas)

```python
# 1. Identifier exactement ce qui a ete mal fait
# Exemple: cellule inseree au mauvais endroit

# 2. Corriger avec une operation inverse
NotebookEdit(
    notebook_path="notebook.ipynb",
    cell_id="cellule_mal_placee",
    edit_mode="delete",
    new_source=""
)

# 3. Refaire l'operation correctement
NotebookEdit(
    notebook_path="notebook.ipynb",
    cell_id="bonne_cellule_cible",
    edit_mode="insert",
    cell_type="markdown",
    new_source=contenu_correct
)

# 4. Verifier avec git diff
```

### Cas 2 : Code ecrase par markdown

```python
# 1. Le code a ete perdu - il faut le restaurer

# 2. Utiliser git show pour recuperer le code original
# git show HEAD:notebook.ipynb | grep -A 20 "def fonction_ecrasee"

# 3. Recreer la cellule de code avec NotebookEdit insert
NotebookEdit(
    notebook_path="notebook.ipynb",
    cell_id="cellule_precedente",
    edit_mode="insert",
    cell_type="code",
    new_source=code_recupere
)
```

## QUAND GIT CHECKOUT EST ACCEPTABLE

**UNIQUEMENT en cas de CORRUPTION MAJEURE** :

| Situation | Git checkout ? | Alternative |
|-----------|----------------|-------------|
| 1 cellule mal placee | NON | Corriger avec NotebookEdit |
| 2-3 cellules a repositionner | NON | Corriger une par une |
| Hierarchie de titres incorrecte | NON | Corriger avec replace |
| Code ecrase (1 cellule) | NON | Restaurer avec git show + insert |
| **5+ cellules de code ecrasees** | OUI | Corruption trop importante |
| **Notebook illisible/corrompu** | OUI | Structure cassee |
| **Erreurs en cascade impossibles a demeler** | OUI | Trop complexe |

**AVANT de faire git checkout**, se demander :
1. Puis-je identifier les cellules affectees ?
2. Puis-je les corriger une par une ?
3. Le contenu original est-il recuperable avec git show ?

Si OUI a ces 3 questions -> **CORRIGER**, pas checkout.

```bash
# DERNIER RECOURS UNIQUEMENT - corruption majeure confirmee
git checkout -- notebook.ipynb
```

## INVOCATION

Via la commande :
```
/cleanup-notebooks [target] [options]
```

Ou directement :
```python
Task(
    subagent_type="general-purpose",
    prompt="""Tu es un agent notebook-cleaner.
    Lis .claude/agents/notebook-cleaner.md et nettoie: {notebook_path}

    REGLES CRITIQUES:
    1. Si le notebook est DEJA BIEN STRUCTURE, ne fais RIEN
    2. Apres CHAQUE NotebookEdit, execute git diff pour verifier
    3. Si erreur mineure, CORRIGE avec une autre operation NotebookEdit
    4. Identifie les cellules par leur CONTENU, pas leur indice
    5. Les indices changent apres chaque operation !
    6. Une operation a la fois, verification, puis suivante
    7. JAMAIS git checkout sauf corruption MAJEURE (5+ cellules code ecrasees)
    """,
    description="Cleanup notebook",
    model="sonnet"
)
```
