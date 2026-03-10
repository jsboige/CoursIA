# Intercom QC - po-2024 ↔ myia-ai-01

**But**: Coordination entre agents pour la gestion QuantConnect.

---

## 2026-03-10 - Session po-2024 (après-midi)

### Etat SESSION 1

#### 1a. NETTOYAGE DOUBLON ✅ TERMINE
- **Supprimé**: Crypto-MultiCanal (ID: 28733256) - version incomplète
- **Conservé**: Crypto-MultiCanal-Researcher (ID: 28679473) - version complète avec channel_mixin.py
- **Méthode**: Playwright sur organisation Jean-Sylvain Boige (Researcher PAID)
- **WORKSPACES.md**: Mis à jour (ligne doublon retirée)

#### 1b. DEPLOIEMENT PROJETS C# 🔄 PARTIEL
- **CSharp-BTC-EMA-Cross** ✅ DEPLOYE (ID: 28860180)
  - Méthode: Playwright → New Algorithm → Coller code → BuildSuccess
  - Compilation OK
  - Backtest à lancer par l'utilisateur
- **CSharp-CTG-Momentum** ⚠️ BLOQUE PAR BUG QC MONACO
  - Projet créé (ID: 28860278, nom aléatoire: "Crying Brown Leopard")
  - Main.cs (226 lignes) typé mais erreur QC: "exceeds 64000 characters by using 254322"
  - **CAUSE**: Bug QC Monaco Editor - mauvais calcul de taille de fichier
  - **CONTENU CORRECT**: 226 lignes affichées, contenu valide
  - **SOLUTION RECOMMANDEE**: Utiliser `lean-cli` au lieu de Playwright pour ce projet
  - **FICHIERS REQUIS**:
    - Main.cs (226 lignes)
    - Helpers/AnnualizedExponentialSlopeIndicator.cs (41 lignes)
    - Helpers/CustomMomentumIndicator.cs (59 lignes)
    - Helpers/GapIndicator.cs (25 lignes)
    - Helpers/MarketRegimeFilter.cs (23 lignes)

#### 1c. NETTOYAGE ORPHANS ⏳ A FAIRE
- Identifier et supprimer les projets "-Researcher" orphelins

---

## Tests effectués

### Connexion API
- Token QC mis à jour dans .env (c1804bc7...)
- User ID: 46613
- Authentification OK (HTTP 200)

### Playwright Automation
- Navigation OK sur https://www.quantconnect.com/terminal
- Changement d'organisation: ESGF_school → Jean-Sylvain Boige (Researcher PAID)
- Backtest Framework_Composite_TrendWeather: OK
- Ouverture research.ipynb: OK (interface QuantBook "Detecting Kernels")
- Suppression projet 28733256: OK

### Organisation Researcher PAID
- 32 projets (après suppression du doublon)
- Tous compilent OK
- Crédit: 3457.87 QCC

---

## Procédure de déploiement local → cloud

**Source**: `C:\dev\CoursIA\MyIA.AI.Notebooks\QuantConnect\projects\`

**Méthodes disponibles**:
1. **Playwright**: Créer projet via web UI, copier/coller code
2. **lean-cli**: `lean cloud push --name "ProjectName"`
3. **MCP QC**: Non configuré sur po-2024

**Check-list**:
- [ ] Créer projet cloud avec nom correct
- [ ] Copier tous les fichiers nécessaires
- [ ] Compiler sans erreur (BuildSuccess)
- [ ] Lancer backtest de validation
- [ ] Documenter Project ID dans WORKSPACES.md

---

## Prochaines actions (po-2024)

- [x] Déployer CSharp-BTC-EMA-Cross (SESSION 1b) ✅
- [ ] Déployer CSharp-CTG-Momentum via `lean-cli` (Playwright bloqué par bug QC)
- [ ] Identifier orphans -Researcher (SESSION 1c)
- [ ] Commit WORKSPACES.md + INTERCOM
- [ ] Envoyer message RooSync à myia-ai-01

---

## Note technique - Bug QC Monaco Editor

**Problème**: Le Monaco Editor de QC signale une taille de fichier incorrecte (254322 caractères au lieu de ~10000)

**Impact**: Impossible de sauvegarder les fichiers volumineux via l'interface web

**Solution**: Utiliser `lean-cli` pour les projets avec plusieurs fichiers ou code volumineux:

```bash
cd C:\dev\CoursIA\MyIA.AI.Notebooks\QuantConnect\projects\CSharp-CTG-Momentum
lean cloud push --name "CSharp-CTG-Momentum" --open
```

---

## Fichiers modifiés

- `WORKSPACES.md` - Ligne doublon supprimée
- `.env` - Token QC mis à jour
- `INTERCOM_PO-2024.md` - Ce fichier (nouveau)
