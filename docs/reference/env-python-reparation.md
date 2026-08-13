# Environnement Python — REPARER, ne JAMAIS contourner (detail)

Resume operationnel : CLAUDE.md section F.

**Regle user 2026-05-06 (incident scipy DLL/sklearn force-reinstall)** : un environnement Python degrade ne se contourne **jamais** par delegation, fallback ou skip. On repare **coute que coute**, en demandant un UAC user au besoin pour les operations privilegiees.

> **macOS / Linux** : les mode d'echec Python different de Windows (pas de DLL locking au sens Windows, pas d'UAC, pas de Defender quarantine). Le workflow de reparation est le meme en esprit (cleanup `~xxx/` + force-reinstall + verifier l'import), mais les commandes shells different. Cf la section **[Reparation sous macOS / Linux](#reparation-sous-macos--linux)** ci-dessous. Pour le setup d'un poste contributeur Mac/Linux, cf [kernels-runtime.md](kernels-runtime.md) et le doc `setup-linux-macos.md` (a venir, Epic #10643).

---

## Symptomes red-flag

- `ModuleNotFoundError` apres install qui se dit "Successfully installed"
- `ImportError: DLL load failed` (typiquement scipy, numpy, torch CUDA)
- `Access is denied` sur force-reinstall (fichier locke par un process Python)
- Distributions corrompues prefixees `~` (ex: `~cipy/`, `~umpy/`) dans `site-packages`
- Conflits Python 3.12 vs 3.14 vs 3.13 dans `which pip` vs `python --version`
- `pip list` montre le paquet mais `python -c "import pkg"` echoue

---

## Workflow de reparation obligatoire

1. **Identifier l'env vise** (Python systeme vs **env Conda dedie** — voir liste ci-dessous, **utiliser le bon env d'abord** plutot que reparer le mauvais)
2. **Lister les processes Python actifs** (`Get-Process python*`) qui pourraient locker des DLLs, killer si necessaire
3. **Cleanup distributions corrompues** (`~xxx/` dirs dans site-packages) via `Remove-Item -Recurse -Force`
4. **Force-reinstall** avec `python -m pip install --force-reinstall <pkg>` (assure le bon Python)
5. **Si Access denied persiste** → demander UAC user (executer `Start-Process powershell -Verb RunAs ...`) ou desactivation antivirus temporaire
6. **Tester import end-to-end** avant de relancer le job (`python -c "import scipy; import sklearn; print(OK)"`)

---

## Anti-patterns interdits

- Skip de l'env local et delegation a un agent quand le user a explicitement demande l'execution locale
- Workarounds genre "je passe a un autre env" ou "j'ignore le warning"
- Reinstall en boucle sans cleanup des residus `~xxx/`
- Continuer a importer un module en silencant les exceptions (`except Exception: pass`)
- Modifier `PYTHONPATH` pour pointer vers un env autre que celui invoque par `python.exe` actuel
- "Ca marche en dev mais pas en prod" sans diagnostic precis de la divergence d'env

---

## Envs Conda dedies sur ai-01 (utiliser AVANT de toucher Python systeme)

| Env | Usage | Path |
|-----|-------|------|
| `coursia-ml-training` | **ML training (PyTorch CUDA, sklearn, scipy, hmmlearn)** | `C:\Users\MYIA\miniconda3\envs\coursia-ml-training` |
| `mcp-jupyter` | MCP Jupyter server | `C:\Users\MYIA\miniconda3\envs\mcp-jupyter` |
| `epita_symbolic_ai` | EPITA SymbolicAI series | `C:\Users\MYIA\.conda\envs\epita_symbolic_ai` |

Pour `train_moe.py`, `train_lstm.py`, `train_mamba.py` etc. : **toujours** activer `coursia-ml-training` :

```powershell
& "C:\Users\MYIA\miniconda3\envs\coursia-ml-training\python.exe" train_lstm.py
# ou
conda activate coursia-ml-training
python train_lstm.py
```

Liste complete via `conda env list`.

---

## Cas particuliers

### Cas A : Distribution corrompue `~xxx/`

```powershell
$site = & python -c "import site; print(site.getsitepackages()[0])"
Get-ChildItem $site -Directory | Where-Object Name -like "~*" | Remove-Item -Recurse -Force
python -m pip install --force-reinstall <pkg>
```

### Cas B : DLL locked par process actif

```powershell
Get-Process python* | Stop-Process -Force
# Verifier kernels Jupyter ouverts dans VS Code/notebooks et les fermer
python -m pip install --force-reinstall <pkg>
```

### Cas C : Access Denied persistant

1. Verifier que Defender n'a pas mis le fichier en quarantaine
2. Demander UAC user avec elevation : `Start-Process powershell -Verb RunAs -ArgumentList "-c", "python -m pip install --force-reinstall <pkg>"`
3. En dernier recours : creer un nouvel env Conda et reinstaller from scratch

### Cas D : Multi-Python confusion

```powershell
where.exe python  # voit-on plusieurs ?
python --version
python -c "import sys; print(sys.executable)"  # qui est REELLEMENT execute ?
```

Forcer le bon Python : `& "<path-complet>/python.exe" -m pip install ...` au lieu de `python -m pip ...`.

---

## Reference incident

**2026-05-06** : agent a tente force-reinstall sklearn sans cleanup prealable `~xxx/` residues + sans tuer les processes Python qui lockaient scipy DLL. 3 cycles d'install "Successfully installed" suivis de `ImportError: DLL load failed` au runtime. Resolution : `Get-Process python* | Stop-Process` + cleanup `~scipy/` + reinstall force = SUCCESS.

**Lecon** : la complaisance "ca devrait marcher cette fois" est l'ennemi #1 d'un env Python sain. Diagnostiquer le pourquoi avant le comment.

---

## Reparation sous macOS / Linux

Le workflow de reparation est **le meme en esprit** que sous Windows (identifier l'env, tuer les processes lockant les fichiers, nettoyer les distributions corrompues, force-reinstall, tester l'import). Les differences : pas de DLL-locking au sens Windows (un fichier en cours d'execution reste renommable/supprimable sous Linux/macOS), pas d'UAC (elevation via `sudo`), pas de Defender (pas de quarantine silencieuse). Pour le setup du poste, cf [kernels-runtime.md](kernels-runtime.md).

### Workflow equivalent

1. **Identifier l'env vise** : `which python && python --version` (ne pas reparer le mauvais interpreteur). Preferer un env Conda dedie.
2. **Lister/killer les processes Python actifs** qui pourraient locker des fichiers ouverts :
   ```bash
   ps aux | grep -i "[p]ython"        # lister (les crochets evitent de matcher grep lui-meme)
   pkill -f "python.*train_"          # killer par motif ; ou kill -9 <PID>
   ```
3. **Cleanup distributions corrompues** (`~xxx/` dirs dans site-packages) :
   ```bash
   site=$(python -c "import site; print(site.getsitepackages()[0])")
   rm -rf "$site"/~*                   # retirer les residus ~cipy/, ~umpy/ etc.
   python -m pip install --force-reinstall <pkg>
   ```
4. **Si permission refusee** (ecriture dans un env systeme) → elevation `sudo` **ou, preferable**, utiliser un env Conda/venv utilisateur (ne jamais `sudo pip` qui casse le Python systeme) :
   ```bash
   sudo python -m pip install --force-reinstall <pkg>   # DERNIER RECOURS sur un env systeme
   # Prefere : creer/reutiliser un env utilisateur
   conda create -n repair python=3.12 -y && conda activate repair
   ```
5. **Tester import end-to-end** avant de relancer le job :
   ```bash
   python -c "import scipy, sklearn; print('OK')"
   ```

### Cas particuliers equivalents

- **Cas A (distribution corrompue `~xxx/`)** : `rm -rf "$site"/~*` (cf workflow step 3). Les prefixes `~` apparaissent aussi sous Linux/macOS quand un install interrompu laisse un dossier renomme.
- **Cas B (fichier occupe)** : contrairement a Windows (DLL locked = Access denied), Linux/macOS permettent de supprimer un fichier en cours d'usage (l'inode persiste pour le process qui l'a ouvert, mais le nom disparait). Le `ImportError` vient alors d'un **module ghost** : `pkill -f python` puis reinstaller.
- **Cas C (permission refusee)** : `sudo` au lieu de `Start-Process -Verb RunAs`. **Jamais `sudo pip install`** sur le Python systeme (casse le gestionnaire de paquets OS) — toujours `sudo` sur le Python cible explicite, ou mieux un env utilisateur.
- **Cas D (multi-Python)** : `which -a python python3` au lieu de `where.exe python` ; `python -c "import sys; print(sys.executable)"` identique. Forcer l'interpreteur explicite : `/chemin/vers/python -m pip install ...`.

### Activation Conda (bash/zsh au lieu de PowerShell)

Sur macOS/Linux, `conda activate` exige un `conda init` prealable (une fois) du shell :

```bash
conda init bash        # ou: conda init zsh (macOS default)
# relancer le shell, puis :
conda activate coursia-ml-training     # (env cree localement, nom libre sous Mac/Linux)
python train_lstm.py
```

---

## References connexes

- [.claude/rules/genai-config.md](../../.claude/rules/genai-config.md) — Env GenAI Docker
- [kernels-runtime.md](kernels-runtime.md) — Inventaire kernels par machine
- [docs/regles-validation-detail.md](regles-validation-detail.md) — Regle H.2 (tous agents installent l'env complet)
