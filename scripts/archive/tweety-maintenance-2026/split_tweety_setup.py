#!/usr/bin/env python3
"""Script pour splitter les cellules monolithiques de Tweety-1-Setup.ipynb"""
import json
from pathlib import Path

# Lire le notebook
notebook_path = Path("MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-1-Setup.ipynb")
with open(notebook_path, 'r', encoding='utf-8') as f:
    nb = json.load(f)

print(f"Structure actuelle: {len(nb['cells'])} cellules")

# Nouvelles cellules a inserer apres l'index 10 (configuration de base)
new_cells = [
    # Cellule markdown Clingo
    {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "#### 1.5.1 Clingo - Solveur ASP (Answer Set Programming)\n",
            "\n",
            "**Clingo** est le solveur ASP de reference du projet [Potassco](https://potassco.org/). ",
            "Il combine le grounder *gringo* et le solveur *clasp*.\n",
            "\n",
            "**Utilisation dans Tweety** :\n",
            "- `lp.asp.reasoner.ClingoSolver` : Raisonnement ASP\n",
            "- Support des programmes avec defauts et contraintes d'integrite\n",
            "\n",
            "**Installation** : Si non present, telechargement automatique depuis GitHub."
        ]
    },
    # Cellule code Clingo
    {
        "cell_type": "code",
        "metadata": {},
        "source": [
            "# === Configuration de Clingo ===\n",
            "print(\"=== 1. Configuration de Clingo ===\")\n",
            "\n",
            "clingo_dir = EXT_TOOLS_DIR / \"clingo\"\n",
            "clingo_dir.mkdir(exist_ok=True)\n",
            "clingo_exe = clingo_dir / (\"clingo.exe\" if system == \"Windows\" else \"clingo\")\n",
            "\n",
            "# Verifier si clingo est deja present\n",
            "clingo_in_path = shutil.which(\"clingo\") or shutil.which(\"clingo.exe\")\n",
            "if clingo_in_path:\n",
            "    EXTERNAL_TOOLS[\"CLINGO\"] = clingo_in_path\n",
            "    print(f\"  OK Clingo trouve dans PATH: {clingo_in_path}\")\n",
            "elif clingo_exe.exists():\n",
            "    EXTERNAL_TOOLS[\"CLINGO\"] = str(clingo_exe.resolve())\n",
            "    print(f\"  OK Clingo deja present: {clingo_exe}\")\n",
            "else:\n",
            "    # Telecharger automatiquement\n",
            "    print(\"  Telechargement de Clingo...\")\n",
            "    clingo_version = \"5.4.0\"\n",
            "    \n",
            "    if system == \"Windows\":\n",
            "        clingo_url = f\"https://github.com/potassco/clingo/releases/download/v{clingo_version}/clingo-{clingo_version}-win64.zip\"\n",
            "        clingo_archive = clingo_dir / \"clingo.zip\"\n",
            "        try:\n",
            "            urllib.request.urlretrieve(clingo_url, clingo_archive)\n",
            "            with zipfile.ZipFile(clingo_archive, 'r') as zip_ref:\n",
            "                zip_ref.extractall(clingo_dir)\n",
            "            for exe in clingo_dir.rglob(\"clingo.exe\"):\n",
            "                shutil.move(str(exe), str(clingo_exe))\n",
            "                EXTERNAL_TOOLS[\"CLINGO\"] = str(clingo_exe.resolve())\n",
            "                print(f\"  OK Clingo installe: {clingo_exe}\")\n",
            "                break\n",
            "            clingo_archive.unlink(missing_ok=True)\n",
            "            for d in clingo_dir.glob(\"clingo-*\"):\n",
            "                if d.is_dir(): shutil.rmtree(d, ignore_errors=True)\n",
            "        except Exception as e:\n",
            "            print(f\"  Erreur telechargement Clingo: {e}\")\n",
            "    elif system == \"Linux\":\n",
            "        import tarfile\n",
            "        clingo_url = f\"https://github.com/potassco/clingo/releases/download/v{clingo_version}/clingo-{clingo_version}-linux-x86_64.tar.gz\"\n",
            "        clingo_archive = clingo_dir / \"clingo.tar.gz\"\n",
            "        try:\n",
            "            urllib.request.urlretrieve(clingo_url, clingo_archive)\n",
            "            with tarfile.open(clingo_archive, \"r:gz\") as tar:\n",
            "                tar.extractall(path=clingo_dir)\n",
            "            for exe in clingo_dir.rglob(\"clingo\"):\n",
            "                if exe.is_file():\n",
            "                    shutil.move(str(exe), str(clingo_exe))\n",
            "                    os.chmod(clingo_exe, stat.S_IRWXU | stat.S_IRGRP | stat.S_IXGRP)\n",
            "                    EXTERNAL_TOOLS[\"CLINGO\"] = str(clingo_exe.resolve())\n",
            "                    print(f\"  OK Clingo installe: {clingo_exe}\")\n",
            "                    break\n",
            "            clingo_archive.unlink(missing_ok=True)\n",
            "        except Exception as e:\n",
            "            print(f\"  Erreur installation Clingo: {e}\")"
        ],
        "outputs": [],
        "execution_count": None
    },
    # Cellule markdown SPASS
    {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "#### 1.5.2 SPASS - Prouveur de Logique Modale\n",
            "\n",
            "**SPASS** est un prouveur automatique de theoremes pour la logique du premier ordre ",
            "avec support pour la logique modale.\n",
            "\n",
            "**Utilisation dans Tweety** :\n",
            "- `logics.ml.reasoner.SPASSMlReasoner` : Raisonnement en logique modale (Section 2.4)\n",
            "\n",
            "**Note** : Sans SPASS, `SimpleMlReasoner` peut bloquer indefiniment. ",
            "SPASS est donc fortement recommande pour les notebooks sur la logique modale."
        ]
    },
    # Cellule code SPASS
    {
        "cell_type": "code",
        "metadata": {},
        "source": [
            "# === Configuration de SPASS ===\n",
            "print(\"=== 2. Configuration de SPASS ===\")\n",
            "\n",
            "spass_dir = EXT_TOOLS_DIR / \"spass\"\n",
            "spass_dir.mkdir(exist_ok=True)\n",
            "spass_exe = spass_dir / (\"SPASS.exe\" if system == \"Windows\" else \"SPASS\")\n",
            "\n",
            "spass_in_path = shutil.which(\"SPASS\") or shutil.which(\"SPASS.exe\")\n",
            "if spass_in_path:\n",
            "    EXTERNAL_TOOLS[\"SPASS\"] = spass_in_path\n",
            "    print(f\"  OK SPASS trouve dans PATH: {spass_in_path}\")\n",
            "elif spass_exe.exists():\n",
            "    EXTERNAL_TOOLS[\"SPASS\"] = str(spass_exe.resolve())\n",
            "    print(f\"  OK SPASS deja present: {spass_exe}\")\n",
            "else:\n",
            "    if system == \"Windows\":\n",
            "        print(\"  Telechargement de SPASS pour Windows...\")\n",
            "        spass_url = \"https://www.spass-prover.org/download/binaries/spass30windows.exe\"\n",
            "        try:\n",
            "            urllib.request.urlretrieve(spass_url, spass_exe)\n",
            "            if spass_exe.exists():\n",
            "                EXTERNAL_TOOLS[\"SPASS\"] = str(spass_exe.resolve())\n",
            "                print(f\"  OK SPASS installe: {spass_exe}\")\n",
            "        except Exception as e:\n",
            "            print(f\"  Erreur telechargement SPASS: {e}\")\n",
            "    elif system == \"Linux\":\n",
            "        import tarfile\n",
            "        arch = \"64\" if platform.architecture()[0] == \"64bit\" else \"32\"\n",
            "        spass_url = f\"https://www.spass-prover.org/download/binaries/spass35pclinux{arch}.tgz\"\n",
            "        spass_archive = spass_dir / \"spass.tgz\"\n",
            "        try:\n",
            "            urllib.request.urlretrieve(spass_url, spass_archive)\n",
            "            with tarfile.open(spass_archive, \"r:gz\") as tar:\n",
            "                tar.extractall(path=spass_dir)\n",
            "            extracted = spass_dir / \"SPASS\" / \"SPASS\"\n",
            "            if extracted.exists():\n",
            "                shutil.move(str(extracted), str(spass_exe))\n",
            "                os.chmod(spass_exe, stat.S_IRWXU | stat.S_IRGRP | stat.S_IXGRP)\n",
            "                EXTERNAL_TOOLS[\"SPASS\"] = str(spass_exe.resolve())\n",
            "                print(f\"  OK SPASS installe: {spass_exe}\")\n",
            "            spass_archive.unlink(missing_ok=True)\n",
            "            shutil.rmtree(spass_dir / \"SPASS\", ignore_errors=True)\n",
            "        except Exception as e:\n",
            "            print(f\"  Erreur installation SPASS: {e}\")"
        ],
        "outputs": [],
        "execution_count": None
    },
    # Cellule markdown EProver
    {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "#### 1.5.3 EProver - Prouveur FOL de Haute Performance\n",
            "\n",
            "**E Prover** est un prouveur automatique de theoremes pour la logique du premier ordre (FOL). ",
            "C'est l'un des prouveurs les plus performants, regulierement gagnant des competitions CASC.\n",
            "\n",
            "**Utilisation dans Tweety** :\n",
            "- `logics.fol.reasoner.EFOLReasoner` : Raisonnement FOL avance\n",
            "- Alternative a `SimpleFolReasoner` qui peut avoir des problemes de memoire\n",
            "\n",
            "**Note** : EProver est fourni dans le depot (ext_tools/EProver/)."
        ]
    },
    # Cellule code EProver
    {
        "cell_type": "code",
        "metadata": {},
        "source": [
            "# === Configuration de EProver (prouveur FOL) ===\n",
            "print(\"=== 3. Configuration de EProver ===\")\n",
            "\n",
            "eprover_search_paths = [\n",
            "    pathlib.Path(\"../ext_tools/EProver\"),\n",
            "    pathlib.Path(\"ext_tools/EProver\"),\n",
            "    pathlib.Path(\"../../ext_tools/EProver\"),\n",
            "]\n",
            "eprover_exe_name = \"eprover.exe\" if system == \"Windows\" else \"eprover\"\n",
            "\n",
            "eprover_in_path = shutil.which(\"eprover\") or shutil.which(\"eprover.exe\")\n",
            "if eprover_in_path:\n",
            "    EXTERNAL_TOOLS[\"EPROVER\"] = eprover_in_path\n",
            "    print(f\"  OK EProver trouve dans PATH: {eprover_in_path}\")\n",
            "else:\n",
            "    for search_path in eprover_search_paths:\n",
            "        eprover_exe = search_path / eprover_exe_name\n",
            "        if eprover_exe.exists():\n",
            "            EXTERNAL_TOOLS[\"EPROVER\"] = str(eprover_exe.resolve())\n",
            "            print(f\"  OK EProver trouve: {eprover_exe.resolve()}\")\n",
            "            break\n",
            "    else:\n",
            "        print(\"  EProver non trouve dans les chemins standards.\")\n",
            "        print(\"  Telecharger depuis https://eprover.org/\")"
        ],
        "outputs": [],
        "execution_count": None
    },
    # Cellule markdown SAT Solvers
    {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "#### 1.5.4 Solveurs SAT - Satisfaction Booleenne\n",
            "\n",
            "Les **solveurs SAT** sont au coeur de nombreuses fonctionnalites de Tweety :\n",
            "- Raisonnement en logique propositionnelle\n",
            "- Calcul des extensions d'argumentation (ADF)\n",
            "- Mesures d'incoherence\n",
            "\n",
            "**Hierarchie des solveurs** (du plus rapide au plus portable) :\n",
            "\n",
            "| Solveur | Type | Performance | Portabilite |\n",
            "|---------|------|-------------|-------------|\n",
            "| CaDiCaL 1.9.5 | Python (pySAT) | Champion SAT | Multi-plateforme |\n",
            "| Lingeling | DLL native | Tres rapide | Windows/Linux |\n",
            "| MiniSat | DLL native | Rapide | Windows/Linux |\n",
            "| PicoSAT | DLL native | Rapide | Windows/Linux |\n",
            "| Sat4j | Pure Java | Modere | Multi-plateforme |\n",
            "\n",
            "**Nouveau** : Le wrapper `sat_solver.py` donne acces aux solveurs modernes via pySAT."
        ]
    },
    # Cellule code SAT
    {
        "cell_type": "code",
        "metadata": {},
        "source": [
            "# === Configuration des solveurs SAT ===\n",
            "print(\"=== 4. Configuration des solveurs SAT ===\")\n",
            "\n",
            "# 4.1 Bibliotheques SAT natives (pour ADF via JNI)\n",
            "print(\"\\n--- 4.1 Bibliotheques SAT natives ---\")\n",
            "if NATIVE_LIBS_DIR.exists():\n",
            "    print(f\"  Repertoire libs/native: {NATIVE_LIBS_DIR.resolve()}\")\n",
            "    sat_libs_found = []\n",
            "    for solver in [\"lingeling\", \"minisat\", \"picosat\"]:\n",
            "        dll = NATIVE_LIBS_DIR / f\"{solver}.dll\"\n",
            "        so = NATIVE_LIBS_DIR / f\"{solver}.so\"\n",
            "        if dll.exists(): sat_libs_found.append(f\"{solver}.dll\")\n",
            "        elif so.exists(): sat_libs_found.append(f\"{solver}.so\")\n",
            "    if sat_libs_found:\n",
            "        print(f\"  OK Bibliotheques trouvees: {', '.join(sat_libs_found)}\")\n",
            "    else:\n",
            "        print(\"  Aucune bibliotheque native trouvee\")\n",
            "else:\n",
            "    print(\"  Repertoire libs/native non trouve\")\n",
            "\n",
            "# 4.2 Sat4j (Pure Java - toujours disponible)\n",
            "print(\"\\n--- 4.2 Sat4j (integre) ---\")\n",
            "EXTERNAL_TOOLS[\"SAT_SOLVER\"] = \"Sat4j (integre)\"\n",
            "print(\"  OK Sat4j disponible (org.tweetyproject.logics.pl.sat.Sat4jSolver)\")\n",
            "\n",
            "# 4.3 Wrapper Python avec CaDiCaL et autres (nouveau!)\n",
            "print(\"\\n--- 4.3 Wrapper Python SAT (CaDiCaL, Glucose, etc.) ---\")\n",
            "sat_solver_paths = [\n",
            "    pathlib.Path(\"../ext_tools/sat_solver.py\"),\n",
            "    pathlib.Path(\"ext_tools/sat_solver.py\"),\n",
            "]\n",
            "for sp in sat_solver_paths:\n",
            "    if sp.exists():\n",
            "        EXTERNAL_TOOLS[\"SAT_SOLVER_PYTHON\"] = str(sp.resolve())\n",
            "        print(f\"  OK sat_solver.py trouve: {sp.resolve()}\")\n",
            "        try:\n",
            "            from pysat.solvers import SolverNames\n",
            "            solvers = ['cadical195', 'glucose42', 'maplechrono', 'lingeling']\n",
            "            available = [s for s in solvers if hasattr(SolverNames, s)]\n",
            "            print(f\"  Solveurs disponibles: {', '.join(available)}\")\n",
            "        except ImportError:\n",
            "            print(\"  Note: pip install python-sat pour activer\")\n",
            "        break\n",
            "else:\n",
            "    print(\"  sat_solver.py non trouve\")"
        ],
        "outputs": [],
        "execution_count": None
    },
    # Cellule markdown MUS/MaxSAT
    {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "#### 1.5.5 MARCO et MaxSAT - Analyse d'Incoherence\n",
            "\n",
            "Ces outils sont utilises pour l'analyse des bases de croyances incoherentes :\n",
            "\n",
            "**MARCO** (MUS enumerator) :\n",
            "- Enumere les **MUS** (Minimal Unsatisfiable Subsets) et **MCS** (Maximal Consistent Subsets)\n",
            "- Utilise Z3 comme backend\n",
            "- Utilise par `MarcoMusEnumerator` dans Tweety\n",
            "\n",
            "**MaxSAT** :\n",
            "- Resout le probleme d'optimisation : maximiser le nombre de clauses satisfaites\n",
            "- Wrapper Python utilisant l'algorithme RC2 (gagnant MaxSAT Evaluation 2018)\n",
            "- Utilise par les mesures d'incoherence basees sur MinSum"
        ]
    },
    # Cellule code MARCO/MaxSAT + Resume
    {
        "cell_type": "code",
        "metadata": {},
        "source": [
            "# === Configuration de MARCO et MaxSAT ===\n",
            "print(\"=== 5. Configuration de MARCO (MUS enumerator) ===\")\n",
            "\n",
            "marco_search_paths = [\n",
            "    pathlib.Path(\"../ext_tools/marco.py\"),\n",
            "    pathlib.Path(\"ext_tools/marco.py\"),\n",
            "]\n",
            "for mp in marco_search_paths:\n",
            "    if mp.exists():\n",
            "        EXTERNAL_TOOLS[\"MARCO\"] = str(mp.resolve())\n",
            "        print(f\"  OK MARCO trouve: {mp.resolve()}\")\n",
            "        try:\n",
            "            import z3\n",
            "            print(f\"  OK Z3 disponible (version {z3.get_version_string()})\")\n",
            "        except ImportError:\n",
            "            print(\"  Note: pip install z3-solver pour activer\")\n",
            "        break\n",
            "else:\n",
            "    print(\"  MARCO non trouve\")\n",
            "\n",
            "print(\"\\n=== 6. Configuration de MaxSAT ===\")\n",
            "maxsat_search_paths = [\n",
            "    pathlib.Path(\"../ext_tools/maxsat_solver.py\"),\n",
            "    pathlib.Path(\"ext_tools/maxsat_solver.py\"),\n",
            "]\n",
            "for mp in maxsat_search_paths:\n",
            "    if mp.exists():\n",
            "        EXTERNAL_TOOLS[\"OPEN_WBO\"] = str(mp.resolve())\n",
            "        print(f\"  OK MaxSAT solver trouve: {mp.resolve()}\")\n",
            "        try:\n",
            "            import pysat\n",
            "            print(f\"  OK python-sat disponible (RC2 algorithm)\")\n",
            "        except ImportError:\n",
            "            print(\"  Note: pip install python-sat pour activer\")\n",
            "        break\n",
            "else:\n",
            "    print(\"  MaxSAT solver non trouve\")\n",
            "\n",
            "# === Resume final ===\n",
            "print(\"\\n\" + \"=\"*50)\n",
            "print(\"RESUME DES OUTILS EXTERNES\")\n",
            "print(\"=\"*50)\n",
            "for tool, path in EXTERNAL_TOOLS.items():\n",
            "    status = \"OK\" if (path and (path.startswith(\"Sat4j\") or get_tool_path(tool))) else \"Non configure\"\n",
            "    display_path = path[:50] + \"...\" if path and len(path) > 50 else (path or \"-\")\n",
            "    print(f\"  {tool:<18}: [{status:^12}] {display_path}\")\n",
            "print(\"=\"*50)"
        ],
        "outputs": [],
        "execution_count": None
    }
]

# Inserer les nouvelles cellules apres l'index 10
old_cells = nb['cells']
nb['cells'] = old_cells[:11] + new_cells + old_cells[11:]

# Sauvegarder
with open(notebook_path, 'w', encoding='utf-8') as f:
    json.dump(nb, f, indent=1, ensure_ascii=False)

print(f"Notebook modifie: {len(nb['cells'])} cellules (avant: {len(old_cells)})")
print(f"Nouvelles cellules inserees: {len(new_cells)}")
