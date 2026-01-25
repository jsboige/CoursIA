#!/usr/bin/env python3
"""Script pour splitter la cellule JVM de Tweety-1-Setup.ipynb"""
import json
from pathlib import Path

# Lire le notebook
notebook_path = Path("MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-1-Setup.ipynb")
with open(notebook_path, 'r', encoding='utf-8') as f:
    nb = json.load(f)

print(f"Structure actuelle: {len(nb['cells'])} cellules")

# Trouver l'index de la cellule JVM (devrait etre 22)
jvm_cell_index = None
for i, cell in enumerate(nb['cells']):
    if cell['cell_type'] == 'code':
        source = ''.join(cell['source'])
        if '1.6 Demarrage de la JVM' in source or 'find_java_home' in source:
            jvm_cell_index = i
            print(f"Cellule JVM trouvee a l'index {i}")
            print(f"  Taille: {len(source)} caracteres")
            break

if jvm_cell_index is None:
    print("ERREUR: Cellule JVM non trouvee")
    exit(1)

# Nouvelles cellules pour remplacer la cellule monolithique
new_cells = [
    # Markdown intro JVM
    {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "#### 1.6.1 Fonctions Utilitaires JDK\n",
            "\n",
            "Avant de demarrer la JVM, nous definissons des fonctions pour localiser ou telecharger automatiquement un JDK compatible.\n",
            "\n",
            "**Strategie de detection JDK** (par ordre de priorite) :\n",
            "1. JDK portable existant dans `jdk-17-portable/`\n",
            "2. Telechargement automatique de Zulu JDK 17 (Azul)\n",
            "3. Variable d'environnement `JAVA_HOME`\n",
            "4. Detection automatique des JDKs systeme"
        ]
    },
    # Code fonctions JDK
    {
        "cell_type": "code",
        "metadata": {},
        "source": [
            "# --- 1.6.1 Fonctions Utilitaires JDK ---\n",
            "import jpype\n",
            "import jpype.imports\n",
            "import os\n",
            "import pathlib\n",
            "import platform\n",
            "import urllib.request\n",
            "import zipfile\n",
            "import shutil\n",
            "from jpype.types import *\n",
            "import stat\n",
            "\n",
            "# URLs de telechargement Zulu JDK 17 (Azul)\n",
            "JDK_DOWNLOAD_URLS = {\n",
            "    \"Windows\": \"https://cdn.azul.com/zulu/bin/zulu17.50.19-ca-jdk17.0.11-win_x64.zip\",\n",
            "    \"Linux\": \"https://cdn.azul.com/zulu/bin/zulu17.50.19-ca-jdk17.0.11-linux_x64.tar.gz\",\n",
            "    \"Darwin\": \"https://cdn.azul.com/zulu/bin/zulu17.50.19-ca-jdk17.0.11-macosx_x64.zip\"\n",
            "}\n",
            "\n",
            "def find_portable_jdk():\n",
            "    \"\"\"Localise le JDK portable dans l'arborescence du projet.\"\"\"\n",
            "    print(\"Recherche JDK portable dans l'arborescence projet...\")\n",
            "    search_paths = [\n",
            "        pathlib.Path(\"jdk-17-portable\"),\n",
            "        pathlib.Path(\"../jdk-17-portable\"),\n",
            "        pathlib.Path(\"../Argument_Analysis/jdk-17-portable\"),\n",
            "        pathlib.Path(\"../../jdk-17-portable\"),\n",
            "    ]\n",
            "    exe_suffix = \".exe\" if platform.system() == \"Windows\" else \"\"\n",
            "    for base_path in search_paths:\n",
            "        if base_path.exists():\n",
            "            for pattern in [\"*jdk*\", \"zulu*\"]:\n",
            "                for jdk_dir in base_path.glob(pattern):\n",
            "                    if jdk_dir.is_dir():\n",
            "                        java_exe = jdk_dir / \"bin\" / f\"java{exe_suffix}\"\n",
            "                        if java_exe.exists():\n",
            "                            print(f\"  OK JDK portable trouve: {jdk_dir.absolute()}\")\n",
            "                            return str(jdk_dir.absolute())\n",
            "    print(\"  JDK portable non trouve\")\n",
            "    return None\n",
            "\n",
            "def download_portable_jdk():\n",
            "    \"\"\"Telecharge et extrait le JDK portable Zulu 17.\"\"\"\n",
            "    system = platform.system()\n",
            "    if system not in JDK_DOWNLOAD_URLS:\n",
            "        print(f\"Systeme {system} non supporte pour telechargement auto\")\n",
            "        return None\n",
            "    url = JDK_DOWNLOAD_URLS[system]\n",
            "    jdk_dir = pathlib.Path(\"jdk-17-portable\")\n",
            "    jdk_dir.mkdir(exist_ok=True)\n",
            "    archive_name = url.split(\"/\")[-1]\n",
            "    archive_path = jdk_dir / archive_name\n",
            "    print(f\"Telechargement JDK depuis {url}...\")\n",
            "    try:\n",
            "        urllib.request.urlretrieve(url, archive_path)\n",
            "        print(f\"Extraction de {archive_name}...\")\n",
            "        if archive_name.endswith(\".zip\"):\n",
            "            with zipfile.ZipFile(archive_path, 'r') as zf:\n",
            "                zf.extractall(jdk_dir)\n",
            "        elif archive_name.endswith(\".tar.gz\"):\n",
            "            import tarfile\n",
            "            with tarfile.open(archive_path, 'r:gz') as tf:\n",
            "                tf.extractall(jdk_dir)\n",
            "        archive_path.unlink()\n",
            "        return find_portable_jdk()\n",
            "    except Exception as e:\n",
            "        print(f\"Erreur telechargement JDK: {e}\")\n",
            "        return None\n",
            "\n",
            "print(\"Fonctions JDK definies: find_portable_jdk(), download_portable_jdk()\")"
        ],
        "outputs": [],
        "execution_count": None
    },
    # Markdown detection JDK
    {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "#### 1.6.2 Detection et Configuration du JDK\n",
            "\n",
            "Cette cellule detecte le JDK disponible et le telecharge si necessaire.\n",
            "\n",
            "**Important** : JPype necessite un JDK 11+ (JDK 17 recommande pour Tweety 1.29)."
        ]
    },
    # Code detection JDK
    {
        "cell_type": "code",
        "metadata": {},
        "source": [
            "# --- 1.6.2 Detection du JDK ---\n",
            "\n",
            "def find_java_home():\n",
            "    \"\"\"Trouve JAVA_HOME selon la strategie de priorite.\"\"\"\n",
            "    # 1. JDK portable existant\n",
            "    portable_jdk = find_portable_jdk()\n",
            "    if portable_jdk:\n",
            "        os.environ['JAVA_HOME'] = portable_jdk\n",
            "        return portable_jdk\n",
            "    \n",
            "    # 2. Telechargement automatique\n",
            "    print(\"JDK portable non trouve - telechargement automatique...\")\n",
            "    downloaded_jdk = download_portable_jdk()\n",
            "    if downloaded_jdk:\n",
            "        os.environ['JAVA_HOME'] = downloaded_jdk\n",
            "        return downloaded_jdk\n",
            "    \n",
            "    # 3. Variable JAVA_HOME\n",
            "    java_home_env = os.getenv(\"JAVA_HOME\")\n",
            "    exe_suffix = \".exe\" if platform.system() == \"Windows\" else \"\"\n",
            "    if java_home_env and pathlib.Path(java_home_env).is_dir():\n",
            "        if (pathlib.Path(java_home_env) / \"bin\" / f\"java{exe_suffix}\").exists():\n",
            "            print(f\"  Utilisation JAVA_HOME: {java_home_env}\")\n",
            "            return java_home_env\n",
            "    \n",
            "    # 4. Detection systeme\n",
            "    print(\"Detection automatique des JDKs systeme...\")\n",
            "    possible_locations = []\n",
            "    if platform.system() == \"Windows\":\n",
            "        java_dir = pathlib.Path(\"C:/Program Files/Java/\")\n",
            "        if java_dir.is_dir():\n",
            "            possible_locations = sorted(java_dir.glob(\"jdk-*/\"), reverse=True)\n",
            "    elif platform.system() == \"Linux\":\n",
            "        for p_str in [\"/usr/lib/jvm\"]:\n",
            "            p_obj = pathlib.Path(p_str)\n",
            "            if p_obj.is_dir():\n",
            "                possible_locations.extend(sorted(p_obj.glob(\"java-*\"), reverse=True))\n",
            "    for p in possible_locations:\n",
            "        java_bin = p / \"bin\" / f\"java{exe_suffix}\"\n",
            "        if java_bin.exists():\n",
            "            print(f\"  JDK systeme detecte: {p}\")\n",
            "            os.environ['JAVA_HOME'] = str(p)\n",
            "            return str(p)\n",
            "    \n",
            "    print(\"ERREUR: Aucun JDK trouve ou telechargeable\")\n",
            "    return None\n",
            "\n",
            "# Executer la detection\n",
            "java_home_path = find_java_home()\n",
            "if java_home_path:\n",
            "    print(f\"\\nJAVA_HOME configure: {java_home_path}\")"
        ],
        "outputs": [],
        "execution_count": None
    },
    # Markdown classpath
    {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "#### 1.6.3 Construction du Classpath\n",
            "\n",
            "Le **classpath** indique a la JVM ou trouver les classes Java.\n",
            "Nous assemblons tous les JARs Tweety du dossier `libs/`."
        ]
    },
    # Code classpath
    {
        "cell_type": "code",
        "metadata": {},
        "source": [
            "# --- 1.6.3 Construction du Classpath ---\n",
            "classpath_separator = os.pathsep\n",
            "if 'LIB_DIR' not in globals():\n",
            "    LIB_DIR = pathlib.Path(\"libs\")\n",
            "\n",
            "jar_list = [str(p.resolve()) for p in LIB_DIR.glob(\"*.jar\")]\n",
            "num_jars_found = len(jar_list)\n",
            "\n",
            "if not jar_list:\n",
            "    print(\"ERREUR: Aucun JAR trouve dans libs/\")\n",
            "    classpath = \"\"\n",
            "else:\n",
            "    classpath = classpath_separator.join(jar_list)\n",
            "    print(f\"Classpath assemble: {num_jars_found} JARs\")\n",
            "    \n",
            "    # Verification presence JAR beliefdynamics\n",
            "    beliefdynamics_found = any(\"beliefdynamics\" in j for j in jar_list)\n",
            "    if beliefdynamics_found:\n",
            "        print(\"  OK JAR beliefdynamics present\")\n",
            "    else:\n",
            "        print(\"  ATTENTION: JAR beliefdynamics non trouve\")"
        ],
        "outputs": [],
        "execution_count": None
    },
    # Markdown demarrage JVM
    {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "#### 1.6.4 Demarrage de la JVM\n",
            "\n",
            "**Important** : Si des JARs ont ete telecharges dans les cellules precedentes,\n",
            "**redemarrez le noyau** avant d'executer cette cellule.\n",
            "\n",
            "La JVM est demarree une seule fois par session Python. Une fois demarree,\n",
            "toutes les classes Java sont accessibles via les imports Python."
        ]
    },
    # Code demarrage JVM
    {
        "cell_type": "code",
        "metadata": {},
        "source": [
            "# --- 1.6.4 Demarrage de la JVM ---\n",
            "\n",
            "if not jpype.isJVMStarted():\n",
            "    if not java_home_path:\n",
            "        print(\"ERREUR: Impossible de demarrer la JVM sans JAVA_HOME\")\n",
            "    elif num_jars_found == 0:\n",
            "        print(\"ERREUR: Classpath vide - verifiez le dossier libs/\")\n",
            "    else:\n",
            "        print(\"Demarrage de la JVM...\")\n",
            "        jvm_args = [\"-ea\", f\"-Djava.class.path={classpath}\"]\n",
            "        \n",
            "        # Ajouter bibliotheques natives si presentes\n",
            "        if 'NATIVE_LIBS_DIR' in globals() and NATIVE_LIBS_DIR.exists():\n",
            "            jvm_args.append(f\"-Djava.library.path={NATIVE_LIBS_DIR.resolve()}\")\n",
            "            print(f\"  Avec bibliotheques natives: {NATIVE_LIBS_DIR}\")\n",
            "        \n",
            "        try:\n",
            "            jpype.startJVM(*jvm_args, convertStrings=False)\n",
            "            jpype.imports.registerDomain(\"org\")\n",
            "            jpype.imports.registerDomain(\"java\")\n",
            "            jpype.imports.registerDomain(\"net\")\n",
            "            print(\"OK JVM demarree et domaines enregistres\")\n",
            "        except Exception as e:\n",
            "            print(f\"ERREUR demarrage JVM: {e}\")\n",
            "else:\n",
            "    print(\"JVM deja en cours d'execution\")"
        ],
        "outputs": [],
        "execution_count": None
    },
    # Markdown tests imports
    {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "#### 1.6.5 Verification des Imports Java\n",
            "\n",
            "Verification que les classes Tweety essentielles sont accessibles.\n",
            "\n",
            "**Note sur InformationObject** : Cette classe a ete supprimee dans Tweety 1.28\n",
            "(refactoring API). Seule la section CrMas (Revision de Croyances multi-agents)\n",
            "est affectee. Le reste du notebook fonctionne normalement."
        ]
    },
    # Code tests imports
    {
        "cell_type": "code",
        "metadata": {},
        "source": [
            "# --- 1.6.5 Verification des Imports ---\n",
            "print(\"Test des imports Java essentiels...\")\n",
            "\n",
            "if jpype.isJVMStarted():\n",
            "    imports_ok = True\n",
            "    missing = []\n",
            "    \n",
            "    # Test InformationObject (optionnel - absent dans Tweety 1.28+)\n",
            "    try:\n",
            "        from org.tweetyproject.beliefdynamics import InformationObject\n",
            "        print(\"  OK InformationObject (ancienne API)\")\n",
            "    except ImportError:\n",
            "        print(\"  INFO InformationObject absent (normal pour Tweety 1.28+)\")\n",
            "    \n",
            "    # Tests critiques\n",
            "    try:\n",
            "        from org.tweetyproject.commons import Formula\n",
            "        print(\"  OK commons.Formula\")\n",
            "    except ImportError:\n",
            "        missing.append(\"commons.Formula\")\n",
            "        imports_ok = False\n",
            "    \n",
            "    try:\n",
            "        from org.tweetyproject.logics.pl.syntax import Proposition, PlFormula\n",
            "        print(\"  OK logics.pl.syntax (Proposition, PlFormula)\")\n",
            "    except ImportError:\n",
            "        missing.append(\"logics.pl.syntax\")\n",
            "        imports_ok = False\n",
            "    \n",
            "    try:\n",
            "        from org.tweetyproject.arg.dung.syntax import Argument, DungTheory\n",
            "        print(\"  OK arg.dung.syntax (Argument, DungTheory)\")\n",
            "    except ImportError:\n",
            "        missing.append(\"arg.dung.syntax\")\n",
            "        imports_ok = False\n",
            "    \n",
            "    try:\n",
            "        from java.util import ArrayList, HashSet\n",
            "        print(\"  OK java.util (ArrayList, HashSet)\")\n",
            "    except ImportError:\n",
            "        missing.append(\"java.util\")\n",
            "        imports_ok = False\n",
            "    \n",
            "    if imports_ok:\n",
            "        print(\"\\nTous les imports critiques sont disponibles.\")\n",
            "        print(\"Tweety est pret a etre utilise!\")\n",
            "    else:\n",
            "        print(f\"\\nERREUR: Imports manquants: {', '.join(missing)}\")\n",
            "        print(\"Verifiez les JARs dans libs/\")\n",
            "else:\n",
            "    print(\"JVM non demarree - impossible de tester les imports\")"
        ],
        "outputs": [],
        "execution_count": None
    }
]

# Remplacer la cellule JVM par les nouvelles cellules
old_cells = nb['cells']
nb['cells'] = old_cells[:jvm_cell_index] + new_cells + old_cells[jvm_cell_index+1:]

# Sauvegarder
with open(notebook_path, 'w', encoding='utf-8') as f:
    json.dump(nb, f, indent=1, ensure_ascii=False)

print(f"Notebook modifie: {len(nb['cells'])} cellules (avant: {len(old_cells)})")
print(f"Cellule JVM remplacee par {len(new_cells)} cellules")
