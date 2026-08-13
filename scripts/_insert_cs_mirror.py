#!/usr/bin/env python3
"""
Insert 3 cells (md intro + C# code + md interpretation) into the C# twin
of GameTheory-16-MechanismDesign to mirror the Python twin's Gibbard-Satterthwaite
addition from PR #10699.

Position: insert AFTER cell 16 (Lecture du resultat : efficacite et partage
du surplus) and BEFORE cell 17 (## 6. Exercices).

This is a SEMANTIC twin mirror -- the C# cells explain the same theorem
(Gibbard-Satterthwaite: Borda manipulable + Dictature strategy-proof) using
C# idioms (BCL .NET 9 pur, 0 NuGet, s.Display()) rather than Python idioms.
"""
import json
import sys
from pathlib import Path

NB_PATH = Path('MyIA.AI.Notebooks/GameTheory/GameTheory-16-MechanismDesign-Csharp.ipynb')

# ---- Cell 1: Markdown intro (mirrors Python md "Illustration : Gibbard-Satterthwaite...")
md1_source = (
    "### 5.1 Gibbard-Satterthwaite : Borda manipulable + dictature strategy-proof\n"
    "\n"
    "La section 6 (impossibilites) du jumeau Python enonce le theoreme de "
    "**Gibbard-Satterthwaite** : pour toute fonction de choix social sur au moins "
    "3 alternatives, **non-dictatoriale** et **surjective**, il existe un profil "
    "ou un electeur a interet a mentir. C'est un resultat d'impossibilite : il "
    "ne montre pas *comment* manipuler, il affirme que l'occasion existe.\n"
    "\n"
    "Nous le **verifions computatoirement** sur la regle de **Borda** (non-"
    "dictatoriale, surjective, $\\geq 3$ alternatives -- donc dans le scope du "
    "theoreme) : pour chaque profil sincere de 3 electeurs sur 3 alternatives, "
    "nous cherchons par **enumeration force brute** si un electeur peut, en "
    "declarant un bulletin different de ses vraies preferences, faire elire un "
    "candidat qu'il prefere au gagnant sincere. Si le theoreme est exact, "
    "l'enumeration doit trouver un temoin.\n"
    "\n"
    "Puis nous verifions que la **dictature** (l'electeur 0 decide seul) est "
    "strategy-proof sur les memes 216 profils : c'est le contre-point du "
    "theoreme -- les seules regles strategy-proof sur $\\geq 3$ alternatives "
    "sont dictatoriales."
)

# ---- Cell 2: C# code (mirrors Python enumeration brute-force, BCL .NET 9 pur)
code_source = (
    "// Gibbard-Satterthwaite - demonstration computatoire (C# / .NET 9 BCL pur).\n"
    "// 3 alternatives, regle de Borda (points m-1 ... 0, ex aequo resolus\n"
    "// alphabetiquement). Permutations generees recursivement (sans NuGet).\n"
    "char[] ALTS = {'A', 'B', 'C'};\n"
    "int m = ALTS.Length;\n"
    "\n"
    "// Generation recursive des permutations sur un tableau de T.\n"
    "// Variante non-generique (char[]) pour compatibilite top-level statements.\n"
    "// NOTE: pas de `static` ici -- en .NET Interactive top-level, m et ALTS sont\n"
    "// des champs d'instance de la classe implicite ; static ne les verrait pas.\n"
    "List<char[]> Permute(char[] items)\n"
    "{\n"
    "    var result = new List<char[]>();\n"
    "    void Rec(char[] prefix, char[] rest)\n"
    "    {\n"
    "        if (rest.Length == 0)\n"
    "        {\n"
    "            result.Add(prefix.ToArray());\n"
    "            return;\n"
    "        }\n"
    "        for (int i = 0; i < rest.Length; i++)\n"
    "        {\n"
    "            var newPrefix = prefix.Concat(new[] { rest[i] }).ToArray();\n"
    "            var newRest = rest.Where((_, idx) => idx != i).ToArray();\n"
    "            Rec(newPrefix, newRest);\n"
    "        }\n"
    "    }\n"
    "    Rec(new char[0], items);\n"
    "    return result;\n"
    "}\n"
    "\n"
    "// Regle de Borda : points = m-1-rank par electeur, gagnant = max(score, -ord).\n"
    "char BordaWinner(char[][] ballots)\n"
    "{\n"
    "    var score = new Dictionary<char, int> { ['A'] = 0, ['B'] = 0, ['C'] = 0 };\n"
    "    foreach (var ballot in ballots)\n"
    "        for (int rank = 0; rank < ballot.Length; rank++)\n"
    "            score[ballot[rank]] += (m - 1 - rank);\n"
    "    char best = ALTS[0];\n"
    "    int bestScore = -1, bestOrd = 0;\n"
    "    foreach (var a in ALTS)\n"
    "    {\n"
    "        int sc = score[a];\n"
    "        int ord = -(int)a;\n"
    "        if (sc > bestScore || (sc == bestScore && ord < bestOrd))\n"
    "        {\n"
    "            bestScore = sc;\n"
    "            bestOrd = ord;\n"
    "            best = a;\n"
    "        }\n"
    "    }\n"
    "    return best;\n"
    "}\n"
    "\n"
    "// Position d'une alternative dans un ranking (0 = la preferee).\n"
    "int Rang(char[] prefs, char alt)\n"
    "{\n"
    "    for (int i = 0; i < prefs.Length; i++)\n"
    "        if (prefs[i] == alt) return i;\n"
    "    return -1;\n"
    "}\n"
    "\n"
    "// Cherche un electeur qui gagne a mentir. Retourne le tuple temoin ou null.\n"
    "// (profile, i, vraies, mensonge, gs, gn) -- gs = gagnant sincere, gn = gagnant sous mensonge.\n"
    "(char[][] profile, int i, char[] vraies, char[] mensonge, char gs, char gn)?\n"
    "    TrouverManipulation(char[][] profile, Func<char[][], char> regle)\n"
    "{\n"
    "    char gs = regle(profile);\n"
    "    for (int i = 0; i < profile.Length; i++)\n"
    "    {\n"
    "        var vraies = profile[i];\n"
    "        foreach (var mensonge in Permute(ALTS))\n"
    "        {\n"
    "            if (mensonge.SequenceEqual(vraies)) continue;\n"
    "            var nouveau = new char[profile.Length][];\n"
    "            for (int k = 0; k < profile.Length; k++) nouveau[k] = profile[k];\n"
    "            nouveau[i] = mensonge;\n"
    "            char gn = regle(nouveau);\n"
    "            if (Rang(vraies, gn) < Rang(vraies, gs))\n"
    "                return (profile, i, vraies, mensonge, gs, gn);\n"
    "        }\n"
    "    }\n"
    "    return null;\n"
    "}\n"
    "\n"
    "char GagnantDictature(char[][] profile) { return profile[0][0]; }\n"
    "\n"
    "// --- Demonstration ---\n"
    "\"Gibbard-Satterthwaite - demonstration computatoire\".Display();\n"
    "new string('=', 64).Display();\n"
    "\n"
    "var toutesPrefs = Permute(ALTS);\n"
    "// Generer les 6^3 = 216 profils (3 electeurs, chacun choisit une permutation de 3 alternatives).\n"
    "var profilesBorda = new List<char[][]>();\n"
    "foreach (var p0 in toutesPrefs)\n"
    "    foreach (var p1 in toutesPrefs)\n"
    "        foreach (var p2 in toutesPrefs)\n"
    "            profilesBorda.Add(new[] { p0, p1, p2 });\n"
    "\n"
    "\"[1] Regle de Borda (non-dictatoriale, surjective, >= 3 alternatives) :\".Display();\n"
    "var temoin = (object)null;\n"
    "foreach (var profile in profilesBorda)\n"
    "{\n"
    "    var r = TrouverManipulation(profile, BordaWinner);\n"
    "    if (r != null) { temoin = r; break; }\n"
    "}\n"
    "if (temoin != null)\n"
    "{\n"
    "    var t = ((char[][], int, char[], char[], char, char))temoin;\n"
    "    var profile = t.Item1;\n"
    "    var i = t.Item2;\n"
    "    var vraies = t.Item3;\n"
    "    var mensonge = t.Item4;\n"
    "    var gs = t.Item5;\n"
    "    var gn = t.Item6;\n"
    "    $\"    Profil sincere : (({string.Join(\",\", profile[0])}), ({string.Join(\",\", profile[1])}), ({string.Join(\",\", profile[2])}))\".Display();\n"
    "    $\"    Gagnant sincere : {gs}\".Display();\n"
    "    $\"    L'electeur {i} (prefs vraies ({string.Join(\",\", vraies)})) declare ({string.Join(\",\", mensonge)})\".Display();\n"
    "    $\"    -> Nouveau gagnant : {gn} (qu'il prefere a {gs})\".Display();\n"
    "    \"    => Borda est MANIPULABLE. Temoin trouve par enumeration des 216 profils.\".Display();\n"
    "}\n"
    "else\n"
    "{\n"
    "    \"    Aucune manipulation trouvee.\".Display();\n"
    "}\n"
    "\n"
    "\"\".Display();\n"
    "\"[2] Dictature (l'electeur 0 decide seul) :\".Display();\n"
    "bool manipDict = false;\n"
    "foreach (var profile in profilesBorda)\n"
    "{\n"
    "    if (TrouverManipulation(profile, GagnantDictature) != null) { manipDict = true; break; }\n"
    "}\n"
    "(manipDict ? \"    Manipulation trouvee (!)\" : \"    Aucune manipulation sur les 216 profils -> la dictature est STRATEGY-PROOF.\").Display();\n"
    "\n"
    "\"\".Display();\n"
    "\"[3] Gibbard-Satterthwaite en acte :\".Display();\n"
    "\"    Borda (non-dictatorial) = manipulable ; Dictature = strategy-proof.\".Display();\n"
    "\"    Sur >= 3 alternatives, les SEULS mecanismes strategy-proof sont dictatoriaux.\".Display();"
)

# ---- Cell 3: Markdown interpretation (mirrors Python md "Interpretation : le theoreme en acte")
md2_source = (
    "### Lecture : le theoreme en acte\n"
    "\n"
    "L'enumeration a trouve un **temoin de manipulation** : sur un profil sincere "
    "donne, Borda elirait le candidat $g_s$. L'electeur $i$ (dont les vraies "
    "preferences sont $v$) a interet a declarer $m \\neq v$ : Borda elire alors "
    "$g_n$ que l'electeur prefere strictement a $g_s$. Le mensonge rationnel est "
    "recompense -- et c'est l'enumeration qui l'a decouvert, non une construction "
    "ad hoc.\n"
    "\n"
    "La deuxieme mesure est le **contre-point** du theoreme : la **dictature** "
    "(l'electeur 0 decide seul) est **strategy-proof** sur les 216 profils. Le "
    "dictateur n'a rien a gagner a mentir (son choix sincere gagne deja), et les "
    "autres electeurs sont ignores. C'est exactement la conclusion de Gibbard-"
    "Satterthwaite : **les seules regles strategy-proof sur $\\geq 3$ alternatives "
    "sont dictatoriales**.\n"
    "\n"
    "**Pourquoi Vickrey et VCG echappent-ils au theoreme ?** Parce qu'ils "
    "utilisent des **transferts monetaires** -- le theoreme de Gibbard-Satterthwaite "
    "porte sur les fonctions de choix social *sans paiements*. Des qu'on autorise "
    "un paiement (l'enchere au second prix, le critere de Clarke), on sort du cadre "
    "d'impossibilite et l'incitativite redevient possible.\n"
    "\n"
    "**Note sur le temoin** : l'ordre des permutations en C# (`Permute` recursif) "
    "differe de l'ordre Python (`itertools.permutations`), donc le **premier "
    "temoin** renvoye peut varier entre les deux jumeaux. C'est attendu : le "
    "theoreme garantit l'**existence** d'un temoin, pas un temoin specifique. "
    "Les deux jumeaux trouvent un temoin valide et aboutissent a la meme "
    "conclusion (Borda manipulable, Dictature strategy-proof)."
)

# ---- Build cell objects (un-executed; will be re-executed by .NET Interactive)
def make_md_cell(source):
    src_list = source.split('\n')
    # nbformat expects list with newlines preserved between lines except the last
    src = [line + '\n' for line in src_list[:-1]] + [src_list[-1]]
    return {
        "cell_type": "markdown",
        "metadata": {"tags": []},
        "source": src
    }

def make_code_cell(source):
    src_list = source.split('\n')
    src = [line + '\n' for line in src_list[:-1]] + [src_list[-1]]
    return {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {"tags": []},
        "outputs": [],
        "source": src
    }

new_md1 = make_md_cell(md1_source)
new_code = make_code_cell(code_source)
new_md2 = make_md_cell(md2_source)

# ---- Load notebook, find insertion point (BEFORE cell 17 = "## 6. Exercices")
nb = json.loads(NB_PATH.read_text(encoding='utf-8'))
cells = nb['cells']

# Find insertion index: first cell whose source contains "## 6. Exercices"
ins_idx = None
for i, c in enumerate(cells):
    src = ''.join(c.get('source', [])) if isinstance(c.get('source'), list) else c.get('source', '')
    if c['cell_type'] == 'markdown' and src.startswith('## 6. Exercices'):
        ins_idx = i
        break
if ins_idx is None:
    print("ERROR: could not find insertion point ('## 6. Exercices')", file=sys.stderr)
    sys.exit(1)

# Insert 3 cells at ins_idx (markdown, code, markdown)
new_cells = cells[:ins_idx] + [new_md1, new_code, new_md2] + cells[ins_idx:]
nb['cells'] = new_cells

# Write back
NB_PATH.write_text(json.dumps(nb, indent=1, ensure_ascii=False), encoding='utf-8')
print(f"OK: inserted 3 cells before cell {ins_idx} ('## 6. Exercices')")
print(f"Total cells: {len(cells)} -> {len(new_cells)}")