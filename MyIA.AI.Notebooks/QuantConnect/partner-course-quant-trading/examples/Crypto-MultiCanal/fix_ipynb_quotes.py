# region imports
from AlgorithmImports import *
# endregion
#!/usr/bin/env python3
# ------------------------------------------------------------
#   fix_ipynb_quotes_robust.py
#   Répare les guillemets non-échappés des notebooks Python
#   (c) 2024 – GPL-3.0
# ------------------------------------------------------------
import sys
import pathlib
import json
import io

def main():
    if len(sys.argv) != 3:
        print("Usage: python fix_ipynb_quotes_robust.py input.ipynb output.ipynb")
        sys.exit(1)
    
    src_path = pathlib.Path(sys.argv[1])
    dst_path = pathlib.Path(sys.argv[2])
    
    # Lire contenu du notebook
    print(f"Lecture de {src_path}...")
    raw_text = src_path.read_text(encoding='utf-8')
    
    # Première étape: Extraire la structure du JSON autant que possible
    # (même si le document est techniquement invalide)
    fixed_text = repair_notebook(raw_text)
    
    # Vérifier validité JSON
    try:
        json.loads(fixed_text)
        print("✓ Validation JSON réussie")
    except json.JSONDecodeError as e:
        print(f"✗ Le JSON reste invalide: {e}")
        print(f"  Erreur à la ligne {e.lineno}, colonne {e.colno}")
        # Afficher contexte
        lines = fixed_text.splitlines()
        start = max(0, e.lineno - 3)
        end = min(len(lines), e.lineno + 3)
        for i in range(start, end):
            marker = ">>>" if i+1 == e.lineno else "   "
            print(f"{marker} {i+1}: {lines[i][:100]}")
        sys.exit(2)
    
    # Écrire résultat
    dst_path.write_text(fixed_text, encoding='utf-8')
    print(f"✓ Notebook réparé écrit dans {dst_path}")

def repair_notebook(text):
    """Répare les guillemets dans les blocs source d'un notebook Jupyter."""
    # Approche sans regex: parcourir bloc par bloc
    result = []
    source_start = '"source": ['
    in_source = False
    buffer = io.StringIO(text)
    
    for line in buffer:
        # Début d'un bloc source
        if source_start in line and not in_source:
            in_source = True
            result.append(line)
            continue
        
        # Fin d'un bloc source
        if in_source and line.strip().startswith("]"):
            in_source = False
            result.append(line)
            continue
        
        # À l'intérieur d'un bloc source
        if in_source:
            # Si la ligne contient au moins deux guillemets, elle a besoin de réparation
            if line.count('"') >= 2:
                line = escape_string_line(line)
        
        result.append(line)
    
    return "".join(result)

def escape_string_line(line):
    """Répare une ligne qui semble contenir une chaîne dans un bloc source."""
    line = line.rstrip()
    
    # Garder la virgule de fin (si présente)
    has_comma = line.endswith(',')
    if has_comma:
        line = line[:-1].rstrip()
    
    # Trouver premier et dernier guillemet
    first_quote = line.find('"')
    last_quote = line.rfind('"')
    
    if first_quote == -1 or first_quote == last_quote:
        return line + (',' if has_comma else '') + '\n'
    
    # Extraire les 3 parties: indentation, contenu, reste
    indent = line[:first_quote]
    content = line[first_quote+1:last_quote]
    
    # ⭐ LA CLEF: utiliser json.dumps pour échapper correctement le contenu
    # (y compris les guillemets internes et les backslashes)
    try:
        # NE PAS utiliser de regex qui pourrait se confondre avec le contenu
        escaped = json.dumps(content)[1:-1]  # enlever guillemets ajoutés par dumps
        result = f'{indent}"{escaped}"'
        if has_comma:
            result += ','
        return result + '\n'
    except:
        # En cas d'erreur, retourner la ligne inchangée
        return line + (',' if has_comma else '') + '\n'

if __name__ == "__main__":
    main()