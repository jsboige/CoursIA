import subprocess
import csv
import io
import sys

def get_gpu_memory():
    """
    Récupère les informations sur la mémoire GPU via nvidia-smi.
    Retourne une liste de dictionnaires.
    """
    try:
        # Exécute la commande nvidia-smi
        cmd = [
            'nvidia-smi',
            '--query-gpu=index,name,memory.total,memory.used,memory.free',
            '--format=csv,noheader,nounits'
        ]
        
        result = subprocess.run(cmd, capture_output=True, text=True, check=True)
        
        # Parse la sortie CSV
        gpus = []
        csv_reader = csv.reader(io.StringIO(result.stdout))
        
        for row in csv_reader:
            if len(row) == 5:
                gpus.append({
                    'index': row[0].strip(),
                    'name': row[1].strip(),
                    'total': int(row[2].strip()),
                    'used': int(row[3].strip()),
                    'free': int(row[4].strip())
                })
        return gpus
        
    except FileNotFoundError:
        print("Erreur: nvidia-smi n'est pas trouvé. Assurez-vous que les pilotes NVIDIA sont installés.")
        return []
    except subprocess.CalledProcessError as e:
        print(f"Erreur lors de l'exécution de nvidia-smi: {e}")
        return []
    except Exception as e:
        print(f"Une erreur inattendue est survenue: {e}")
        return []

def print_gpu_table(gpus):
    """
    Affiche un tableau formaté des informations GPU.
    """
    if not gpus:
        print("Aucun GPU détecté ou erreur de lecture.")
        return

    print(f"{'Index':<6} | {'Nom':<30} | {'Libre / Total (MiB)':<25} | {'Utilisé':<10}")
    print("-" * 80)
    
    for gpu in gpus:
        memory_str = f"{gpu['free']} / {gpu['total']} MiB"
        percent_used = (gpu['used'] / gpu['total']) * 100
        used_str = f"{gpu['used']} MiB ({percent_used:.1f}%)"
        
        print(f"{gpu['index']:<6} | {gpu['name']:<30} | {memory_str:<25} | {used_str:<10}")

if __name__ == "__main__":
    gpus = get_gpu_memory()
    print_gpu_table(gpus)
    
    # Sortie simplifiée pour parsing facile si besoin
    # print("\n--- JSON Output ---")
    # import json
    # print(json.dumps(gpus))