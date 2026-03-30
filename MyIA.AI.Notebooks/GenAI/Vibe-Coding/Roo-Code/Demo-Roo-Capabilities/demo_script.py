print("Bonjour depuis la démo Roo !")

somme = sum(range(1, 11))
print(f"La somme des nombres de 1 à 10 est : {somme}")

with open("resultat_demo.txt", "w", encoding="utf-8") as f:
    f.write(f"Résultat : {somme}")