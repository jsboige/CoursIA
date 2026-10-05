# Resharp — RE-sharp (Veanes et al, POPL 2025) en attente d'accueil

## État au 2026-10-05

Ce dossier porte le **package compilé** RE-sharp (3 DLLs : `Resharp.dll`, `Resharp.Runtime.dll`, `FSharp.Core.dll`) dans `.deploy/`. RE-sharp est le point d'arrivée 2025 de l'arc SFA de Margus Veanes ([voir la section "Fondements bibliographiques" du README parent](../README.md#fondements-bibliographiques)).

## Pourquoi pas de notebook d'accueil pour l'instant

Le **papier RE-sharp (POPL 2025) a un PDF structurellement corrompu** sur la machine worker po-2026 au 2026-10-05 (taille disque non-nulle, 0 page extractible par PyMuPDF). Tant qu'une copie lisible n'est pas réacquise sur le disque GDrive, l'accueil pédagogique de RE-sharp ne peut pas être écrit sans inventer des details techniques (anti-régression §D, mandat user 2026-04-26).

## Action en attente (issue de suivi à ouvrir par le mainteneur)

1. Réacquérir `2025 - Veanes et al - RE-sharp - High-Performance Derivative-Based Regex Matching (POPL).pdf` en version lisible sur le disque GDrive.
2. Une fois le PDF lisible, créer un notebook d'accueil (`Resharp-01-Introduction-Python.ipynb` ou équivalent) qui démontre l'usage du package compilé sur un cas de matching regex étendu.
3. Le présent dossier `Resharp/` reste en place avec ses DLLs, en attendant le notebook d'accueil.

## Pourquoi ne pas retirer les DLLs maintenant

Les 3 DLLs sont référencées par 8 fichiers du dépôt (cf. `git grep -ilE "Resharp"` au 2026-10-05, dont `Config/Settings.cs`, `Config/SkiaUtils.cs`, `Sudoku/Sudoku-13-SymbolicAutomata-{CSharp,Python}.ipynb`, etc.). Un retrait brutal casserait des notebooks et la config de chargement. Anti-régression §D : un retrait de code de production appelle un diagnostic explicite et des tactiques d'adaptation, pas un `git rm` opportun.
