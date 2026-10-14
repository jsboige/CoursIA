# Resharp — RE-sharp (Veanes et al, POPL 2025) en attente d'accueil

## État au 2026-10-09

Ce dossier porte le **package compilé** RE-sharp (3 DLLs : `Resharp.dll`, `Resharp.Runtime.dll`, `FSharp.Core.dll`) dans `.deploy/`. RE-sharp est le point d'arrivée 2025 de l'arc SFA de Margus Veanes ([voir la section "Fondements bibliographiques" du README parent](../README.md#fondements-bibliographiques)).

## Pourquoi pas de notebook d'accueil pour l'instant

Le **papier RE-sharp (POPL 2025) n'est pas extractible localement** sur la machine worker po-2026 au 2026-10-09 — mais ce n'est pas une propriété du document : le fichier **existe** sur le disque GDrive, et la non-lecture est celle d'un **cache Drive non hydraté** (voir la « Note de lecture » du [README parent](../README.md#fondements-bibliographiques)). Aucune réacquisition n'est nécessaire. L'accueil pédagogique de RE-sharp reste à écrire : il demande de **lire le papier**, ce qui suppose une copie locale extractible, faute de quoi les détails techniques seraient inventés (anti-régression §D, mandat user 2026-04-26).

## Action en attente

1. Lire le papier RE-sharp (POPL 2025) depuis une copie locale extractible, puis créer un notebook d'accueil (`Resharp-01-Introduction-Python.ipynb` ou équivalent) qui démontre l'usage du package compilé sur un cas de matching regex étendu.
2. Le présent dossier `Resharp/` reste en place avec ses DLLs, en attendant le notebook d'accueil.

## Pourquoi ne pas retirer les DLLs maintenant

Les 3 DLLs sont référencées **hors les DLLs elles-mêmes** par plusieurs fichiers et configurations du dépôt — `git grep -ilE "Resharp" | grep -v 'Resharp/\.deploy/'` au 2026-10-05 : `.gitignore`, `Config/{Settings,SkiaUtils,Utils}.cs`, `Sudoku/Sudoku-13-SymbolicAutomata-{CSharp,Python}.ipynb`, le présent README, `SMT/README.md`, `README.md` racine, `translations/smt/README.md`, `translations/sudoku/sudoku.csv`. Un retrait brutal casserait des notebooks et la config de chargement. Anti-régression §D : un retrait de code de production appelle un diagnostic explicite et des tactiques d'adaptation, pas un `git rm` opportun.
