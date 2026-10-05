# Stable Marriage -- port Lean 4 (Gale-Shapley)

Lake d'amorce pour le port du résultat classique de Gale-Shapley (1962) sur le matching bilatéral stable. Le port est documenté dans [`PORT_ANALYSIS.md`](PORT_ANALYSIS.md) (Track 2, Cycle 29) : verdict **HIGH-EFFORT PORT** (800-1200 LOC, 46 lemmes, 5 théorèmes depuis [mmaaz-git/stable-marriage-lean](https://github.com/mmaaz-git/stable-marriage-lean) v4.25.0).

## État actuel

**Tranche 0** (issue #19276) : structure de la lake + stubs qui compilent + références bibliographiques honnêtes. Aucun lemme ni théorème porté -- c'est un terrain prêt pour les phases suivantes.

## Référence bibliographique

### Ouvrage-ancrage (références par métadonnées, politique d'honnêteté)

- **Roth, A. E., & Sotomayor, M. A. O. (1990)**, *Two-Sided Matching: A Study in Game-Theoretic Modeling and Analysis*, Cambridge University Press. **Ancre à confirmer** : ouvrage absent de la biblio partagée au 2026-10-05 ; pas de source libre légitime trouvée (dokumen.pub refusé, archive.org = prêt non automatisable). Acquisition à la discrétion du mainteneur. Les ancrages spécifiques (ch. 1-2 sur Gale-Shapley et optimalité, ch. 4 sur la stratégie) sont marqués `a_confirmer` jusqu'à lecture effective.

### Papier fondateur

- **Gale, D., & Shapley, L. S. (1962)**, « College Admissions and the Stability of Marriage », *American Mathematical Monthly* 69(1), pp. 9-15. Le papier fondateur de l'algorithme. Disponible en accès ouvert via JSTOR (jstor.org/stable/2312726) -- le notebook pédagogique peut le citer directement avec DOI 10.2307/2312726.

## Architecture cible (issue #19276 + PORT_ANALYSIS)

```
stable_marriage_lean/
├── lakefile.toml              # Lean 4 lake, library StableMarriage
├── README.md                  # ce fichier
├── PORT_ANALYSIS.md           # analyse du port, source inchangée
└── StableMarriage/
    ├── Basic.lean             # preferences totales + matching bijectif
    ├── GaleShapley.lean       # algorithme + GSState intermediaire
    ├── Lemmas.lean            # 46 lemmes des invariants
    └── Properties.lean        # 5 theoremes (stable, termination, etc.)
```

## Conformité i18n (EPIC #4980)

Le `lakefile.toml` utilise `globs` (et non `roots`) pour que `lake build` auto-découvre un éventuel sibling `_en` racine (`StableMarriage_en.lean`, namespace distinct). Sans globs, le sibling EN serait un **orphan-trap** non type-checké par la CI (cf. conway #6678). Convention ratifiée par user le 2026-07-04.

## Plan de port (rappel PORT_ANALYSIS)

1. **Phase 1 (200-300 LOC, 3-5 j)** : `GSState` + `step` + `runSteps` + conversion `GSState.matching → Matching n`.
2. **Phase 2 (400-600 LOC, 5-7 j)** : invariants simplifies (modele total = tout acceptable) + preservation step.
3. **Phase 3 (200-300 LOC, 3-5 j)** : `proposedCount` + `galeShapley_noBlockingPairs` + `gale_shapley_stable` (resolution du sorry L73 amont).
4. **Phase 4 (optionnelle, 300-500 LOC)** : man-optimal / woman-pessimal (Knuth 1976 lattice theory) -- non couvert par le source, developpement independant requis.

## Blocages connus

- Lean version : source v4.25.0, pin CoursIA v4.33.0. Chaque lemme du source demandera une verification de compatibilite (10-20% des preuves attendues avec adaptations tactiques).
- Blocage amont : prover BG sur fichiers casses necessite bump v4.30 depuis po-2025 avant qu'on puisse tester les preuves substantielles localement.

## Politique d'honnêteté

Aucun numero de chapitre ou d'exemple inventé. Les ancrages specifiques de Roth & Sotomayor sont marques `a_confirmer` jusqu'a lecture effective de l'ouvrage. Le papier fondateur Gale-Shapley 1962 est accessible en ligne, ses citations sont verifiables.

Co-Authored-By: Claude Haiku 4.5 (1M context) <noreply@anthropic.com>
