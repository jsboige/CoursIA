# Chantier 1 — tranche A5 : opérations 2, 6, 10 après la distillation Sandholm

**EPIC** : [#12204](https://github.com/jsboige/CoursIA/issues/12204) · **lane** `myia-po-2024:CoursIA` · **date de mesure** 2026-09-27 · **base** `1e19752a233`
**Tranches sœurs** : [A2](12204-ict-chantier-1-a2.md) (opération 1) · [A3](12204-ict-chantier-1-a3.md) (opérations 3, 9) · [A4](12204-ict-chantier-1-a4.md) (opération 4) · [audit froid](12204-ict-chantier-1-audit-froid.md) (les 14 opérations, trois axes) · [A6](12204-ict-chantier-1-a6.md) (statuation 11-13 + file d'attente)

## Ce que cette tranche fait

A5 vérifiait « **2, 6, 10** — dépendent de la distillation Sandholm (chantier 5) : à faire **après** elle ». Le chantier 5 ([#12208](https://github.com/jsboige/CoursIA/issues/12208)) est **CLOSED COMPLETED** depuis le 2026-09-18 (fermeture sur vérification firsthand ai-01, 5 volets #12211-#12215) — la précondition est levée. Cette tranche confronte les verdicts de l'audit froid (rendus quand #12208 était OPEN) aux artefacts désormais sur `main`, et statue.

## Opération 2 — « Abstraire à dette bornée » : première attestation in-repo atterrie, reste en file d'attente

L'audit froid la descendait : « Kroer-Sandholm **externe** tant que sa distillation (#12208) n'a pas atterri ; `MechanismDesign.lean` atteste un mécanisme (op 10), pas une borne d'abstraction » — in-repo : **0 attestation**.

**Ce que la distillation a laissé sur `main`** : `GameTheory/GameTheory-19-Abstraction-a-Dette.ipynb` — relu et mesuré firsthand ce cycle :

- **Toutes les cellules code exécutées, 0 erreur, sorties réelles.**
- Exercice 1 : abstraction par **fusion d'états** (partition de 6 duels 2×2 en 3 blocs, duels moyens) — le geste *compresser*.
- Exercice 2 : **solve exact** de l'abstrait (énumération de supports), **retransport** dans le jeu d'origine, **mesure dans G** — le geste *résoudre et relever*. Sortie mesurée : `v(G) = -4.2143`.
- Exercice 3 : **courbe de dette** sur la chaîne de raffinement P6 < P4 < P3 < P2 (chaîne **vérifiée** dans la sortie), exploitability retransportée mesurée : `6 → 0.0000 · 4 → 1.9091 · 3 → 1.9091 · 2 → …` — le témoin de la loi (`Exploitability(σ_G) ≤ ε(α)` sous forme de courbe).

**Verdict** : première attestation **in-repo** de l'op 2, exécutée, témoin en la forme attendue (la dette mesurée, pas alléguée). Une seule ⇒ **file d'attente maintenue** — le critère §1 est mécanique. À promouvoir **dès le second usage** (candidat naturel : une seconde série du dépôt — Search, p. ex. — qui abstrait un problème de recherche à perte bornée mesurée).

## Opération 6 — « Réparer localement sous garantie » : première attestation in-repo atterrie, reste en file d'attente

L'audit froid la descendait : « une seule famille (Sandholm) » — in-repo : **0 attestation** (le « mauvais recollement → déviation » n'était qu'une lecture).

**Ce que la distillation a laissé sur `main`** : la paire `GameTheory-13b-Safe-Subgame-Solving.ipynb` (toutes ses cellules code exécutées, 0 erreur) + son jumeau C# auditeur `13c` (idem, 40 sorties) :

- 13b développe le triplet complet : **blueprint** avec exploitabilité baseline → **raffinement naïf** qui *détruit* l'équilibre (le contre-témoin) → **recollement sûr avec conditions de bord** (safe subgame solving) → exercice 3 : **contrôler la garantie** du recollement. La conclusion relie explicitement à la LOI I (obstruction → témoin exploitable).
- 13c (jumeau .NET) **audit** 13b et calcule « la vraie best-response que 13b assertait sans la calculer » — la paire porte donc témoin **mesuré**, pas asserté. Les jumeaux d'une même paire ne comptent pas pour deux attestations (même contenu mathématique, convention twins).

**Verdict** : première attestation **in-repo** de l'op 6 (la paire 13b/13c), exécutée, garantie contrôlée. Une seule ⇒ **file d'attente maintenue**, à promouvoir dès le second usage.

## Opération 10 — déjà TABLE, reconfirmée firsthand

L'audit froid l'avait promue (GT-16b, GT-20, SC-27 — trois familles). Relecture firsthand ce cycle de `GameTheory-16b-Automated-Mechanism-Design.ipynb` (toutes les cellules code exécutées, 0 erreur) : le mécanisme **est** la variable de décision (`M* = argmax_{M∈ℳ} J(M)` s.c. IC/IR/budget, énoncé verbatim), générateur et vérificateur **séparés**, et l'exercice 3 exhibe le **témoin d'impossibilité** (déviation profitable, ensemble admissible vide). La conclusion borne honnêtement le scope (« un bond dans l'espace, pas la strate 7 »). **Aucun changement** — la promotion tient.

## État de la table après cette tranche

Inchangé en composition (voir [A6](12204-ict-chantier-1-a6.md) pour l'état courant) : **TABLE** = numérotées 1, 4, 7, 8, 9, 10, 11, 12, 13, 14 + `point fixe` · **FILE D'ATTENTE** = **2** et **6** (désormais **1 attestation in-repo chacune**, premières posées par la distillation) · 3, 5 (1 chacune) · `institutionnaliser`, `inhiber`, `réviser une croyance`.

**Ce que A5 change** : les opérations 2 et 6 passent de « zéro attestation in-repo, précondition externe non remplie » à « première attestation posée et mesurée, seconde manquante ». La gate (#12208) qui conditionnait A5 est levée — la suite n'attend plus rien d'externe : les secondes attestations sont des grains de **contenu** créables dans d'autres séries (patron op 12 : GT-21 + Search-12a).
