/-
  Visite guidée des résultats de DominikPeters/SocialChoiceLean
  =============================================================

  Ce fichier propose une présentation commentée des principaux résultats
  formalisés dans DominikPeters/SocialChoiceLean, importé comme dépendance Lake.

  Dépôt : https://github.com/DominikPeters/SocialChoiceLean
  Auteur : Dominik Peters (Université de Glasgow)
  Licence : MIT

  Contributions majeures :
  1. Théorème de Gibbard-Satterthwaite (non-manipulabilité ⇒ dictature)
  2. 4 impossibilités de Condorcet
  3. Théorème de Duggan-Schwartz (non-manipulabilité multi-vainqueurs)
  4. Impossibilité de Holliday (résolvabilité du Split Cycle)
  5. 15+ règles de vote avec satisfaction d'axiomes vérifiée
-/

-- Cadre de base
import SocialChoice.Profile
import SocialChoice.Margin
import SocialChoice.Rules

-- Axiomes
import SocialChoice.Axioms.Core
import SocialChoice.Axioms.Pareto
import SocialChoice.Axioms.Dictatorship
import SocialChoice.Axioms.Strategyproofness
import SocialChoice.Axioms.Condorcet
import SocialChoice.Axioms.Monotonicity
import SocialChoice.Axioms.Neutrality
import SocialChoice.Axioms.Anonymity
import SocialChoice.Axioms.Clones

-- Théorèmes d'impossibilité
import SocialChoice.Impossibilities.GibbardSatterthwaite.Main

-- Règles de vote
import SocialChoice.Rules.SplitCycle.Defs
import SocialChoice.Rules.Schulze.Defs
import SocialChoice.Rules.Black.Defs
import SocialChoice.Rules.Copeland.Defs
import SocialChoice.Rules.Minimax.Defs
import SocialChoice.Rules.TopCycle.Defs
import SocialChoice.Rules.UncoveredSet.Defs

namespace PetersTour

open SocialChoice

/-! ## 1. Vue d'ensemble du cadre

DominikPeters utilise un type `VotingRule` polymorphe :
```
abbrev VotingRule := ∀ {V A : Type} [Fintype V] [Fintype A], Profile V A → Finset A
```

Un `Profile V A` associe chaque votant `v : V` à un `LinearOrder A` (ordre linéaire strict).
Cela diffère de notre cadre fondé sur `PrefOrder` (qui utilise des relations réflexives +
totales + transitives via `R x y : Prop`).

Différences clés avec notre port (asouther4/chasenorman) :
- Peters : `LinearOrder A` (classe Mathlib Lean 4, décidable)
- Notre : `PrefOrder α` (structure personnalisée, `R x y : Prop`)
- Peters : `VotingRule` polymorphe sur tous V, A
- Notre : `SCC ι σ` types fixes, fondé sur `PrefOrder`

-/


/-! ## 2. Théorème de Gibbard-Satterthwaite

**Théorème** (Gibbard 1973, Satterthwaite 1975) :
Toute règle de vote résolue avec ≥ 3 candidats qui satisfait
l'Unanimité et la Non-manipulabilité doit être dictatoriale.

Ceci est formalisé dans `SocialChoice.Impossibilities.GibbardSatterthwaite.Main` :
```
theorem gibbard_satterthwaite
    {V A : Type} [Fintype V] [Nonempty V] [Fintype A] [Nonempty A]
    (hcardA : 3 ≤ Fintype.card A)
    (f : VotingRule)
    (hf_res : Resolute f)
    (hf_unan : Unanimity f)
    (hf_sp : ResoluteStrategyproofness f hf_res) :
    ∃ d : V, ∀ P : Profile V A, f P = {topChoice P d}
```

Structure de la preuve :
- Récurrence forte sur le nombre de votants
- Cas de base (1 votant) : trivialement dictatoriale
- Pas inductif : cloner un votant, appliquer l'hypothèse de récurrence à
  l'électorat réduit, puis analyser si le dictateur est le votant cloné (Cas 2)
  ou un autre votant (Cas 1)
-/


/-! ## 3. Impossibilités de Condorcet

DominikPeters formalise 4 résultats d'impossibilité liés à Condorcet :

1. **Condorcet + Participation ⇒ impossible** (Moulin 1988)
   `SocialChoice.Impossibilities.CondorcetParticipation`

2. **Condorcet + Renforcement ⇒ impossible** (Young 1975)
   `SocialChoice.Impossibilities.CondorcetReinforcement`

3. **Condorcet + Non-manipulabilité ⇒ impossible** (variante de Gibbard-Satterthwaite)
   `SocialChoice.Impossibilities.CondorcetStrategyproofness`

4. **Anonyme + Neutre + Résolu ⇒ impossible** (pour un nombre pair de votants)
   `SocialChoice.Impossibilities.AnonymousNeutralResolute`
-/


/-! ## 4. Théorème de Duggan-Schwartz

Le théorème de Duggan-Schwartz étend Gibbard-Satterthwaite aux règles multi-vainqueurs :
si une règle de vote satisfait OptimistStrategyproof ET PessimistStrategyproof,
est non triviale et surjective, alors elle admet un « ensemble nominatif » qui agit
comme une coalition dictatoriale.

Formalisé dans `SocialChoice.Impossibilities.DugganSchwartz.Main`.
-/


/-! ## 5. Règles de vote et leurs propriétés

DominikPeters vérifie la satisfaction d'axiomes pour 15+ règles de vote :

### Règles consistantes avec Condorcet
- **Split Cycle** (Holliday & Pacuit 2023) : méthode acyclique par comparaison de marges
  `SocialChoice.Rules.SplitCycle`
  Vérifié : Condorcet, Monotonicité, Pareto, Neutralité, Smith, Clones

- **Schulze** (Schulze 2011) : comparaison par chemins
  `SocialChoice.Rules.Schulze`
  Vérifié : Condorcet, Monotonicité, Neutralité, Smith, Clones, Transitivité

- **Copeland** : score victoires/défaites
  `SocialChoice.Rules.Copeland`
  Vérifié : Condorcet, Monotonicité, Neutralité, Pareto, Smith

- **Top Cycle** (ensemble de Smith) : élément maximal de la relation de majorité
  `SocialChoice.Rules.TopCycle`
  Vérifié : Condorcet, Monotonicité, Smith, Majorité mutuelle

- **Uncovered Set** : fondé sur la relation de couverture
  `SocialChoice.Rules.UncoveredSet`
  Vérifié : Condorcet, Monotonicité, Neutralité, Smith, Clones

- **Black** : vainqueur de Condorcet s'il existe, sinon Borda
  `SocialChoice.Rules.Black`
  Vérifié : Condorcet, Monotonicité, Neutralité, Pareto

### Règles à élimination
- **Instant Runoff Voting (IRV)** : élimination séquentielle
  `SocialChoice.Rules.ScoringElimination.InstantRunoffVoting`
  Vérifié : CondorcetLoser, Majorité, Majorité mutuelle, Clones

- **Baldwin** : élimination fondée sur Borda
  `SocialChoice.Rules.ScoringElimination.Baldwin`
  Vérifié : Condorcet, CondorcetLoser, Smith

- **Coombs** : élimination du dernier rang
  `SocialChoice.Rules.ScoringElimination.Coombs`
  Vérifié : Condorcet, CondorcetLoser, Majorité

### Règles de score
- **Compte de Borda** : `SocialChoice.Rules.ScoringRules.Borda`
  Vérifié : Monotonicité, Neutralité, Pareto, Participation

- **Pluralité** : `SocialChoice.Rules.ScoringRules.Plurality`
  Vérifié : Monotonicité, Majorité

- **Veto/Anti-pluralité** : `SocialChoice.Rules.ScoringRules.Veto`
  Vérifié : Monotonicité, Majorité
-/


/-! ## 6. Référence des définitions clés

```
-- Profile : associe les votants à des ordres linéaires stricts
structure Profile (V A : Type) [Fintype V] [Fintype A] where
  pref : V → LinearOrder A

-- Margin : différence de soutien par paires
noncomputable def margin {V A} [Fintype V] [Fintype A]
    (P : Profile V A) (a b : A) : Int

-- Condorcet winner : bat tous les autres à la majorité stricte
def CondorcetWinner {V A} [Fintype V] [Fintype A]
    (P : Profile V A) (c : A) : Prop

-- Split Cycle defeat : marge positive, pas de cycle plus fort
noncomputable def splitCycleDefeats {V A} [Fintype V] [Fintype A]
    (P : Profile V A) (x y : A) : Prop :=
  margin_pos P x y ∧
    ¬ ∃ c : List A, x ∈ c ∧ y ∈ c ∧
      cycle (fun a b => margin P x y ≤ margin P a b) c
```
-/


/-! ## 7. Tableau récapitulatif des axiomes

Les attributs `@[scAxiom]` et `@[scRule]` marquent les définitions pour le
cadre de vérification d'axiomes. Chaque fichier de règle prouve la satisfaction
d'axiomes à l'aide de lemmes `PreservedUnderRefinement` pour un raisonnement compositionnel.

| Axiome | Définition |
|-------|------------|
| Resolute | Vainqueur unique pour chaque profil |
| NonTrivial | Un candidat peut perdre |
| Onto | Chaque candidat peut gagner |
| Unanimity | Si tous classent c premier, c gagne |
| ParetoEfficiency | Les candidats unanimement dominés perdent |
| CondorcetConsistency | Le vainqueur de Condorcet gagne uniquement |
| CondorcetLoserCriterion | Les perdants de Condorcet ne gagnent jamais |
| Monotonicity | Monter c préserve la victoire de c |
| Neutrality | Permuter les candidats permute les vainqueurs |
| Anonymity | Permuter les votants ne change pas le résultat |
| Strategyproofness | Aucun votant ne peut gagner en mentant |
| Clones | Cloner un candidat préserve le résultat |
| Smith | Seuls les candidats de l'ensemble de Smith gagnent |
| Reinforcement | Union d'électorats disjoints ⇒ intersection |
| Participation | Ajouter des votants avec c en tête préserve c gagnant |
| Reversal | Inverser tous les bulletins inverse les perdants |
| Resolvability | Une sortie non singleton peut être résolue |
-/

end PetersTour
