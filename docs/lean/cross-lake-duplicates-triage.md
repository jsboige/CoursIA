# Doublons entre lacs Lean : triage des paires de l'organe

L'organe `scripts/lean/lean_theorem_duplicates.py` (tranche T0 de #24183) publie ses paires dans
[`docs/reference/lean-theorem-duplicates.md`](../reference/lean-theorem-duplicates.md), une page
**generee** : elle liste un signal, elle ne tranche pas. Ce document porte la moitie qui manquait —
le **triage firsthand** de chaque paire, c'est-a-dire la reponse a la question pour laquelle
l'organe a ete construit : *la duplication de preuves est-elle locale a GameTheory, ou repandue ?*

Mesure du 2026-11-02 sur `origin/main`, sortie de l'organe en mode `--json` (14 paires, 2 fortes
et 12 faibles). Chaque verdict ci-dessous vient de la lecture des enonces a la source, pas du
label de l'organe.

## Criteres de triage

Le mot « doublon » dit trois choses differentes ; le triage les separe explicitement :

- **doublon reel** : memes hypotheses et meme conclusion au contenu mathematique pres, la
  formalisation et le vocabulaire pouvant differer totalement — un resultat, deux preuves. La
  traduction d'un enonce a l'autre est un changement de vocabulaire, pas de theoreme.
- **double formalisme** : le meme resultat informel porte par deux enonces dont aucun n'est un cas
  de l'autre — deux structures (un modele de jeu contre une theorie arithmetique, par exemple)
  qu'aucune traduction directe ne relie. Renvoi croise legitime, pas de preuve a economiser.
- **homonymes** : deux enonces distincts — hypotheses de force differente, conclusion de forme
  differente — qui partagent un nom ou un token. Le lien est de famille, pas de theoreme.

## Verdict par famille

| Famille | Paires | Verdict | Raison mesuree |
|---|---|---|---|
| Arrow | 1 | **doublon reel** | meme theoreme d'impossibilite (pareto faible + IIA entrainent la dictature) sous deux encodages disjoints — Mathlib sur `Finset` contre core sur `Fin` ; consolidation en cours au triage : T1 (#24193) et T2 (#24206), ouvertes |
| Sen | 1 | **homonymes apparentes** | deux enonces du meme paradoxe, pas le meme theoreme : `minimal_liberal` (une paire decisive par individu, sans chaine imposee) contre `SenLiberalism` (chaine x≠y≠z imposee), existence d'un profil sans optimum contre negation d'une propriete — mesure T1 (#24193) |
| `fairBot_*_cooperation` | 4 | **pas des doublons** | meme theoreme, **deux formalismes** : egalite d'actions dans un modele de jeu contre prouvabilite dans une theorie de Hilbert |
| `one_sub_pow_le_exp` | 1 | **doublon reel** | meme inegalite, la seconde etant une **specialisation** de la premiere |
| `reconstruction` | 6 | faux positifs | homonymes : reconstruction de trames de Conway contre reconstruction de Fourier |
| `countP_length_filter` / `Canonical.filter` | 1 | faux positifs | objets differents partageant le token `filter` |

## Le seul doublon reel hors GameTheory

`one_sub_pow_le_exp_mul` (`SymbolicAI/Lean/mimo_lean/Converse.lean:179`) est une **instance** de
`one_sub_pow_le_exp` (`ML/learning_theory_lean/PacLearning/PacFiniteBound.lean:116`), avec
`ε = p` :

```lean
-- learning_theory_lean : la forme generale
theorem one_sub_pow_le_exp (x : ℝ) (n : ℕ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (ε : ℝ)
    (hxe : ε ≤ x) : (1 - x) ^ n ≤ Real.exp (-(ε * n))

-- mimo_lean : le cas ε = p
theorem one_sub_pow_le_exp_mul {n : ℕ} {p : ℝ} (hn : 0 < n) (hp0 : 0 ≤ p) (hp : p ≤ 1) :
    (1 - p) ^ n ≤ Real.exp (-((n : ℝ) * p))
```

L'organe classe la paire **faible** parce que les docstrings ne se ressemblent pas (Jaccard 0,00) ;
c'est un angle mort assume de son filtre de contenu, et il ne coute rien ici : l'enonce, lui, est
sans ambiguite (similarite d'enonce 0,33, la plus haute des paires faibles). La paire est **reelle**
au sens de la doctrine R4 de #24183 : un resultat, deux preuves.

Elle n'appelle **pas** une fusion : les deux lacs sont independants (`mimo_lean` et
`learning_theory_lean` ne s'importent pas), et chacun a besoin du helper dans son propre contexte de
build. La consequence R4 est de **declarer** le doublon, pas de le supprimer — renvoi croise dans
les docstrings des deux declarations et de leurs freres `_en`, en nommant laquelle est la forme
generale. Suivi : #24273.

## Pourquoi les paires FairBot ne sont pas des doublons

`game_theory_lean/ProgramGames/FairBot.lean:205` enonce l'egalite des actions des deux joueurs dans
un modele de duel :

```lean
theorem fairBot_fairBot_cooperation (d : FairBotDuel box) :
    (modalAction d.rowCooperates, modalAction d.colCooperates) = (cooperate, cooperate)
```

`formal_logic_lean/FormalLogic/FairBotLoeb.lean` enonce la cooperativite comme un **fait de
prouvabilite** dans une theorie arithmetique (`T ⊢ fairBotSelf 𝔅`, `T ⊢ p ⋏ q`). Les deux disent
bien « deux FairBots cooperent, par Lob », mais aucun des deux enonces n'est un cas de l'autre : ce
sont deux formalisations du meme theoreme, dans deux series qui ne partagent pas de vocabulaire.
Un renvoi croise y serait legitime ; il n'y a pas de preuve a economiser, donc pas de doublon.

## Consequences pour la suite

1. **La duplication de preuves est locale.** Sur 14 candidates, l'organe en trouve 1 de reelle dans
   GameTheory (Arrow — le Concern d'origine citait aussi Sen, requalifie homonyme apparente par la
   mesure T1 #24193), 1 helper analytique partage hors GameTheory, et 12 homonymes ou doubles
   formalismes. La phrase de #23097 (« aucune duplication de preuves entre lacs ») etait fausse
   pour Arrow, mais elle decrivait correctement le reste du depot.
2. **Un doublon sans fusion possible n'est pas une dette.** `one_sub_pow_le_exp` et
   `one_sub_pow_le_exp_mul` se dupliquent legitimement ; le defaut a corriger est le **silence**,
   pas la copie.
3. **L'organe ne doit pas etre elargi** pour rattraper les paires faibles qu'il rate (comme celle-ci,
   docstrings dissemblables) : son filtre de docstring est ce qui evite de noyer le tableau sous les
   lemmes generiques. Le triage humain est la couche prevue.

Part of #24183 (tranche T0, ballotage de la sortie).
