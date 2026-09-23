# formal_logic_lean — pont Tweety ↔ Lean et logique de prouvabilité

Lake du companion `Lean-3b-Formalized-Formal-Logic.ipynb` : le notebook exécute
les formules avec le vrai raisonneur Tweety (JVM via jpype), ce lake certifie les
mêmes formules avec le noyau Lean via la bibliothèque
[Formalized Formal Logic](https://github.com/FormalizedFormalLogic/Foundation).

## Dépendances (CONSUMER_PINNÉ, verdict #15520)

| Dépendance | Pin | Rôle |
|---|---|---|
| `FormalizedFormalLogic/Foundation` | `81810b9f` | syntaxe/sémantique propositionnelles et métathéorie arithmétique |
| `FormalizedFormalLogic/ProvabilityLogic` | `01628c51` | calcul GL, modèles de Kripke finis, points fixes et interprétation arithmétique |
| `MyIntelligenceAgency/ModalLogic` | `71968137` | cadres de Kripke génériques et cadres S4 finis (fork de compatibilité v4.33.1 de l'upstream `9c485ca9`, trois commits sans changement sémantique) |
| `mathlib4` | `v4.33.1` | transitif commun et toolchain du lake |

Aucun module upstream n'est vendu ou adapté ici : les trois bibliothèques sont
consommées à des commits exacts. Pour `ModalLogic`, l'upstream reste en Lean
4.31.0 ; le lake consomme donc un fork qui ne porte que la compatibilité avec la
toolchain 4.33.1 (le détail est dans le commentaire du `lakefile.lean`).
`require mathlib` reste en dernier, pour que les révisions transitives soient
celles de mathlib v4.33.1 et non celles du manifeste 4.31 de `ModalLogic`. Le nom Lake `Foundation`, sensible à la casse,
est déclaré à la racine afin que le pin `81810b9f` remplace bien la dépendance
transitive de même nom de `ProvabilityLogic`, plutôt que de cloner deux copies.

Le verdict du pilote #15916 est **CONSUMER_PINNÉ** : l'API upstream suffit sans
port ni adaptation locale. La fermeture propositionnelle historique reste légère
(17 modules, mesure du pilote #15520). Le fragment GL modal a compilé 1107 jobs ;
le module `FormalLogic.GLBridge`, puis le lake complet avec sa fermeture
arithmétique, ont compilé respectivement 1356 et 1361 jobs. Mesure du 2026-09-23,
après l'ajout de `ModalBridge` et de `FairBotLoeb` : le lake complet compile
1403 jobs, et `FormalLogic.FairBotLoeb` seul 1225.

L'import arithmétique reste cantonné à deux modules. `GLBridge` en a besoin pour
le théorème de correction arithmétique ; `FairBotLoeb` importe directement
`Foundation.FirstOrder.Incompleteness`, pour instancier le théorème de Löb sur la
prouvabilité standard de 𝗣𝗔. `FolBridge` n'importe que la logique du premier
ordre (sémantique, correction, complétude), sans arithmétique.

`Foundation`, `ProvabilityLogic` et `ModalLogic` déclarent Apache-2.0. Deux
dépendances transitives, `Forgive@32667a19` et `LeanTypst@2158f3de`, ne portent
aucun fichier de licence racine détecté à ces pins (vérifié le 2026-09-23 ; le
pin de `LeanTypst` est passé de `888d8656` à `2158f3de` avec l'ajout de
`ModalLogic`, #17017). Elles ne sont pas vendues
dans CoursIA, mais ce caveat doit être levé avant toute redistribution autonome
de la fermeture complète.

## Structure

- `FormalLogic/Bridge.lean` — les formules du notebook (`φPeirce`, `φOr`),
  les quatre lignes de la table de vérité comme théorèmes d'évaluation
  (`simp [models_iff_val, val]` — la sémantique FFL est Prop-valuée,
  `Valuation α := α → Prop`, un `decide` y est structurellement impossible),
  `peirce_valid` (validité par exhaustivité de la table), le contre-modèle
  `or_not_valid`, le contrôle négatif satisfiable-non-valide, et
  `peirce_provable` (versant preuve, reprise de `FFL.Entailment.peirce`).
- `FormalLogic/FolBridge.lean` — versant Lean du notebook
  `Tweety-02d-FOL-Lab-Lean.ipynb` : la même micro-théorie du premier ordre
  (quatre prédicats unaires, deux constantes). `KB ⊨ Mortel(socrate)` y devient
  un théorème de conséquence sémantique. Un contre-modèle fini à deux éléments
  montre que les deux existentiels ne fusionnent pas en un témoin unique, et que
  `∀X Mortel(X)` n'est pas conséquence.
- `FormalLogic/GLBridge.lean` — le schéma de Löb dérivé dans le calcul de
  Hilbert, une instance concrète de membership, la disponibilité de la décision
  GL sans `native_decide`, un contre-modèle fini certifiant que `¬□⊥` n'est pas
  un théorème, une spécialisation du point fixe de de Jongh–Sambin et le pont
  vers la correction arithmétique sous les conditions de Hilbert–Bernays–Löb.
- `FormalLogic/ModalBridge.lean` — l'axiome `K` est valide sur tout cadre de
  Kripke. `T`, `4` et `5` échouent chacun sur un cadre témoin qui viole
  exactement sa condition (irréflexif, non transitif, non euclidien) ; ce sont
  des contre-modèles certifiés par le noyau. Sur les cadres réflexifs et
  transitifs de `Fin74`, les duaux diamant de `T` et `4` sont des théorèmes.
- `FormalLogic/FairBotLoeb.lean` — la coopération FairBot × FairBot du
  dilemme du prisonnier entre programmes (Barasz et al., 2014) est déduite du
  théorème de Löb que FFL **prouve** (`ProvabilityAbstraction.löb_theorem`), et
  non d'un champ postulé. Le résultat est d'abord abstrait (tout prédicat de
  prouvabilité vérifiant D1–D3 sur une théorie diagonalisable), puis instancié
  sur la prouvabilité standard de 𝗣𝗔. Le module contient aussi une paire de
  FairBots de **codes distincts** (`exclusiveMultifixedpoint`). Il établit que
  FairBot n'est pas exploitable (sous l'hypothèse de Kreisel), qu'il coopère
  avec CooperateBot, et qu'il n'est pas prouvable face à DefectBot. Il montre
  enfin que la défection n'y est pas prouvable non plus (second théorème de
  Gödel), alors qu'elle est vraie dans le modèle standard. La leçon de ce
  module : une modalité qui vérifie D1–D3 sans lemme diagonal ne donne pas le
  théorème de Löb. C'est la `Diagonalization` qui manque, pas une quatrième
  condition.

La procédure de décision GL est exposée comme instance `Decidable`. Sur le
schéma concret de Löb, sa réduction par `decide` reste bloquée dans la réduction
noyau de `search0`; le certificat de membership utilise donc la dérivation de
Hilbert. Le projet n'emploie pas `native_decide`, interdit par l'audit d'axiomes.

## Build

```bash
cd MyIA.AI.Notebooks/SymbolicAI/Lean/formal_logic_lean
lake exe cache get   # oleans Mathlib 4.33.1
lake build
```

Voir aussi : `Lean-3b-Formalized-Formal-Logic.ipynb` (le notebook),
`../Tweety/Tweety-5d-Stable-Synthesis-Lean.ipynb` (le patron générateur →
certificat), `../../../docs/lean/` (pièges tactiques).
