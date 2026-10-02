# Inventaire de parité — Famille `Probas/` (Infer ⇄ PyMC)

> Snapshot daté du **HEAD `bbde4dd0eb`**, branche `docs/12933-probas-parity-inventory`,
> tranche **P1** de l'[EPIC #12933](https://github.com/jsboige/CoursIA/issues/12933) (« Renumérotation
> paritaire des séries parallèles — stabiliser les identifiants sans uniformiser les contenus »),
> résidu nommé : *« étendre l'inventaire aux paires dont les suffixes ou titres ne sont pas encore
> canoniques »*.
>
> Pendant DONNÉES de l'inventaire P0 `DecisionTheory/PARITY-INVENTORY.md` (PR #13017) : sans
> inventaire, la doctrine #5081/#12933 ne dispose pas de mapping de référence pour argumenter
> les tranches de renommage à venir.

## Périmètre strict de la tranche

- **Fichiers concernés** : création du présent Markdown, lecture seule partout ailleurs.
- **Hors scope** : tout renommage (`git mv`), le registre `twin_pairs.d/`, le registre
  `zero_pad_series.json`, les README et navlinks — chaque renommage est une tranche à part
  (cf `zero_pad_series.json::_how_to_extend` : « Migrer une série est une tranche à part,
  avec ses README et ses navlinks »).
- **Sources mesurées** : arbre `Probas/Infer/` (21 notebooks) et `Probas/PyMC/` (19 notebooks)
  au HEAD ci-dessus ; les 19 paires `probas-*.yaml` du registre `twin_pairs.d` ; le registre
  `zero_pad_series.json` (#15489) ; extraction programmatique préfixe/numéro/accrétion/titre
  par stem (script jetable, non committé).

## Vue d'ensemble

```
Probas/Infer/   (C#/.NET Interactive — 21 notebooks)
  └── Infer-1   Setup                     (pad divergent)      ─┐
        Infer-1b  Premiers-Modeles          (NON APPARIÉ, C#)    │ 10 fichiers
        Infer-2   Gaussian-Mixtures         (pad divergent)      │ à numéro
        Infer-2b  Debugging-Bonnes-Pratiques (pad + titre)       │ non zero-padé
        Infer-3 … Infer-9                   (pad divergent)      │ (série NON déclarée
        Infer-08b TrueSkill-Formules-Fermees-CSharp (NON APPARIÉ)│  au garde #15489)
                                                                  ─┘
        Infer-10 … Infer-19                 (alignés)           — 10 paires alignées

Probas/PyMC/    (Python — 19 notebooks, SÉRIE DÉCLARÉE zero-pad #15489)
  └── PyMC-01 … PyMC-09 (pairs de 1-9 côté C#), PyMC-02b, PyMC-10 … PyMC-19
```

## 1. Table de parité — verdict par paire (19 paires du registre twin)

| Paire (registre) | C# (Infer) | Python (PyMC) | Verdict identifiant | Commentaire |
|---|---|---|---|---|
| Probas-1 Setup | `Infer-1-Setup` | `PyMC-01-Setup` | **PAD-DIVERGENT** (1 ↔ 01) | numéro pair, padding non |
| Probas-2 Gaussian-Mixtures | `Infer-2-Gaussian-Mixtures` | `PyMC-02-…` | **PAD-DIVERGENT** | |
| Probas-2b Debugging | `Infer-2b-Debugging-Bonnes-Pratiques` | `PyMC-02b-Debugging-Python` | **PAD + TITRE-DIVERGENT** | le titre porte le SOUS-TITRE du contenu, pas le concept commun ; `-Python` en fin de titre Python est un résidu du renommage #14873 |
| Probas-3 Factor-Graphs | `Infer-3-…` | `PyMC-03-…` | **PAD-DIVERGENT** | |
| Probas-4 Bayesian-Networks | `Infer-4-…` | `PyMC-04-…` | **PAD-DIVERGENT** | |
| Probas-5 Causal-Inference | `Infer-5-…` | `PyMC-05-…` | **PAD-DIVERGENT** | |
| Probas-7 Skills-IRT | `Infer-7-…` | `PyMC-07-…` | **PAD-DIVERGENT** | pas de paire 6 (voir §3) |
| Probas-8 TrueSkill | `Infer-8-…` | `PyMC-08-…` | **PAD-DIVERGENT** | |
| Probas-9 Classification | `Infer-9-…` | `PyMC-09-…` | **PAD-DIVERGENT** | |
| Probas-10 … 19 | `Infer-10-…` … `Infer-19-…` | `PyMC-10-…` … `PyMC-19-…` | **ALIGNÉ ×10** | Model-Selection, Topic-Models, Modeles-Hierarchiques, Crowdsourcing, Sequences, Recommenders, Sparse-Gaussian-Process, Kalman-Filter, Change-Point, Survival-Analysis |

**Aucun NUM-DIVERGENT** — contrairement à l'arc DecisionTheory (6 paires décalées d'un cran),
la famille Probas n'a jamais dérivé numériquement : les 19 numéros d'arc commun correspondent
exactement. La divergence de cette famille est **entièrement** celle du padding et, pour une
paire, du titre.

## 2. Extensions unilatérales (notebooks NON appariés)

| Notebook | Côté | Accrétion | Anomalie de nom |
|---|---|---|---|
| `Infer-1b-Premiers-Modeles.ipynb` | C# | `1b` | numéro non zero-padé (la série PyMC n'a pas de `01b`) — extension unilatérale C# à documenter, ou future paire `PyMC-01b` |
| `Infer-08b-TrueSkill-Formules-Fermees-CSharp.ipynb` | C# | `08b` | **double non-canonicité** : (a) zero-pad `08b` alors que toute la série Infer est à numéro nu — incohérent dans les DEUX conventions ; (b) suffixe kernel `-CSharp` DANS le titre, redondant avec le préfixe de série `Infer` (doctrine : le kernel ne vit que dans le suffixe canonique) |

Aucune extension unilatérale côté Python : les 19 notebooks PyMC sont tous appariés.

## 3. Trous de l'arc

- **Pas de paire 6** dans le registre ni de `PyMC-06` / `Infer-6` sur l'arbre : le numéro 6 est
  sauté des deux côtés (héritage du renommage `Infer-6 → Infer-2b` #13753 puis du
  repositionnement Python `PyMC-06 → PyMC-02b` #14873). Le trou est SYMÉTRIQUE : à préserver
  tel quel lors de toute tranche de renommage (ne pas re-numéroter 7→6).

## 4. État des gardes — ce que chaque tranche débloquerait

| Garde / registre | État mesuré pour cette famille |
|---|---|
| `check_series_zero_pad.py` (#15489, registre `zero_pad_series.json`) | **PyMC : DÉCLARÉE adoptée** (« 9 noms zero-pades, 10 numéros à deux chiffres ») · **Infer : `would_red_on_activation`, 10 violations** (les fichiers 1, 1b, 2, 2b, 3, 4, 5, 7, 8, 9) |
| `numbering_exception` du registre twin (paires 1-9) | « Zero-padding cote Python uniquement PyMC-1..9 → PyMC-01..09 (renommage #13760) ; jumeau C# Infer-1..9 non concerne » — exception **documentée mais inverse de la doctrine #12933** (« même préfixe, numéro, accrétion et titre ») |
| `check_twin_parity.py` | vert (19 paires OK au 02/10, attestations à jour) — la divergence de padding est hors de son périmètre (il compare les contenus, pas les stems) |

## 5. Mapping proposé — tranches de renommage (arbitrage coordinateur)

La doctrine ferme du 2026-09-10 (#12933) et le registre #15489 convergent : le zero-padding
est la convention d'avenir du corpus (PyMC, DecInfer, GameTheory, Search… l'ont adoptée).
La reconciliation naturelle padding la série **Infer** sur la série **PyMC** :

- **Tranche A — migration zero-pad Infer (10 renommages)** : `Infer-1 → Infer-01` …
  `Infer-9 → Infer-09`, `Infer-1b → Infer-01b`, `Infer-2b → Infer-02b`. Accompagnements
  obligatoires : README de la série, navlinks (chaînes de navigation inter-carnets),
  déclaration `Infer` dans `zero_pad_series.json` (mesure (a)+(b) du `_criterion` alors
  satisfaite), retrait de l'`numbering_exception` des 9 paires du registre twin (les deux
  côtés deviennent paddés), guard `check_series_zero_pad.py` exit 0 sur main après.
- **Tranche B — titre de la paire 2b (arbitrage)** : deux lectures possibles,
  (i) aligner sur le concept commun `Debugging` (`Infer-02b-Debugging` / `PyMC-02b-Debugging`,
  le suffixe kernel vit dans le préfixe de série — forme du reste du corpus), ou
  (ii) conserver les sous-titres distincts et documenter la paire comme extension
  partiellement distincte. Le `-Python` résiduel de `PyMC-02b-Debugging-Python` (#14873)
  ne correspond à aucune convention du corpus : à retirer dans les deux lectures.
- **Tranche C — `Infer-08b-TrueSkill-Formules-Fermees-CSharp`** : après Tranche A, le
  zero-pad devient cohérent ; reste à retirer le suffixe `-CSharp` redondant →
  `Infer-08b-TrueSkill-Formules-Fermees`. Décider en même temps si l'accrétion `08b` doit
  être rapprochée de la paire 8 (companion formel de TrueSkill, comme `DecInfer-02-Lean-…`
  dans DecisionTheory) et enregistrée comme extension unilatérale.
- **Tranche D — `Infer-1b-Premiers-Modeles`** : zero-paddé par la Tranche A (`01b`) ;
  statut (extension unilatérale C# vs future paire `PyMC-01b`) à trancher au moment de la
  Tranche A.

Ordre recommandé : A (mécanique, guard vérifiable) puis C et D (même geste de renommage,
décisions légères), B en dernier (arbitrage de fond). Chaque tranche = une PR dédiée,
jamais de composite renommage + contenu.

## 6. Ce que cette tranche ne fait pas

Aucun renommage, aucune écriture de registre, aucune modification de notebook — la donnée et
le mapping ci-dessus sont le livrable. Les arbitrages (B, C, D) appartiennent au coordinateur
au vu de cette table.
