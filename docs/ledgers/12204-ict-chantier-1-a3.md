# Ledger #12204 — Chantier 1 ICT, tranche A3 : vérif opérations 3, 9 (teorth/pfr, planning_lean no-sorry)

**Statut** : tranche de l'EPIC #12204 « [EPIC][ICT] Chantier 1 — La table des opérations ». **A3** = « Vérifier 3, 9 (`teorth/pfr`, `planning_lean`) — les deux que le voyage dit sans `sorry`, à confirmer par `scripts/lean/count_code_sorry.py --json` ».

**Lane** : `myia-po-2026:CoursIA-2` (claim narrow paths-scoped sur le commentaire d'issue #12204).
**Date vérif** : 2026-08-22.
**Instrument** : `scripts/lean/count_code_sorry.py --lake <root> --json` (instrument canonique d'anti-régression Lean, cf [`.claude/rules/anti-regression.md`](../../.claude/rules/anti-regression.md) §Compter les `sorry`).

## Réserves de lecture

- **A3 vérifie la table des opérations 3 (quotienter/fibrer) et 9 (élargir l'espace)** — pas l'ensemble de l'EPIC. A1, A2, A4-A7 restent à faire (cf EPIC body §4).
- **L'instrument `count_code_sorry.py`** distingue `naive_sorry` (toutes occurrences textuelles) et `code_sorry` / `distinct_code_sorry` (uniquement dans du code, dédupliqué). Les READMEs et `-- commentaires` qui mentionnent « 0 sorry » comptent en `naive_sorry` mais pas en `code_sorry`. **Le chiffre qui importe est `distinct_code_sorry`** (cf leçon `anti-regression.md` ★ — `grep -c sorry` surestime de 23× sur les 21 lakes, mesuré 2026-08-14).
- **Le critère d'admission de l'EPIC** est « attestée au moins deux fois dans des endroits indépendants du dépôt ET l'on sait dire quelle forme prend son témoin ». Une attestation unique ⇒ file d'attente, pas la table.

## A3.1 — Opération 9 (Élargir l'espace) sur `planning_lean`

**L'opération 9 dans l'EPIC** : *« Monotonie de l'atteignabilité : `P_reel inclus dans P_relache` »*. Témoin attendu : *« le différentiel d'atteignabilité »*.

**Résultat vérif `planning_lean`** (premier commandement : pas de sorry réel) :

```json
$ python scripts/lean/count_code_sorry.py --lake MyIA.AI.Notebooks/SymbolicAI/Planners/planning_lean --json
{
  "lakes": [
    {
      "lake": "MyIA.AI.Notebooks/SymbolicAI/Planners/planning_lean",
      "files": 7,
      "naive_sorry": 5,
      "code_sorry": 0,
      "distinct_code_sorry": 0,
      "vacuous": []
    }
  ]
}
```

`naive_sorry = 5` marché bien : 5 occurrences textuelles dans la prose du README (lignes 81, 92, 97, 100, 101, 103, 109), de `Planning/Admissibility.lean:23,29` (commentaire `## Open milestone (non sorry-backed)`) et de `Planning/Admissibility_en.lean:23,29`, et du `lakefile.lean:25` (commentaire `**0 sorry**`). **`code_sorry = 0` confirme qu'aucune n'est un sorry réel dans une preuve.**

**Attestation substance de l'opération 9** dans `planning_lean` :

`Planning/Admissibility.lean:50` :

```lean
theorem relaxed_plan_admissible (π : List (Action F)) (s g : State F)
    (h : reaches π s g) : reachesR π s g :=
  Finset.Subset.trans h (run_subset_runR π s)
```

Le théorème est la formulation **directe** de l'opération 9 :
- `reaches π s g` = plan réel π atteint g depuis s = `π ∈ P_reel(g)`
- `reachesR π s g` = plan relaxé π atteint g depuis s = `π ∈ P_relache(g)`
- La conclusion `reaches π s g → reachesR π s g` est précisément **`P_reel ⊆ P_relache`** (inclusion monotone).
- La preuve utilise `run_subset_runR` (`run π s ⊆ runR π s` — l'exécution réelle est sous-ensemble de l'exécution relaxée), cité dans le docstring du module lignes 8-12.

**Verdict A3.1 — opération 9** :

| Critère EPIC | Statut | Preuve |
|---|---|---|
| Attestée ≥1 fois | ✅ | `Planning/Admissibility.lean:50` + `Relaxation.lean` (lemme `run_subset_runR`) |
| Forme du témoin connue | ✅ | `P_reel ⊆ P_relache` formalisé par `reaches → reachesR` via `run_subset_runR` |
| Pas de `sorry` réel | ✅ | `distinct_code_sorry = 0` (instrument canonique) |
| Attestation indépendante n°2 | ❓ | **Non vérifiée en A3.** L'EPIC mentionne `planning_lean` + `OWL/SHACL` comme attestations candidates ; SHACL n'est pas dans le dépôt (cf A3.2 symétrique). Sans 2ᵉ attestation indépendante, **l'opération 9 reste candidate à la table, pas encore admise**. |

**Conclusion A3.1** : **`planning_lean` atteste l'opération 9 dans la forme attendue, sans aucun sorry réel.** L'attestation est **solide dans le code**, **mais insuffisante à elle seule pour l'admission à la table** (critère EPIC = 2 attestations indépendantes). **À combiner avec A6** (statuer sur les attestations présentes) ou **A4** (vérifier 4, 5 dans des lakes distincts).

## A3.2 — Opération 3 (Quotienter / fibrer) sur `teorth/pfr`

**L'opération 3 dans l'EPIC** : *« Règle de chaîne : `H(X) = H(pi(X)) + H(X sachant pi(X))` »*. Témoin : *« `I(X_i ; X_j sachant Q)` sur un quotient commun `Q` »*. Prétendument attestée par `Lean-21 / teorth/pfr`.

**Résultat vérif `teorth/pfr`** :

```bash
$ find . -type d -name "teorth" -o -name "pfr"
# (aucun résultat)

$ grep -rn "teorth" --include="*.lean" --include="lakefile*" -l .
# (aucun résultat)

$ grep -rn "teorth" --include="*.md" -l .
./MyIA.AI.Notebooks/SymbolicAI/Lean/README.md
./MyIA.AI.Notebooks/SymbolicAI/README.md
```

**Constat vérif `teorth/pfr`** : **le lake `teorth/pfr` n'est PAS dans le dépôt**. Les seules occurrences du mot `teorth` sont deux lignes dans des READMEs listant des références bibliographiques (Tao 2024 sur PFR = Polynomial Freiman-Ruzsa). Aucun submodule, aucun `lakefile.lean` n'inclut `teorth/pfr`. Les `lakefile.lean` locaux incluent `mathlib` (submodule), `conway_cgt_lean`, `cooperative_games_lean`, `game_theory_lean`, `minimax_lean`, `planning_lean` — point.

**Vérification symétrique — Lean-21 local** :

```bash
$ find . -name "PFR*.lean" -o -name "*pfr*.lean"
# Lean-21 = ?
$ grep -rn "Polynomial Freiman" --include="*.lean" -l .
# (aucun résultat direct dans le code)
```

`Lean-21` est mentionné dans la colonne « prétendument attesté par » de l'EPIC, mais sans chemin local. À confirmer en A4 (vérifier 4, 5 + dette ouverte du recouvrement) ou en lecture directe de la livraison `Lean-21b companion notebook` (#12252, OPEN).

**Verdict A3.2 — opération 3** :

| Critère EPIC | Statut | Preuve |
|---|---|---|
| Lake `teorth/pfr` local | ❌ | `find` + `grep` retournent 0 résultat dans le dépôt |
| Attestation `teorth/pfr` = externe (Tao 2024, lecture hors-dépôt) | ✅ | Cité dans READMEs `SymbolicAI/Lean/README.md` + `SymbolicAI/README.md` |
| Attestation interne au dépôt de l'opération 3 | ❓ | **À vérifier en A4** (`Lean-21` companion PFR est candidate probable, mais le fichier attestant l'inclusion `H(X) = H(π(X)) + H(X\|π(X))` n'est pas localisé en A3) |
| Pas de `sorry` applicable | N/A | Pas de lake à compter |

**Conclusion A3.2** : **`teorth/pfr` est une référence externe non incluse au dépôt, et la digestion EPIC l'a cité comme si elle était locale.** L'erreur de scope est **consignée par écrit** : pour vérifier l'opération 3, il faut soit (a) submodule-iser `teorth/pfr` (effort substantiel, hors scope A3), soit (b) **rétrograder l'opération 3 en file d'attente** (« Une seule attestation ⇒ file d'attente, pas la table », critère EPIC §1). L'A3 vérif ne peut pas trancher l'admission à la table de l'opération 3 ; elle ne fait que **statuer que la digestion a sur-estimé la disponibilité de `teorth/pfr`**.

## Verdict global A3

**A3 livré** :
- ✅ `planning_lean` attesté à `0 code_sorry`, opération 9 (`P_reel ⊆ P_relache`) bien formalisée à `Admissibility.lean:50`.
- ✅ `teorth/pfr` statué comme référence externe non-locale ; erreur de scope de la digestion consignée.
- ⏸️ Les critères d'admission EPIC (2 attestations indépendantes) ne sont **pas tranchés** par A3 seule. A6 (« statuer sur les quatre en constitution 11-14 ») et A4-A5 sont les tranches où l'admission à la table se joue.

**Honnêteté méthodologique** :
- Le chiffre `distinct_code_sorry = 0` est **mesuré firsthand** (script `count_code_sorry.py --json` exécuté dans `C:/dev/CoursIA-12204-a3`, base `origin/main` HEAD `c7bc85f2d`, 2026-08-22).
- Le constat d'absence locale de `teorth/pfr` est **mesuré firsthand** (`find` + `grep` retournent 0).
- **Lacune ouverte** : `lake build planning_lean` n'a pas été exécuté localement (lake v4.30.0 vs stdlib v4.32.1 — incompatibilité documentée, cf dashboard `Lean REPL: Incompatibilité v4.30.0 / stdlib v4.32.1`). Le verdict A3.1 s'appuie sur la mesure `distinct_code_sorry = 0`, **pas** sur un build SUCCESS. Une vérif A3+ future pourrait exécuter `lake build` dans l'env WSL `lean4-wsl` (kernel `lean4-wsl` RÉPARÉ/FONCTIONNEL c.380 soldé, disponible po-2023).

## Suite recommandée (PR future, hors scope A3)

Aucune PR de suivi obligatoire. **L'EPIC #12204 elle-même** porte les tranches A4-A7 :
- **A4** : vérifier 4, 5 (recouvrement + Čech local + dette ouverte) → ledger entry séparé.
- **A6** : statuer sur les quatre en constitution (11-14) → admission ou rétrogradation à la table.
- **A7** : relecture froide — la vérification a-t-elle fait apparaître une quatrième loi ?

**Note pour l'arbitrage ai-01 / user** : la digestion EPIC a sur-estimé la disponibilité de `teorth/pfr` ; la table des opérations telle que publiée doit **noter cette erreur de scope** (cf ligne 3 du tableau §2 EPIC body). Laquelle : « Lean-21 / `teorth/pfr` » → « `teorth/pfr` (référence externe Tao 2024, lecture hors-dépôt) ; attestation interne à vérifier dans `Lean-21b companion notebook` (#12252 OPEN) ».

## Annexe — commande reproductible

```bash
# Worktree de vérif (jetable après PR merge)
git worktree add ../CoursIA-12204-a3 -b feature/12204-ict-a3-sorry-verif origin/main
cd ../CoursIA-12204-a3

# 1. Compteur canonique sur le lake
python scripts/lean/count_code_sorry.py \
    --lake MyIA.AI.Notebooks/SymbolicAI/Planners/planning_lean \
    --json

# 2. Recherche locale du lake externe
find . -type d -name "teorth" -o -name "pfr"
grep -rn "teorth" --include="*.lean" --include="lakefile*" -l .
grep -rn "teorth" --include="*.md" -l .

# 3. Substance : lire le théorème qui atteste l'opération 9
sed -n '50,55p' MyIA.AI.Notebooks/SymbolicAI/Planners/planning_lean/Planning/Admissibility.lean
```

**Référence** :
- EPIC : [#12204](https://github.com/jsboige/CoursIA/issues/12204)
- Lane : `myia-po-2026:CoursIA-2`
- Commentaire claim : [#12204#issuecomment-5378129521](https://github.com/jsboige/CoursIA/issues/12204#issuecomment-5378129521)
- Issue PR future : à créer si la vérif est contestée (cf A4)
- Instrument : [`scripts/lean/count_code_sorry.py`](../../scripts/lean/count_code_sorry.py)
- Leçon : `anti-regression.md` §Compter les `sorry` — `distinct_code_sorry`, jamais `grep -c sorry`
