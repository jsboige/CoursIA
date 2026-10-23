# Volet B #18430 — Banc comparatif LeanDojo-v2 vs harnais maison : décision Pantograph

**Lane :** myia-po-2024:CoursIA · **Date :** 2026-10-12 · **Parent :** #18430 (volet B) · **Mesure rapportée sur :** #1453

## 1. La question du volet B

> « Faire passer les mêmes paliers de calibration, avec le même budget, à un
> prouveur LeanDojo-v2 et à notre harnais multi-agents, puis **rapporter
> l'écart plutôt que de le moyenner**. »

Palier retenu : **rung 52** `CALIBRATION_CONWAY_LAS_ROUND_TRIP`
(`Conway/LookAndSayLemmas.lean:41`, `digitsToNat_natToDigits`, DIFF hard) —
le rung qui a produit le verdict maison le plus documenté (passe 17,
2026-09-27 : **FAILED honnête 1→1 en 1 925,1 s**, timeout du budget de
raisonnement 1 800 s, plan correct posé en 125 s, 7 insertions BUILD-FAIL
révertées, 0 faux succès ; retry @3 600 s du 29/09 : yield delta0-stagnation).

Le banc : [`agent_tests/prover/integration/leandojo_v2_bench.py`](../../MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/prover/integration/leandojo_v2_bench.py),
pins anti-drift : [`scripts/tests/test_leandojo_v2_bench.py`](../../scripts/tests/test_leandojo_v2_bench.py).

## 2. Décision écrite : Pantograph, pas lean_runner.py (5 questions organ-first)

La question posée par le volet B était **quel organe joue le prouveur v2** :
le REPL officiel de LeanDojo-v2 (Pantograph, livré avec le package) ou une
adaptation de notre `lean_runner.py` maison. Réponses, par les 5 questions du
protocole organ-first :

1. **Quelle série possède déjà la sémantique ?** LeanDojo-v2 1.0.9 possède
   son propre REPL : le binaire `pantograph-repl` (247 Mo) embarqué dans le
   wheel, piloté par `pantograph/server.py`. C'est l'organe officiel du
   prouveur qu'on mesure — le comparer via NOTRE runner mesurerait notre
   runner, pas lui.
2. **Peut-on invoquer son module réel ?** Oui : `pip install pantograph==0.3.15`
   (pin du smoke test `MyIA.AI.Notebooks/SymbolicAI/Lean/scripts/tests/test_leandojo_v2_smoke.py`), `Server(project_path=...)`
   + `goal_start_async`/`goal_tactic_async`/`check_compile_async`. Aucun
   refactor requis côté série source.
3. **Sinon, qu'exporter/refactorer ?** Non applicable — l'organe est
   consommable tel quel. Seul le générateur de tactiques exigait un shim
   (§4 ci-dessous), qui reste DANS le banc, sans toucher au package.
4. **Quel témoin négatif l'organe fournit-il ?** Pantograph rejette
   explicitement : toolchain projet ≠ toolchain binaire (« Lean version
   mismatch »), oleans d'une autre toolchain (« incompatible header »),
   tactiques invalides (exceptions `TacticFailure`). Chaque pas du mode
   pas-à-pas est vérifié par le noyau Lean, pas par une heuristique.
5. **Quelle autre série assure la vérification indépendante ?** Le verdict
   maison du même rung (trace `multi_CALIBRATION_CONWAY_LAS_ROUND_TRIP_
   openrouter.json`, baselines/) constitue le second membre de la
   comparaison ; le mode « preuve entière » du banc passe par
   `check_compile` — compilation par le noyau, pas par le banc.

**Décision : le banc pilote Pantograph, l'organe officiel v2.** `lean_runner.py`
reste l'organe du harnais maison (second membre) ; réutiliser l'un pour jouer
l'autre contaminerait la mesure — l'écart mesuré doit être l'écart des
organes, à budget et moteur égal.

## 3. Écarts de protocole mesurés (tous documentés, aucun contourné en silence)

| # | Écart | Mesure (po-2024, 2026-10-12) |
|---|---|---|
| 1 | **Toolchain** | Le wheel Pantograph 0.3.15 embarque `pantograph/lean-toolchain` = `leanprover/lean4:v4.29.1`. conway_lean porte v4.33.0 → le REPL refuse (`Lean version mismatch`) ; des oleans v4.34.1 sont rejetées `incompatible header`. Le banc monte un **mini-lake snapshot** : code source byte-identique, Mathlib pin `v4.29.1`, sorry réintroduit au rung (1 seul `sorry`, assert au montage). |
| 2 | **Mathlib** | v4.29.1 (celle de la toolchain binaire) ≠ v4.33.0 du lake de référence. L'énoncé du rung ne dépend d'aucune API post-v4.29 (les définitions `natToDigits`/`digitsToNat` sont propres à `Conway/LookAndSay.lean`, byte-identique). |
| 3 | **LEAN_PATH** | `pantograph.utils.get_lean_path` appelle `lake env printenv LEAN_PATH`, qui rend une chaîne **vide** sur lake 5.0.0 — le banc parse `lake env printenv` intégral (`lake_lean_path`). De plus `Server(_sync_init=False)` ne résout pas `lean_path` (server.py:73) : valeur explicite obligatoire. |
| 4 | **Moteur LLM** | Aucun écart : `anthropic/claude-opus-4.7` via openrouter, le modèle des traces maison (`config.py` PROVIDERS). C'est la condition de validité de la comparaison (pin de test). |
| 5 | **Budget** | Aucun écart : plafond 1 800 s de raisonnement (aligné passe 17) + plafond d'appels LLM. |

Le shim de générateur (volet C d'ai-01, 2026-10-04, confirmé au source) :
`HFTacticGenerator` code en dur l'URL HF (`hf_runner.py:24/:67`) ET le champ
`model` du payload (`:30/:73`) — l'argument `model_name` n'agit que sur le
pre/post-traitement. La sous-classe `OpenRouterTacticGenerator` recopie les
deux corps de méthode en paramétrant URL, modèle et auth (transport OpenAI
chat-completions commun). Validée bout-en-bout sur mock CPU par ai-01.

## 4. Protocole du banc

Deux modes, même énoncé, même modèle, même budget :

- **pas-à-pas** : `goal_start(rung)` → boucle `generate(state)` →
  `goal_tactic(state, tactic)` — chaque tactique appliquée et vérifiée par
  le noyau ; les tentatives en échec sont retentées avec le dédoublonnage
  `used_tactics` du générateur.
- **preuve entière** : `generate_whole_proof(énoncé)` → `check_compile` du
  théorème complet (une seule génération, comme la passe maison « proof
  search »).

Sortie : JSON de mesure (appels LLM, pas, durée, terminaison, tactiques
essayées) + verdict `success`/`termination` par mode. L'écart au verdict
maison (FAILED 1 925,1 s / timeout raisonnement) est **rapporté** dans le fil
#1453, jamais moyenné.

## 5. Transport corrigé (2026-10-20) — le run du 2026-10-12 mesurait le transport, pas l'organe

Le premier run (2026-10-12) était **dégénéré sur les deux modes** : pas-à-pas
`generator_exhausted` en 3 appels / 5,9 s (contre 1 925 s maison), preuve
entière réduite à une ligne puis `compile_error`. Deux défauts de transport,
mesurés puis corrigés dans le shim du banc :

| # | Défaut | Mesure (po-2024, 2026-10-20) | Correctif |
|---|---|---|---|
| 1 | **`n` non honoré** | Sonde HTTP 200 sur openrouter avec `"n": 4` : **1 seul choix** rendu (l'API Anthropic n'a pas de sampling `n`). Le générateur v2 attend n échantillons par pas ; à 1 seul, le dédoublonnage `used_tactics` épuise la recherche dès que le modèle réitère. | `_post` émule `n` par requêtes successives, chacune bornée par la deadline résiduelle ; erreur API ou budget épuisé interrompt et rend les choix déjà collectés. |
| 2 | **Parser upstream une-ligne** | Branche `"claude"` de `external_parser.post_process_output` : `.split("lean")[-1].split("```")[0].split("\n")[1]` — **tronque toute sortie à une ligne**. La preuve entière brute est multi-ligne (fence comprise) ; le banc du 12/10 n'en recevait qu'une. La branche `deepseek` du même parser garde la preuve complète — bug copy-paste upstream. | `_extract_whole_proof` (module) : dés-enveloppe le bloc fence, préserve le multi-ligne — sémantique de la branche deepseek, appliquée au shim sans toucher au package. |
| 3 | **Blocs `<think>` avant la fence** | Run corrigé du 2026-10-20 : claude-opus-4.7 via openrouter peut ouvrir sa sortie d'un bloc de raisonnement `<think>...</think>` **avant** la fence — l'extracteur du correctif 2 ne regardait que le début de chaîne et rendait le bloc entier au `check_compile` (échec de parse de transport, pas un verdict d'organe). | `_extract_whole_proof` retire d'abord les blocs think (regex DOTALL), puis prend le **dernier** bloc fence s'il existe. |

Pins : `scripts/tests/test_leandojo_v2_bench.py` — l'émulation compte chaque
sous-requête **partie** (`gen.calls`, réponse en erreur et échec de transport
compris), ne part jamais avec `"n": k` dans le payload, et s'arrête net sur
budget épuisé ou erreur ; le parser injecté dans les tests **imite la branche
claude réelle** — le test exige que la preuve entière lui survive, et que le
**dernier** bloc fence gagne même lorsqu'une phrase finale le suit ou qu'un
bloc le précède.

### Run corrigé (2026-10-20) — verdicts d'organe sur les deux modes

Provenance : chiffres publiés le 2026-10-20 dans le fil de référence,
[#1453, commentaire 6300672049](https://github.com/jsboige/CoursIA/issues/1453#issuecomment-6300672049).
Le répertoire de sortie de ce run était un scratch local, **non préservé** (il
n'a jamais existé dans l'arbre) : les chiffres restent tracés par ce
commentaire, et le run se rejoue par la commande du §6 — le rejeu daté du
2026-10-23 est versé ci-dessous en agrégé committé.

| Mode | success | appels LLM | durée | terminaison |
|---|---|---|---|---|
| pas-à-pas | non | 12 (3 tours × 4 échantillons émulés) | 28,5 s | `generator_exhausted` |
| preuve entière | non | 1 | 9,5 s | `compile_error` (noyau) |

Les deux verdicts sont cette fois des comportements de l'organe, pas du
transport : en pas-à-pas le modèle ne produit que **deux familles de
tactiques** (`simp [Conway.digitsToNat, Conway.natToDigits]` et `induction n
using Conway.natToDigits.induct <;> simp [...]`), toutes deux rejetées au
noyau avec l'erreur imbriquée « maximum » dans `simp` — le dédoublonnage
`used_tactics` épuise alors la recherche. En preuve entière, la sortie
extraite est une vraie preuve multi-ligne (sans bloc think, sans fence) que
le noyau rejette. L'écart au verdict maison (FAILED 1 925,1 s / timeout du
budget) est rapporté dans le fil #1453 : mêmes verdicts FAIL des deux côtés,
mais des chemins d'effort d'un ordre de grandeur d'écart (recherche soutenue
plan/revert de 1 925 s contre épuisement du générateur en 28,5 s).

### Rejeu du 2026-10-23 (parser corrigé) — agrégé committé

Agrégé vérifiable : `scripts/results/leandojo_v2_bench_rung52_2026-10-23.json`
(même rung, même modèle, mêmes budgets, commande du §6).

| Mode | success | appels LLM | durée | terminaison |
|---|---|---|---|---|
| pas-à-pas | non | 12 | 38,8 s | `generator_exhausted` |
| preuve entière | non | 1 | 18,6 s | `compile_error` (noyau) |

Verdicts et terminaisons identiques à ceux du 2026-10-20 ; seules les durées
diffèrent (échantillonnage LLM). En preuve entière, la sortie extraite est
multi-ligne — la troncature une-ligne ne se reproduit pas sur le parser
corrigé.

## 6. Reproduction (machine po-2024)

```bash
# WSL, venv dédié (smoke 6/6 : `MyIA.AI.Notebooks/SymbolicAI/Lean/scripts/tests/test_leandojo_v2_smoke.py`)
set -a; . /mnt/d/Dev/CoursIA/.secrets/master.env; set +a   # OPENROUTER_API_KEY
export GITHUB_ACCESS_TOKEN="$(gh auth token)"             # requis constants.py
~/venvs/leandojo-v2/bin/python leandojo_v2_bench.py --mode both \
    --project ~/leandojo-v2-work/bench/rung52_conway_las
```

Le montage du mini-lake (lakefile pin v4.29.1, snapshot du sorry au rung) est
documenté dans le script de montage du scratchpad de session ; le banc
vérifie à l'exécution que le projet fourni répond (imports du REPL).

## Parametres d'echantillonnage (hypothese declaree)

Le banc code en dur : temperature 0.6, top_p 0.9, n=4 / max_tokens 256
pour la generation de tactiques, n=1 / max_tokens 1024 pour les preuves
completes (`leandojo_v2_bench.py`, `_post`). La lecture « comparaison de
l'organe, pas du moteur » suppose que la reference maison (traces du
harnais existant) a tourne aux memes parametres : cette parite n'est PAS
etablie dans le code — les parametres des traces maison ne sont pas
relisibles depuis ce depot. La comparaison se lit donc sous cette
hypothese, declaree ici (advisory 4 de la review NanoClaw).
