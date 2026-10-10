# P15294 — Veille bornée : datasets RL calibrés pour petits modèles (0.8-2B)

Note de veille (acceptance 1 de #15294 ; suite review user de PR #15249, probe B #15099). See #15099, See #15249, See #1454.

Objet : recenser des datasets RL-ready **calibrés pour des backbones 0.8-2B**, là où DAPO-Math-17k (maths compétitives) rend le signal RL bruité par inaccessibilité de la tâche — le défaut de casting nommé par le user.

## Critère de calibration (les 4 conditions)

Un dataset est **calibré** pour un backbone B s'il satisfait :

1. **Accessibilité de base** — taux de réussite non trivial du backbone au prompt de base (cible indicative **20-60 %**). Sous ~10 %, le reward RL est quasi partout nul : pas de gradient utile, le verdict « trainabilité » mesure du bruit. Au-dessus de ~80 %, le plafond est trop proche pour discriminer deux backbones.
2. **Récompense vérifiable déterministe** — extraction + vérification programmatique (exact-match numérique, schéma JSON, exécution d'outil). Pas de reward model appris : le harnais probe doit rester ré-utilisable tel quel.
3. **Chaîne courte** — solutions de quelques lignes. Les traces longues type DAPO/R1 dépassent la fenêtre utile d'un 0.8-2B sous GRPO borné.
4. **Classe d'usage réelle des petits modèles** (review user) : aiguillage/outils, formulation contrainte, arithmétique simple — pas le raisonnement mathématique nu.

## Candidats

| # | Dataset | Classe de tâche | Reward vérifiable | Calibrage 0.8-2B | Source |
|---|---------|------------------|-------------------|------------------|--------|
| 1 | **xlam-function-calling-60k** | Function-calling (aiguillage/outils) — exactement la classe d'usage visée | Oui : JSON structurel + exécution réelle ; 3 stades de vérification publiés (format, exécution, sémantique), >95 % de taux correct sur échantillon humain | Conçu pour ce tier : le modèle xLAM-**1b**-fc-r en est issu | [huggingface.co/datasets/Salesforce/xlam-function-calling-60k](https://huggingface.co/datasets/Salesforce/xlam-function-calling-60k) — CC-BY-4.0, **accès gated** |
| 2 | **TinyGSM** | Arithmétique/grade-school à chaîne courte (solutions Python) | Oui : réponse numérique exacte + programme exécutable (vérificateur déterministe) | Entièrement conçu pour petits modèles : 12,3 M de problèmes synthétiques GSM-style ; le papier rapporte **81,5 % GSM8K pour un duo 1,3 B génération + 1,3 B vérification** (le vérificateur sélectionne la sortie parmi plusieurs candidats à l'inférence — pas le score du générateur seul) | Artefact [huggingface.co/datasets/TinyGSM/TinyGSM](https://huggingface.co/datasets/TinyGSM/TinyGSM) (11,8 M lignes {question, code}, MIT, non gated) ; papier [arXiv 2312.09241](https://arxiv.org/abs/2312.09241) |
| 3 | GSM8K (split train) | Contrôle grade-school (non compétitif) | Oui : exact-match numérique | Plus facile que DAPO-Math-17k ; retenu comme **bras contrôle** pour situer la courbe de difficulté, pas comme dataset d'entraînement principal | [huggingface.co/datasets/openai/gsm8k](https://huggingface.co/datasets/openai/gsm8k) |
| 4 | Countdown (synthétique, généré dans le harnais) | Arithmétique simple / jeu de composition (cibles et nombres tirés) | Oui : évaluation arithmétique déterministe de l'expression produite | Difficulté **réglable par construction** (plage des opérandes) — permet de tracer la frontière d'accessibilité des deux backbones avant tout run | Généré par le harnais (aucune source externe) |
| 5 | Hermes function-calling v1 | Function-calling single/multi-tour + JSON mode | Oui : structure JSON (schéma) — ground truth = blocs `<tool_call>` | Alternative à #1 si licence/format mieux adapté au harnais | [huggingface.co/datasets/NousResearch/hermes-function-calling-v1](https://huggingface.co/datasets/NousResearch/hermes-function-calling-v1) — Apache-2.0, non gated (~10,7 k lignes sur 5 subsets) |

## Décision — les 2 datasets retenus pour le re-run probe

1. **xlam-function-calling-60k** : c'est la classe d'usage que le user désigne comme la valeur réelle des petits modèles (aiguillage temps réel), avec un reward structurel vérifiable — l'adaptation du matcher du harnais est mince (JSON au lieu de `\boxed{}`).

**Licences & accès** (vérifiées à la source au moment de la veille) : xlam est CC-BY-4.0 **gated** (acceptation des conditions + citation APIGen, arXiv:2406.18518, par un compte habilité — pas un simple pull) ; tant que l'accès n'est pas obtenu, le harnais exécutera le **substitut documenté Hermes** (Apache-2.0, non gated, même forme de tâche single-turn). TinyGSM est MIT, non gated.
2. **TinyGSM** : math, mais à la bonne échelle de difficulté et à chaîne courte — teste si le classement 2B > 0.8B observé sur DAPO tient quand la tâche devient *accessible*, ce qui isole l'artefact de casting.

Bras contrôle optionnel : GSM8K train (intermédiaire DAPO ↔ TinyGSM en difficulté).

## Plan des runs (acceptances 2-3, cycles suivants)

- Harnais `scripts/probe_15099_dapo_grpo.py` **inchangé dans son protocole** (budget borné, multi-seed, held-out 40x4, GRPO+QLoRA) ; seule la fonction de reward/matcher change par dataset (numérique TinyGSM/GSM8K, JSON xlam).
- Backbones : MiniCPM5-2B vs Qwen3.5-0.8B (mêmes que la probe B).
- GPU : étage moyen po-2026 (16 Go, ~6,7 Go libres au claim) — suffisant pour 0.8-2B en QLoRA.
- Verdict attendu : le classement 2B > 0.8B **tient-il** sur tâche calibrée ? Si oui sur xlam mais pas sur TinyGSM, la « trainabilité RL » mesurée sur DAPO était bien un artefact de difficulté, pas une propriété des backbones.

## Résultats — runs GRPO Hermes (2026-10-08, acceptance 2 partielle)

Premiers runs du plan ci-dessus, côté Qwen3.5-0.8B (2/2 seeds). Harnais inchangé,
`run --dataset hermes` (substitut documenté de xlam, cf « Décision »). Manifestes :
`scripts/results/p15294_hermes_grpo/qwen35_seed{0,1}.json` ; entrée REGISTRY
« P15294 Hermes GRPO — Qwen3.5-0.8B 2/2 seeds ».

| seed | pre | post | Δ | longueur eval |
|---|---|---|---|---|
| 0 | 0,2063 | 0,2688 | +0,0625 | 399 → 402 |
| 1 | 0,1688 | 0,6063 | +0,4375 | 393 → 538 |

**Ce que cela répond (acceptance 3, côté 0.8B)** : le même backbone, la même
recette et le même budget qui rendaient +0,0063 ± 0,0063 (plat, courbes erratiques)
sur DAPO-Math-17k rendent **+0,2500 ± 0,1875** sur Hermes, 2/2 seeds post>pre,
sans effondrement de longueur. Le verdict M19 côté 0.8B était donc bien un
artefact de casting : la tâche olympiaque masquait le signal RL du petit modèle
au lieu de le mesurer.

**Ce qui restait ouvert (acceptance 2, côté 2B)** : les runs MiniCPM5-2B × hermes ×
2 seeds, en chaîne détachée sur le 3070 — `summarize` exige ≥ 2 modèles pour le
verdict de paire. **Livré ci-dessous le 2026-10-10.**

## Résultats — verdict de paire 2B vs 0.8B (2026-10-10, acceptances 2 et 3 closes)

Runs MiniCPM5-2B livrés par la chaîne GPU 2 (lane myia-ai-01:CoursIA-2, `SEED 1
DONE 09:59:11Z`), manifestes `scripts/results/p15294_hermes_grpo/minicpm5_seed{0,1}.json` ;
même recette GRPO+QLoRA non-thinking, même budget (100 steps, complétion ≤ 384),
même eval held-out (40 prompts × 4 générations).

| seed | pre | post | Δ | longueur eval | wallclock |
|---|---|---|---|---|---|
| 0 | 0,2125 | 0,6438 | +0,4313 | 319 → 403 | 10 657 s |
| 1 | 0,2500 | 0,6813 | +0,4313 | 326 → 437 | 7 688 s |

**Contrôle de dégénérescence (le no-op `m19` ne s'est pas reproduit).** Les runs
`m19` MiniCPM5 étaient des no-op par construction (`eos_token` du tokenizer ≠
terminateur du template → `clipped_ratio=1` + masque → loss/grad/entropy = 0,
verdict `BEATS` = bruit). Les runs de cette chaîne portent la signature inverse :
loss et grad non nuls sur 63-66 % des steps, entropy qui décroît (0,229 → 0,178 et
0,137 → 0,006), complétions d'entraînement qui raccourcissent (262 → 178 et
350 → 136 : le modèle apprend à émettre EOS) — et **aucun effondrement de longueur
à l'eval** (319 → 403, 326 → 437). Le correctif eos par modèle a bien mordu ;
les ~34-37 % de steps à loss nulle résiduelle sont les complétions encore
tronquées au budget, masquées par design.

**Verdict de paire (n=2 par modèle — tendance, pas un verdict formel)** :

| modèle | Δ moyen (2 seeds) | dispersion | post reached |
|---|---|---|---|
| MiniCPM5-2B | **+0,4313** | ±0,0000 (réplication stricte) | 0,644 / 0,681 |
| Qwen3.5-0.8B | +0,2500 | ±0,1875 (0,0625 vs 0,4375) | 0,269 / 0,606 |

Le classement 2B > 0.8B **tient en tendance** sur la tâche calibrée : delta moyen
supérieur, réplication stricte entre seeds là où le 0.8B disperse d'un facteur 7,
et post-niveau atteint plus haut et plus reproductible — pour ~3,9× moins de
wallclock cumulé (18 344 s vs 70 717 s). **À n=2 par modèle, ce n'est
pas un verdict BEATS formel** (le protocole maison exige ≥ 4 seeds) : c'est une
tendance convergente, à confirmer si l'EPIC rouvre des seeds supplémentaires.

**Ce que cela close (acceptance 3)** : le `BEATS` M19 « 2B > 0.8B » mesuré sur
DAPO-Math-17k était un double artefact — casting (la tâche olympiaque masquait le
signal du 0.8B, démontré côté Qwen 2026-10-08) **et** no-op eos (le contraste 2B
mesurait un gradient nul contre du bruit, démontré ici par la signature loss/grad
inverse). Sur Hermes avec le correctif eos, **les deux backbones produisent du
signal RL réel** et se comparent sur des gradients authentiques ; le classement
observé alors (2B devant, réplication plus propre) est la première mesure non
artefactée de la paire.

## Hors périmètre

- #15293 (retest ≥ 8-9B) : route explicitement vers po-2024/ai-01 (24 Go) — pas ce grain.
- Aucun changement au protocole de la probe B ni à ses conclusions déjà mergées : cette veille prépare leur réfutation ou confirmation, elle ne les réécrit pas.
