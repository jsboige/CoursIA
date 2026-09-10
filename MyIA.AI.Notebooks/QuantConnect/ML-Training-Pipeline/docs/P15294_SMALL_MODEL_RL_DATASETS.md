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

## Hors périmètre

- #15293 (retest ≥ 8-9B) : route explicitement vers po-2024/ai-01 (24 Go) — pas ce grain.
- Aucun changement au protocole de la probe B ni à ses conclusions déjà mergées : cette veille prépare leur réfutation ou confirmation, elle ne les réécrit pas.
