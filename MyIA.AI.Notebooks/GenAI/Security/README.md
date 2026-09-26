# GenAI Security — Oversight scalable et contrôle par interprétabilité

Cette section héberge la distillation GenAI/sécurité issue de l'EPIC #16741 (distillation corpus Tegmark). Deux axes y cohabitent :

- **Oversight scalable** (sub-grain #16754) — la surveillance d'agents plus forts par des agents plus faibles — et ses statistiques d'accompagnement (Elo oversight-spécifique, scaling laws double-ReLU, NSO imbriqué). Source : R12.
- **Contrôle par interprétabilité** (sub-grain #16758) — direction du refus, ablation directionnelle, steering, finetuning shallow, machine unlearning et évaluation awareness, mesurés sur un témoin synthétique. Sources : R11 et R14.

## Sources canoniques

- **R12** — Engels, Baek, Kantamneni, Tegmark. *Scaling Laws For Scalable Oversight*. NeurIPS 2025. arXiv:2504.18530.
  PDF archivé hors dépôt : `G:\Mon Drive\MyIA\IA\Bibliographie IA\XAI\2025 - Engels et al - Scaling Laws For Scalable Oversight.pdf` (sha8 `FDA29C9A`).
- **R11** — Casper et al. *The 2026 Singapore Consensus on Global AI Safety Research Priorities*. arXiv:2608.14611.
  PDF archivé hors dépôt : `G:\Mon Drive\MyIA\IA\Bibliographie IA\XAI\2026 - Casper et al - The 2026 Singapore Consensus on Global AI Safety Research Priorities.pdf` (sha8 `134E9DA8`).
- **R14** — Sharkey et al. *Open Problems in Mechanistic Interpretability*. arXiv:2501.16496.
  PDF archivé hors dépôt : `G:\Mon Drive\MyIA\IA\Bibliographie IA\XAI\2025 - Sharkey et al - Open Problems in Mechanistic Interpretability.pdf` (sha8 `9A50CDC6`).

## Pourquoi cette section

Notre cluster CoursIA-2 héberge plusieurs agents reviewers (Hermes, NanoClaw, jsboige self-bot) qui supervisent les PRs ouvertes sur `jsboige/CoursIA`. Le parallèle explicite que R12 appelle « scalable oversight » est **exactement** notre situation : des bots watchers qui doivent signaler des défauts dans du code généré par d'autres bots (potentiellement plus forts qu'eux). Le cadre Elo + scaling laws offre une métrique falsifiable du taux de détection, et la courbe NSO prédit combien de niveaux d'oversight imbriqués sont nécessaires pour maintenir un taux de succès cible.

## Notebooks et contenu

| Support | Type | Vous y trouverez |
|---------|------|------------------|
| [`Oversight/Oversight-Scaling-Laws-Nim.ipynb`](Oversight/Oversight-Scaling-Laws-Nim.ipynb) | Notebook pratique | Validation du cadre R12 sur le jeu de Nim modifié : stratégie résolue par force brute, Houdini bruité vs PerfectPlayer, fit double-ReLU par L-BFGS-B + AIC, formule NSO analytique + exploration paramétrique. Auto-contenu, exécutable sans GPU ni LLM externe. Parallèle explicite avec nos bots reviewers. |
| [`Oversight/Oversight-Scaling-Laws-Analytics.ipynb`](Oversight/Oversight-Scaling-Laws-Analytics.ipynb) | Notebook pratique | Balayage paramétrique exhaustif des formules R12 : inversion analytique de l'Elo oversight-spécifique, heatmap du niveau d'oversight optimal `n*(D, q)`, fit double-ReLU sur données synthétiques. |
| [`Oversight/Oversight-Scaling-Laws-Wargames.ipynb`](Oversight/Oversight-Scaling-Laws-Wargames.ipynb) | Notebook pratique | Scénario Wargames de R12 §5 en simulation stochastique pure : protocole 3 rôles (Defender / Attacker bayésien / Judge), sans LLM externe. |
| [`Oversight/Oversight-Scaling-Laws-Statistics.ipynb`](Oversight/Oversight-Scaling-Laws-Statistics.ipynb) | Notebook pratique | Consolidation du module statistique du sub-grain #16754 (Elo L-BFGS-B, double-ReLU 3 phases + AIC, NSO imbriqué n*) et relecture des trois notebooks précédents. |
| [`Control/Control-Refusal-Direction.ipynb`](Control/Control-Refusal-Direction.ipynb) | Notebook pratique | Contrôle par interprétabilité (R11 §2.2.5, R14 §3.1-3.2) sur un témoin synthétique entraîné from scratch : direction du refus par différence de moyennes, ablation directionnelle (brute vs centrée) et son contrôle aléatoire, dose-réponse de steering, finetuning shallow à dix exemples avec contrôle négatif, tableau forget/retain et simulation du biais d'évaluation awareness. Auto-contenu, exécutable sans GPU ni LLM externe ; le passage à une famille open-weights réelle est déclaré `RECOVERABLE-MACHINE`. |

## État des livraisons du sub-grain #16754

Les quatre notebooks annoncés par le plan initial (PR 1 à PR 4) sont livrés dans `Oversight/` : le notebook Nim (PR 1, base expérimentale), puis `Oversight-Scaling-Laws-Analytics`, `Oversight-Scaling-Laws-Wargames` et `Oversight-Scaling-Laws-Statistics` (module consolidé). Les noms de fichiers ont évolué par rapport au plan d'origine ; les fichiers listés dans le tableau ci-dessus sont la référence.

## Pourquoi ces notebooks ne rejouent pas les LLMs d'Engels

R12 utilise des LLMs réels (GPT-4, Claude, Mistral) comme Houdini et Guard. po-2024 n'a pas la stack GenAI (Tell c.1261-L1 ★★★ strict), et l'exécution réelle demanderait :
- API OpenAI/Anthropic/Mistral (token-bound, hors scope session worker)
- ou stack vLLM locale sur ai-01 (91,9% idle mais sk-agent/RX9 collision non résolue)
- ou stack ComfyUI/docker sur po-2023 (GenAI dédié)

Le notebook Nim est donc une **validation du cadre théorique** sur un terrain simple auto-contenu. La transposition aux 4 jeux de R12 demanderait une PR spécifique avec accès LLM — à provisionner sur po-2023 ou ai-01 si l'EPIC continue.

Le notebook de contrôle suit la même discipline : la chaîne R14 §3.1-3.2 est implémentée **au code près** (différence de moyennes, ablation directionnelle, steering, finetuning court, tableau forget/retain), mais sur un témoin synthétique entraîné from scratch plutôt que sur un LLM réel. Le verdict est écrit dans le notebook : le passage à une famille open-weights (Qwen) est `RECOVERABLE-MACHINE` et se porterait sur une lane disposant de la stack GenAI ou d'un cache HuggingFace.

## Acceptance commune

- Notebook pédagogique en français, Python, exécutable de bout en bout avec outputs réels committés.
- Module stats implémenté from scratch (Elo + L-BFGS-B + AIC + NSO).
- Parallèle explicite avec notre cluster (bots reviewers = Guards).
- Honnêteté sur les limites : ce qui n'est PAS mesuré (LLM réel), avec verdict RECOVERABLE-* posé si nécessaire (cf sota-not-workaround Prong A).

## Remerciements

Sources primaires : Engels, Baek, Kantamneni, Tegmark, *Scaling Laws For Scalable Oversight* (R12, NeurIPS 2025) ; Casper et al., *The 2026 Singapore Consensus on Global AI Safety Research Priorities* (R11) ; Sharkey et al., *Open Problems in Mechanistic Interpretability* (R14).

Contexte distillation : issues T13 (#16754, oversight scalable) et T17 (#16758, contrôle par interprétabilité) de l'EPIC #16741.

Sub-grains liés : #16754 (claim posé c.1335 par myia-po-2024:CoursIA-2) et #16758 (claim posé c.1441 par myia-po-2024:CoursIA-2).

[← GenAI](../README.md)
