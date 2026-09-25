# GenAI Security — Oversight scalable et statistiques associées

Cette section héberge la distillation GenAI/sécurité issue de l'EPIC #16741 (distillation corpus Tegmark). Le fil conducteur est l'**oversight scalable** — la surveillance d'agents plus forts par des agents plus faibles — et ses statistiques d'accompagnement (Elo oversight-spécifique, scaling laws double-ReLU, NSO imbriqué).

## Source canonique

- **R12** — Engels, Baek, Kantamneni, Tegmark. *Scaling Laws For Scalable Oversight*. NeurIPS 2025. arXiv:2504.18530.
  PDF archivé hors dépôt : `G:\Mon Drive\MyIA\IA\Bibliographie IA\XAI\2025 - Engels et al - Scaling Laws For Scalable Oversight.pdf` (sha8 `FDA29C9A`).

## Pourquoi cette section

Notre cluster CoursIA-2 héberge plusieurs agents reviewers (Hermes, NanoClaw, jsboige self-bot) qui supervisent les PRs ouvertes sur `jsboige/CoursIA`. Le parallèle explicite que R12 appelle « scalable oversight » est **exactement** notre situation : des bots watchers qui doivent signaler des défauts dans du code généré par d'autres bots (potentiellement plus forts qu'eux). Le cadre Elo + scaling laws offre une métrique falsifiable du taux de détection, et la courbe NSO prédit combien de niveaux d'oversight imbriqués sont nécessaires pour maintenir un taux de succès cible.

## Notebooks et contenu

| Support | Type | Vous y trouverez |
|---------|------|------------------|
| [`Oversight/Oversight-Scaling-Laws-Nim.ipynb`](Oversight/Oversight-Scaling-Laws-Nim.ipynb) | Notebook pratique | Validation du cadre R12 sur le jeu de Nim modifié : stratégie résolue par force brute, Houdini bruité vs PerfectPlayer, fit double-ReLU par L-BFGS-B + AIC, formule NSO analytique + exploration paramétrique. Auto-contenu, exécutable sans GPU ni LLM externe. Parallèle explicite avec nos bots reviewers. |

## À venir (PR 2+)

- **PR 2** : `Oversight/Backdoor-Code-From-Scratch.ipynb` — transposition conceptuelle au cas Backdoor Code avec module stats + protocole Houdini 3 étages vs Guard majority-vote. Sans exécution LLM réelle (mandat user GenAI sur po-2023, Tell c.1261-L1 ★★★ strict). Référence : R12 §4.
- **PR 3** : `Oversight/Wargames-Simulation.ipynb` — simulation 3 rôles (R12 §5), anecdote Dr. Anya Sharma (mémorisation 12% transcripts), parallèle social-engineering sur coordinateur.
- **PR 4** : `Oversight/Oversight-Statistics.ipynb` — module stats consolidé (Elo L-BFGS-B, double-ReLU 3 phases + AIC, NSO imbriqué n*, demi-vie de contrôle) sur les 4 jeux.

## Pourquoi ces notebooks ne rejouent pas les LLMs d'Engels

R12 utilise des LLMs réels (GPT-4, Claude, Mistral) comme Houdini et Guard. po-2024 n'a pas la stack GenAI (Tell c.1261-L1 ★★★ strict), et l'exécution réelle demanderait :
- API OpenAI/Anthropic/Mistral (token-bound, hors scope session worker)
- ou stack vLLM locale sur ai-01 (91,9% idle mais sk-agent/RX9 collision non résolue)
- ou stack ComfyUI/docker sur po-2023 (GenAI dédié)

Le notebook Nim est donc une **validation du cadre théorique** sur un terrain simple auto-contenu. La transposition aux 4 jeux de R12 demanderait une PR spécifique avec accès LLM — à provisionner sur po-2023 ou ai-01 si l'EPIC continue.

## Acceptance commune

- Notebook pédagogique en français, Python, exécutable de bout en bout avec outputs réels committés.
- Module stats implémenté from scratch (Elo + L-BFGS-B + AIC + NSO).
- Parallèle explicite avec notre cluster (bots reviewers = Guards).
- Honnêteté sur les limites : ce qui n'est PAS mesuré (LLM réel), avec verdict RECOVERABLE-* posé si nécessaire (cf sota-not-workaround Prong A).

## Remerciements

Source primaire : Engels, Baek, Kantamneni, Tegmark. *Scaling Laws For Scalable Oversight*. NeurIPS 2025.

Contexte distillation : Issue T13 (Oversight scalable) de l'EPIC #16741.

Sub-grain lié : #16754. Claim posé c.1335 par myia-po-2024:CoursIA-2.

[← GenAI](../README.md)
