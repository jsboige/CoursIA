# GenAI Security — Oversight scalable, contrôle par interprétabilité et red team

Cette section héberge la distillation GenAI/sécurité issue de l'EPIC #16741 (distillation corpus Tegmark), complétée par un axe sécurité des outils d'agents, un axe red team opérationnelle et un axe défense par construction des agents outillés. Cinq axes y cohabitent :

- **Oversight scalable** (sub-grain #16754) — la surveillance d'agents plus forts par des agents plus faibles — et ses statistiques d'accompagnement (Elo oversight-spécifique, scaling laws double-ReLU, NSO imbriqué). Source : R12.
- **Contrôle par interprétabilité** (sub-grain #16758) — direction du refus, ablation directionnelle, steering, finetuning shallow, machine unlearning et évaluation awareness, mesurés sur un témoin synthétique. Sources : R11 et R14.
- **Surface d'attaque des outils** (issue #18213) — les attaques du client MCP sur la couche outils : injection par description (tool poisoning), rug pull (mutation du catalogue après approbation), collision de noms entre serveurs — et leurs défenses (empreinte SHA-256, diff d'inventaire, allowlist qualifiée), démontrées sur des serveurs MCP locaux réels.
- **Red team au-delà de l'injection** (pli 3 de #19543, thème 9) — les familles d'attaque que l'injection ne couvre pas : jailbreaks mesurés sur un modèle local réel, empoisonnement de corpus et backdoor de données d'entraînement, typosquatting et intégrité de la chaîne d'approvisionnement, bac à sable et permissions d'un agent outillé.
- **Défense par construction des agents outillés** (issue #27512) — l'inversion du problème : plutôt que *détecter* l'injection, la rendre *structurellement impossible* — le plan est produit par le modèle sur la seule demande de l'user (les données ne sont jamais dans son contexte), chaque valeur porte une étiquette de provenance `USER`/`DATA` propagée par fusion, et une politique refuse tout appel d'outil dont un argument sensible est teinté `DATA`. Mesuré sur un banc de 40 scénarios contre trois agents (capacités, ReAct, ReAct + filtre) sur un modèle local 7B.

## Sources canoniques

- **R12** — Engels, Baek, Kantamneni, Tegmark. *Scaling Laws For Scalable Oversight*. NeurIPS 2025. arXiv:2504.18530.
  PDF archivé hors dépôt : `G:\Mon Drive\MyIA\IA\Bibliographie IA\XAI\2025 - Engels et al - Scaling Laws For Scalable Oversight.pdf` (sha8 `FDA29C9A`).
- **R11** — Casper et al. *The 2026 Singapore Consensus on Global AI Safety Research Priorities*. arXiv:2608.14611.
  PDF archivé hors dépôt : `G:\Mon Drive\MyIA\IA\Bibliographie IA\XAI\2026 - Casper et al - The 2026 Singapore Consensus on Global AI Safety Research Priorities.pdf` (sha8 `134E9DA8`).
- **R14** — Sharkey et al. *Open Problems in Mechanistic Interpretability*. arXiv:2501.16496.
  PDF archivé hors dépôt : `G:\Mon Drive\MyIA\IA\Bibliographie IA\XAI\2025 - Sharkey et al - Open Problems in Mechanistic Interpretability.pdf` (sha8 `9A50CDC6`).
- **R15** — Zeng, Severi, Bullwinkel, Horvitz, Papailiopoulos. *Lazare, veni foras: Reprogramming Dormant Neurons to Backdoor AI Agents*. Microsoft Research, 10/11/2026. Code : `github.com/microsoft/lazarus`.
  PDF archivé hors dépôt : `G:\Mon Drive\MyIA\IA\Bibliographie IA\AI\2026 - Zeng Severi Bullwinkel Horvitz Papailiopoulos - Lazare veni foras - Reprogramming Dormant Neurons to Backdoor AI Agents.pdf`.
- **R16** — Gu, Dolan-Gavitt, Garg. *BadNets: Identifying Vulnerabilities in the Machine Learning Model Supply Chain*. 2017. arXiv:1708.06733.
  PDF archivé hors dépôt : `G:\Mon Drive\MyIA\IA\Bibliographie IA\MachineLearning\Image Generation, Multimodality and Robustness\2017 - Gu et al - BadNets - Identifying Vulnerabilities in the Machine Learning Model Supply Chain (arXiv 1708.06733).pdf`.
- **R17** — Tran, Li, Madry. *Spectral Signatures in Backdoor Attacks*. 2018. arXiv:1811.00636.
  PDF archivé hors dépôt : `G:\Mon Drive\MyIA\IA\Bibliographie IA\MachineLearning\Image Generation, Multimodality and Robustness\2018 - Tran et al - Spectral Signatures in Backdoor Attacks (arXiv 1811.00636).pdf`.
- **R18** — Chen, Carvalho, Baracaldo, Li, et al. *Detecting Backdoor Attacks on Deep Neural Networks by Activation Clustering*. 2018. arXiv:1811.03728.
  PDF archivé hors dépôt : `G:\Mon Drive\MyIA\IA\Bibliographie IA\MachineLearning\Image Generation, Multimodality and Robustness\2018 - Chen et al - Detecting Backdoor Attacks on Deep Neural Networks by Activation Clustering (arXiv 1811.03728).pdf`.

## Pourquoi cette section

Notre cluster CoursIA-2 héberge plusieurs agents reviewers (Hermes, NanoClaw, jsboige self-bot) qui supervisent les PRs ouvertes sur `jsboige/CoursIA`. Le parallèle explicite que R12 appelle « scalable oversight » est **exactement** notre situation : des bots watchers qui doivent signaler des défauts dans du code généré par d'autres bots (potentiellement plus forts qu'eux). Le cadre Elo + scaling laws offre une métrique falsifiable du taux de détection, et la courbe NSO prédit combien de niveaux d'oversight imbriqués sont nécessaires pour maintenir un taux de succès cible.

## Notebooks et contenu

| Support | Type | Vous y trouverez |
|---------|------|------------------|
| [`Oversight/Oversight-Scaling-Laws-Nim.ipynb`](Oversight/Oversight-Scaling-Laws-Nim.ipynb) | Notebook pratique | Validation du cadre R12 sur le jeu de Nim modifié : stratégie résolue par force brute, Houdini bruité vs PerfectPlayer, fit double-ReLU par L-BFGS-B + AIC, formule NSO analytique + exploration paramétrique. Auto-contenu, exécutable sans GPU ni LLM externe. Parallèle explicite avec nos bots reviewers. |
| [`Oversight/Oversight-Scaling-Laws-Analytics.ipynb`](Oversight/Oversight-Scaling-Laws-Analytics.ipynb) | Notebook pratique | Balayage paramétrique exhaustif des formules R12 : inversion analytique de l'Elo oversight-spécifique, heatmap du niveau d'oversight optimal `n*(D, q)`, fit double-ReLU sur données synthétiques. |
| [`Oversight/Oversight-Scaling-Laws-Wargames.ipynb`](Oversight/Oversight-Scaling-Laws-Wargames.ipynb) | Notebook pratique | Scénario Wargames de R12 §5 en simulation stochastique pure : protocole 3 rôles (Defender / Attacker bayésien / Judge), sans LLM externe. |
| [`Oversight/Backdoor-Code-From-Scratch.ipynb`](Oversight/Backdoor-Code-From-Scratch.ipynb) | Notebook pratique | Jeu **Backdoor Code** de R12 §3.3 et §A.3 : pipeline de Houdini en trois étages (cinq idées → implémentation pour une entrée précise → entrée déclencheuse), relancé jusqu'à cinq fois, contre un Guard à cinq jugements au vote majoritaire. Mesure les deux taux que le papier distingue — viabilité et tromperie — et reproduit la nuance de la Fig. 13 : conditionnellement à une porte viable, la tromperie ne croit pas avec la capacité, si bien que la montée apparente du taux non conditionnel est un pur effet de composition. Contient aussi l'inversion du vote majoritaire sous le seuil de Condorcet (empiler des juges faibles dégrade le verdict) et le constat que le modèle NSO le plus simple ne produit pas la *Goldilocks zone* de R12. Auto-contenu, sans GPU ni appel réseau ; transposition aux LLMs de R12 déclarée `RECOVERABLE-MACHINE`. |
| [`Oversight/Oversight-Scaling-Laws-Statistics.ipynb`](Oversight/Oversight-Scaling-Laws-Statistics.ipynb) | Notebook pratique | Consolidation du module statistique du sub-grain #16754 (Elo L-BFGS-B, double-ReLU 3 phases + AIC, NSO imbriqué n*) et relecture des trois notebooks précédents. |
| [`Oversight/Backdoor-Dormant-Neurons.ipynb`](Oversight/Backdoor-Dormant-Neurons.ipynb) | Notebook pratique | Rejeu de **R15** (*Lazarus*) à petite échelle, sur un transformeur SwiGLU entraîné ici : sélection des neurones dormants du dernier bloc MLP (filtre par norme d'écriture, puis sélection gloutonne par KL), calibration de la porte sur une expression déclencheuse apprise, écriture alignée sur le jeton de charge utile (Lazarus-Analytic) puis affinage limité aux poids édités (Lazarus-SGD). Mesure le taux de déclenchement, la fuite sur trafic bénin et la dérive bénine, puis la contre-mesure : sonde de poids (colinéarité de la porte) et audit de checkpoints par un agent de frontière, sans modèle de référence. Charge utile volontairement inerte. Transposition à l'échelle réelle déclarée `RECOVERABLE-MACHINE`. |
| [`Oversight/Backdoor-Detection-Spectral-Clustering.ipynb`](Oversight/Backdoor-Detection-Spectral-Clustering.ipynb) | Notebook pratique | Détection de porte dérobée par **activation** dans un petit classifieur de texte : empoisonnement BadNets à trois taux de contamination (précision propre 100 %, ASR ~90 %), deux détecteurs d'activation réimplémentés — signature spectrale (Tran, 2018) et clustering des activations (Chen, 2018) — dont le second pointe nettement la classe cible, nettoyage (retirer les porteurs, réentraîner) qui ramène l'ASR au hasard en préservant la précision, mesure multi-graine, et la limite honnête du déclencheur paraphrasé. CPU seul, from scratch, corpus synthétique ; la transposition à un LLM open-weights réel est déclarée `RECOVERABLE-MACHINE`. |
| [`Control/Control-Refusal-Direction.ipynb`](Control/Control-Refusal-Direction.ipynb) | Notebook pratique | Contrôle par interprétabilité (R11 §2.2.5, R14 §3.1-3.2) sur un témoin synthétique entraîné from scratch : direction du refus par différence de moyennes, ablation directionnelle (brute vs centrée) et son contrôle aléatoire, dose-réponse de steering, finetuning shallow à dix exemples avec contrôle négatif, tableau forget/retain et simulation du biais d'évaluation awareness. Auto-contenu, exécutable sans GPU ni LLM externe ; le passage à une famille open-weights réelle est déclaré `RECOVERABLE-MACHINE`. |
| [`Tooling/Tooling-MCP-Attack-Surface.ipynb`](Tooling/Tooling-MCP-Attack-Surface.ipynb) | Notebook pratique | Surface d'attaque des outils MCP (issue #18213) : trois attaques démontrées de bout en bout sur des serveurs MCP stdio locaux écrits puis exécutés dans le notebook (injection par description, rug pull après approbation, collision de noms entre serveurs), et trois défenses mesurables (empreinte SHA-256 par outil, diff d'inventaire AJOUT/RETRAIT/MUTATION, allowlist qualifiée par serveur). Auto-contenu, exécutable sans GPU ni LLM externe. |
| [`RedTeam/RedTeam-Beyond-Injection.ipynb`](RedTeam/RedTeam-Beyond-Injection.ipynb) | Notebook pratique | Red team au-delà de l'injection (pli 3 de #19543) : quatre familles mesurées une par une — jailbreaks (six gabarits d'attaque × deux cibles de politique bénignes contre `qwen2.5:7b` servi en local par Ollama, juge déterministe, température nulle), empoisonnement (détournement d'un TF-IDF from scratch par trois documents piégés, backdoor d'un classifieur de sentiment à 10 % de données contaminées avec contrôle), chaîne d'approvisionnement (détection de typosquatting par distance de Levenshtein, vérification SHA-256), bac à sable (allow-list + prison de chemins opposées à huit tentatives d'injection par résultat d'outil, trou de quota mesuré). Trois exercices C.1. Auto-contenu ; la section jailbreak exige Ollama en local (`RECOVERABLE-LOCAL` sinon). |
| [`Capability/Capability-Plan-Data-Separation.ipynb`](Capability/Capability-Plan-Data-Separation.ipynb) | Notebook pratique | Défense **par construction** contre l'injection indirecte (issue #27512) : séparation plan/données — le plan est produit sur la seule demande de l'user, les données lues par une étape isolée sans appel d'outil, étiquettes de provenance `USER`/`DATA` propagées par fusion, politique refusant tout argument sensible teinté `DATA`. Banc de 40 scénarios (20 tâches légitimes + 20 injections) mesurant trois agents (capacités, ReAct, ReAct + filtre d'allowlist) sur `qwen2.5:7b` servi en local par Ollama ; chaîne de provenance d'un appel ; point aveugle du filtre (le corps du message n'est pas inspecté). Trois exercices C.1. Auto-contenu ; le modèle local 7B est exigé (`RECOVERABLE-LOCAL` sinon). |

## Sous-séries

Chaque axe de la section porte son propre README, écrit depuis les carnets de main :

| Sous-série | README |
|---|---|
| [Oversight](Oversight/README.md) | Mesurer la surveillance d'un agent : scaling laws, backdoors, détection |
| [Control](Control/README.md) | Contrôle par interprétabilité : direction du refus, ablation, unlearning |
| [Tooling](Tooling/README.md) | Surface d'attaque des outils MCP et leurs défenses mesurées |
| [RedTeam](RedTeam/README.md) | Red team au-delà de l'injection : jailbreaks, empoisonnement, chaîne, bac à sable |
| [Capability](Capability/README.md) | Défense par construction : séparation plan/données, provenance `USER`/`DATA` |

## État des livraisons du sub-grain #16754

Les quatre notebooks annoncés par le plan initial (PR 1 à PR 4) sont livrés dans `Oversight/` : le notebook Nim (PR 1, base expérimentale), puis `Oversight-Scaling-Laws-Analytics`, `Oversight-Scaling-Laws-Wargames` et `Oversight-Scaling-Laws-Statistics` (module consolidé). Les noms de fichiers ont évolué par rapport au plan d'origine ; les fichiers listés dans le tableau ci-dessus sont la référence.

La vérification tierce du 2026-10-07 (commentaire `[PARTIAL]` sur #16754) a nommé deux carnets du plan qui n'étaient pas matérialisés : `Backdoor-Code-From-Scratch.ipynb` et `Wargames-Simulation.ipynb`. Le premier est livré ici ; le second reste ouvert sur #16754.

## Pourquoi ces notebooks ne rejouent pas les LLMs d'Engels

R12 utilise des LLMs réels (GPT-4, Claude, Mistral) comme Houdini et Guard. po-2024 n'a pas la stack GenAI ([cluster-agents.md](../../../docs/reference/cluster-agents.md)), et l'exécution réelle demanderait :
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

Sources primaires : Engels, Baek, Kantamneni, Tegmark, *Scaling Laws For Scalable Oversight* (R12, NeurIPS 2025) ; Casper et al., *The 2026 Singapore Consensus on Global AI Safety Research Priorities* (R11) ; Sharkey et al., *Open Problems in Mechanistic Interpretability* (R14) ; Zeng, Severi, Bullwinkel, Horvitz, Papailiopoulos, *Lazare, veni foras: Reprogramming Dormant Neurons to Backdoor AI Agents* (R15, Microsoft Research, 10/11/2026).

Contexte distillation : issues T13 (#16754, oversight scalable) et T17 (#16758, contrôle par interprétabilité) de l'EPIC #16741.

Sub-grains liés : #16754 (claim posé c.1335 par myia-po-2024:CoursIA-2) et #16758 (claim posé c.1441 par myia-po-2024:CoursIA-2).

[← GenAI](../README.md)
