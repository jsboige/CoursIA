#!/usr/bin/env python3
"""#17417 Phase 2 -- migration DataScienceWithAgents -> ML/ML.Python.

Applique la table de correspondance validee (c.5786704244 sur l'issue #17417,
amendement WS retenu par ai-01, DM ai01-dispatch-17417-table-20260923) :

  T5  MyIA.AI.Notebooks/ML/DataScienceWithAgents/  -> MyIA.AI.Notebooks/ML/ML.Python/
  T2  sous-repertoires (04b -> 05, Track1 -> 06-Agents-LangChain, Track2 -> 07-Agents-GoogleADK,
      aplanissement de 01-Python-For-Data-Science/notebooks/)
  T3  notebooks N.M<acc>-Titre -> <Prefixe>-<NN><acc>-<Titre>-<Noyau> (94 mappages ci-dessous)

SEQUENCEMENT PAR FICHIER (decision ai-01 2026-10-23 sur #17417, T2-b) : une PR
ouverte ne retient que les fichiers du plan qu'elle touche (git mv et sweep
confondus) -- un fichier tenu attend sa PR, les autres partent. Le gel sur le
hub entier a ete retire : il ne se levait jamais, la flotte n'etant pas freinee.
Ce script se livre en mode dry-run par defaut : il construit le plan complet,
execute toutes les verifications fail-closed, et n'ecrit rien.

    python scripts/notebook_tools/migrate_dsa_mlpython.py                # dry-run complet
    python scripts/notebook_tools/migrate_dsa_mlpython.py --report-gating  # + fichiers retenus, par PR (gh)
    python scripts/notebook_tools/migrate_dsa_mlpython.py --apply        # execute (saute les fichiers tenus)

Modes inspires de la convention check_* du depot : sortie lisible par defaut,
--json pour la machine. Le dry-run sort 0 si toutes les verifications passent,
1 sinon -- il peut donc servir de garde d'execution avant --apply.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
HUB_OLD = "MyIA.AI.Notebooks/ML/DataScienceWithAgents"
HUB_NEW = "MyIA.AI.Notebooks/ML/ML.Python"

# T2 -- sous-repertoires (ancien -> nouveau), appliques au chemin relatif au hub.
# T2-01 (PR #20274, mergee le 2026-10-17) a deja renomme le dossier 01 sur main :
# la cle de la table suit le nom reel du hub, sinon la branche 01 sort de la table
# en silence (mesure c.2294 : plus aucune entree de la table ne s'appliquait a 01).
DIR_MAP = {
    "01-Python-For-Data-Science": "01-Python-For-Data-Science",
    "02-ML-Cours": "02-ML-Cours",
    "03-Deep-Learning": "03-Deep-Learning",
    "04-Vision": "04-Vision",
    "04b-Wavelet-Scattering": "05-Wavelet-Scattering",
    "Track1-LangChain": "06-Agents-LangChain",
    "Track2-GoogleADK": "07-Agents-GoogleADK",
}

# Niveau a aplatir : ces prefixes voient leur segment "notebooks/" retire.
FLATTEN_PREFIX = "01-Python-For-Data-Science/notebooks/"

# T3 -- notebooks mappes (chemin relatif au hub -> chemin relatif a ML.Python).
# Suffixe noyau d'apres kernelspec LU dans chaque notebook (mesure c.5786704244).
NOTEBOOK_MAP: dict[str, str] = {
    "01-Python-For-Data-Science/notebooks/1.1-Python_pour_la_Data_Science.ipynb":
        "01-Python-For-Data-Science/PyDS-01-Python-pour-la-Data-Science-Python.ipynb",
    "01-Python-For-Data-Science/notebooks/1.2-Manipulation_de_Donnees_avec_NumPy.ipynb":
        "01-Python-For-Data-Science/PyDS-02-Manipulation-de-Donnees-avec-NumPy-Python.ipynb",
    "01-Python-For-Data-Science/notebooks/1.3-Analyse_de_Donnees_avec_Pandas.ipynb":
        "01-Python-For-Data-Science/PyDS-03-Analyse-de-Donnees-avec-Pandas-Python.ipynb",
    "01-Python-For-Data-Science/notebooks/1.4-Visualisation_Matplotlib_Seaborn.ipynb":
        "01-Python-For-Data-Science/PyDS-04-Visualisation-Matplotlib-Seaborn-Python.ipynb",
    "01-Python-For-Data-Science/notebooks/1.5-Exploration_Nettoyage_Donnees_Reelles.ipynb":
        "01-Python-For-Data-Science/PyDS-05-Exploration-Nettoyage-Donnees-Reelles-Python.ipynb",
    "01-Python-For-Data-Science/notebooks/1.6-Statistiques_Descriptives.ipynb":
        "01-Python-For-Data-Science/PyDS-06-Statistiques-Descriptives-Python.ipynb",
    "02-ML-Cours/2.1-Workflow-ML.ipynb": "02-ML-Cours/MLPy-01-Workflow-ML-Python.ipynb",
    "02-ML-Cours/2.10-Optimisation-Hyperparametres.ipynb": "02-ML-Cours/MLPy-10-Optimisation-Hyperparametres-Python.ipynb",
    "02-ML-Cours/2.11-Regularisation-Sparse-LASSO.ipynb": "02-ML-Cours/MLPy-11-Regularisation-Sparse-LASSO-Python.ipynb",
    "02-ML-Cours/2.11b-Proximal-Operators-From-Scratch.ipynb": "02-ML-Cours/MLPy-11b-Proximal-Operators-From-Scratch-Python.ipynb",
    "02-ML-Cours/2.11c-Lasso-SOTA-Comparison.ipynb": "02-ML-Cours/MLPy-11c-Lasso-SOTA-Comparison-Python.ipynb",
    "02-ML-Cours/2.11d-Optimisation-ADMM-From-Scratch.ipynb": "02-ML-Cours/MLPy-11d-Optimisation-ADMM-From-Scratch-Python.ipynb",
    "02-ML-Cours/2.12-Donnees-Desequilibrees.ipynb": "02-ML-Cours/MLPy-12-Donnees-Desequilibrees-Python.ipynb",
    "02-ML-Cours/2.13-Analyse-Erreurs.ipynb": "02-ML-Cours/MLPy-13-Analyse-Erreurs-Python.ipynb",
    "02-ML-Cours/2.14-Explicabilite-SHAP-LIME-Contrefactuels.ipynb": "02-ML-Cours/MLPy-14-Explicabilite-SHAP-LIME-Contrefactuels-Python.ipynb",
    "02-ML-Cours/2.14b-XAI-Shap-Attribution-Causal-Bridge.ipynb": "02-ML-Cours/MLPy-14b-XAI-Shap-Attribution-Causal-Bridge-Python.ipynb",
    "02-ML-Cours/2.2-Descente-de-gradient.ipynb": "02-ML-Cours/MLPy-02-Descente-de-gradient-Python.ipynb",
    "02-ML-Cours/2.3-Regression-lineaire-logistique.ipynb": "02-ML-Cours/MLPy-03-Regression-lineaire-logistique-Python.ipynb",
    "02-ML-Cours/2.3b-Naive-Bayes-Generatif.ipynb": "02-ML-Cours/MLPy-03b-Naive-Bayes-Generatif-Python.ipynb",
    "02-ML-Cours/2.3c-Regression-Grande-Dimension.ipynb": "02-ML-Cours/MLPy-03c-Regression-Grande-Dimension-Python.ipynb",
    "02-ML-Cours/2.3d-Modele-Gaussien-LDA-QDA.ipynb": "02-ML-Cours/MLPy-03d-Modele-Gaussien-LDA-QDA-Python.ipynb",
    "02-ML-Cours/2.4-Arbres-Forets-Ensembles.ipynb": "02-ML-Cours/MLPy-04-Arbres-Forets-Ensembles-Python.ipynb",
    "02-ML-Cours/2.5-Biais-Variance-CV-ROC.ipynb": "02-ML-Cours/MLPy-05-Biais-Variance-CV-ROC-Python.ipynb",
    "02-ML-Cours/2.5b-Calibration-Probabilites.ipynb": "02-ML-Cours/MLPy-05b-Calibration-Probabilites-Python.ipynb",
    "02-ML-Cours/2.5c-Equite-Sous-Groupes.ipynb": "02-ML-Cours/MLPy-05c-Equite-Sous-Groupes-Python.ipynb",
    "02-ML-Cours/2.6-Clustering-KMeans-PCA.ipynb": "02-ML-Cours/MLPy-06-Clustering-KMeans-PCA-Python.ipynb",
    "02-ML-Cours/2.7-Modeles-Non-Parametriques.ipynb": "02-ML-Cours/MLPy-07-Modeles-Non-Parametriques-Python.ipynb",
    "02-ML-Cours/2.7b-SMO-From-Scratch.ipynb": "02-ML-Cours/MLPy-07b-SMO-From-Scratch-Python.ipynb",
    "02-ML-Cours/2.7c-SVM-SOTA-Comparison.ipynb": "02-ML-Cours/MLPy-07c-SVM-SOTA-Comparison-Python.ipynb",
    "02-ML-Cours/2.8-Theorie-PAC.ipynb": "02-ML-Cours/MLPy-08-Theorie-PAC-Python.ipynb",
    "02-ML-Cours/2.8b-Theorie-PAC-Lean.ipynb": "02-ML-Cours/MLPy-08b-Theorie-PAC-Lean.ipynb",
    "02-ML-Cours/2.8c-Borne-Temoin-Concentration.ipynb": "02-ML-Cours/MLPy-08c-Borne-Temoin-Concentration-Python.ipynb",
    "02-ML-Cours/2.8d-Lean-Novikoff-Convergence.ipynb": "02-ML-Cours/MLPy-08d-Lean-Novikoff-Convergence-Lean.ipynb",
    "02-ML-Cours/2.9-Grokking-Generalisation.ipynb": "02-ML-Cours/MLPy-09-Grokking-Generalisation-Python.ipynb",
    "02-ML-Cours/2.9b-GenEFT-Theorie-Effective.ipynb": "02-ML-Cours/MLPy-09b-GenEFT-Theorie-Effective-Python.ipynb",
    "02-ML-Cours/2.9d-Features-Circulaires-Helice-Nombres.ipynb": "02-ML-Cours/MLPy-09d-Features-Circulaires-Helice-Nombres-Python.ipynb",
    "02-ML-Cours/2.9e-MIPS-Extraction-Programme.ipynb": "02-ML-Cours/MLPy-09e-MIPS-Extraction-Programme-Python.ipynb",
    # T2-a -- les 8 carnets de 02-ML-Cours que le dry-run refusait (fail-closed mesure c.2294).
    "02-ML-Cours/2.4b-AdaBoost-From-Scratch.ipynb": "02-ML-Cours/MLPy-04b-AdaBoost-From-Scratch-Python.ipynb",
    "02-ML-Cours/2.5d-Derive-Distribution-Deploiement.ipynb": "02-ML-Cours/MLPy-05d-Derive-Distribution-Deploiement-Python.ipynb",
    "02-ML-Cours/2.9c-Grokking-Diagrammes-Phases.ipynb": "02-ML-Cours/MLPy-09c-Grokking-Diagrammes-Phases-Python.ipynb",
    "02-ML-Cours/2.9f-Grokking-Theorie-Effective-Lean.ipynb": "02-ML-Cours/MLPy-09f-Grokking-Theorie-Effective-Lean.ipynb",
    "02-ML-Cours/2.9g-Geometrie-de-la-Verite.ipynb": "02-ML-Cours/MLPy-09g-Geometrie-de-la-Verite-Python.ipynb",
    "02-ML-Cours/2.11e-CVXPY-Optimisation.ipynb": "02-ML-Cours/MLPy-11e-CVXPY-Optimisation-Python.ipynb",
    "02-ML-Cours/2.11f-Comparaison-Optimisation-Convexe.ipynb": "02-ML-Cours/MLPy-11f-Comparaison-Optimisation-Convexe-Python.ipynb",
    "02-ML-Cours/2.15-Donnee-Comme-Responsabilite-Python.ipynb": "02-ML-Cours/MLPy-15-Donnee-Comme-Responsabilite-Python.ipynb",
    "03-Deep-Learning/3.0-Theorie-Information.ipynb": "03-Deep-Learning/DL-00-Theorie-Information-Python.ipynb",
    "03-Deep-Learning/3.1-Retropropagation.ipynb": "03-Deep-Learning/DL-01-Retropropagation-Python.ipynb",
    "03-Deep-Learning/3.10-Modeles-Generatifs-Diffusion-SOTA.ipynb": "03-Deep-Learning/DL-10-Modeles-Generatifs-Diffusion-SOTA-Python.ipynb",
    "03-Deep-Learning/3.2-Optimisateurs.ipynb": "03-Deep-Learning/DL-02-Optimisateurs-Python.ipynb",
    "03-Deep-Learning/3.3-Regularisation.ipynb": "03-Deep-Learning/DL-03-Regularisation-Python.ipynb",
    "03-Deep-Learning/3.4-Attention-Transformer-From-Scratch.ipynb": "03-Deep-Learning/DL-04-Attention-Transformer-From-Scratch-Python.ipynb",
    "03-Deep-Learning/3.4c-MoE-from-scratch.ipynb": "03-Deep-Learning/DL-04c-MoE-from-scratch-Python.ipynb",
    "03-Deep-Learning/3.5-Phenomenes-de-Generalisation.ipynb": "03-Deep-Learning/DL-05-Phenomenes-de-Generalisation-Python.ipynb",
    "03-Deep-Learning/3.6-Modeles-Generatifs.ipynb": "03-Deep-Learning/DL-06-Modeles-Generatifs-Python.ipynb",
    "03-Deep-Learning/3.6b-Modeles-Generatifs-PyTorch.ipynb": "03-Deep-Learning/DL-06b-Modeles-Generatifs-PyTorch-Python.ipynb",
    "03-Deep-Learning/3.6c-Modeles-Generatifs-Diffusion-from-scratch.ipynb": "03-Deep-Learning/DL-06c-Modeles-Generatifs-Diffusion-from-scratch-Python.ipynb",
    "03-Deep-Learning/3.6d-Modeles-Generatifs-Score-SDE-from-scratch.ipynb": "03-Deep-Learning/DL-06d-Modeles-Generatifs-Score-SDE-from-scratch-Python.ipynb",
    "03-Deep-Learning/3.6e-Modeles-Generatifs-Conditionnels-from-scratch.ipynb": "03-Deep-Learning/DL-06e-Modeles-Generatifs-Conditionnels-from-scratch-Python.ipynb",
    "03-Deep-Learning/3.7-Distillation-Maitre-Eleve.ipynb": "03-Deep-Learning/DL-07-Distillation-Maitre-Eleve-Python.ipynb",
    "03-Deep-Learning/3.8-Representations-Contrastives.ipynb": "03-Deep-Learning/DL-08-Representations-Contrastives-Python.ipynb",
    "03-Deep-Learning/3.9-Compression-Quantization-FP.ipynb": "03-Deep-Learning/DL-09-Compression-Quantization-FP-Python.ipynb",
    "03-Deep-Learning/3.9a-Compression-Quantization-INT8.ipynb": "03-Deep-Learning/DL-09a-Compression-Quantization-INT8-Python.ipynb",
    "03-Deep-Learning/3.9b-Compression-Pruning-from-scratch.ipynb": "03-Deep-Learning/DL-09b-Compression-Pruning-from-scratch-Python.ipynb",
    "03-Deep-Learning/3.9c-Pruning-From-Scratch.ipynb": "03-Deep-Learning/DL-09c-Pruning-From-Scratch-Python.ipynb",
    "03-Deep-Learning/3.9e-Compression-Quantization-SOTA.ipynb": "03-Deep-Learning/DL-09e-Compression-Quantization-SOTA-Python.ipynb",
    "03-Deep-Learning/3.9f-Compression-Pruning-SOTA.ipynb": "03-Deep-Learning/DL-09f-Compression-Pruning-SOTA-Python.ipynb",
    # T2-a -- les 8 carnets de 03-Deep-Learning que le dry-run refusait (fail-closed mesure c.2294).
    "03-Deep-Learning/3.4d-Fourier-Features-Biais-Spectral-Python.ipynb": "03-Deep-Learning/DL-04d-Fourier-Features-Biais-Spectral-Python.ipynb",
    "03-Deep-Learning/3.9d-Compression-Distillation-from-scratch.ipynb": "03-Deep-Learning/DL-09d-Compression-Distillation-from-scratch-Python.ipynb",
    "03-Deep-Learning/3.9g-Compression-Comparatif-A-vs-B.ipynb": "03-Deep-Learning/DL-09g-Compression-Comparatif-A-vs-B-Python.ipynb",
    "03-Deep-Learning/3.11-Budget-Memoire-Entrainement.ipynb": "03-Deep-Learning/DL-11-Budget-Memoire-Entrainement-Python.ipynb",
    "03-Deep-Learning/3.12-Les-Collectives.ipynb": "03-Deep-Learning/DL-12-Les-Collectives-Python.ipynb",
    "03-Deep-Learning/3.13-Decouper-le-Modele-DDP-ZeRO-FSDP.ipynb": "03-Deep-Learning/DL-13-Decouper-le-Modele-DDP-ZeRO-FSDP-Python.ipynb",
    "03-Deep-Learning/3.13b-Deux-Cartes-Reelles-DDP-FSDP-nccl.ipynb": "03-Deep-Learning/DL-13b-Deux-Cartes-Reelles-DDP-FSDP-nccl-Python.ipynb",
    "03-Deep-Learning/3.14-Debug-Entrainement-N-Apprend-Pas-Python.ipynb": "03-Deep-Learning/DL-14-Debug-Entrainement-N-Apprend-Pas-Python.ipynb",
    "04-Vision/4.1-Conv-NumPy-Torch-Allclose.ipynb": "04-Vision/Vision-01-Conv-NumPy-Torch-Allclose-Python.ipynb",
    "04-Vision/4.2-ConvNet-Profonde-Residuelles.ipynb": "04-Vision/Vision-02-ConvNet-Profonde-Residuelles-Python.ipynb",
    "04-Vision/4.2b-Lean-GradientFlow-Vanishing.ipynb": "04-Vision/Vision-02b-Lean-GradientFlow-Vanishing-Lean.ipynb",
    "04-Vision/4.3-TransferLearning-ResNet.ipynb": "04-Vision/Vision-03-TransferLearning-ResNet-Python.ipynb",
    # T2-a -- les 10 carnets de 04-Vision que le dry-run refusait (fail-closed mesure
    # c.2294). Les blocs Detection 4.2c..4.2k ont ete renumerotes 4.4/4.5/4.6 par
    # #19468 (renum 04-Vision, preuve git log --diff-filter=R) : les sept entrees
    # 4.2c..4.2i de la table pointaient des fichiers disparus et sont retirees ici.
    "04-Vision/4.4-Detection-Anchor-From-Scratch.ipynb": "04-Vision/Vision-04-Detection-Anchor-From-Scratch-Python.ipynb",
    "04-Vision/4.4b-Detection-AnchorFree-From-Scratch.ipynb": "04-Vision/Vision-04b-Detection-AnchorFree-From-Scratch-Python.ipynb",
    "04-Vision/4.4c-Detection-FocalLoss-From-Scratch.ipynb": "04-Vision/Vision-04c-Detection-FocalLoss-From-Scratch-Python.ipynb",
    "04-Vision/4.5-Detection-SOTA-Torchvision.ipynb": "04-Vision/Vision-05-Detection-SOTA-Torchvision-Python.ipynb",
    "04-Vision/4.5b-Detection-SOTA-Ultralytics.ipynb": "04-Vision/Vision-05b-Detection-SOTA-Ultralytics-Python.ipynb",
    "04-Vision/4.5c-YOLOv5-Bench-Ultralytics.ipynb": "04-Vision/Vision-05c-YOLOv5-Bench-Ultralytics-Python.ipynb",
    "04-Vision/4.5d-Detection-SOTA-LibreYOLO.ipynb": "04-Vision/Vision-05d-Detection-SOTA-LibreYOLO-Python.ipynb",
    "04-Vision/4.6-Detection-Ultralytics-Difficult-Scenes.ipynb": "04-Vision/Vision-06-Detection-Ultralytics-Difficult-Scenes-Python.ipynb",
    "04-Vision/4.6b-Detection-Adversarial-Camouflage.ipynb": "04-Vision/Vision-06b-Detection-Adversarial-Camouflage-Python.ipynb",
    "04-Vision/4.6c-Detection-Dazzle-Garment-StyleTransfer.ipynb": "04-Vision/Vision-06c-Detection-Dazzle-Garment-StyleTransfer-Python.ipynb",
    "04b-Wavelet-Scattering/WS-00a-Ondelettes-1D-from-scratch.ipynb": "05-Wavelet-Scattering/WS-00a-Ondelettes-1D-from-scratch-Python.ipynb",
    "04b-Wavelet-Scattering/WS-00b-Ondelettes-2D-from-scratch.ipynb": "05-Wavelet-Scattering/WS-00b-Ondelettes-2D-from-scratch-Python.ipynb",
    "04b-Wavelet-Scattering/WS-00c-Scattering-from-scratch.ipynb": "05-Wavelet-Scattering/WS-00c-Scattering-from-scratch-Python.ipynb",
    "04b-Wavelet-Scattering/WS-01-Denoising-SOTA.ipynb": "05-Wavelet-Scattering/WS-01-Denoising-SOTA-Python.ipynb",
    "04b-Wavelet-Scattering/WS-02-Scattering-SOTA.ipynb": "05-Wavelet-Scattering/WS-02-Scattering-SOTA-Python.ipynb",
    "04b-Wavelet-Scattering/WS-03-Synthese-Scattering-vs-ResNet.ipynb": "05-Wavelet-Scattering/WS-03-Synthese-Scattering-vs-ResNet-Python.ipynb",
}

# Histogramme des noyaux du hub, etendu par T2-a a deux noyaux mesures sur main
# (c.2294) : "coursia-drift" (2.5d -- `kernelspec.language` = "python",
# `language_info.name` = "python" 3.11.16) et "py310-gpu" (4.6c --
# `kernelspec.language` vaut LITTERALEMENT "py310-gpu", c'est `language_info.name`
# qui vaut "python" 3.13.15 : le suffixe se lit la, pas dans `kernelspec.language`).
# Tous deux sont des noyaux Python : suffixe "-Python", mesure et non suppose.
KERNEL_SUFFIX = {
    "python3": "-Python",
    "coursia-ml-training": "-Python",
    "python3-coursia2": "-Python",
    "coursia-drift": "-Python",
    "py310-gpu": "-Python",
    "lean4-wsl": "-Lean",
}

# Suffixes texte balayes pour la reecriture des referents (binaire exclu).
TEXT_SUFFIXES = {".md", ".ipynb", ".yml", ".yaml", ".json", ".csv", ".py", ".txt", ".html", ".qml", ".toml", ".cfg", ".rst"}


def git(*args: str) -> str:
    r = subprocess.run(["git", "-C", str(REPO_ROOT), *args], capture_output=True, text=True, encoding="utf-8", errors="replace")
    if r.returncode != 0:
        raise RuntimeError(f"git {' '.join(args)} -> {r.returncode}: {r.stderr.strip()}")
    return r.stdout


def read_kernelspec(repo_path: str) -> str | None:
    p = REPO_ROOT / repo_path
    try:
        nb = json.loads(p.read_text(encoding="utf-8"))
    except Exception:
        return None
    ks = nb.get("metadata", {}).get("kernelspec", {})
    return ks.get("name")


def build_plan() -> tuple[list[tuple[str, str]], list[str]]:
    """Plan de deplacement : liste (ancien, nouveau) repo-relative + erreurs fail-closed."""
    errors: list[str] = []
    tracked = [l for l in git("ls-files", HUB_OLD).splitlines() if l.strip()]
    plan: list[tuple[str, str]] = []
    for old in sorted(tracked):
        rel = old[len(HUB_OLD) + 1:]
        if rel in NOTEBOOK_MAP:
            new_rel = NOTEBOOK_MAP[rel]
        else:
            new_rel = rel
            if new_rel.startswith(FLATTEN_PREFIX):
                new_rel = new_rel[len(FLATTEN_PREFIX):]
            top = new_rel.split("/", 1)[0]
            if top in DIR_MAP:
                new_rel = new_rel.replace(f"{top}/", f"{DIR_MAP[top]}/", 1)
            else:
                # fichier a la racine du hub (README.md etc.) : suit la racine
                pass
            if rel.endswith(".ipynb") and not rel.startswith(("Track1-LangChain/", "Track2-GoogleADK/")):
                # Les Labs des Tracks suivent T4 (option retenue : deplacement de
                # repertoire seulement, notebooks intacts -- table c.5786704244) :
                # ils ne relevent PAS du fail-closed T3.
                errors.append(f"notebook non couvert par la table (fail-closed): {rel}")
        plan.append((old, f"{HUB_NEW}/{new_rel}"))
    return plan, errors


def check_plan(plan: list[tuple[str, str]]) -> list[str]:
    errors: list[str] = []
    targets = [t for _, t in plan]
    dupes = {t for t in targets if targets.count(t) > 1}
    for t in sorted(dupes):
        errors.append(f"collision de cible: {t}")
    # cible deja existante hors plan (le hub ML.Python n'existe pas encore en principe)
    existing = set(git("ls-files", HUB_NEW).splitlines())
    for t in targets:
        if t in existing:
            errors.append(f"cible deja trackee sur le depot: {t}")
    # cle de table sans fichier dans l'arbre : build_plan ignore silencieusement une
    # cle morte, donc une table qui derive reste verte. Mesure c.2294 : les sept
    # entrees 4.2c..4.2i ont survecu au renumerotage 4.2x -> 4.4/4.5/4.6 (PR #19468)
    # sans qu'aucune verification ne rougisse -- fail-closed ici.
    tracked = {l[len(HUB_OLD) + 1:] for l in git("ls-files", HUB_OLD).splitlines() if l.strip()}
    for key in sorted(NOTEBOOK_MAP):
        if key not in tracked:
            errors.append(f"cle de table sans fichier dans le hub (cle morte): {key}")
    # Forme des VALEURS : le suffixe noyau ne se double pas. Le garde des cles
    # mortes ci-dessus controle les cles contre l'arbre, pas la forme des cibles --
    # il ne pouvait donc pas voir une source dont le titre porte deja le suffixe
    # (`...-Lean`, `...-Python`) et qui le recoit une seconde fois. Mesure
    # 2026-10-23 (revue NanoClaw sur #22195) : cinq cibles sortaient en
    # `...-Lean-Lean` / `...-Python-Python`, figees dans l'arbre ET dans les
    # renvois reecrits par build_replacements. On couvre la classe, sans
    # dependre de la vigilance au prochain carnet ajoute.
    kernel_suffixes = sorted(set(KERNEL_SUFFIX.values()))
    for t in sorted(set(targets)):
        stem = Path(t).stem
        for sfx in kernel_suffixes:
            if stem.endswith(sfx + sfx):
                errors.append(f"suffixe noyau double ({sfx}{sfx}): {t}")
    # kernelspec re-lu vs suffixe noyau de la table
    for old, new in plan:
        rel = old[len(HUB_OLD) + 1:]
        if rel not in NOTEBOOK_MAP:
            continue
        ks = read_kernelspec(old)
        if ks is None:
            errors.append(f"kernelspec illisible: {old}")
            continue
        expected = KERNEL_SUFFIX.get(ks)
        if expected is None:
            errors.append(f"kernelspec hors histogramme connu ({ks}): {old}")
        elif not new.endswith(expected + ".ipynb"):
            errors.append(f"suffixe noyau incoherent (kernelspec={ks}, attendu {expected}): {old} -> {new}")
    return errors


def build_replacements(plan: list[tuple[str, str]]) -> list[tuple[str, str]]:
    """Regles de reecriture, de la plus longue a la plus courte (anti remplacement partiel)."""
    reps: list[tuple[str, str]] = []
    for old, new in plan:
        rel_old, rel_new = old[len(HUB_OLD) + 1:], new[len(HUB_NEW) + 1:]
        reps.append((f"{HUB_OLD}/{rel_old}", f"{HUB_NEW}/{rel_new}"))       # chemin complet
        reps.append((f"DataScienceWithAgents/{rel_old}", f"ML.Python/{rel_new}"))  # forme serie-relative
    # formes hub-relatives pour les notebooks mappes T3 uniquement (navlinks internes)
    for rel_old, rel_new in NOTEBOOK_MAP.items():
        reps.append((rel_old, rel_new))
    # prefixes de repertoire (references a un dossier, pas a un fichier)
    for old_dir, new_dir in sorted(DIR_MAP.items(), key=lambda kv: -len(kv[0])):
        reps.append((f"{HUB_OLD}/{old_dir}", f"{HUB_NEW}/{new_dir}"))
        reps.append((f"DataScienceWithAgents/{old_dir}", f"ML.Python/{new_dir}"))
    # residu : le hub lui-meme
    reps.append((HUB_OLD, HUB_NEW))
    reps.append(("DataScienceWithAgents/", "ML.Python/"))
    # dedup + tri longueur decroissante
    seen, out = set(), []
    for a, b in reps:
        if a != b and a not in seen:
            seen.add(a)
            out.append((a, b))
    return sorted(out, key=lambda ab: -len(ab[0]))


def sweep_files() -> list[str]:
    """Fichiers texte balayes : TOUT le depot, hub inclus.

    Les notebooks du hub portent des navlinks internes RELATIFS (formes T3
    hub-relatives) qui doivent etre reecrits comme les referents externes --
    les exclure laisserait des liens morts apres migration.

    Exclusions :
      - scripts/results/ : artefacts de mesure FIGES a leur date (results-artifact-policy) ;
        le chemin d'une mesure passee est un fait de mesure, pas un lien vivant.
      - COURSE_CATALOG.generated.* : appartient a l'automation (catalog-pr-hygiene) ;
        il suivra le hub par REGENERATION a l'apply, pas par sweep manuel -- et sur
        une branche feature il reste byte-identique a main.
    """
    excluded_parts = {".lake", ".git", "_archives", "node_modules", ".venv", "venv", "__pycache__", "_peters"}
    out = []
    for line in git("ls-files").splitlines():
        p = Path(line)
        if p.suffix.lower() in TEXT_SUFFIXES and not (excluded_parts & set(p.parts)) \
                and not line.startswith("scripts/results/") \
                and not p.name.startswith("COURSE_CATALOG.generated."):
            out.append(line)
    return out


def run_sweep(reps: list[tuple[str, str]], paths: list[str] | None = None) -> tuple[dict[str, int], int]:
    """Mesure (et applique via --apply dans main) les reecritures sur les chemins donnes.

    Pre-filtre : une regex d'alternation (une passe) ecarte la grande majorite
    des fichiers qui ne referencent pas le hub ; la boucle fine sequentielle
    (ordre longueur decroissante) ne tourne que sur les fichiers concernes.
    Rend (fichier -> occurrences remplacees, total) SANS ecrire -- l'ecriture
    est faite par apply_sweep, sur le meme pre-filtre.
    """
    detector = re.compile("|".join(re.escape(a) for a, _ in reps))
    touched: dict[str, int] = {}
    total = 0
    for path in paths if paths is not None else sweep_files():
        p = REPO_ROOT / path
        try:
            raw = p.read_text(encoding="utf-8")
        except (UnicodeDecodeError, OSError):
            continue
        if not detector.search(raw):
            continue
        new = raw
        n = 0
        for a, b in reps:
            if a in new:
                n += new.count(a)
                new = new.replace(a, b)
        if n:
            touched[path] = n
            total += n
    return touched, total


def apply_sweep(reps: list[tuple[str, str]], paths: list[str]) -> int:
    """Applique les reecritures sur les chemins donnes ; rend le total ecrit."""
    detector = re.compile("|".join(re.escape(a) for a, _ in reps))
    total = 0
    for path in paths:
        p = REPO_ROOT / path
        try:
            raw = p.read_text(encoding="utf-8")
        except (UnicodeDecodeError, OSError):
            continue
        if not detector.search(raw):
            continue
        new = raw
        for a, b in reps:
            if a in new:
                new = new.replace(a, b)
        if new != raw:
            p.write_text(new, encoding="utf-8", newline="")
            total += 1
    return total


# Nombre de PRs ouvertes lues en une passe. `gh pr list` ne pagine pas
# au-dela de cette borne : atteindre la limite est une MESURE PARTIELLE, pas
# une mesure complete (reserve Hermes sur #23114). La valeur est haute (le
# pool tourne autour de 330 PRs ouvertes) mais elle reste une borne, donc
# son atteinte se detecte et se refuse -- cf. report_gating.
GH_PR_LIST_LIMIT = 1000

# Plafond de la liste `files` de `gh pr list --json files` : GraphQL ramene
# 100 entrees par PR. Une PR qui en tient plus perd la fin de sa liste, et un
# fichier du plan qu'elle detient serait alors declare LIBRE sans que rien ne
# le dise -- la classe de defaut que ce mode corrige. On repasse donc par
# l'API REST paginee des que la liste GraphQL atteint ce plafond ; si cette
# mesure echoue, la porte refuse (None), comme pour tout echec de mesure.
GH_PR_FILES_GRAPHQL_CAP = 100


def pr_files_via_rest(pr_number: int) -> list[str] | None:
    """Chemins des fichiers d'une PR via l'API REST paginee.

    None = mesure impossible (gh absent, gh en echec, reponse illisible,
    pagination sans fin). Une liste tronquee serait pire qu'un echec : elle
    ferait passer un fichier tenu pour un fichier libre.
    """
    paths: list[str] = []
    for page in range(1, 31):
        try:
            r = subprocess.run(
                ["gh", "api",
                 f"repos/jsboige/CoursIA/pulls/{pr_number}/files?per_page=100&page={page}"],
                capture_output=True, text=True, encoding="utf-8", errors="replace",
                cwd=str(REPO_ROOT))
        except FileNotFoundError:
            return None
        if r.returncode != 0:
            return None
        try:
            batch = json.loads(r.stdout or "[]")
        except json.JSONDecodeError:
            return None
        if not isinstance(batch, list):
            return None
        if not batch:
            break
        paths.extend(f["path"] for f in batch if isinstance(f, dict) and f.get("path"))
        if len(batch) < 100:
            break
    return paths


def report_gating(concerned: set[str]) -> dict[str, list[str]] | None:
    """Fichiers du plan retenus par des PRs ouvertes, PAR PR (best-effort via gh).

    Porte par fichier (decision ai-01 2026-10-23, #17417 T2-b) : une PR ouverte
    ne retient que l'INTERSECTION entre ses fichiers et les fichiers concernes
    par la migration (git mv du plan + sweep des referents) -- plus la seule
    presence d'un fichier dans le hub, qui ne se levait jamais.

    Rend {"#N": [chemins retenus tries]} ; {} = mesure faite, aucun fichier
    tenu. None = mesure impossible : gh absent, gh en echec, **liste
    tronquee** (GH_PR_LIST_LIMIT atteinte), ou PR dont la liste de fichiers
    atteint le plafond GraphQL et dont la re-mesure REST echoue. L'appelant
    refuse --apply sur None (fail-closed).

    La troncature est fail-closed pour la meme raison que l'echec gh : une
    PR hors fenetre est indiscernable d'une PR inexistante, donc un fichier
    qu'elle tient serait declare libre en silence. Une mesure partielle qui
    se tait est exactement la classe de defaut que ce mode corrige."""
    try:
        out = subprocess.run(
            ["gh", "pr", "list", "-R", "jsboige/CoursIA", "--state", "open",
             "--json", "number,files", "--limit", str(GH_PR_LIST_LIMIT)],
            capture_output=True, text=True, encoding="utf-8", errors="replace", cwd=str(REPO_ROOT))
        if out.returncode != 0:
            print(f"[gating] gh a echoue ({out.stderr.strip()[:80]}) -- mesure impossible")
            return None
    except FileNotFoundError:
        print("[gating] gh absent -- mesure impossible")
        return None
    prs = json.loads(out.stdout or "[]")
    if len(prs) >= GH_PR_LIST_LIMIT:
        print(f"[gating] TRONCATURE : {len(prs)} PRs lues (limite {GH_PR_LIST_LIMIT} atteinte) "
              "-- les PRs plus anciennes ne sont pas mesurees, mesure impossible")
        return None
    holding: dict[str, list[str]] = {}
    for pr in prs:
        files = [f["path"] for f in (pr.get("files") or [])
                 if isinstance(f, dict) and f.get("path")]
        if len(files) >= GH_PR_FILES_GRAPHQL_CAP:
            rest = pr_files_via_rest(pr["number"])
            if rest is None:
                print(f"[gating] PR #{pr['number']} : {GH_PR_FILES_GRAPHQL_CAP} fichiers ou plus, "
                      "mesure REST paginee impossible -- mesure incomplete")
                return None
            files = rest
        held = sorted({p for p in files if p in concerned})
        if held:
            holding[f"#{pr['number']}"] = held
    return holding


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description="Migration DataScienceWithAgents -> ML/ML.Python (#17417, sequencement par fichier : un fichier tenu par une PR ouverte attend sa PR)")
    ap.add_argument("--apply", action="store_true", help="execute les git mv et reecritures, en sautant les fichiers tenus par des PRs ouvertes (defaut: dry-run, aucune ecriture)")
    ap.add_argument("--report-gating", action="store_true", help="liste, par PR ouverte, les fichiers du plan qu'elle retient (via gh)")
    ap.add_argument("--json", action="store_true", help="sortie machine")
    args = ap.parse_args(argv)

    plan, errors = build_plan()
    errors += check_plan(plan)
    reps = build_replacements(plan)

    measure = args.report_gating or args.apply

    if not args.json:
        print(f"=== PLAN : {len(plan)} fichiers {HUB_OLD} -> {HUB_NEW} ===")
        print(f"--- git mv ({len(plan)}) dont notebooks renommes T3 ({len(NOTEBOOK_MAP)}) ---")
        for old, new in plan:
            marker = " [T3]" if old[len(HUB_OLD) + 1:] in NOTEBOOK_MAP else ""
            print(f"  {old} -> {new}{marker}")
        print(f"\n=== SWEEP referents ({len(reps)} regles de remplacement, ordre longueur decroissante) ===")
    touched, total = run_sweep(reps)
    gating = None
    if measure:
        # Fichiers que la migration toucherait : git mv du plan + referents sweep.
        # Une PR ouverte ne retient que cette intersection (porte par fichier).
        concerned = {old for old, _ in plan} | set(touched)
        gating = report_gating(concerned)
    if not args.json:
        print(f"--- {len(touched)} fichiers referents touches, {total} occurrences a reecrire ---")
        for path, n in sorted(touched.items(), key=lambda kv: -kv[1]):
            print(f"  {n:4d}  {path}")
    if not args.json:
        print(f"\n=== VERIFICATIONS ===")
        for e in errors:
            print(f"  ERREUR: {e}")
        if not errors:
            print("  toutes les verifications passent (collisions, cibles, kernelspecs, couverture notebooks)")
        if measure:
            if gating is None:
                print("\n=== FICHIERS RETENUS : mesure impossible (fail-closed) ===")
            elif gating:
                n_held = sum(len(v) for v in gating.values())
                print(f"\n=== FICHIERS RETENUS par des PRs ouvertes ({len(gating)} PRs, {n_held} fichiers -- attendent leur PR) ===")
                for pr_id in sorted(gating, key=lambda k: int(k[1:])):
                    print(f"  {pr_id} retient {len(gating[pr_id])} fichier(s) :")
                    for f in gating[pr_id]:
                        print(f"    {f}")
            else:
                print("\n=== FICHIERS RETENUS : aucun (aucune PR ouverte ne touche le plan) ===")
        print(f"\nmode {'APPLY' if args.apply else 'DRY-RUN (aucune ecriture)'}")

    if args.json:
        print(json.dumps({
            "plan_size": len(plan), "t3_renames": len(NOTEBOOK_MAP),
            "sweep_files": len(touched), "sweep_occurrences": total,
            "errors": errors, "gating_prs": gating,
        }, ensure_ascii=False, indent=1))

    if errors:
        return 1
    if args.apply:
        if gating is None:
            print("REFUS : mesure des PRs gelantes impossible (gate #5.4 fail-closed) -- aucun git mv execute.")
            return 1
        held = {f for files in gating.values() for f in files}
        plan_free = [(old, new) for old, new in plan if old not in held]
        # Ordre : git mv d'abord, puis sweep -- apres le mv, `git ls-files` liste
        # le hub a ses NOUVEAUX chemins (navlinks internes relatifs reecrits la),
        # les referents externes a leurs chemins inchanges. Les fichiers tenus ne
        # sont ni mv ni sweep : leur PR ouverte les tient a leur chemin actuel.
        for old, new in plan_free:
            git("mv", old, new)
        all_paths = sweep_files()
        free_paths = [f for f in all_paths if f not in held]
        n_out = apply_sweep(reps, [f for f in free_paths if not f.startswith(HUB_NEW)])
        n_hub = apply_sweep(reps, [f for f in free_paths if f.startswith(HUB_NEW)])
        if held:
            print(f"ATTENDENT leur PR ({len(held)} fichiers, porte par fichier -- #17417 T2-b) :")
            for pr_id in sorted(gating, key=lambda k: int(k[1:])):
                for f in gating[pr_id]:
                    print(f"  {pr_id}: {f}")
        if not plan_free and n_out == 0 and n_hub == 0:
            print("REFUS : tous les fichiers du plan sont retenus par des PRs ouvertes -- rien n'a ete applique.")
            return 1
        print(f"APPLIQUE : {len(plan_free)}/{len(plan)} git mv + sweep ({n_out} referents externes + {n_hub} fichiers du hub reecrits). Aucun commit -- la lane reviewe puis commit.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
