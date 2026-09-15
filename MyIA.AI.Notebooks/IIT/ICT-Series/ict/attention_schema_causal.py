"""Case 5bis (#15798) — extension causale du case 5 (Graziano AST, #8182).

Le case 5 (#15547, verdict readout INCONCLUSIF) mesurait UNE seule chose : le
taux de propagation workspace ``propa`` distingue-t-il une cible attentionnelle
d'une cible d'objet ? Non, a ce substrat (SAE layer 12/24 de
Qwen3.5-2B-Base) : le broadcast est quasi-uniforme. C'est une limite de
l'AXE readout, pas une preuve d'absence du schema dans l'ETAT interne.

Le moteur d'interventions causales #15479 (``ict/causal_engine.py`` +
``scripts/causal_hooks.py``, tranches #15599/#15605/#15609 mergees) ajoute
exactement l'axe manquant : intervertir / ecrire / clamper l'etat et mesurer
SEPAREMENT les canaux etat / readout / comportement (EPIC #15475 : « toujours
separer effet sur l'etat, effet sur le readout et effet comportemental »).

Les trois axes de case 5bis
---------------------------

**Etat (numpy, traces gelees).** Les 9 prompts d'une graine sont 3 bras
(attn_self / attn_other / obj_chaise) x 3 contextes partage a l'identique :
seul le segment terminal (la clause de tache) differe. On densifie les
panneaux SAE sur l'univers {features differentielles de la paire} u {features
aleatoires appariees du controle}, on localise la fenetre de divergence par
comparaison des tokens, puis via le moteur : ``patch`` de la tranche clause du
donneur dans le receveur (+ ``interchange_panels`` bilateral en verrou de
coherence), sham (ecriture de soi-meme, voie de code partagee) et controle
aleatoire apparie en norme ET frequence (:func:`random_target_matched`).
Effet = deplacement du centroide de clause du receveur vers le centroide du
donneur (cosinus), cible vs sham vs aleatoire, dommage general
(:func:`damage_metrics`) et selectivite rendus par le moteur.

**Readout (numpy, traces gelees).** La question case 5 etait : la SIGNATURE
workspace (top-64 de l'activation moyenne du bras) capture-t-elle les
consommateurs reels ? Case 5bis demande : apres patch de l'etat, la signature
du bras VIRTUEL (moyenne recalcullee avec la clause patchee) migre-t-elle de
la signature du bras receveur vers celle du donneur (Jaccard), et le taux de
consommateurs reels captures par la nouvelle signature bouge-t-il ? Les
consommateurs restent les vrais (traces gelees) : l'axe est honnete sur ce
qu'il ne peut pas faire (pas de re-forward), et c'est exactement la limite
que le verdict case 5 avait mesuree.

**Comportement (GPU, ``scripts/run_case5bis_live.py``).** Sur modele vivant :
capture-puis-ecriture de la tranche clause en espace latent SAE (encode ->
edition moteur sur le panneau latent -> decode ``h' = h - acts@W_dec +
acts'@W_dec``), generation greedy 24 tokens, classification LEXICON
deterministe de la cible verbale + ecart de logits sur marqueurs contrastes
``mon``/``son`` en position de reponse. Les deux mesures vivent ici (fonctions
pures) pour etre testees CPU ; le runner GPU ne fait que les alimenter.

Anti-HARKing (meme garde structurelle que ``ict.attention_schema``)
-------------------------------------------------------------------
Les seuils epsilon des axes etat/readout derivent d'un NULL execute sur les
traces de CALIBRATION (paire neutre calib_obj1 <-> calib_obj2, meme
machinerie d'intervention) AVANT les bras principaux : le runner CLI exige le
fichier null gele pour la phase principale, l'ordre inverse est impossible.
Forme continue de ``calibration_frozen.json`` (#15547) : meme formule
``epsilon = 0.5 * sigma * echelle_mediane``, le sigma venant ici de la paire
neutre plutot que du rapport propa.

Verdict PAR AXE (jamais global) : SUPPORTED / NOT_SUPPORTED / INCONCLUSIF,
avec kill_details nommes. La lecture AST minimale (le schema attentionnel
existe en ETAT meme si le readout ne le discrimine pas) exige etat SUPPORTED ;
le comportement tranche la portee fonctionnelle du schema ; le readout reste
l'axe connu-faible, son INCONCLUSIF n'invalide pas les deux autres.

Grade C documentaire : aucune phenomenologie n'est mesuree ; l'isomorphisme
avec le schema attentionnel neurobiologique de Graziano n'est pas garanti
(avertissements grade C de la matrice, case 5).
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field
from pathlib import Path

import numpy as np

from .attention_schema import ARM_SETS, SEEDS
from .causal_engine import (
    InterventionSpec,
    apply_intervention,
    damage_metrics,
    interchange_panels,
    random_target_matched,
    selectivity_verdict,
    sham_of,
)
from .sae_traces import densify, load_traces, mean_activation_by_set

__all__ = [
    "SEEDS",
    "MAIN_PAIRS",
    "K_DIFF",
    "BEHAVIOR_LEXICON",
    "MARKER_TOKENS",
    "clause_divergence",
    "pairwise_differential",
    "feature_profiles",
    "state_intervention_effects",
    "calibrate_null",
    "readout_axis",
    "classify_target",
    "marker_logit_gap",
    "axis_verdict",
    "run_traces_axes",
]

#: Paires dirigees testees dans les deux sens. La paire AST critique est
#: (attn_self <-> attn_other) ; (attn_self <-> obj_chaise) replique la
#: comparaison readout du case 5 cote etat ; (attn_other <-> obj_chaise)
#: complete le triangle pour detecter une directionnalite d'objet.
MAIN_PAIRS = (
    ("attn_self", "attn_other"),
    ("attn_self", "obj_chaise"),
    ("attn_other", "obj_chaise"),
)

#: Taille de la cible differentielle par paire — 64, la taille de signature
#: du case 5 (coherence d'instrument : on intervient sur ce que le readout
#: aurait du lire).
K_DIFF = 64

#: Bande d'appariement du controle aleatoire, en relatif. Le moteur propose
#: 0.25 par defaut ; le corpus case 5 (9 prompts par trace) QUANTISE la
#: frequence par pas de 1/9 et la bande etroite peut vider le voisinage
#: (norme, frequence) d'une cible forte — le moteur echoue alors
#: explicitement, ce qui est son contrat, mais ruine la couverture du
#: controle. ±50 % garde un appariement en norme ET frequence (le controle
#: reste difficile a distinguer a priori de la cible) tout en couvrant la
#: quantization du corpus.
REL_TOL_MATCHED = 0.5

#: Plafond de l'escalation de tolerance du controle apparie (voit
#: :func:`matched_random_spec`) : au-dela, l'appariement deviendrait une
#: paille (strawman) — on prefere echouer avec le diagnostic du moteur.
MATCHED_TOL_CAP = 1.5

#: Lexique comportemental GELE avant le run (anti-HARKing) : un marquesseur
#: est present dans la continuation generee => la cible verbale penche vers
#: ce bras. Deterministe, sans juge-LLM. Les formes sont des sous-chaines
#: normalisees (minuscules, apostrophes droites, espaces aplatis) —
#: :func:`classify_target` normalise l'entree de la meme facon.
BEHAVIOR_LEXICON = {
    "attn_self": ("mon attention", "je porte", "mes pensées", "moi-même",
                  "je me", "mon esprit", "ma concentration"),
    "attn_other": ("l'agent y", "son attention", "agent y", "l'agent",
                   "il porte", "sa concentration"),
    "obj_chaise": ("chaise", "posée", "le bois", "en bois", "le siège",
                   "les pieds"),
}

#: Marqueurs contrastes pour l'ecart de logits en position de reponse :
#: premier token de chaque marqueur de cible apres le prefixe sonde
#: (`` Réponse : ``). Le runner GPU resoud les ids ; ici seul le contrat.
MARKER_TOKENS = {"attn_self": "mon", "attn_other": "son", "obj_chaise": "une"}


# --------------------------------------------------------------------------- #
# Localisation de la fenetre causale (divergence de clause)
# --------------------------------------------------------------------------- #

def clause_divergence(tokens_a, tokens_b) -> int:
    """Premiere position ou deux prompts apparies divergent (tokens str).

    Les bras d'une graine partagent le contexte amont a l'identique ; la
    clause de tache diverge. Si un prompt est prefixe de l'autre (clause
    vide d'un cote), la divergence est la fin du prefixe — jamais hors
    bornes silencieusement.
    """
    n = min(len(tokens_a), len(tokens_b))
    for i in range(n):
        if str(tokens_a[i]) != str(tokens_b[i]):
            return i
    if len(tokens_a) != len(tokens_b):
        return n
    raise ValueError("deux prompts identiques — pas de fenetre causale")


# --------------------------------------------------------------------------- #
# Selection de cible : differentiel par paire + profils corpus
# --------------------------------------------------------------------------- #

def pairwise_differential(traces: dict, arm_a: str, arm_b: str,
                          *, k: int = K_DIFF) -> np.ndarray:
    """Top-k features par |mean(arm_a) - mean(arm_b)|, garde non-fini.

    Contrairement a :func:`ict.sae_traces.differential_features` (variance
    inter-jeux, tous bras confondus), la cible d'intervention est PAIRE : ce
    qui distingue exactement le donneur du receveur. Colonnes a score non
    fini exclues du classement (meme garde que #12560).
    """
    means = mean_activation_by_set(traces)
    diff = np.abs(means[arm_a].astype(np.float64) - means[arm_b].astype(np.float64))
    finite = np.isfinite(diff)
    finite_idx = np.flatnonzero(finite)
    if finite_idx.size < k:
        raise ValueError(f"paire ({arm_a}, {arm_b}) : {finite_idx.size} features "
                         "finies seulement — trace polluee, refus de classer")
    order = finite_idx[np.argsort(diff[finite_idx])[::-1][:k]]
    return order.astype(np.int64)


def feature_profiles(traces: dict) -> tuple[np.ndarray, np.ndarray]:
    """(normes L2, frequences d'activation) par feature sur tout le corpus.

    Calcul exact depuis le sparse top-k : norme = sqrt(sum vals^2) accumulee ;
    frequence = (prompts ou la feature est dans le top-k) / total prompts.
    Alimente :func:`random_target_matched` (appariement en norme ET frequence).
    """
    d_sae = int(traces["meta"]["d_sae"])
    sq = np.zeros(d_sae, dtype=np.float64)
    cnt = np.zeros(d_sae, dtype=np.float64)
    n_prompts = 0
    for entry in traces["prompts"].values():
        ids, vals = entry["ids"], entry["vals"]
        np.add.at(sq, ids.ravel(), vals.ravel().astype(np.float64) ** 2)
        np.add.at(cnt, np.unique(ids).ravel(), 1.0)
        n_prompts += 1
    return np.sqrt(sq), cnt / max(n_prompts, 1)


def matched_random_spec(panel: np.ndarray, template: InterventionSpec, *,
                        feature_norms: np.ndarray,
                        feature_freqs: np.ndarray,
                        rng: np.random.Generator,
                        start: float = REL_TOL_MATCHED,
                        cap: float = MATCHED_TOL_CAP
                        ) -> tuple[InterventionSpec, float]:
    """Controle apparie avec escalation de tolerance DISCLOSEE.

    Le moteur exige une candidate dans la bande (norme, frequence) a +- rel_tol
    de CHAQUE cible, et exclut les cibles + les picks deja consommes : sur le
    corpus de 9 prompts, une cible en region creuse du profil (ex. feature
    UBIQUINTE de faible norme — le couple (freq ~1.0, norme faible) a tres peu
    de voisins) peut vider la bande apres consommation par les cibles
    precedentes. Plutot que de sacrifier le controle (strawman silencieux) ou
    de ruiner la couverture du plan, on elargit la bande par doublements et on
    REND la tolerance effectivement utilisee : l'appelant la consigne dans ses
    resultats (champ ``matched_rel_tol``). Le plafond ``cap`` borne
    l'appariement avant qu'il ne devienne une paille ; a ``cap`` atteint on
    laisse le diagnostic du moteur passer (echec explicite).
    """
    tol = start
    while True:
        try:
            return random_target_matched(
                panel, template, feature_norms=feature_norms,
                feature_freqs=feature_freqs, rel_tol=tol, rng=rng), tol
        except ValueError:
            if tol >= cap:
                raise
            tol = min(cap, tol * 2.0)


# --------------------------------------------------------------------------- #
# Axe ETAT : effets cible / sham / aleatoire apparie
# --------------------------------------------------------------------------- #

@dataclass
class StateEffects:
    """Effets d'axe etat pour UNE paire dirigee x contexte d'une graine."""

    seed: int
    recipient: str
    donor: str
    ctx: int
    cos_target: float
    cos_before: float
    cos_sham: float
    cos_random: float
    damage: dict = field(default_factory=dict)
    selectivity: str = ""
    interchange_coherent: bool = False
    matched_rel_tol: float = float("nan")


def _pair_geometry(traces: dict, recipient: str, donor: str):
    """Divergences par contexte + fenetre commune L par contexte.

    Rend ``(div_by_ctx, L_by_ctx)`` : pour chaque contexte i, la position de
    divergence des clauses et la longueur commune ``min(T_r - div, T_d - div)``
    — l'ancrage est le debut de divergence (debut de la difference causale).
    """
    div_by_ctx: dict[int, int] = {}
    L_by_ctx: dict[int, int] = {}
    for i in range(3):
        e_r, e_d = traces["prompts"][(recipient, i)], traces["prompts"][(donor, i)]
        div = clause_divergence(e_r["tokens"], e_d["tokens"])
        div_by_ctx[i] = div
        L_by_ctx[i] = min(e_r["ids"].shape[0] - div, e_d["ids"].shape[0] - div)
        if L_by_ctx[i] <= 0:
            raise ValueError(f"({recipient},{donor},ctx {i}) : fenetre de clause vide")
    return div_by_ctx, L_by_ctx


def state_intervention_effects(traces: dict, recipient: str, donor: str,
                               ctx: int, *, k_diff: int = K_DIFF,
                               rng: np.random.Generator | None = None,
                               with_random_control: bool = True
                               ) -> StateEffects:
    """Patch de la tranche clause du donneur dans le receveur + controles.

    Rend les trois effets cosinus (cible / sham / aleatoire apparie) du
    centroide de clause du receveur vers celui du donneur, plus dommage
    general et verdict de selectivite du moteur. ``interchange_panels`` est
    execute en verrou de coherence : le cote A' de l'echange bilateral doit
    etre IDENTIQUE au patch unilateral (meme ecriture, litteralement).

    ``with_random_control=False`` omet le bras aleatoire apparie (cos_random
    = NaN) : reserve au NULL de calibration, dont le controle est la
    dispersion inter-graines — pas un appariement par run. L'appariement
    bande-etroite du moteur peut legitiment echouer sur une paire neutre
    (differentiel pilote par le bruit), et le null ne doit pas dependre de
    cette recherche.
    """
    if rng is None:
        rng = np.random.default_rng(0)
    entry_r = traces["prompts"][(recipient, ctx)]
    entry_d = traces["prompts"][(donor, ctx)]
    layer = int(traces["meta"]["layer"])
    seed = int(traces["meta"].get("seed", 0))
    div_by_ctx, L_by_ctx = _pair_geometry(traces, recipient, donor)
    div, L = div_by_ctx[ctx], L_by_ctx[ctx]
    T_r = entry_r["ids"].shape[0]
    positions = tuple(range(div, div + L))
    rows = np.asarray(positions)  # un tuple nu indexerait (ligne, colonne)

    diff_feats = pairwise_differential(traces, recipient, donor, k=k_diff)
    norms, freqs = feature_profiles(traces)

    # Controle aleatoire apparie : meme operation, features differentes,
    # apparies en norme ET frequence sur le corpus de la trace. Le panneau
    # factice ne sert qu'a la forme — les profils fournis gouvernent. Le
    # template porte un donneur placeholder (le contrat exige un donneur
    # pour ``patch`` des la construction) ; il n'est JAMAIS applique — les
    # specs appliquees sont construites plus bas avec l'univers definitif.
    placeholder = tuple(tuple(0.0 for _ in diff_feats) for _ in positions)
    template = InterventionSpec(
        operation="patch", instrument="sae", layer=layer,
        positions=positions, features=tuple(int(f) for f in diff_feats),
        donor=placeholder,
        tensor_space="sae_latent",
        run=f"case5bis/{recipient}-ctx{ctx}", paired_run=f"case5bis/{donor}-ctx{ctx}",
        seed=seed)
    if with_random_control:
        random_spec, matched_tol = matched_random_spec(
            np.zeros((T_r, int(traces["meta"]["d_sae"]))), template,
            feature_norms=norms, feature_freqs=freqs, rng=rng)
        universe = np.unique(
            np.concatenate([diff_feats, np.asarray(random_spec.features)]))
    else:
        random_spec, matched_tol = None, float("nan")
        universe = np.asarray(diff_feats)
    panel_r = densify(entry_r["ids"], entry_r["vals"], universe)   # [T_r, F]
    panel_d = densify(entry_d["ids"], entry_d["vals"], universe)   # [T_d, F]
    col_of = {int(f): j for j, f in enumerate(universe)}
    diff_cols = tuple(col_of[int(f)] for f in diff_feats)
    donor_full = panel_d[div:div + L]                  # fenetre clause (L, F)
    donor_diff = donor_full[:, list(diff_cols)]        # tranche cible (L, 64)

    # Centroids de clause : moyenne des moyennes de fenetre commune, 3 ctx.
    cent_r = np.mean([densify(traces["prompts"][(recipient, i)]["ids"],
                              traces["prompts"][(recipient, i)]["vals"], universe)
                      [div_by_ctx[i]:div_by_ctx[i] + L_by_ctx[i]].mean(axis=0)
                      for i in range(3)], axis=0)
    cent_d = np.mean([densify(traces["prompts"][(donor, i)]["ids"],
                              traces["prompts"][(donor, i)]["vals"], universe)
                      [div_by_ctx[i]:div_by_ctx[i] + L_by_ctx[i]].mean(axis=0)
                      for i in range(3)], axis=0)

    def _cos(v: np.ndarray) -> float:
        na, nb = float(np.linalg.norm(v)), float(np.linalg.norm(cent_d))
        if na == 0 or nb == 0:
            raise ValueError("centroide/deplacement nul — cosinus non defini")
        return float(v @ cent_d / (na * nb))

    cos_before = _cos(panel_r[rows].mean(axis=0))

    target_spec = InterventionSpec(
        operation="patch", instrument="sae", layer=layer,
        positions=positions, features=diff_cols,
        donor=tuple(tuple(float(v) for v in row) for row in donor_diff),
        tensor_space="sae_latent",
        run=f"case5bis/{recipient}-ctx{ctx}", paired_run=f"case5bis/{donor}-ctx{ctx}",
        seed=seed)
    patched = apply_intervention(panel_r, target_spec)
    cos_target = _cos(patched[rows].mean(axis=0))

    # Sham : ecriture de soi-meme par la voie de code partagee.
    sham_spec = sham_of(target_spec, panel_r)
    shammed = apply_intervention(panel_r, sham_spec)
    cos_sham = _cos(shammed[rows].mean(axis=0))

    # Aleatoire apparie : donneur sur les features NON differentielles
    # (omis quand with_random_control=False : cos_random = NaN).
    if random_spec is None:
        cos_random = float("nan")
    else:
        rand_cols = tuple(col_of[int(f)] for f in random_spec.features)
        rand_spec = InterventionSpec(
            operation="patch", instrument="sae", layer=layer,
            positions=positions, features=rand_cols,
            donor=tuple(tuple(float(v) for v in row)
                        for row in donor_full[:, list(rand_cols)]),
            tensor_space="sae_latent",
            run=f"case5bis/{recipient}-ctx{ctx}", paired_run=f"case5bis/{donor}-ctx{ctx}",
            seed=seed)
        randed = apply_intervention(panel_r, rand_spec)
        cos_random = _cos(randed[rows].mean(axis=0))

    # Verrou de coherence : cote A' de l'interchange bilateral == patch
    # unilateral. Joue sur les sous-panneaux de la fenetre commune (l'echange
    # exige des panneaux de meme forme, or T_r != T_d des que les clauses
    # diffarent en longueur).
    inter_a, _ = interchange_panels(
        panel_r[rows], panel_d[rows],
        InterventionSpec(
            operation="interchange", instrument="sae", layer=layer,
            positions=tuple(range(L)), features=diff_cols,
            tensor_space="sae_latent",
            run=f"case5bis/{recipient}-ctx{ctx}", paired_run=f"case5bis/{donor}-ctx{ctx}",
            seed=seed))
    coherent = bool(np.allclose(np.asarray(inter_a),
                                np.asarray(patched)[rows]))

    damage = damage_metrics(panel_r, patched, target_spec)
    return StateEffects(
        seed=seed, recipient=recipient, donor=donor, ctx=ctx,
        cos_target=cos_target, cos_before=cos_before,
        cos_sham=cos_sham, cos_random=cos_random,
        damage=damage, selectivity=selectivity_verdict(damage),
        interchange_coherent=coherent, matched_rel_tol=matched_tol,
    )


# --------------------------------------------------------------------------- #
# Axe READOUT : signature du bras virtuel + consommateurs reels
# --------------------------------------------------------------------------- #

def readout_axis(traces: dict, recipient: str, donor: str, ctx: int,
                 *, k_features: int = 64, k_diff: int = K_DIFF,
                 rng: np.random.Generator | None = None) -> dict:
    """Migration de la signature workspace apres patch de l'etat.

    Rend : ``jaccard_shift`` (J(sig(virtuel), sig(donneur)) - J(sig(receveur),
    sig(donneur)) sur top-``k_features`` de l'activation moyenne), et
    ``consumer_hit_shift`` (taux de consommateurs REELS du bras captures par
    la nouvelle signature - taux avec la signature d'origine). Les
    consommateurs ne bougent pas (traces gelees) : la seconde quantite
    documente ce que l'axe ne peut pas faire sans re-forward.
    """
    if rng is None:
        rng = np.random.default_rng(0)
    means = mean_activation_by_set(traces)
    entry_r = traces["prompts"][(recipient, ctx)]
    entry_d = traces["prompts"][(donor, ctx)]
    div = clause_divergence(entry_r["tokens"], entry_d["tokens"])
    L = min(entry_r["ids"].shape[0] - div, entry_d["ids"].shape[0] - div)
    if L <= 0:
        raise ValueError(f"({recipient},{donor},ctx {ctx}) : fenetre vide")

    diff_feats = pairwise_differential(traces, recipient, donor, k=k_diff)
    panel_r = densify(entry_r["ids"], entry_r["vals"], diff_feats)
    panel_d = densify(entry_d["ids"], entry_d["vals"], diff_feats)
    patched_clause = panel_d[div:div + L]           # patch integral de la
    # fenetre sur l'univers differentiel : cohérent avec l'axe etat (donor
    # slice ecrit sur les memes positions/features).

    # Vecteur moyen virtuel : delta = (patche - reel) sur l'univers, divise
    # par le TOTAL de positions du bras (convention mean_activation_by_set).
    n_rows = sum(e["ids"].shape[0] for k, e in traces["prompts"].items()
                 if k[0] == recipient)
    mean_vec = means[recipient].astype(np.float64).copy()
    delta = (patched_clause - panel_r[div:div + L]).sum(axis=0)
    for j, f in enumerate(diff_feats):
        mean_vec[int(f)] += float(delta[j]) / max(n_rows, 1)

    def _sig(vec: np.ndarray) -> set[int]:
        return set(int(f) for f in np.argsort(vec)[::-1][:k_features])

    def _jac(a: set[int], b: set[int]) -> float:
        return len(a & b) / len(a | b)

    sig_r, sig_d = _sig(means[recipient]), _sig(means[donor])
    sig_v = _sig(mean_vec)
    j_before, j_after = _jac(sig_r, sig_d), _jac(sig_v, sig_d)

    # Consommateurs reels (meme operationalisation que propa : ignition top-1%
    # parmi les positions laissant un token aval, 5 tokens suivants) — taux
    # d'argmax dans la signature, avant/apres patch.
    hits_before = hits_after = total = 0
    for (name, _i), entry in traces["prompts"].items():
        if name != recipient:
            continue
        ids, vals = entry["ids"], entry["vals"]
        T = ids.shape[0]
        candidates = np.arange(0, T - 1)
        joint = vals.sum(axis=1)[candidates]
        threshold = np.quantile(joint, 0.99)
        ignitions = candidates[joint >= threshold]
        consumers: set[int] = set()
        for t in ignitions:
            consumers.update(range(int(t) + 1, min(int(t) + 6, T)))
        for c in consumers:
            total += 1
            if int(ids[c, 0]) in sig_r:
                hits_before += 1
            if int(ids[c, 0]) in sig_v:
                hits_after += 1

    return {
        "seed": int(traces["meta"].get("seed", 0)),
        "recipient": recipient, "donor": donor, "ctx": ctx,
        "jaccard_before": j_before, "jaccard_after": j_after,
        "jaccard_shift": j_after - j_before,
        "consumer_hit_rate_before": hits_before / max(total, 1),
        "consumer_hit_rate_after": hits_after / max(total, 1),
        "consumer_hit_shift": (hits_after - hits_before) / max(total, 1),
    }


# --------------------------------------------------------------------------- #
# Axe COMPORTEMENT : fonctions pures (CPU-testables)
# --------------------------------------------------------------------------- #

def _normalize(text: str) -> str:
    return " ".join(text.lower().replace("’", "'").split())


def classify_target(text: str) -> str:
    """Classe la cible verbale d'une continuation generee (lexique gele).

    Rend le bras dont un marquesseur apparait, "ambiguous" si plusieurs bras
    matchent, "none" sinon. Deterministe : meme texte, meme verdict.
    """
    norm = _normalize(text)
    hits = {arm for arm, markers in BEHAVIOR_LEXICON.items()
            if any(_normalize(m) in norm for m in markers)}
    if len(hits) == 1:
        return hits.pop()
    if len(hits) > 1:
        return "ambiguous"
    return "none"


def marker_logit_gap(logits_row: np.ndarray, id_self: int, id_other: int) -> float:
    """Ecart logit mon/son en position de reponse (comportement probe).

    ``logits_row`` : logits du VOCABULAIRE a la position sondee (runner GPU).
    L'ecart est la quantite pre-enregistree : positif = penche self, negatif
    = penche other. Le verdict comportemental n'utilise JAMAIS la valeur
    absolue (non calibree inter-tokenisation), seulement son SIGNE et sa
    DERIVEE sous intervention.
    """
    return float(logits_row[id_self] - logits_row[id_other])


# --------------------------------------------------------------------------- #
# Verdict PAR AXE
# --------------------------------------------------------------------------- #

def axis_verdict(target_values: list[float], control_values: list[float],
                 epsilon: float, *, min_seeds_above: int = 4) -> tuple[str, list[str]]:
    """Verdict d'un axe : cible vs controle apparie, seuil epsilon.

    - SUPPORTED : mediane(cible - controle) > 0 ET mediane(cible) >= epsilon
      ET cible > controle sur >= ``min_seeds_above`` graines ;
    - NOT_SUPPORTED : mediane(cible - controle) <= 0 (l'intervention ne
      deplace pas l'axe au-dela de son controle apparie) ;
    - INCONCLUSIF : entre les deux (effet present mais inconsistent).
    """
    if len(target_values) != len(control_values):
        raise ValueError("cible et controle doivent etre apparies par graine")
    t = np.asarray(target_values, dtype=float)
    c = np.asarray(control_values, dtype=float)
    delta = t - c
    kills: list[str] = []
    if float(np.median(delta)) <= 0:
        kills.append(f"médiane(cible-contrôle) = {float(np.median(delta)):.4f} <= 0")
        return "NOT_SUPPORTED", kills
    n_above = int((delta > 0).sum())
    med_t = float(np.median(t))
    if med_t < epsilon:
        kills.append(f"médiane cible {med_t:.4f} < ε = {epsilon:.4f}")
    if n_above < min_seeds_above:
        kills.append(f"cible > contrôle sur {n_above}/{len(t)} graines "
                     f"(< {min_seeds_above})")
    if kills:
        return "INCONCLUSIF", kills
    return "SUPPORTED", []


# --------------------------------------------------------------------------- #
# Null de calibration (paire neutre) — AVANT les bras principaux
# --------------------------------------------------------------------------- #

@dataclass
class CausalNull:
    """Null des axes etat/readout sur la paire neutre (anti-HARKing)."""

    state_shift_by_seed: dict[int, float]
    readout_shift_by_seed: dict[int, float]
    sigma_state: float
    sigma_readout: float
    state_scale: float | None = None
    readout_scale: float | None = None
    epsilon_state: float | None = None
    epsilon_readout: float | None = None
    notes: list[str] = field(default_factory=list)


def calibrate_null(calib_traces_by_seed: dict[int, dict],
                   *, rng_by_seed: dict[int, np.random.Generator] | None = None
                   ) -> CausalNull:
    """Sigma des axes depuis la paire neutre — phase 1 obligatoire.

    La paire calib_obj1 <-> calib_obj2 est neutre par construction du case 5
    (entites publiques non impliquees identitairement ni attentionnellement) :
    deplacer l'etat de l'un vers l'autre ne devrait RIEN signifier pour un
    schema attentionnel. La dispersion de ces deplacements fixe sigma ; les
    memes fonctions d'effet tournent sur les bras principaux en phase 2.

    Le bras aleatoire apparie n'est PAS execute ici
    (``with_random_control=False``) : le controle du null est la dispersion
    inter-graines de la paire neutre, pas un appariement par run — et la
    recherche bande-etroite du moteur peut legitiment echouer sur une paire
    neutre (differentiel pilote par le bruit), ce qui ne doit pas rendre le
    null inexploitable.
    """
    state_shifts: dict[int, float] = {}
    readout_shifts: dict[int, float] = {}
    notes: list[str] = []
    for seed, traces in sorted(calib_traces_by_seed.items()):
        rng = (rng_by_seed or {}).get(seed, np.random.default_rng(seed))
        try:
            fx = state_intervention_effects(
                traces, "calib_obj1", "calib_obj2", 0, rng=rng,
                with_random_control=False)
            state_shifts[seed] = fx.cos_target - fx.cos_before
        except ValueError as exc:  # fenetre vide / centroide nul : documente
            notes.append(f"seed {seed}: état neutre exclu ({exc})")
        try:
            ro = readout_axis(traces, "calib_obj1", "calib_obj2", 0, rng=rng)
            readout_shifts[seed] = ro["jaccard_shift"]
        except ValueError as exc:
            notes.append(f"seed {seed}: readout neutre exclu ({exc})")
    if len(state_shifts) < 3 or len(readout_shifts) < 3:
        raise ValueError(
            f"null invalide : {len(state_shifts)} déplacements état / "
            f"{len(readout_shifts)} readout exploitables (<3) — epsilon non "
            "fixable, verdicts INCONCLUSIF par construction")
    return CausalNull(
        state_shift_by_seed=state_shifts,
        readout_shift_by_seed=readout_shifts,
        sigma_state=float(np.std(list(state_shifts.values()), ddof=1)),
        sigma_readout=float(np.std(list(readout_shifts.values()), ddof=1)),
        notes=notes,
    )


# --------------------------------------------------------------------------- #
# Runner : axes etat + readout sur les bras principaux
# --------------------------------------------------------------------------- #

def run_traces_axes(null: CausalNull, main_traces_by_seed: dict[int, dict],
                    behavior_json: str | Path | None = None,
                    *, k_diff: int = K_DIFF) -> dict:
    """Assemble les epsilon puis les deux axes numpy + l'axe comportemental.

    Echelle de reference (continuite de la formule #15547) : la mediane des
    effets CIBLE des bras principaux — epsilon = 0.5 * sigma * echelle. Le
    JSON comportemental optionnel (runner GPU) est integre tel quel s'il
    existe ; sinon l'axe est rapporte PENDING, jamais fabrique.
    """
    per_pair_state: dict[str, list[dict]] = {}
    per_pair_readout: dict[str, list[dict]] = {}
    for seed, traces in sorted(main_traces_by_seed.items()):
        for recipient, donor in MAIN_PAIRS:
            for r, d in ((recipient, donor), (donor, recipient)):
                for ctx in range(3):
                    rng = np.random.default_rng(seed * 100 + ctx)
                    fx = state_intervention_effects(
                        traces, r, d, ctx, k_diff=k_diff, rng=rng)
                    per_pair_state.setdefault(f"{r}<-{d}", []).append({
                        "seed": fx.seed, "ctx": fx.ctx,
                        "cos_before": fx.cos_before, "cos_target": fx.cos_target,
                        "cos_sham": fx.cos_sham, "cos_random": fx.cos_random,
                        "shift_target": fx.cos_target - fx.cos_before,
                        "shift_sham": fx.cos_sham - fx.cos_before,
                        "shift_random": fx.cos_random - fx.cos_before,
                        "damage": fx.damage, "selectivity": fx.selectivity,
                        "interchange_coherent": fx.interchange_coherent,
                        "matched_rel_tol": fx.matched_rel_tol,
                    })
                    ro = readout_axis(traces, r, d, ctx, k_diff=k_diff, rng=rng)
                    per_pair_readout.setdefault(f"{r}<-{d}", []).append(ro)

    state_scales = [e["shift_target"] for runs in per_pair_state.values()
                    for e in runs]
    readout_scales = [e["jaccard_shift"] for runs in per_pair_readout.values()
                      for e in runs]
    null.state_scale = float(np.median(state_scales))
    null.readout_scale = float(np.median(readout_scales))
    null.epsilon_state = 0.5 * null.sigma_state * max(null.state_scale, 1e-12)
    null.epsilon_readout = 0.5 * null.sigma_readout * max(null.readout_scale, 1e-12)

    axes: dict[str, dict] = {}
    for pair_key, runs in per_pair_state.items():
        by_seed: dict[int, list[dict]] = {}
        for e in runs:
            by_seed.setdefault(e["seed"], []).append(e)
        target = [float(np.median([e["shift_target"] for e in v]))
                  for _, v in sorted(by_seed.items())]
        control = [float(np.median([e["shift_random"] for e in v]))
                   for _, v in sorted(by_seed.items())]
        verdict, kills = axis_verdict(target, control, null.epsilon_state)
        axes[f"etat:{pair_key}"] = {
            "target_by_seed": target, "random_by_seed": control,
            "sham_max_abs": max(abs(e["shift_sham"]) for e in runs),
            "selectivity_counts": {
                s: sum(1 for e in runs if e["selectivity"] == s)
                for s in ("selective", "not_selective", "global_damage")},
            "interchange_coherent_all": all(e["interchange_coherent"] for e in runs),
            "matched_rel_tol_max": max(
                (e["matched_rel_tol"] for e in runs
                 if np.isfinite(e["matched_rel_tol"])), default=None),
            "epsilon": null.epsilon_state,
            "verdict": verdict, "kill_details": kills,
        }
    for pair_key, runs in per_pair_readout.items():
        by_seed = {}
        for e in runs:
            by_seed.setdefault(e["seed"], []).append(e)
        target = [float(np.median([e["jaccard_shift"] for e in v]))
                  for _, v in sorted(by_seed.items())]
        # Controle readout = 0 par graine : le null de calibration (sigma sur
        # paire neutre) porte deja le bruit de reference de cet axe.
        verdict, kills = axis_verdict(target, [0.0] * len(target),
                                      null.epsilon_readout)
        axes[f"readout:{pair_key}"] = {
            "target_by_seed": target,
            "consumer_hit_shift_median": float(np.median(
                [e["consumer_hit_shift"] for e in runs])),
            "epsilon": null.epsilon_readout,
            "verdict": verdict, "kill_details": kills,
        }

    behavior: dict = {"verdict": "PENDING", "note": "runner GPU non fourni"}
    if behavior_json is not None and Path(behavior_json).exists():
        behavior = json.loads(Path(behavior_json).read_text(encoding="utf-8"))

    return {
        "case": "case5bis_attention_schema_causal",
        "issue": 15798,
        "prediction": ("le schéma attentionnel existe en ÉTAT (déplacement "
                       "dirigé du centroïde de clause par patch du donneur) "
                       "même si le readout workspace ne le discrimine pas "
                       "(#15547) ; le comportement verbal tranche la portée"),
        "null": {
            "state_shift_by_seed": null.state_shift_by_seed,
            "readout_shift_by_seed": null.readout_shift_by_seed,
            "sigma_state": null.sigma_state,
            "sigma_readout": null.sigma_readout,
            "state_scale": null.state_scale,
            "readout_scale": null.readout_scale,
            "epsilon_state": null.epsilon_state,
            "epsilon_readout": null.epsilon_readout,
            "formula": "epsilon = 0.5 * sigma(neutre) * médiane(effet cible)",
            "notes": null.notes,
        },
        "axes": axes,
        "matched_control": {
            "default_rel_tol": REL_TOL_MATCHED,
            "cap": MATCHED_TOL_CAP,
            "escalated_calls": sum(
                1 for runs in per_pair_state.values() for e in runs
                if np.isfinite(e["matched_rel_tol"])
                and e["matched_rel_tol"] > REL_TOL_MATCHED),
            "note": ("tolerance elargie par doublements quand la bande "
                     "(norme, frequence) d'une cible est vide a +-%.0f%% ; "
                     "tolerance effective consignee par run "
                     "(matched_rel_tol)" % (REL_TOL_MATCHED * 100)),
        },
        "behavior": behavior,
    }


def _cli(argv: list[str] | None = None) -> None:
    """Runner CLI : ``null`` DOIT preceder ``run`` (fichier exige).

    ``python -m ict.attention_schema_causal null <calib.npz...> --out n.json``
    gele sigma etat/readout sur la paire neutre ; ``run --null n.json`` refuse
    de tourner sans ce fichier — meme garde anti-HARKing que le case 5.
    """
    import argparse

    ap = argparse.ArgumentParser(description="Case 5bis (#15798) — axes causaux")
    sub = ap.add_subparsers(dest="cmd", required=True)
    n = sub.add_parser("null", help="phase 1 : sigma sur paire neutre, AVANT")
    n.add_argument("traces", nargs="+", help=".npz de calibration (5 seeds)")
    n.add_argument("--out", required=True)
    r = sub.add_parser("run", help="phase 2 : bras principaux + verdicts")
    r.add_argument("traces", nargs="+", help=".npz des bras principaux (5 seeds)")
    r.add_argument("--null", required=True, help="JSON produit par 'null'")
    r.add_argument("--behavior-json", default=None,
                   help="sortie du runner GPU comportemental (optionnel)")
    r.add_argument("--out", required=True)

    args = ap.parse_args(argv)
    if args.cmd == "null":
        null = calibrate_null({i: load_traces(p) for i, p in enumerate(args.traces)})
        Path(args.out).write_text(json.dumps({
            "state_shift_by_seed": null.state_shift_by_seed,
            "readout_shift_by_seed": null.readout_shift_by_seed,
            "sigma_state": null.sigma_state,
            "sigma_readout": null.sigma_readout,
            "notes": null.notes,
        }, ensure_ascii=False, indent=1), encoding="utf-8")
        print(f"[null] sigma_state={null.sigma_state:.6f} "
              f"sigma_readout={null.sigma_readout:.6f} -> {args.out}")
        return
    frozen = json.loads(Path(args.null).read_text(encoding="utf-8"))
    null = CausalNull(
        state_shift_by_seed={int(k): v for k, v in frozen["state_shift_by_seed"].items()},
        readout_shift_by_seed={int(k): v for k, v in frozen["readout_shift_by_seed"].items()},
        sigma_state=float(frozen["sigma_state"]),
        sigma_readout=float(frozen["sigma_readout"]),
        notes=list(frozen.get("notes", [])))
    result = run_traces_axes(
        null, {i: load_traces(p) for i, p in enumerate(args.traces)},
        behavior_json=args.behavior_json)
    Path(args.out).write_text(json.dumps(result, ensure_ascii=False, indent=1),
                              encoding="utf-8")
    n_supported = sum(1 for a in result["axes"].values() if a["verdict"] == "SUPPORTED")
    print(f"[run] {n_supported}/{len(result['axes'])} axes SUPPORTED -> {args.out}")


if __name__ == "__main__":
    _cli()
