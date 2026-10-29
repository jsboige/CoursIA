"""MDL / code en deux parties et complexite-entropie (ICT-16, strate 5 Epic #4588).

ICT-0 a pose que l'integration (Phi), la surprise (F) et la compression (K) sont
trois facettes d'un meme quantite. ICT-13 (compression.py) a attache la jambe
K a la **longueur** d'une trajectoire reelle par contraste shuffle. Mais un
``k_gain`` positif ne dit rien sur la *forme* du modele : toute la complexite
est-elle dans la matrice de transition, ou dans les fluctuations atypiques ?
Ce module attache la jambe K a la **structure interne** du modele via le
principe MDL (Minimum Description Length, Rissanen 1978) -- **code en deux
parties** : ``bits_modele`` (decrire la TPM avec un prior) + ``bits_residuel``
(encoder les residuals d'un modele idealise par cette TPM).

Cinq estimateurs, tous numpy-only, volontairement honnetes sur leurs bornes :

  - ``kt_codelength(counts)`` / ``tpm_description_length(counts)`` :
    codelength d'une ligne de comptes sous le **prior de Krichevsky-Trofimov**
    (KT = Dirichlet symetrique ``alpha = 1/2``). Pour des comptes
    ``n_1 .. n_k`` de total ``n``, la marginale exacte est

        ``[log2 Gamma(k/2) - log2 Gamma(n + k/2)
           + sum_i (log2 Gamma(n_i + 1/2) - log2 Gamma(1/2))]``

    Cette quantite est **toujours >= 0** et **vaut exactement 0 pour une
    ligne vide** (aucune transition a transmettre). Bits de modele = somme
    sur les lignes, plus ``log2(k)`` pour declarer le nombre d'etats.
  - ``two_part_code(states, split=0.5)`` : split fixe (defaut 50/50
    apprentissage / held-out). ``model_bits`` = codelength d'une TPM
    estimee sur la moitie d'apprentissage, sous prior KT ; ``residual_bits``
    = -log2(proba TPM_apprentissage) sur la moitie held-out ;
    ``total_bits = model_bits + residual_bits``.
  - ``fit_markov_order(states, heldout, max_order)`` : selection de l'ordre
    d'une chaine de Markov par MDL exact (somme des codelengths KT des lignes
    + declaration des contextes), avec le NLL held-out comme controle
    independant. C'est l'organe du pont MDL -> generalisation : il rend
    ``mdl_bits`` et ``nll_heldout`` par ordre, donc la coincidence (ou la
    rupture) se **mesure** au lieu de se revendiquer.
  - ``entropy_rate_estimate(states, block)`` : plug-in par entropies de bloc
    ``H(block) / block`` -- la codelength par symbole du **meilleur code
    longueur-fixe** adapte a des blocs de taille ``block``. Biais de
    sous-estimation documente (plug-in < vrai, Miller-Madow corrige en
    O(1/n) mais pas implemente ici par souci de simplicite).
  - ``complexity_entropy_sweep(trajectories)`` : boucle ``block`` x
    ``trajectoire`` -> scatter (H_taux, model_bits) et (H_taux, ec_gain)
    pour la **bosse complexite-entropie** (Crutchfield-Feldman 1998) --
    verifiee sur le Notebook ICT-16.

Dependances : bibliotheque standard + numpy. Aucune dependance au package
``ict`` -- ce module est volontairement autonome, comme
``causal_emergence``.
"""

from __future__ import annotations

import math
from typing import Iterable, List, Sequence

import numpy as np


# ---------------------------------------------------------- prior Krichevsky-Trofimov
ALPHA = 0.5  # KT = Dirichlet symetrique alpha = 1/2
_LOG2 = math.log(2.0)


def kt_log2(count: int, k: int) -> float:
    """Terme **par categorie** du prior KT (bits), pour un compte ``count``.

    Le prior de Krichevsky-Trofimov est le Dirichlet symetrique
    ``alpha = 1/2``. Dans la marginale multinomiale, chaque categorie
    contribue le facteur ``Gamma(n_i + 1/2) / Gamma(1/2)``, soit en bits

        ``log2 Gamma(n_i + 1/2) - log2 Gamma(1/2)``

    Attention : c'est un **terme de produit**, pas une codelength. Il peut
    etre negatif (``count=1`` donne ``-1`` bit) et il vaut ``0`` pour
    ``count=0``. Seul l'agregat ``kt_codelength`` est une longueur de code,
    et lui seul est garanti positif.

    Parametres :
      - ``count`` : compte empirique ``n_i >= 0``.
      - ``k`` : nombre de categories (valide, non utilise : le terme
        par categorie n'en depend pas ; la dependance en ``k`` vit dans la
        constante ``-log2 Gamma(n + k/2)`` de ``kt_codelength``).

    Retourne le terme en bits (log base 2), croissant puis decroissant en
    ``count`` -- ``Gamma`` n'est pas monotone sur ``(0, 1.5)``.
    """
    if count < 0:
        raise ValueError(f"count doit etre >= 0, recu {count}")
    if k < 1:
        raise ValueError(f"k doit etre >= 1, recu {k}")
    return (math.lgamma(count + ALPHA) - math.lgamma(ALPHA)) / _LOG2


def kt_codelength(counts) -> float:
    """Codelength KT exacte (bits) d'un vecteur de comptes multinomial.

    C'est la longueur du code optimal (au sens KT) pour transmettre les
    ``n = sum_i n_i`` tirages dont les comptes sont ``counts`` :

        ``[log2 Gamma(k/2) - log2 Gamma(n + k/2)
           + sum_i (log2 Gamma(n_i + 1/2) - log2 Gamma(1/2))]``

    Proprietes verifiees par les tests (``tests/test_mdl.py``) :
      - **>= 0** partout, et **exactement 0** quand tous les comptes sont
        nuls (rien a transmettre : la distribution est connue) ;
      - egale, a ``1e-12`` pres, a la somme des couts predictifs sequentiels
        ``-log2 p(x_t | x_<t)`` avec ``p = (n_i + 1/2) / (n + k/2)``
        (identite de la regle de la chaine pour un prior echangeable) ;
      - egale a la reference rationnelle exacte pour de petits comptes.

    Parametres :
      - ``counts`` : vecteur de comptes ``n_i >= 0`` (liste, tuple ou
        ``np.ndarray``).

    Retourne la codelength en bits. ``0.0`` pour un vecteur vide.
    """
    row = np.asarray(counts, dtype=float).ravel()
    k = row.size
    if k == 0:
        return 0.0
    if np.any(row < 0):
        raise ValueError("counts doit etre >= 0 partout")
    n = float(row.sum())
    terms = sum(math.lgamma(v + ALPHA) - math.lgamma(ALPHA) for v in row)
    log_p = math.lgamma(k * ALPHA) - math.lgamma(n + k * ALPHA) + terms
    # ``log_p`` est le logarithme de la probabilite ; la codelength est son
    # oppose. Le calcul flottant peut rendre -1e-16 sur un vecteur vide ; la
    # codelength y est nulle par construction, on ne laisse pas passer un
    # epsilon negatif qui ferait echouer la garde de positivite.
    return float(max(-log_p / _LOG2, 0.0))


def _tpm_line_bits(row_counts: np.ndarray) -> float:
    """KT-codelength d'une ligne ``n_i`` (vecteur de comptes de transition).

    Delegue a ``kt_codelength`` : la longueur est celle des ``n`` transitions
    sortant d'un etat, ventilees sur les ``k`` etats d'arrivee. L'auto-comptage
    ``count[i, i]`` est inclus si present -- la distinction "self-transition
    vs pas" est laissee a l'appelant.
    """
    return kt_codelength(row_counts)


# ---------------------------------------------------------- codelength du modele
def tpm_description_length(counts: np.ndarray) -> float:
    """Codelength (bits, prior KT) d'une TPM empirique ``counts``.

    ``counts`` est une matrice ``(k, k)`` de comptes de transitions
    ``(s_t, s_{t+1})``. La codelength totale est la somme sur les lignes
    de la KT-complexicite marginale, plus une surcharge fixe ``log2(k)``
    pour declarer la taille du modele (le nombre d'etats).

    Parametres :
      - ``counts`` : matrice carree ``np.ndarray`` ou convertible, comptes
        >= 0 (eventuellement zeros sur des lignes jamais observees).

    Retourne la codelength en bits.
    """
    arr = np.asarray(counts, dtype=float)
    if arr.ndim != 2 or arr.shape[0] != arr.shape[1]:
        raise ValueError(
            f"counts doit etre une matrice carree, recu shape {arr.shape}"
        )
    if np.any(arr < 0):
        raise ValueError("counts doit etre >= 0 partout")
    k = arr.shape[0]
    line_bits = float(np.sum([_tpm_line_bits(arr[i]) for i in range(k)]))
    # Surcharge pour declarer la taille k (le destinataire doit savoir
    # combien de lignes sont codees -- ~log2(k) bits de modele structurel).
    overhead = math.log2(max(k, 2))
    return line_bits + overhead


# ---------------------------------------------------------- code deux parties
def two_part_code(states: Sequence, split: float = 0.5,
                  states_to_index: dict | None = None) -> dict:
    """MDL : ``bits_modele`` + ``bits_residuel`` pour une trajectoire.

    Etape 1 -- apprenstissage : les ``floor(split * (n - 1))`` premieres
    transitions servent a estimer une TPM (KT-prior regule).
    Etape 2 -- held-out : les transitions restantes sont evaluees sous le
    modele appris, par ``-log2 p(s_{t+1} | s_t)``. La somme des log-probs
    negatives est le **residu** du modele : il est nul pour une trajectoire
    periodique alignee avec la TPM apprise, maximal pour une trajectoire
    aleatoire.

    Parametres :
      - ``states`` : sequence d'etats hashables et comparables.
      - ``split`` : proportion de transitions gardees pour l'apprentissage
        (defaut 0.5). Le residuel est evalue sur le reste. ``split=1.0``
        laisse un residuel vide (= 0) ; ``split=0.0`` laisse un modele vide.
      - ``states_to_index`` : mapping optionnel label -> index (reutilise
        ``ict.tpm_estimation.state_index_map`` quand ``None``).

    Le residu held-out est calcule sous la **predictive KT normalisee**
    ``p_ij = (n_ij + 1/2) / (n_i* + k/2)``, dont les lignes somment a 1.

    Retourne ``{"model_bits": float, "residual_bits": float,
    "total_bits": float, "n_train": int, "n_heldout": int, "n_covered": int,
    "n_escaped": int, "states_count": int}``.
    ``total_bits = model_bits + residual_bits``, et ``model_bits >= 0``
    toujours.
    """
    seq = list(states)
    n = len(seq)
    if n < 2:
        raise ValueError(
            f"il faut au moins 2 etats pour definir une transition, recu n={n}"
        )
    transitions = list(zip(seq[:-1], seq[1:]))
    n_trans = len(transitions)
    n_train = int(math.floor(split * n_trans))
    if n_train < 1 and split > 0:
        n_train = 1
    if n_train > n_trans - 1:
        n_train = n_trans - 1
    train, heldout = transitions[:n_train], transitions[n_train:]

    # Mapping label -> index.
    if states_to_index is None:
        labels: List = []
        for a, b in train:
            if a not in labels:
                labels.append(a)
            if b not in labels:
                labels.append(b)
        mapping = {s: i for i, s in enumerate(labels)}
    else:
        mapping = dict(states_to_index)
    k = len(mapping)

    # Comptes d'apprentissage.
    counts = np.zeros((k, k), dtype=float)
    for a, b in train:
        counts[mapping[a], mapping[b]] += 1.0

    # Bits de modele : KT sur les comptes d'apprentissage.
    model_bits = tpm_description_length(counts)

    # Probabilites predictives KT : p_ij = (n_ij + 1/2) / (n_i* + k/2).
    # Le denominateur est la **masse KT de la ligne** (``n_i* + k*alpha``) et
    # rien de plus : c'est ce qui rend ``sum_j p_ij == 1``. Un terme
    # additionnel (l'ancien ``+ alpha``) gonflait le denominateur, donc
    # sous-estimait le residu, sans aucune justification.
    row_sums = counts.sum(axis=1)
    denom = row_sums + k * ALPHA
    # Ligne jamais observee en train : la predictive KT y est l'uniforme
    # ``1/k`` sur les ``k`` etats connus (tous les ``n_ij`` valent 0,
    # ``n_i* = 0``). L'ancien ``1/(k+1)`` correspondait a un alphabet de
    # ``k+1`` symboles qui n'existe pas.
    # ``k == 0`` : la moitie d'apprentissage ne contient aucune transition
    # (``split`` tres petit ou plafonnement a ``n_trans - 1``). Le modele est
    # vide et toutes les transitions held-out passent par l'echappement ; on
    # ne divise pas par zero pour autant.
    prob = np.full((k, k), 1.0 / k) if k else np.zeros((0, 0), dtype=float)
    for i in range(k):
        if row_sums[i] > 0:
            prob[i] = (counts[i] + ALPHA) / denom[i]
        # sinon : on garde le prior uniforme 1/(k+1) ; les labels
        # jamais vus en train ne sont PAS dans ``mapping``, donc ce cas
        # ne survient que sur des transitions dont l'etat source n'a jamais
        # ete observe (uniquement possibles si ``states_to_index`` est
        # injecte par l'appelant).

    # Residuel held-out : -log2 p(s_{t+1} | s_t) pour chaque transition.
    resid = 0.0
    covered = 0
    escaped = 0
    for a, b in heldout:
        if a not in mapping or b not in mapping:
            # Convention d'echappement, explicite et non ambigue : un symbole
            # absent de l'alphabet d'apprentissage coute ``log2(k+1)`` pour
            # etre declare nouveau, et la transition est ensuite codee sous
            # l'uniforme du meme alphabet elargi, soit ``log2(k+1)`` de plus.
            # Ce chemin n'est atteint que si un etat de la partie held-out
            # n'apparait jamais en apprentissage.
            resid += 2.0 * math.log2(k + 1.0)
            escaped += 1
            continue
        i, j = mapping[a], mapping[b]
        p = float(prob[i, j])
        if p <= 0:
            # Numerique : KT evite le zero, mais defensive.
            resid += 1000.0
        else:
            resid += -math.log2(p)
        covered += 1

    return {
        "model_bits": float(model_bits),
        "residual_bits": float(resid),
        "total_bits": float(model_bits + resid),
        "n_train": int(n_train),
        "n_heldout": int(len(heldout)),
        "n_covered": int(covered),
        "n_escaped": int(escaped),
        "states_count": int(k),
    }


# ---------------------------------------------------------- selection d'ordre
def _context_index(seq: Sequence[int], i: int, order: int, k: int) -> int:
    """Index de contexte en base ``k`` des ``order`` symboles precedant ``i``."""
    ctx = 0
    for j in range(order):
        ctx = ctx * k + seq[i - order + j]
    return ctx


def fit_markov_order(states, heldout=None, max_order: int = 4,
                     split: float = 0.5,
                     states_to_index: dict | None = None) -> dict:
    """Selection de l'ordre d'une chaine de Markov par **MDL exact** (KT).

    Pour chaque ordre ``k`` de 0 a ``max_order``, le modele est code en deux
    parties strictes :

      - ``payload_bits`` : ``sum`` des codelengths KT des lignes de comptes
        (``kt_codelength``), c'est-a-dire la longueur du code optimal des
        transitions d'apprentissage sous ce modele ;
      - ``declare_bits`` : ``log2(k_states**order)`` pour annoncer au
        decodeur combien de contextes existent ;
      - ``mdl_bits = payload_bits + declare_bits``.

    Le controle independant est le ``nll_heldout`` : la surprise cumulee
    ``-log2 p(s_{t+1} | contexte)`` sur une sequence tenue a l'ecart, sous la
    predictive KT normalisee ``(n_ij + 1/2) / (n_i* + k/2)``. La selection
    MDL est *falsifiable* : si elle est saine, ``best_mdl_order`` et
    ``best_nll_order`` coincident sur une source structurée et retombent sur
    0 sur un nul i.i.d.

    **Ce que cette fonction ne fait pas, et qu'il faut savoir** : la
    codelength KT ne facture pas l'existence des contextes restes vides (elle
    vaut 0 pour une ligne vide). Sous ``n`` tres petit devant
    ``k_states**order``, l'ordre eleve peut donc gagner par chance ; ce
    regime se mesure, il ne se suppose pas -- voir ``tests/test_mdl.py``.

    Parametres :
      - ``states`` : sequence d'apprentissage (symboles hashables).
      - ``heldout`` : sequence tenue a l'ecart. ``None`` -> decoupage de
        ``states`` a ``split``.
      - ``max_order`` : ordre maximal evalue (defaut 4).
      - ``split`` : part d'apprentissage quand ``heldout is None``.
      - ``states_to_index`` : mapping optionnel label -> index. ``None`` ->
        alphabet deduit de la sequence d'apprentissage.

    Retourne ``{"rows": [...], "best_mdl_order": int, "best_nll_order": int,
    "k_states": int}`` ou chaque ligne porte ``order, n_contexts,
    n_nonempty, payload_bits, declare_bits, mdl_bits, nll_heldout,
    n_escaped``.
    """
    train_seq = list(states)
    if len(train_seq) < 2:
        raise ValueError(
            f"il faut au moins 2 etats, recu n={len(train_seq)}"
        )
    if heldout is None:
        n_tr = int(math.floor(split * len(train_seq)))
        n_tr = max(1, min(n_tr, len(train_seq) - 1))
        train_seq, held_seq = train_seq[:n_tr], train_seq[n_tr:]
    else:
        held_seq = list(heldout)

    if states_to_index is None:
        labels: List = []
        for s in train_seq:
            if s not in labels:
                labels.append(s)
        mapping = {s: i for i, s in enumerate(labels)}
    else:
        mapping = dict(states_to_index)

    k = len(mapping)
    train = [mapping[s] for s in train_seq]
    held = [mapping.get(s, -1) for s in held_seq]

    rows: List[dict] = []
    for order in range(max_order + 1):
        if order >= len(train):
            break
        n_ctx = k ** order
        counts = np.zeros((n_ctx, k), dtype=float)
        for i in range(order, len(train)):
            counts[_context_index(train, i, order, k), train[i]] += 1.0

        payload = float(np.sum([kt_codelength(row) for row in counts]))
        declare = math.log2(n_ctx)
        n_nonempty = int(np.count_nonzero(counts.sum(axis=1)))

        # Controle held-out sous la predictive KT normalisee.
        prob = (counts + ALPHA) / (
            counts.sum(axis=1, keepdims=True) + k * ALPHA
        )
        # Les ``order`` derniers symboles d'apprentissage amorcent le
        # contexte de la sequence tenue a l'ecart : aucune transition
        # held-out n'est perdue.
        eval_seq = (train[-order:] if order else []) + held
        nll = 0.0
        escaped = 0
        for i in range(order, len(eval_seq)):
            ctx = _context_index(eval_seq, i, order, k)
            sym = eval_seq[i]
            if sym < 0:
                # Symbole absent de l'alphabet d'apprentissage : meme
                # convention d'echappement que ``two_part_code``.
                nll += 2.0 * math.log2(k + 1.0)
                escaped += 1
            else:
                nll += -math.log2(prob[ctx, sym])

        rows.append({
            "order": int(order),
            "n_contexts": int(n_ctx),
            "n_nonempty": n_nonempty,
            "payload_bits": payload,
            "declare_bits": float(declare),
            "mdl_bits": float(payload + declare),
            "nll_heldout": float(nll),
            "n_escaped": int(escaped),
        })

    if not rows:
        raise ValueError("aucun ordre evaluable sur cette sequence")
    return {
        "rows": rows,
        "best_mdl_order": int(np.argmin([r["mdl_bits"] for r in rows])),
        "best_nll_order": int(np.argmin([r["nll_heldout"] for r in rows])),
        "k_states": int(k),
    }


# ---------------------------------------------------------- entropie par bloc
def _entropy_from_counts(counts: np.ndarray) -> float:
    """Entropie de Shannon (log2) d'une distribution de comptes ``counts``."""
    total = float(counts.sum())
    if total <= 0:
        return 0.0
    p = counts.astype(float).ravel() / total
    p = p[p > 0]
    return float(-np.sum(p * np.log2(p)))


def _ngrams(seq: Sequence, k: int) -> dict:
    """Denombre les ``k``-grammes consecutifs dans ``seq``."""
    if k < 1 or k > len(seq):
        return {}
    out: dict = {}
    for i in range(len(seq) - k + 1):
        gram = tuple(seq[i:i + k])
        out[gram] = out.get(gram, 0) + 1
    return out


def entropy_rate_estimate(states: Sequence, block: int = 2) -> dict:
    """Estime le **taux d'entropie** ``H(block) / block`` d'une trajectoire.

    Plug-in par entropies de bloc ``H_k = -sum p(gram) log2 p(gram)`` sur les
    ``k``-grammes consecutifs, avec ``H(block)`` divise par ``block`` pour
    obtenir un estimateur du **taux** d'entropie par symbole. Pour les
    dynamiques Markoviennes d'ordre 0 (independantes), on a
    ``H_k = k * H_1`` : le taux converge vers ``H_1`` ; pour les
    dynamiques d'ordre superieur, ``H_k / k`` decroit en ``k`` et tend
    vers le **vrai taux d'entropie** de la source (par definition le
    supremum des plug-in, mais celui-ci le surestime systematiquement --
    le biais de plug-in << Miller-Madow).

    Parametres :
      - ``states`` : sequence d'etats hashables.
      - ``block`` : taille du bloc ``k`` (defaut 2 -- ordre 1 implicite).
        ``block=1`` redonne ``H_1`` (taux marginal).

    Retourne ``{"H_block": float, "entropy_rate": float, "vocab_size":
    int, "n_blocks": int}``.
    """
    seq = list(states)
    if len(seq) < max(block, 1):
        raise ValueError(
            f"il faut au moins {max(block, 1)} etats pour block={block}, "
            f"recu {len(seq)}"
        )
    grams = _ngrams(seq, block)
    if not grams:
        return {"H_block": 0.0, "entropy_rate": 0.0,
                "vocab_size": 0, "n_blocks": 0}
    counts = np.array(list(grams.values()), dtype=float)
    return {
        "H_block": _entropy_from_counts(counts),
        "entropy_rate": _entropy_from_counts(counts) / block,
        "vocab_size": len(grams),
        "n_blocks": int(counts.sum()),
    }


# ---------------------------------------------------------- bosse complexite-entropie
def complexity_entropy_sweep(
        trajectories: Iterable[Sequence],
        blocks: Sequence[int] = (1, 2, 3, 4),
        splits: Sequence[float] = (0.5,),
        rng: np.random.Generator | None = None,
        n_shuffles: int = 5) -> dict:
    """Boucle ``trajectoire`` x ``block`` -> scatter (H_taux, model_bits, ec_gain).

    Pour chaque trajectoire, chaque taille de bloc dans ``blocks``, chaque
    split dans ``splits`` :

      - ``H_taux`` = plug-in ``entropy_rate_estimate``
      - ``model_bits`` = ``two_part_code(traj, split=split)["model_bits"]``
      - ``ec_gain`` = gain de compression de la trajectoire reelle vs
        permutation shuffle (moyenne sur ``n_shuffles``), via
        ``ict.compression.compression_gain``. C'est l'increment MDL
        attribuable a la structure temporelle (par opposition au contenu
        du reservoir d'etats).

    Le retour est structure pour le scatter de la **bosse
    complexite-entropie** (Crutchfield-Feldman 1998) : pour un systeme
    appris sur des donnees reelles, ``C`` (``statistical complexity``,
    approximee ici par ``model_bits`` en log2) tend a passer par un
    **maximum** a entropie intermediaire entre 0 (determinisme) et la
    borne H_1 du reservoir. La position et la hauteur de la bosse
    dependent de la discretisation et du split (Gate 7 d'ICT-16).

    Parametres :
      - ``trajectories`` : iterable de sequences.
      - ``blocks`` : tailles de bloc a balayer (defaut ``(1, 2, 3, 4)``).
      - ``splits`` : valeurs de split a tester (defaut ``(0.5,)`` ; >= 2
        pour explorer la sensibilite discretisation).
      - ``rng`` : ``np.random.Generator`` (defaut = nouveau seed). Utilise
        pour les permutations shuffle.
      - ``n_shuffles`` : nombre de permutations par trajectoire (defaut 5).

    Retourne ``{"rows": list[dict], "summary": dict}`` ou chaque ``row``
    contient ``traj_id, block, split, n, H_rate, model_bits, residual_bits,
    total_bits, ec_gain, k_gain``.
    """
    # Importation locale pour eviter cycle et garder le module autonome.
    from . import compression as C

    if rng is None:
        rng = np.random.default_rng()
    rows: List[dict] = []
    for t_id, traj in enumerate(trajectories):
        seq = list(traj)
        n = len(seq)
        if n < 4:
            continue
        # Gain de compression shuffle (K, cf compression.py) -- le signal
        # "structure d'ordre", complementaire au modele.
        try:
            kg = C.compression_gain(seq, rng=rng, n_shuffles=n_shuffles)
        except Exception:
            kg = {"k_gain": float("nan"), "len_real": 0,
                  "len_shuffled": float("nan")}
        for block in blocks:
            if n < max(block, 2):
                continue
            try:
                h = entropy_rate_estimate(seq, block=block)
                H_rate = h["entropy_rate"]
            except ValueError:
                continue
            for split in splits:
                if not (0.0 < split < 1.0):
                    continue
                if int(math.floor(split * (n - 1))) < 1:
                    continue
                mdl = two_part_code(seq, split=split)
                rows.append({
                    "traj_id": int(t_id),
                    "block": int(block),
                    "split": float(split),
                    "n": int(n),
                    "H_rate": float(H_rate),
                    "model_bits": float(mdl["model_bits"]),
                    "residual_bits": float(mdl["residual_bits"]),
                    "total_bits": float(mdl["total_bits"]),
                    "k_gain": float(kg["k_gain"]),
                })

    # Resume : bosse H_rate vs model_bits (position du pic, hauteur max).
    if rows:
        Hs = np.array([r["H_rate"] for r in rows], dtype=float)
        Ms = np.array([r["model_bits"] for r in rows], dtype=float)
        Kg = np.array([r["k_gain"] for r in rows], dtype=float)
        # Pic de la bosse : argmax de model_bits sur H_rate moyen.
        order = np.argsort(Hs)
        Hs_s = Hs[order]
        Ms_s = Ms[order]
        # Hauteur par fenetre glissante de 3 indices (lissage plug-in).
        if len(Ms_s) >= 3:
            kernel = np.ones(3) / 3.0
            Ms_smooth = np.convolve(Ms_s, kernel, mode="same")
            peak_idx = int(np.argmax(Ms_smooth))
        else:
            peak_idx = int(np.argmax(Ms_s))
        summary = {
            "n_rows": int(len(rows)),
            "H_rate_min": float(Hs.min()) if Hs.size else float("nan"),
            "H_rate_max": float(Hs.max()) if Hs.size else float("nan"),
            "peak_H_rate": float(Hs_s[peak_idx]) if Hs.size else float("nan"),
            "peak_model_bits": float(Ms_s[peak_idx]) if Ms.size else float("nan"),
            "k_gain_mean": float(np.nanmean(Kg)) if Kg.size else float("nan"),
            "k_gain_max": float(np.nanmax(Kg)) if Kg.size else float("nan"),
        }
    else:
        summary = {"n_rows": 0}

    return {"rows": rows, "summary": summary}
