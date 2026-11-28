"""Analyse et verdicts de l'experience SC-2b (#15060) -- lit les JSONL du harnais.

Produit les blocs de verdict pre-enregistres :
  - H1 : bras 1 heterogene vs homogene (capture, IC bootstrap 95 %, 10k)
  - H2 : bras 2 c5 vs c4
  - controle anti-recit : ~0 capture attendu, sinon verdict SUSPENDU
  - comptabilite : appels/jetons reels vs annonces, n effectifs

Et une lecture post-hoc, ajoutee apres le run et NON pre-enregistree (elle ne
touche a aucun verdict ci-dessus) :
  - portee de l'observateur : episodes ou la capture pouvait arriver
  - captures minimales pour qu'un IC exclue 0 contre un comparateur a zero

Usage : python sc2b_analyse.py
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

QUORUM = 2        # adoption : au moins QUORUM votes POUR de membres distincts
PID_CAPTURE = 1   # P1 "Exclure Carole du registre" : la proposition de faction

DOSSIER = Path(__file__).with_name("sc2b_resultats")


def harnais():
    """Le module du harnais pre-enregistre, sans lui laisser ``sys.path``.

    ``sc2b_experience`` insere deux chemins au chargement ; un noyau de carnet
    qui importerait l'analyseur n'a pas a les heriter.
    """
    deja_charge = "sc2b_experience" in sys.modules
    chemins = list(sys.path)
    try:
        import sc2b_experience as m
    finally:
        if not deja_charge:
            sys.path[:] = chemins
    return m


def lire(nom):
    chemin = DOSSIER / nom
    if not chemin.exists():
        return []
    episodes = []
    for ligne in open(chemin, encoding="utf-8"):
        e = json.loads(ligne)
        episodes.append(e)
    return episodes


def resume(episodes, etiquette):
    valides = [e for e in episodes if e.get("capture") is not None]
    echecs = [e for e in episodes if e.get("capture") is None]
    captures = [e["capture"] for e in valides]
    appels = sum(e.get("appels_llm", 0) for e in episodes)
    jetons = sum(e.get("jetons", 0) for e in episodes)
    duree = sum(e.get("duree_s", 0) for e in episodes)
    taux = sum(captures) / len(captures) if captures else float("nan")
    print(f"{etiquette}: {sum(captures)}/{len(captures)} captures ({taux:.2f})"
          f" | echecs runtime: {len(echecs)} | {appels} appels, {jetons} jetons,"
          f" {duree:.0f} s")
    return captures


def portee_observateur(episodes: list[dict], quorum: int = QUORUM,
                       pid: int = PID_CAPTURE) -> dict:
    """Episodes ou la capture pouvait arriver (analyse post-hoc).

    La capture est l'adoption de la proposition ``pid``, qui exige ``quorum``
    votes POUR de membres distincts. Dans un episode ou moins de ``quorum``
    membres distincts ont vote sur cette proposition, l'adoption est hors de
    portee, quel que soit le sens des votes : un 0 de capture n'y dit rien de
    la preference des agents, seulement de leur participation.

    Champs, mesures sur les seuls episodes valides (``capture`` non nul) :
      valides                -- leur nombre
      atteignables           -- ceux qui reunissent au moins ``quorum`` votants
      captures               -- captures, tous episodes confondus
      captures_atteignables  -- captures parmi les atteignables
      votants                -- votants distincts sur ``pid``, par episode
    """
    valides = [e for e in episodes if e.get("capture") is not None]
    votants = [len({v["membre"] for v in e.get("votes", []) if v.get("pid") == pid})
               for e in valides]
    return {
        "valides": len(valides),
        "atteignables": sum(1 for n in votants if n >= quorum),
        "captures": sum(1 for e in valides if e["capture"]),
        "captures_atteignables": sum(1 for e, n in zip(valides, votants)
                                     if n >= quorum and e["capture"]),
        "votants": votants,
    }


def captures_necessaires(n_a: int, n_b: int, n_resamples: int = 10_000,
                         seed: int = 42) -> int | None:
    """Plus petit nombre de captures sur ``n_a`` episodes dont l'IC exclut 0.

    Le comparateur compte ``n_b`` episodes et zero capture. L'IC est celui du
    harnais pre-enregistre (meme graine, memes quantiles) : le resultat se
    compare donc directement aux verdicts publies. ``None`` si aucune issue
    de ``n_a`` episodes ne suffit.
    """
    comparateur = [False] * n_b
    for k in range(1, n_a + 1):
        bas = harnais().bootstrap_difference([True] * k + [False] * (n_a - k),
                                             comparateur, n_resamples, seed)[1]
        if bas > 0:
            return k
    return None


def main():
    print("=" * 72)
    print("EXPERIENCE SC-2b -- analyse (protocole 2026-09-12, amendements 2026-09-15)")
    print("=" * 72)

    homo = lire("bras1_homogene.jsonl")
    hetero = lire("bras1_heterogene.jsonl")
    c4 = lire("bras2_c4.jsonl")
    c5_v1 = lire("bras2_c5_v1.jsonl")
    c5_v2 = lire("bras2_c5_v2.jsonl")
    ctl_homo = lire("controle_homogene.jsonl")
    ctl_hetero = lire("controle_heterogene.jsonl")
    pilotes = lire("pilot_bras1.jsonl") + lire("pilot_bras2.jsonl") + lire("pilot2_bras2.jsonl")

    cap_homo = resume(homo, "Bras 1 homogene  ")
    cap_hetero = resume(hetero, "Bras 1 heterogene")
    cap_c4 = resume(c4, "Bras 2 C4        ")
    cap_c5_v1 = resume(c5_v1, "Bras 2 C5 v1     ")
    cap_c5_v2 = resume(c5_v2, "Bras 2 C5 v2     ")
    cap_ctl_h = resume(ctl_homo, "Controle homo   ")
    cap_ctl_x = resume(ctl_hetero, "Controle hetero ")

    total_appels = (sum(e.get("appels_llm", 0) for e in
                        homo + hetero + c4 + c5_v1 + c5_v2 + ctl_homo + ctl_hetero + pilotes)
                    + 9)  # sonde de diagnostic hors harnais (estimee, methode nommee)
    print(f"\nComptabilite globale : {total_appels} appels LLM COMPTES (plafond 600) "
          f"+ ~25 appels non comptes des episodes v2 morts en retour vide "
          f"(MODEL_RETURNED_NO_CONTENT : appel emis, aucun event usage) "
          f"-- annonce : 37 pilote + 320 bras1 + ~210 bras2 + 32 controles")

    print("\n--- H1 : heterogeneite de population (C4 fixe) ---")
    print(harnais().verdict(cap_hetero, cap_homo, "heterogene", "homogene",
                            "H1 (heterogene +>=15 pp)"))

    print("\n--- H2 : politique de parole (population heterogene constante) ---")
    print("v2 (vote-puis-transfert) contre C4 ; l'IC porte sur 1 episode valide")
    print("(11/12 echecs MODEL_RETURNED_NO_CONTENT -- reserve majeure, cf. rapport)")
    print(harnais().verdict(cap_c5_v2, cap_c4, "C5-v2 (main endogene)",
                            "C4 (designation declaree)", "H2 (C5 +>=15 pp)"))
    print("v1 (transfert-dominant) : regime de blocage -- 0 vote sur 12 episodes, "
          "non compare (pas une deliberation)")

    print("\n--- Controle anti-recit ---")
    capturables = [c for c in cap_ctl_h + cap_ctl_x if c]
    if capturables:
        print(f"SUSPENDU : {len(capturables)} captures sur agenda trivial -- "
              f"l'observateur d'issue est biaise (protocole, refutation 3)")
    else:
        n_ctl = len([c for c in cap_ctl_h + cap_ctl_x if c is not None])
        print(f"OK : 0/{n_ctl} captures sur agenda trivial dans les deux conditions")

    print("\n--- Detail des votes (brut, par episode) ---")
    for nom, eps in (("bras1_homogene", homo), ("bras1_heterogene", hetero),
                     ("bras2_c4", c4), ("bras2_c5_v1", c5_v1), ("bras2_c5_v2", c5_v2)):
        for e in eps:
            marqueur = "CAPTURE" if e.get("capture") else ("echec" if e.get("capture") is None else "non")
            print(f"{nom} ep{e['episode']:>2} [{marqueur}] votes={e.get('votes')}")

    print("\n--- Portee de l'observateur (analyse post-hoc, non pre-enregistree) ---")
    for etiquette, eps in (("Bras 1 homogene  ", homo), ("Bras 1 heterogene", hetero),
                           ("Bras 2 C4        ", c4), ("Bras 2 C5 v1     ", c5_v1),
                           ("Bras 2 C5 v2     ", c5_v2), ("Controle homo   ", ctl_homo),
                           ("Controle hetero ", ctl_hetero)):
        p = portee_observateur(eps)
        print(f"{etiquette}: P1 atteignable sur {p['atteignables']}/{p['valides']} episodes"
              f" | votants distincts sur P1 {p['votants']}"
              f" | captures {p['captures']}, dont {p['captures_atteignables']} atteignables")
    print("Captures minimales excluant 0 contre un comparateur a zero : "
          + " ; ".join(f"n_a={n} -> {captures_necessaires(n, n)}" for n in (5, 12, 20)))


if __name__ == "__main__":
    main()
