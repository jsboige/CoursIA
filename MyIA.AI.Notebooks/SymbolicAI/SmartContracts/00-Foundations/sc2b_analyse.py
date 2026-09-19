"""Analyse et verdicts de l'experience SC-2b (#15060) -- lit les JSONL du harnais.

Produit les blocs de verdict pre-enregistres :
  - H1 : bras 1 heterogene vs homogene (capture, IC bootstrap 95 %, 10k)
  - H2 : bras 2 c5 vs c4
  - controle anti-recit : ~0 capture attendu, sinon verdict SUSPENDU
  - comptabilite : appels/jetons reels vs annonces, n effectifs

Usage : python sc2b_analyse.py
"""

from __future__ import annotations

import json
from pathlib import Path

import sc2b_experience as m

DOSSIER = Path(__file__).with_name("sc2b_resultats")


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
    print(m.verdict(cap_hetero, cap_homo, "heterogene", "homogene",
                    "H1 (heterogene +>=15 pp)"))

    print("\n--- H2 : politique de parole (population heterogene constante) ---")
    print("v2 (vote-puis-transfert) contre C4 ; l'IC porte sur 1 episode valide")
    print("(11/12 echecs MODEL_RETURNED_NO_CONTENT -- reserve majeure, cf. rapport)")
    print(m.verdict(cap_c5_v2, cap_c4, "C5-v2 (main endogene)", "C4 (designation declaree)",
                    "H2 (C5 +>=15 pp)"))
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


if __name__ == "__main__":
    main()
