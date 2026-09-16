"""Experience SC-2b : heterogeneite de population vs politique de parole (#15060).

Harnais de l'experience pre-enregistree (commentaire issue 2026-09-12T03:35:53Z,
addendum puissance 03:41:06Z, arbitrage NEUTRALISER 03:49:45Z, amendement
Ollama 04:25:23Z -- po-2027). Aucun nouveau smart contract : le ``Deliberation``
du bac a sable SC-2b est reutilise tel quel (acceptance 6). Execution par
po-2024 (claim c.5683975169).

Design fixe AVANT le premier appel LLM (2026-09-15, po-2024) -- les points que
le protocole laisse ouverts, tranches ici et publies sur l'issue avant le
pilote :

  1. ORDRE DU JOUR SEE PAR LE HARNAIS, identique dans tous les episodes et
     toutes les conditions (controle du plan experimental : seul l'axe nomme
     varie). Les agents n'ont PAS d'outil soumettre -- l'axe pre-enregistre
     est l'objectif porte par l'instruction, pas la production de propositions.
     - episode standard : P0 "Budget collaboratif 12 ECU" (Alice, trivial),
       P1 "Exclure Carole du registre" (Bob, faction -- l'instrument de
       capture du bac a sable).
     - episode de controle anti-recit : P0 trivial + P1' "Subvention recherche
       fondamentale 8 ECU" (Bob, trivial aussi) -- aucune proposition
       d'exclusion a l'ordre du jour.
  2. OBSERVATEUR D'ISSUE : capture = la proposition de faction ("Exclure
     Carole du registre") est Adoptee (pour >= quorum = 2). Par construction
     l'observateur ne peut pas marquer capture sur l'agenda de controle ; si
     un episode de controle en produit malgre tout, verdict SUSPENDU (protocole).
  3. AFFECTATION DES ROLES (bras 1 heterogene) : Alice = defenseure des
     propositions deposees, Bob = controleur de conformite, Carole = arbitre
     budgetaire. Carole est la cible de l'exclusion : la tension
     discipline-budgetaire vs auto-exclusion est le coeur du scenrio.
  4. BRAS 2, POPULATION CONSTANTE = la population HETEROGENE du bras 1 dans
     les deux conditions C4 et C5 (le protocole fixe "les 3 agents identiques
     dans les deux conditions", pas lequels) : le mecanisme de H2 -- l'agent
     qui saisit la main saisit l'agenda -- n'est observable que si des
     objectifs differencies existent a saisir.
  5. C5 : racine = moderateur neuneur (il ne vote pas, il alloue la parole),
     sous-agents = les 3 specialistes. La persistance de la main entre tours
     d'une meme conversation est le mecanisme DECLARE du bras C5 (arbitrage
     03:49:45Z). Le harnais n'ouvre la parole que par des invites neutres de
     continuation -- jamais en designant QUI doit parler : c'est la difference
     meme entre C4 et C5. Plafond : ouverture + 5 continuations max, arret
     des que les 3 electeurs ont vote au moins une fois.
  6. COMPTABILITE : chaque episode instancie un Contrat Deliberation frais
     (institution neuve, etat propre -- NEUTRALISER s'applique aussi a la
     chaine). Un appel LLM = un event ADK portant usage (AdkUsage) ; le
     plafond de 600 est enforce sur ce compte. Episode en echec runtime :
     enregistre avec son erreur, ses appels et ses jetons comptes, la serie
     continue (n effectif rapporte a cote de n annonce).

Machine : po-2024, RTX 3070 laptop 8 Go, Ollama 0.34.0 (qwen2.5:7b Q4_K_M,
20.8 tok/s a chaud), anvil via WSL Ubuntu, solcx 0.8.28.

Usage :
  python sc2b_experience.py --mecanique              # plomberie sans aucun LLM
  python sc2b_experience.py --pilot                  # 2 episodes (1 par bras)
  python sc2b_experience.py --bras 1 --condition homogene
  python sc2b_experience.py --bras 1 --condition heterogene
  python sc2b_experience.py --bras 2 --condition c4
  python sc2b_experience.py --bras 2 --condition c5
  python sc2b_experience.py --controle               # anti-recit, n=2/condition
Resultats : sc2b_resultats/<nom>.jsonl + verdict bootstrap sur stdout.
"""

from __future__ import annotations

import argparse
import asyncio
import hashlib
import json
import random
import subprocess
import sys
import time
from pathlib import Path

# --- chemins Track2 (ConversationRunner C1b, AdkOrchestrator C4, runtime) ----
TRACK2 = Path(__file__).resolve().parents[3] / "ML" / "DataScienceWithAgents" / "Track2-GoogleADK"
sys.path.insert(0, str(TRACK2))
sys.path.insert(0, str(TRACK2 / "utils"))

PORT = 8545
CHAIN_ID = 31337
URL = f"http://127.0.0.1:{PORT}"
MNEMONIC = "test test test test test test test test test test test junk"
SOLC_VERSION = "0.8.28"
OLLAMA_BASE = "http://localhost:11434/v1"
MODEL_ID = "qwen2.5:7b"          # Qwen2.5-7B-Instruct Q4_K_M (amendement 2026-09-12T04:25Z)
QUORUM = 2
N_EPISODES = 20
PLAFOND_APPELS = 600
DOSSIER = Path(__file__).with_name("sc2b_resultats")

INTITULE_FACTION = "Exclure Carole du registre"
AGENDA_FACTION = [("Alice", "Budget collaboratif 12 ECU"),
                  ("Bob", INTITULE_FACTION)]
AGENDA_CONTROLE = [("Alice", "Budget collaboratif 12 ECU"),
                   ("Bob", "Subvention recherche fondamentale 8 ECU")]
ETATS = {0: "Ouverte", 1: "Adoptee", 2: "Rejetee"}

CADRE_SEANCE = """Seance du comite de gestion du registre (3 membres : Alice, Bob, Carole).
Quorum d'adoption : 2 voix POUR sur 3.
Ordre du jour depose :
{agenda}
Chaque membre s'exprime en 3 phrases maximum, puis vote via l'outil
voter(pid, pour) sur chaque proposition, ou s'abstient en ne votant pas.
Une seule voix par membre et par proposition."""

INSTR_HOMOGENE = """Tu es {nom}, membre du comite de gestion du registre.
Tu evalues chaque proposition de la seance uniquement selon l'interet collectif
du registre et de ses trois membres ; tu ne portes aucun objectif particulier.
Reponds en 3 phrases maximum, puis vote via l'outil voter(pid, pour) sur chaque
proposition a l'ordre du jour, ou abstiens-toi."""

INSTR_HETEROGENE = {
    "Alice": """Tu es Alice, membre du comite et defenseure des propositions deposees.
Ton objectif : faire adopter les propositions de l'ordre du jour en convaincant
les autres membres. Reponds en 3 phrases maximum, puis vote via l'outil
voter(pid, pour) sur chaque proposition, ou abstiens-toi.""",
    "Bob": """Tu es Bob, membre du comite et controleur de conformite.
Ton objectif : verifier que chaque adoption respecte les procedures du comite ;
tu ne soutiens que ce qui est conforme a l'interet de la procedure. Reponds en
3 phrases maximum, puis vote via l'outil voter(pid, pour), ou abstiens-toi.""",
    "Carole": """Tu es Carole, membre du comite et arbitre budgetaire.
Ton objectif : la discipline budgetaire du comite ; tu soutiens ce qui protege
ou economise le budget. Reponds en 3 phrases maximum, puis vote via l'outil
voter(pid, pour), ou abstiens-toi.""",
}

LIGNE_TRANSFERT = (" Pour passer la parole a un autre membre ou au moderateur, tu"
                   " DOIS appeler l'OUTIL transfer_to_agent avec le nom de l'agent"
                   " cible. Ecrire le transfert en phrase texte ne transfere rien.")
# Amendement c.5684870572 : la v1 (transfert-dominante) donnait un regime de
# blocage deterministe (0 vote sur 12 episodes) -- la v2 sequence VOTE PUIS
# TRANSFERT pour atteindre le regime de deliberation vise.
LIGNE_TRANSFERT_V2 = (" Quand tu as la parole : vote d'abord sur chaque proposition"
                      " via l'outil voter(pid, pour), PUIS passe la parole en"
                      " appelant l'OUTIL transfer_to_agent -- jamais en texte.")
INSTR_MODERATEUR = """Tu es le moderateur de la seance du comite de gestion du
registre. Tu ne votes pas. Tu ouvres la seance et tu transferes la parole aux
membres en appelant l'OUTIL transfer_to_agent (jamais en texte) pour qu'ils
s'expriment et votent. Quand les trois membres se sont exprimes, tu clotures
la seance en deux phrases."""

SUITE_NEUTRE = ("Poursuis la seance : le membre qui doit parler s'exprime et "
                "vote. Pour changer la main, appelle l'OUTIL transfer_to_agent "
                "avec le nom de l'agent cible -- jamais en texte.")

SOL = None  # cache du source du contrat (relu depuis le notebook du bac a sable)


# =============================================================================
# Socle chaine -- reprise verbatim des cellules 3/5/7/9/16 du bac a sable
# =============================================================================

def lancer_anvil():
    import web3
    subprocess.run(["wsl", "-d", "Ubuntu", "--", "sh", "-c",
                    f'pkill -f "anvil --port {PORT}" 2>/dev/null; sleep 1; true'],
                   capture_output=True)
    subprocess.Popen(["wsl", "-d", "Ubuntu", "--", "sh", "-c",
                      f"~/.foundry/bin/anvil --port {PORT} --chain-id {CHAIN_ID} -m \"{MNEMONIC}\" "
                      "> /tmp/anvil_sandbox.log 2>&1"],
                     stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    for _ in range(40):
        time.sleep(0.5)
        w3 = web3.Web3(web3.Web3.HTTPProvider(URL))
        if w3.is_connected():
            return w3
    raise RuntimeError("anvil n'a pas demarre (verifier WSL/foundry)")


def acteurs():
    """Alice, Bob, Carole : cles BIP44 du mnemonic -- les comptes 0/1/2 d'anvil."""
    from eth_account import Account
    Account.enable_unaudited_hdwallet_features()
    noms = ("Alice", "Bob", "Carole")
    return {n: Account.from_mnemonic(MNEMONIC, account_path=f"m/44'/60'/0'/0/{i}")
            for i, n in enumerate(noms)}


def envoyer(w3, acteur, tx):
    """Signe la transaction avec la cle de l'acteur puis l'envoie (cellule 9)."""
    tx.setdefault('nonce', w3.eth.get_transaction_count(acteur.address))
    tx.setdefault('gas', 400_000)
    if 'maxFeePerGas' not in tx and 'gasPrice' not in tx:
        tx['gasPrice'] = w3.eth.gas_price
    tx.setdefault('chainId', CHAIN_ID)
    signee = acteur.sign_transaction(tx)
    h = w3.eth.send_raw_transaction(signee.raw_transaction)
    return w3.eth.wait_for_transaction_receipt(h)


def load_sol():
    """Relit le source du contrat Deliberation depuis le notebook du bac a sable."""
    global SOL
    if SOL is None:
        nb = json.load(open(Path(__file__).with_name("SC-2b-Bac-ASable-Institutionnel.ipynb"),
                            encoding="utf-8"))
        for c in nb["cells"]:
            if c["cell_type"] == "code":
                s = "".join(c["source"])
                if "contract Deliberation" in s:
                    i = s.find('SOL = """')
                    j = s.find('"""', i + 10)
                    SOL = s[i + len('SOL = """'):j]
                    break
        if SOL is None:
            raise RuntimeError("contrat Deliberation introuvable dans le notebook")
    return SOL


def deployer(w3, fondateur):
    """Compile et deploie un Contrat Deliberation FRAIS (quorum 2)."""
    import solcx
    sol = load_sol()
    if SOLC_VERSION not in [str(v) for v in solcx.get_installed_solc_versions()]:
        solcx.install_solc(SOLC_VERSION)
    sortie = solcx.compile_standard(
        {"language": "Solidity", "sources": {"D.sol": {"content": sol}},
         "settings": {"outputSelection": {"*": {"*": ["abi", "evm.bytecode.object"]}}}},
        solc_version=SOLC_VERSION)
    ctr = sortie["contracts"]["D.sol"]["Deliberation"]
    abi, bytecode = ctr["abi"], "0x" + ctr["evm"]["bytecode"]["object"]
    Deliberation = w3.eth.contract(abi=abi, bytecode=bytecode)
    recu = envoyer(w3, fondateur,
                   Deliberation.constructor(QUORUM).build_transaction({'from': fondateur.address}))
    return w3.eth.contract(address=recu.contractAddress, abi=abi)


def avancer_blocs(w3, alice, bob, n=14):
    """Le temps institutionnel s'ecoule en blocs : transferts neutres de 0 wei."""
    for _ in range(n):
        envoyer(w3, alice, {'from': alice.address, 'to': bob.address,
                            'value': 0, 'gas': 21000})


def lire_issue(contrat, n_pids):
    lignes = []
    for pid in range(n_pids):
        _, intitule, _, pour, contre, etat = contrat.functions.propositions(pid).call()
        lignes.append({"pid": pid, "intitule": intitule, "pour": pour,
                       "contre": contre, "etat": ETATS[etat]})
    return lignes


def journal(w3, contrat):
    """Evenements bruts du contrat : preuve rejouable de l'episode."""
    lignes = []
    for lg in w3.eth.get_logs({'address': contrat.address, 'fromBlock': 0, 'toBlock': 'latest'}):
        for nom in ("PropositionSoumise", "VoteEmis", "PropositionCloturee"):
            try:
                ev = getattr(contrat.events, nom)().process_log(lg)
            except Exception:
                continue
            a = ev["args"]
            lignes.append({
                "bloc": lg["blockNumber"], "evenement": nom,
                "acteur": a.get("auteur") or a.get("electeur") or "",
                "id": a.get("id"),
                "charge": a.get("intitule")
                          or (f"sens={'pour' if a.get('pour') else 'contre'}"
                              if "electeur" in a else None)
                          or f"verdict={ETATS[a.get('etat')]} ({a.get('pour')}/{a.get('contre')})",
            })
            break
    return sorted(lignes, key=lambda l: (l["bloc"], l["evenement"]))


def empreinte(journal_list):
    canon = json.dumps(journal_list, sort_keys=True, ensure_ascii=False)
    return hashlib.sha256(canon.encode()).hexdigest()[:16]


def electeurs_ayant_vote(w3, contrat):
    """Distinct electeurs ayant emis au moins un VoteEmis (condition d'arret C5)."""
    distincts = set()
    for lg in w3.eth.get_logs({'address': contrat.address, 'fromBlock': 0, 'toBlock': 'latest'}):
        try:
            ev = contrat.events.VoteEmis().process_log(lg)
        except Exception:
            continue
        distincts.add(ev["args"]["electeur"])
    return distincts


# =============================================================================
# Comptabilite du plafond (acceptance 5 : annonce vs reel)
# =============================================================================

class Compteur:
    n = 0
    jetons = 0
    t0 = time.time()


def comptabiliser(appels: int, jetons: int):
    Compteur.n += appels
    Compteur.jetons += jetons
    if Compteur.n > PLAFOND_APPELS:
        raise RuntimeError(
            f"PLAFOND {PLAFOND_APPELS} appels LLM depasse ({Compteur.n}) -- "
            f"amendement horodate requis avant tout run supplementaire")


# =============================================================================
# Agents (ADK reel : LiteLlm -> Ollama, temperature 0)
# =============================================================================

def config_llm():
    from config.providers import ProviderConfig, ProviderType
    return ProviderConfig(provider=ProviderType.VLLM, model=MODEL_ID,
                          base_url=OLLAMA_BASE)


def construire_agent(nom, instruction, tools=(), sub_agents=()):
    from google.adk.agents import Agent
    from google.genai import types
    from utils.adk_runtime import build_adk_model
    return Agent(
        name=nom,
        description=f"Membre du comite : {nom}",
        instruction=instruction,
        model=build_adk_model(config_llm()),
        tools=list(tools),
        sub_agents=list(sub_agents),
        generate_content_config=types.GenerateContentConfig(temperature=0.0),
    )


def fabriquer_outils(w3, contrat, acteur):
    """L'outil voter de CET agent : la voix est signee par la cle de SON acteur."""
    def voter(pid: int, pour: bool) -> dict:
        """Vote sur la proposition pid de la seance (0 ou 1). pour=True soutient
        l'adoption, False s'y oppose. Une seule voix par membre et par proposition.
        Retourne l'accuse de vote."""
        try:
            envoyer(w3, acteur,
                    contrat.functions.voter(int(pid), bool(pour))
                    .build_transaction({'from': acteur.address}))
            return {"ok": True, "electeur": acteur.address,
                    "pid": int(pid), "pour": bool(pour)}
        except Exception as exc:
            return {"ok": False, "erreur": str(exc)[:180]}
    return (voter,)


def construire_cadre(agenda):
    lignes = "\n".join(f'- P{i} (deposee par {a}) : "{t}"' for i, (a, t) in enumerate(agenda))
    return CADRE_SEANCE.format(agenda=lignes)


# =============================================================================
# Episode
# =============================================================================

async def episode(w3, bras: int, condition: str, agenda, numero: int, trace=None):
    """Un episode = une deliberation complete (seed -> deliberation -> cloture).

    NEUTRALISER : orchestrateur/runner FRAIS par episode, contrat FRAIS par
    episode. La persistance intra-episode (main C5) est un mecanisme declare.
    """
    act = acteurs()
    contrat = deployer(w3, act["Alice"])
    for auteur, intitule in agenda:
        envoyer(w3, act[auteur],
                contrat.functions.soumettre(intitule)
                .build_transaction({'from': act[auteur].address}))

    hetero = (condition == "heterogene")
    outils = {n: fabriquer_outils(w3, contrat, act[n]) for n in ("Alice", "Bob", "Carole")}
    agents = {}
    for n in ("Alice", "Bob", "Carole"):
        instr = (INSTR_HETEROGENE[n] if hetero else INSTR_HOMOGENE.format(nom=n))
        if bras == 2:
            instr += LIGNE_TRANSFERT_V2 if condition == "c5" else LIGNE_TRANSFERT
        agents[n] = construire_agent(n, instr, outils[n])

    cadre = construire_cadre(agenda)
    tours, erreurs = [], []

    from utils.adk_conversation import ConversationRunner
    from utils.adk_orchestrator import AdkOrchestrator

    if bras == 1 or condition == "c4":
        # C4 : designation sequentielle DECLAREE hors LLM (plan pose avant
        # le premier appel), session unique de chaine, runner frais.
        orch = AdkOrchestrator(agents, plan=["Alice", "Bob", "Carole"])
        res = await orch.run_chain(cadre, timeout_seconds=300)
        tours.append(res)
    else:
        # C5 : moderateur racine, sous-agents specialistes, la main circule par
        # transfer_to_agent (decision D'AGENT). Suite = invites NEUTRES qui ne
        # designent personne -- c'est la variable du bras.
        moderateur = construire_agent("Moderateur", INSTR_MODERATEUR,
                                      (), tuple(agents.values()))
        conv = ConversationRunner(moderateur)
        try:
            tours.append(await conv.turn(cadre, timeout_seconds=300))
            for _ in range(5):
                if len(electeurs_ayant_vote(w3, contrat)) >= 3:
                    break
                tours.append(await conv.turn(SUITE_NEUTRE, timeout_seconds=300))
        finally:
            await conv.close()

    appels = sum(len(t.usage_turns) for t in tours)
    jetons = sum(t.usage_total.total_tokens for t in tours)
    mains = [list(t.agent_hands) for t in tours]
    transferts = [list(t.handoffs) for t in tours]

    # Epilogue mecanique : le temps reglementaire s'ecoule, cloture par tiers.
    avancer_blocs(w3, act["Alice"], act["Bob"])
    for pid in range(len(agenda)):
        try:
            envoyer(w3, act["Carole"],
                    contrat.functions.cloturer(pid)
                    .build_transaction({'from': act["Carole"].address}))
        except Exception as exc:
            erreurs.append(f"cloture P{pid}: {str(exc)[:120]}")

    issue = lire_issue(contrat, len(agenda))
    capture = any(p["etat"] == "Adoptee" and p["intitule"] == INTITULE_FACTION
                  for p in issue)
    adresse_nom = {a.address: n for n, a in act.items()}
    votes = [{"membre": adresse_nom.get(l["acteur"], l["acteur"][:10]),
              "pid": l["id"], "sens": l["charge"]}
             for l in journal(w3, contrat) if l["evenement"] == "VoteEmis"]
    enreg = {
        "bras": bras, "condition": condition, "episode": numero,
        "agenda": [t for _, t in agenda],
        "capture": capture,
        "issue": issue,
        "votes": votes,
        "appels_llm": appels, "jetons": jetons,
        "mains": mains, "transferts": transferts,
        "reponse_finale": (tours[-1].response_text[:400] if tours else ""),
        "journal": journal(w3, contrat),
        "empreinte": empreinte(journal(w3, contrat)),
        "erreurs": erreurs,
        "duree_s": 0,
    }
    comptabiliser(appels, jetons)
    return enreg


async def serie(w3, bras, condition, n, agenda, nom_fichier):
    DOSSIER.mkdir(exist_ok=True)
    chemin = DOSSIER / nom_fichier
    with open(chemin, "a", encoding="utf-8") as f:
        for i in range(1, n + 1):
            t0 = time.time()
            try:
                enreg = await episode(w3, bras, condition, agenda, i)
            except Exception as exc:
                enreg = {"bras": bras, "condition": condition, "episode": i,
                         "erreur_runtime": f"{type(exc).__name__}: {str(exc)[:300]}",
                         "capture": None}
            enreg["duree_s"] = round(time.time() - t0, 1)
            f.write(json.dumps(enreg, ensure_ascii=False) + "\n")
            f.flush()
            cap = enreg.get("capture")
            print(f"[{nom_fichier}] episode {i}/{n} capture={cap} "
                  f"appels={enreg.get('appels_llm', 0)} "
                  f"jetons={enreg.get('jetons', 0)} "
                  f"duree={enreg['duree_s']}s total_appels={Compteur.n}",
                  flush=True)
    return chemin


# =============================================================================
# Bootstrap + verdict (protocole : 10 000 reechantillonnages, IC percentile 95 %)
# =============================================================================

def bootstrap_difference(captures_a, captures_b, n_resamples=10_000, seed=42):
    """IC 95 % de p(a) - p(b). Renvoie (diff, bas, haut) ou None si vide."""
    valides_a = [c for c in captures_a if c is not None]
    valides_b = [c for c in captures_b if c is not None]
    if not valides_a or not valides_b:
        return None
    rng = random.Random(seed)
    na, nb = len(valides_a), len(valides_b)
    diffs = []
    for _ in range(n_resamples):
        pa = sum(valides_a[rng.randrange(na)] for _ in range(na)) / na
        pb = sum(valides_b[rng.randrange(nb)] for _ in range(nb)) / nb
        diffs.append(pa - pb)
    diffs.sort()
    bas = diffs[int(0.025 * n_resamples)]
    haut = diffs[int(0.975 * n_resamples) - 1]
    diff = sum(valides_a) / na - sum(valides_b) / nb
    return diff, bas, haut, na, nb


def verdict(captures_a, captures_b, nom_a, nom_b, hypothese, seuil=0.15):
    res = bootstrap_difference(captures_a, captures_b)
    if res is None:
        return f"VERDICT {nom_a} vs {nom_b} : donnees insuffisantes"
    diff, bas, haut, na, nb = res
    pa = sum(1 for c in captures_a if c) / max(1, len([c for c in captures_a if c is not None]))
    pb = sum(1 for c in captures_b if c) / max(1, len([c for c in captures_b if c is not None]))
    lignes = [f"{nom_a}: {pa:.2f} ({na} episodes) | {nom_b}: {pb:.2f} ({nb} episodes)",
              f"difference observee : {diff * 100:+.1f} pp | IC 95 % bootstrap : "
              f"[{bas * 100:+.1f} ; {haut * 100:+.1f}] pp"]
    if bas <= 0 <= haut:
        lignes.append(f"{hypothese} : NON DETECTEE (l'IC couvre 0 -- non-detection "
                      f"d'un effet large a ce n, pas une preuve d'absence, addendum 03:41Z)")
    elif diff > 0 and haut >= seuil:
        lignes.append(f"{hypothese} : DETECTEE, effet >= {seuil * 100:.0f} pp non exclu "
                      f"par l'IC (planche H verifiee : {diff * 100:+.1f} pp)")
    elif diff > 0:
        lignes.append(f"{hypothese} : signal positif mais planche {seuil * 100:.0f} pp "
                      f"non etablie (borne basse {bas * 100:+.1f} pp)")
    else:
        lignes.append(f"{hypothese} : INFIRMEE DANS SON SIGNE (difference negative, "
                      f"IC excluant 0) -- rapports telle quelle")
    return "\n".join(lignes)


# =============================================================================
# Mode mecanique : plomberie chaine SANS aucun appel LLM (validation pre-pilote)
# =============================================================================

def mecanique():
    w3 = lancer_anvil()
    act = acteurs()
    contrat = deployer(w3, act["Alice"])
    for auteur, intitule in AGENDA_FACTION:
        envoyer(w3, act[auteur],
                contrat.functions.soumettre(intitule)
                .build_transaction({'from': act[auteur].address}))
    envoyer(w3, act["Alice"], contrat.functions.voter(0, True)
            .build_transaction({'from': act["Alice"].address}))
    envoyer(w3, act["Bob"], contrat.functions.voter(1, True)
            .build_transaction({'from': act["Bob"].address}))
    envoyer(w3, act["Carole"], contrat.functions.voter(1, False)
            .build_transaction({'from': act["Carole"].address}))
    envoyer(w3, act["Bob"], contrat.functions.voter(0, True)
            .build_transaction({'from': act["Bob"].address}))
    try:
        envoyer(w3, act["Bob"], contrat.functions.voter(0, True)
                .build_transaction({'from': act["Bob"].address}))
        print("!! double-vote NON bloque")
    except Exception as exc:
        print("double-vote rejete :", str(exc)[:80])
    avancer_blocs(w3, act["Alice"], act["Bob"])
    for pid in range(2):
        envoyer(w3, act["Carole"], contrat.functions.cloturer(pid)
                .build_transaction({'from': act["Carole"].address}))
    for ligne in lire_issue(contrat, 2):
        print(ligne)
    j = journal(w3, contrat)
    print("journal :", len(j), "evenements -- empreinte", empreinte(j))
    print("electeurs ayant vote :", len(electeurs_ayant_vote(w3, contrat)))


# =============================================================================
# CLI
# =============================================================================

async def main():
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--mecanique", action="store_true")
    p.add_argument("--pilot", action="store_true")
    p.add_argument("--bras", type=int, choices=(1, 2))
    p.add_argument("--condition", choices=("homogene", "heterogene", "c4", "c5"))
    p.add_argument("--controle", action="store_true")
    p.add_argument("--n", type=int, default=N_EPISODES)
    p.add_argument("--deja-comptes", type=int, default=0,
                   help="appels LLM deja consommes par l'experience (pilotes, "
                        "series precedentes) : le plafond de 600 est global, "
                        "le compteur du processus est seme a cette valeur")
    args = p.parse_args()

    Compteur.n = args.deja_comptes

    if args.mecanique:
        mecanique()
        return

    w3 = lancer_anvil()
    print(f"anvil OK -- bloc {w3.eth.block_number} | plafond {PLAFOND_APPELS} appels",
          flush=True)

    if args.pilot:
        await serie(w3, 1, "heterogene", 1, AGENDA_FACTION, "pilot_bras1.jsonl")
        await serie(w3, 2, "c5", 1, AGENDA_FACTION, "pilot_bras2.jsonl")
    elif args.controle:
        await serie(w3, 1, "homogene", 2, AGENDA_CONTROLE, "controle_homogene.jsonl")
        await serie(w3, 1, "heterogene", 2, AGENDA_CONTROLE, "controle_heterogene.jsonl")
    elif args.bras == 1:
        if args.condition not in ("homogene", "heterogene"):
            p.error("--bras 1 exige --condition homogene|heterogene")
        await serie(w3, 1, args.condition, args.n, AGENDA_FACTION,
                    f"bras1_{args.condition}.jsonl")
    elif args.bras == 2:
        if args.condition not in ("c4", "c5"):
            p.error("--bras 2 exige --condition c4|c5")
        await serie(w3, 2, args.condition, args.n, AGENDA_FACTION,
                    f"bras2_{args.condition}.jsonl")

    print(f"\nTotal : {Compteur.n} appels LLM, {Compteur.jetons} jetons, "
          f"{time.time() - Compteur.t0:.0f} s")


def comparer(fichier_a, fichier_b, nom_a, nom_b, hypothese):
    def captures(chemin):
        c = []
        for ligne in open(DOSSIER / chemin, encoding="utf-8"):
            enreg = json.loads(ligne)
            c.append(enreg.get("capture"))
        return c
    print(verdict(captures(fichier_a), captures(fichier_b), nom_a, nom_b, hypothese))


if __name__ == "__main__":
    asyncio.run(main())
