"""Banc comparatif volet B (#18430) : rung 52 passe a un prouveur LeanDojo-v2.

Question du volet B : faire passer **le meme palier de calibration, avec le
meme budget**, a un prouveur LeanDojo-v2 et au harnais multi-agents maison,
puis **rapporter l'ecart** plutot que de le moyenner (cf ``.claude/rules/
organ-first-implementation.md`` transpose a un organe externe).

Verdict maison (mesure de reference, Epic #1453 passe 17, 2026-09-27) :
``CALIBRATION_CONWAY_LAS_ROUND_TRIP`` -- ``digitsToNat_natToDigits``
(``LookAndSayLemmas.lean:41``, DIFF hard) : **FAILED honnete 1->1 en
1 925,1 s** -- timeout du budget de raisonnement (1 800 s). Le coordinateur
du harnais a pose en 125 s un plan correspondant a la structure exacte de la
preuve canonique (lemme d'append + induction sur ``n / 10``), puis 7
insertions BUILD-FAIL revertées ; l'induction n'a jamais demarre.

Ce banc soumet **le meme enonce** au prouveur v2 (ExternalProver via le serveur
RPC Pantograph), **meme modele LLM** (``anthropic/claude-opus-4.7`` sur
openrouter, le modele des traces maison) et **meme budget** (plafond 1 800 s
de raisonnement, plafond d'appels LLM), en deux modes :

  1. pas-a-pas : boucle ``goal_start`` -> ``generate`` -> ``goal_tac``
     (chaque tactique appliquee et verifiee par Lean) ;
  2. preuve entiere : ``generate_whole_proof`` -> ``check_compile``.

Le budget est applique **de bout en bout** : le transport HTTP porte le temps
restant comme timeout (``transport_timeout_s``), un budget epuise arrete
l'appel avant qu'il ne parte (``budget_hit``), et une preuve nee hors budget
est un echec ``budget_s_timeout`` -- jamais une reussite retardee (mesure
adjoint 2026-10-13, c.6143211874).

Ecart de protocole documente (mesure du 2026-10-12, po-2024) : le repl
Pantograph 0.3.15 **refuse une toolchain de projet differente de la sienne**
-- conway_lean porte v4.33.0, le wheel Pantograph embarque ``lean-toolchain``
``leanprover/lean4:v4.29.1`` (fichier ``pantograph/lean-toolchain`` du venv ;
les oleans d'une autre toolchain sont rejetees ``incompatible header``). Le
banc monte donc un mini-lake snapshot (code source byte-identique, Mathlib
pinnee v4.29.1, sorry reintroduit au rung) ; la trace de ce montage vit dans
le rapport. Second ecart mesure : ``pantograph.utils.get_lean_path`` appelle
``lake env printenv LEAN_PATH``, qui rend une chaine VIDE sur lake 5.0.0 --
le banc resout LEAN_PATH en parsant ``lake env printenv`` integral
(cf ``lake_lean_path`` ci-dessous).

Execution de reference (WSL, venv dedie, machine po-2024) :

    set -a; . /mnt/d/Dev/CoursIA/.secrets/master.env; set +a
    export GITHUB_ACCESS_TOKEN="$(gh auth token)"
    ~/venvs/leandojo-v2/bin/python leandojo_v2_bench.py --mode both \
        --project ~/leandojo-v2-work/bench/rung52_conway_las

Aucun secret n'est lu ni ecrit par ce module : ``OPENROUTER_API_KEY`` vient
de l'environnement (secrets-hygiene regle 3).

Defauts de transport mesures puis corriges (po-2024, 2026-10-20 -- le run du
2026-10-12 etait degenere sur les deux modes, il mesurait le transport, pas
l'organe) :

1. **``n`` non honore par openrouter** : la sonde HTTP 200 sur le prompt de
   test avec ``"n": 4`` rend **1 seul choix** (l'API Anthropic n'a pas de
   sampling ``n``). Le generateur v2, concu pour n echantillons par pas,
   n'en recevait qu'un : le dedoublonnage ``used_tactics`` epuisait la
   recherche en 3 appels (run 2026-10-12 : ``generator_exhausted`` en 5,9 s
   contre 1 925 s maison). ``_post`` emule maintenant ``n`` par requetes
   successives, chacune bornee par la deadline residuelle.
2. **Parser upstream une-ligne sur les preuves entieres** : la branche
   ``"claude"`` de ``external_parser.post_process_output`` fait
   ``.split("\\n")[1]`` -- elle tronque toute sortie a UNE ligne (la preuve
   entiere du 2026-10-12 etait reduite a ``induction n using
   Nat.strong_induction_on with``). La branche ``deepseek`` du meme parser
   garde la preuve complete : ``_extract_whole_proof`` aligne le shim sur
   cette semantique (bloc fence des-enveloppe, multi-ligne preserve).
"""
from __future__ import annotations

import argparse
import asyncio
import json
import os
import subprocess
import time
from dataclasses import dataclass, field, asdict
from pathlib import Path
from typing import Optional

# Modele des traces maison (config.py PROVIDERS["openrouter"], defaut non
# surcharge par .env -- mesure du 2026-10-12) : le banc DOIT l'utiliser pour
# que la comparaison porte sur l'organe (prouveur), pas sur le moteur.
HOUSE_MODEL = "anthropic/claude-opus-4.7"

# Budget aligne sur la passe 17 maison : 1 800 s de raisonnement.
HOUSE_REASONING_BUDGET_S = 1800.0

# Plafond du transport HTTP par appel, aligne sur le timeout Pantograph par
# appel (--timeout, defaut 120 s) : la deadline residuelle ne peut pas
# lever ce plafond, seulement l'abaisser.
REQUEST_TIMEOUT_CAP_S = 120.0

# Identifiants pleinement qualifies : le REPL de Pantograph charge le module
# mais pas le namespace -- `digitsToNat` nu leve `Unknown identifier`
# (mesure du 2026-10-12). Le forall ne met pas `n` dans le contexte local :
# le premier pas du mode pas-a-pas est `intro n`.
RUNG_STATEMENT = (
    "forall (n : Nat), Conway.digitsToNat (Conway.natToDigits n) = n"
)
RUNG_NAME = "CALIBRATION_CONWAY_LAS_ROUND_TRIP"


class ConfigError(RuntimeError):
    """Configuration manquante (cle API, env)."""


def _openrouter_key() -> str:
    key = os.environ.get("OPENROUTER_API_KEY", "").strip()
    if not key:
        raise ConfigError(
            "OPENROUTER_API_KEY absente de l'environnement -- "
            "exporter depuis .secrets/master.env avant le banc"
        )
    return key


def deadline_remaining(deadline: Optional[float]) -> Optional[float]:
    """Temps restant avant la deadline (monotonic) ; None sans deadline."""
    if deadline is None:
        return None
    return deadline - time.monotonic()


def transport_timeout_s(remaining: Optional[float]) -> Optional[float]:
    """Timeout ``requests`` borne par le temps restant du budget.

    None = pas de borne (deadline absente). Une valeur <= 0 signifie budget
    epuise : l'appel ne doit pas partir du tout. Mesure fondatrice (adjoint
    2026-10-13, dossier c.6143211874) : ``requests.post`` sans timeout et le
    budget controle seulement avant l'appel synchrone -- une generation
    pendante pouvait depasser ``budget_s`` sans limite.
    """
    if remaining is None:
        return None
    return min(remaining, REQUEST_TIMEOUT_CAP_S)


def lake_lean_path(project: str) -> str:
    """LEAN_PATH du lake, en contournant deux mesures pantograph 0.3.15.

    1. ``Server(_sync_init=False)`` ne resout PAS ``lean_path`` (server.py:73
       conditionne la resolution a ``_sync_init``) : sans valeur explicite, le
       repl part sans LEAN_PATH et rejette les imports du lake.
    2. ``pantograph.utils.get_lean_path`` appelle ``lake env printenv
       LEAN_PATH``, qui rend une chaine VIDE sur lake 5.0.0 (v4.29.1/v4.34.1)
       -- seule la sortie integrale de ``lake env printenv`` porte LEAN_PATH.

    On parse donc ``lake env printenv`` complet. Mesures du 2026-10-12.
    """
    out = subprocess.run(
        ["lake", "env", "printenv"],
        cwd=project, capture_output=True, text=True, check=True,
        encoding="utf-8", errors="replace",
    ).stdout
    for line in out.splitlines():
        if line.startswith("LEAN_PATH="):
            return line[len("LEAN_PATH="):]
    raise ConfigError("LEAN_PATH introuvable dans la sortie de `lake env printenv`")


def _extract_whole_proof(output: str) -> str:
    """Extrait la preuve entiere de la sortie brute du modele.

    Bug mesure du parser upstream (``external_parser.py``, branche
    ``"claude"``) : ``.split("lean")[-1].split("```")[0].split("\\n")[1]``
    tronque toute sortie a UNE ligne -- fatal a ``generate_whole_proof``
    (preuve du 2026-10-12 reduite a ``induction n using
    Nat.strong_induction_on with`` alors que la sortie brute mesurait 7
    lignes, fence comprise). La branche ``deepseek`` du meme parser garde la
    preuve complete : ce des-enveloppement s'aligne sur cette semantique.

    Second defaut mesure (run corrige du 2026-10-20) : claude-opus-4.7 via
    openrouter peut ouvrir sa sortie d'un bloc de raisonnement
    ``<think>...</think>`` AVANT la fence -- un extrateur qui ne regarde
    que le debut de chaine rend le bloc entier au ``check_compile`` (echec
    de parse, pas de preuve). On retire donc d'abord les blocs think,
    puis on prend le DERNIER bloc fence s'il existe.

    Les formes observees passent : bloc fence ferme, bloc non termine,
    sortie nue, think + fence (mesure 2026-10-20).

    Correction du 2026-10-23 (crible adjoint de ``23ce570697``, #21672) : la
    branche ``startswith`` court-circuitait le contrat ci-dessus des que la
    sortie ne finissait PAS sur la fence. Deux contre-exemples reproduits :
    une fence fermee suivie d'une phrase finale rendait la fence ET la
    phrase ; deux blocs successifs rendaient le PREMIER bloc et les fences
    intermediaires. Le contrat vaut desormais pour toutes les formes -- le
    dernier bloc FERME gagne, et seule une fence non terminee (aucun bloc
    ferme dans le texte) est des-envelopee ligne a ligne.

    Seconde correction du 2026-10-23 (verification independante de la meme
    tete, #21672) : la reconnaissance des fences passe du texte brut a la
    LIGNE. Deux contre-exemples reproduits : `` ```lean4 `` (etiquette autre
    que ``lean``) n'etait pas reconnue, donc sa cloture entrait dans la
    preuve rendue ; ``have s := "```"`` etait pris pour une cloture et
    tronquait la preuve a ``have s := "``.

    Troisieme correction du 2026-10-23 (verification adjointe de la tete
    ``20ba1bb2fc4``, #21672) : la fermeture est desormais COMPATIBLE avec la
    longueur de l'ouvreur. L'ouverture acceptait toute longueur (au moins
    trois backticks) mais la fermeture exigeait une ligne exactement
    `` ``` `` : un bloc ouvert a quatre backticks n'etait donc jamais ferme,
    et sa cloture comme la phrase qui suivait entraient dans la preuve rendue
    (``exact rfl``, cloture, puis ``Done.``). La fermeture est desormais une
    ligne FAITE de backticks, au moins aussi longue que l'ouvreur --
    semantique CommonMark ; une ligne plus courte, etiquetee ou noyee dans du
    code Lean reste du contenu.
    """
    import re

    text = output.strip()
    # blocs de raisonnement retires (un ou plusieurs, non imbriques)
    text = re.sub(r"<think>.*?</think>\s*", "", text, flags=re.DOTALL).strip()
    # Fences reconnues PAR LIGNE, jamais par regex sur le texte brut
    # (mesure 2026-10-23, verification independante de #21672). Une regex
    # `` ```(?:lean)?\n(.*?)``` `` prend les backticks d'une chaine Lean pour
    # une cloture -- ``have s := "```"`` tronquait la preuve a ``have s := "``
    # -- et ignore toute etiquette autre que ``lean`` : `` ```lean4 `` n'etait
    # pas reconnue, donc la cloture etait rendue dans la preuve.
    #
    # Ouverture = ligne dont la forme decapee COMMENCE par au moins trois
    # backticks (l'etiquette est libre) ; fermeture = ligne FAITE de
    # backticks, au moins aussi longue que l'ouvreur (compatibilite de
    # longueur, 2026-10-23 : un ouvreur a quatre backticks n'etait ferme que
    # par une ligne exactement ```, et la cloture entrait dans la preuve).
    # Une fence non terminee (aucune fermeture avant la fin) s'ouvre au
    # dernier ouvreur rencontre.
    lines = text.splitlines()
    blocks: list[list[str]] = []
    open_at: Optional[int] = None
    open_ticks = 0
    for i, line in enumerate(lines):
        stripped = line.strip()
        ticks = len(stripped) - len(stripped.lstrip("`"))
        if open_at is None:
            if ticks >= 3:
                open_at = i
                open_ticks = ticks
        elif stripped.strip("`") == "" and ticks >= open_ticks:
            blocks.append(lines[open_at + 1:i])
            open_at = None
            open_ticks = 0
    # dernier bloc FERME, qu'il ouvre le texte ou qu'il le suive : ni une
    # phrase finale ni un bloc precedent ne doit l'emporter.
    if blocks:
        return "\n".join(blocks[-1]).strip()
    # aucun bloc ferme : fence NON TERMINEE (le modele s'est arrete dans le
    # bloc). On retire la ligne d'ouverture et on rend le reste.
    if open_at is not None:
        return "\n".join(lines[open_at + 1:]).strip()
    return text


def _make_openrouter_generator(deadline: Optional[float] = None):
    """Construit le generateur de tactiques branche openrouter.

    ``deadline`` (monotonic) borne le transport : chaque ``_post`` reçoit un
    timeout egal au temps restant du budget (plafonne par
    ``REQUEST_TIMEOUT_CAP_S``), et un budget epuise arrete l'appel avant
    qu'il ne parte -- ``budget_hit`` signale la coupure aux deux modes.

    Sous-classe documentee (mesure #18430 volet C, ai-01 2026-10-04) :
    ``HFTacticGenerator.generate`` code en dur l'URL
    (``hf_runner.py:24/:67``) ET le champ ``model`` du payload
    (``:30/:73`` -- l'argument constructeur ``model_name`` n'agit que sur le
    pre/post-traitement). Aucune sous-classe ne peut surcharger sans recopier
    le corps de methode : on recopie, en parametrant URL, model et auth. Le
    transport etant OpenAI chat-completions, openrouter le parle nativement.
    """
    import requests
    from loguru import logger

    from lean_dojo_v2.external_api.python.external_models.hf_runner import (
        HFTacticGenerator,
    )
    from lean_dojo_v2.external_api.python.external_models.external_parser import (
        post_process_output,
        pre_process_input,
    )

    class OpenRouterTacticGenerator(HFTacticGenerator):
        """HFTacticGenerator branche openrouter (shim volet C, recopie documentee)."""

        API_URL = "https://openrouter.ai/api/v1/chat/completions"

        def __init__(
            self, model_name: str = HOUSE_MODEL,
            deadline: Optional[float] = None,
        ) -> None:
            super().__init__(model_name=model_name)
            self.model = model_name
            self.calls = 0
            self.deadline = deadline
            self.budget_hit = False

        def _post(self, prompt: str, n: int, max_tokens: int) -> list[str]:
            # Emulation de n (mesure 2026-10-20) : openrouter rend 1 seul
            # choix pour les modeles Anthropic malgre "n": k -- le generateur
            # v2 attend n echantillons par pas. On repete la requete jusqu'a
            # n choix, chaque sous-requete bornee par la deadline residuelle
            # (jamais de rafale hors budget) ET comptee dans self.calls des
            # qu'une TENTATIVE de POST est engagee, erreur API comprise. Une
            # erreur API ou une reponse vide interrompt : on rend les choix
            # deja collectes. ``calls`` compte des tentatives, pas des
            # requetes prouvees parties sur le reseau (une resolution DNS ou
            # un refus de connexion incremente aussi) -- ne pas le lire comme
            # une mesure de trafic (verification independante #21672).
            collected: list[str] = []
            while len(collected) < n:
                timeout = transport_timeout_s(deadline_remaining(self.deadline))
                if timeout is not None and timeout <= 0:
                    # Budget epuise : la requete ne part pas, la coupure
                    # remonte aux modes via budget_hit.
                    self.budget_hit = True
                    break
                headers = {"Authorization": f"Bearer {_openrouter_key()}"}
                payload = {
                    "messages": [{"role": "user", "content": prompt}],
                    "model": self.model,
                    "temperature": 0.6,
                    "max_tokens": max_tokens,
                    "top_p": 0.9,
                    "n": 1,
                }
                try:
                    response = requests.post(
                        self.API_URL, headers=headers, json=payload, timeout=timeout
                    )
                finally:
                    # Comptee des que la TENTATIVE de POST est engagee, quel
                    # que soit le sort du transport (crible adjoint du
                    # 2026-10-23 : le compteur restait a 1 pour 2 requetes
                    # emises, parce que la reponse en erreur sortait avant
                    # l'increment). Une tentative qui echoue avant tout envoi
                    # (DNS, connexion refusee) compte aussi : c'est un
                    # compteur de tentatives, pas une mesure de trafic.
                    self.calls += 1
                data = response.json()
                if data.get("error"):
                    logger.error(f"erreur openrouter: {data['error']}")
                    break
                choices = [c["message"]["content"] for c in data.get("choices", [])]
                if not choices:
                    break
                collected.extend(choices)
            return collected[:n]

        def generate(self, input: str, target_prefix: str = "") -> list[tuple[str, float]] | str:
            prompt = pre_process_input(self.model_name, input + target_prefix)
            outs = self._post(prompt, n=4, max_tokens=256)
            result = [post_process_output(self.model_name, o) for o in outs]
            for r in result:
                if (input, r) not in self.used_tactics:
                    self.used_tactics.add((input, r))
                    logger.info(f"tactic: {r}")
                    return r
            return "sorry"

        def generate_whole_proof(self, theorem: str) -> str:
            prompt = (
                "Here is a theorem you need to prove in Lean:```lean\n"
                + theorem
                + "```\nNow you should provide the complete proof of the theorem in lean code. "
                "Only output the proof, no explanation, no comments, no theorem, nothing else:"
            )
            outs = self._post(prompt, n=1, max_tokens=1024)
            if not outs:
                return "sorry"
            # Jamais post_process_output ici : sa branche claude tronque a
            # UNE ligne (mesure 2026-10-20) -- _extract_whole_proof garde la
            # preuve complete (semantique de la branche deepseek upstream).
            return _extract_whole_proof(outs[0])

    # Le joint deadline (mesure adjoint 2026-10-13 sur 4920b146840) : la
    # factory recevait ``deadline`` mais instanciait le generateur sans le
    # transmettre -- self.deadline restait None, timeout None, budget_hit
    # inatteignable depuis le vrai generateur.
    return OpenRouterTacticGenerator(deadline=deadline)


@dataclass
class BenchResult:
    """Resultat d'un mode du banc -- la structure du rapport #1453."""

    rung: str
    mode: str
    model: str
    budget_s: float
    success: bool
    llm_calls: int = 0
    tactic_steps: int = 0
    elapsed_s: float = 0.0
    termination: str = ""
    tactics_tried: list[str] = field(default_factory=list)
    proof_mode_output: str = ""


async def _start_server(project: str, timeout_s: int):
    """Demarre le repl Pantograph sur le mini-lake avec LEAN_PATH resolu.

    Cf ``lake_lean_path`` : sans lean_path explicite, le repl ne voit pas les
    oleans du lake (mesure du 2026-10-12).
    """
    from pantograph.server import Server

    server = Server(
        imports=["Conway.LookAndSayLemmas"],
        project_path=project,
        lean_path=lake_lean_path(project),
        timeout=timeout_s,
        _sync_init=False,
    )
    await server.restart_async()
    return server


async def bench_step_by_step(
    project: str, budget_s: float, max_calls: int, timeout_s: int
) -> BenchResult:
    """Mode pas-a-pas : boucle generate -> goal_tac, chaque pas verifie par Lean."""
    result = BenchResult(
        rung=RUNG_NAME,
        mode="step_by_step",
        model=HOUSE_MODEL,
        budget_s=budget_s,
        success=False,
    )
    t0 = time.monotonic()
    gen = _make_openrouter_generator(deadline=t0 + budget_s)

    server = await _start_server(project, timeout_s)

    state = await server.goal_start_async(RUNG_STATEMENT)
    # Pas mecanique deterministe (pas un appel LLM) : le forall ne met pas
    # `n` dans le contexte local -- `intro n` avant la boucle generate.
    state = await server.goal_tactic_async(state, "intro n")
    result.tactics_tried.append(f"<initial: {str(state)[:80]}>")

    while True:
        elapsed = time.monotonic() - t0
        if elapsed > budget_s:
            result.termination = "budget_s_timeout"
            break
        if gen.calls >= max_calls:
            result.termination = "max_llm_calls"
            break

        tactic = gen.generate(str(state))
        result.llm_calls = gen.calls
        if gen.budget_hit:
            # Distinction chargee : une coupure de budget ne se deguise pas
            # en generator_exhausted (le rapport maison distingue deja les
            # deux terminaisons).
            result.termination = "budget_s_timeout"
            break
        if tactic in ("sorry", ""):
            result.termination = "generator_exhausted"
            break

        result.tactics_tried.append(str(tactic))
        try:
            state = await server.goal_tactic_async(state, tactic)
        except Exception as exc:  # TacticFailure, ServerError, ParseError
            result.tactics_tried.append(f"<fail: {type(exc).__name__}: {str(exc)[:60]}>")
            continue

        result.tactic_steps += 1
        if getattr(state, "done", False):
            result.success = True
            result.termination = "goal_done"
            break

    result.elapsed_s = round(time.monotonic() - t0, 1)
    return result


async def bench_whole_proof(
    project: str, budget_s: float, timeout_s: int
) -> BenchResult:
    """Mode preuve entiere : generation complete puis check_compile."""
    result = BenchResult(
        rung=RUNG_NAME,
        mode="whole_proof",
        model=HOUSE_MODEL,
        budget_s=budget_s,
        success=False,
    )
    t0 = time.monotonic()
    gen = _make_openrouter_generator(deadline=t0 + budget_s)

    server = await _start_server(project, timeout_s)

    theorem = (
        "theorem digitsToNat_natToDigits_bench (n : Nat) : "
        "Conway.digitsToNat (Conway.natToDigits n) = n := by\n"
    )
    proof = gen.generate_whole_proof(theorem)
    result.llm_calls = gen.calls
    result.proof_mode_output = str(proof)[:2000]
    # Deadline de bout en bout : une preuve nee hors budget est un echec de
    # budget, pas une reussite retardee (mesure adjoint 2026-10-13,
    # c.6143211874 : budget_s=0.001 rendait success=True en 0.1 s). Le
    # check_compile ne part pas -- il n'y a rien a verifier.
    if gen.budget_hit or (time.monotonic() - t0) > budget_s:
        result.elapsed_s = round(time.monotonic() - t0, 1)
        result.termination = "budget_s_timeout"
        return result
    code = theorem + proof if proof != "sorry" else theorem + "  sorry"

    units = await server.check_compile_async(code)
    errors = [
        m for u in units for m in u.messages if m.severity.name == "ERROR"
    ]
    has_sorry = any(
        "sorry" in m.data for u in units for m in u.messages
    )
    result.success = not errors and not has_sorry
    result.termination = "compiled_clean" if result.success else "compile_error"
    result.elapsed_s = round(time.monotonic() - t0, 1)
    return result


async def main_async(args: argparse.Namespace) -> int:
    results: list[BenchResult] = []
    if args.mode in ("step", "both"):
        results.append(
            await bench_step_by_step(
                args.project, args.budget_s, args.max_calls, args.timeout
            )
        )
    if args.mode in ("proof", "both"):
        results.append(await bench_whole_proof(args.project, args.budget_s, args.timeout))

    out_dir = Path(args.out or ".")
    out_dir.mkdir(parents=True, exist_ok=True)
    out_path = out_dir / f"bench_v2_{RUNG_NAME.lower()}_{args.mode}.json"
    payload = {
        "rung": RUNG_NAME,
        "statement": RUNG_STATEMENT,
        "model": HOUSE_MODEL,
        "house_reference": {
            "verdict": "FAILED (passe 17, 2026-09-27)",
            "elapsed_s": 1925.1,
            "termination": "reasoning_budget_timeout_1800s",
        },
        "protocol_gap": (
            "Pantograph 0.3.15 exige toolchain projet == v4.29.1 (fichier "
            "pantograph/lean-toolchain du wheel ; conway_lean porte v4.33.0) : "
            "mini-lake snapshot, code byte-identique, Mathlib v4.29.1, sorry "
            "reintroduit au rung."
        ),
        "results": [asdict(r) for r in results],
    }
    out_path.write_text(json.dumps(payload, indent=2, ensure_ascii=False), encoding="utf-8")

    for r in results:
        print(
            f"[{r.mode}] success={r.success} llm_calls={r.llm_calls} "
            f"steps={r.tactic_steps} elapsed={r.elapsed_s}s end={r.termination}"
        )
    print(f"trace: {out_path}")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument(
        "--project",
        required=True,
        help="chemin du mini-lake snapshot (toolchain v4.29.1, sorry au rung)",
    )
    parser.add_argument("--mode", choices=["step", "proof", "both"], default="both")
    parser.add_argument(
        "--budget-s", type=float, default=HOUSE_REASONING_BUDGET_S,
        help="plafond raisonnement (defaut: 1800 s, aligne passe 17 maison)",
    )
    parser.add_argument(
        "--max-calls", type=int, default=200,
        help="plafond d'appels LLM du mode pas-a-pas",
    )
    parser.add_argument("--timeout", type=int, default=120, help="timeout Pantograph par appel")
    parser.add_argument("--out", default=None, help="repertoire de sortie de la trace JSON")
    args = parser.parse_args()
    return asyncio.run(main_async(args))


if __name__ == "__main__":
    raise SystemExit(main())
