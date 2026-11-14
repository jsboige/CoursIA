"""Sonde d'API courante (issue #14499, tranche Q17) -- ce que chaque moteur
expose REELLEMENT, sans appel LLM.

Objet
-----
Les pilotes `sk_distillation_pilot.py`, `maf_distillation_pilot.py` et
`adk_distillation_pilot.py` sont epingles sur des versions de septembre-octobre.
La question posee sur #14499 est : **a quoi ressemble l'API au versions
courantes** (SK Python 1.46.0, MAF 1.24.0 + orchestrations 1.4.1, ADK 2.13.0) ?

Methode -- et pourquoi elle est de ce niveau
---------------------------------------------
Un `import` ne prouve pas qu'une API est *utilisable* ; il prouve qu'elle
existe. Inversement, la documentation ne prouve rien sur le code livre.
La sonde interroge donc **les paquets reellement installes** :

1. un **controle negatif** par capacite (ce qui doit etre ABSENT) et un
   **controle positif** (ce qui doit etre PRESENT) -- un detecteur se valide
   par ses faux negatifs, pas par ses hits ;
2. une **recherche de symboles** dans l'ensemble des sous-modules publics
   (`pkgutil.walk_packages`), pour repondre par la PRESENCE d'un symbole
   nomme, la ou un import cible echouerait sur un renommage de chemin ;
3. la **capture des `DeprecationWarning`** emises a l'import : c'est la seule
   source qui atteste d'une deprecation *dans ce code-la*, a cette version ;
4. une **construction reelle** des objets (client a endpoint local, session,
   service) -- sans emission de requete : la preuve porte sur la forme de
   l'appel, pas sur le resultat d'un modele.

Aucun appel reseau, aucune cle API requise : la sonde est rejouable sur un
poste sans secret (contrainte du depot : les secrets vivent dans
`.secrets/master.env`, jamais dans un litteral).

Sortie
------
Texte sur stdout, une ligne par capacite, avec le verdict
`PRESENT` / `ABSENT` / `ABSENT (attendu)`. Le verdict est calcule, jamais
ecrit a la main : `PRESENCE` = au moins un symbole public trouve ;
`ABSENT` = aucun.

Usage
-----
    python current_api_probe.py --engine sk
    python current_api_probe.py --engine maf
    python current_api_probe.py --engine adk

Chaque moteur a son propre environnement (les versions sont incompatibles
entre elles) : voir `eval-pilots/README.md`.
"""

from __future__ import annotations

import argparse
import importlib
import io
import os
import pkgutil
import sys
import warnings
from contextlib import redirect_stdout
from datetime import date

# La sonde ne doit pas dependre de l'encodage de la console Windows (cp1252)
# : on force l'UTF-8 sur stdout, sinon un accent casse l'execution.
if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")


def walk_public_symbols(root_name: str) -> dict[str, str]:
    """Retourne {symbole: module} pour les symboles PUBLICS du paquet.

    Le parcours est tolerant : un sous-module qui casse a l'import (dependance
    optionnelle absente) est note et ignore, jamais fatal -- sinon la sonde
    rendrait "0 symbole" sur un paquet mal installe, indiscernable d'un
    paquet qui n'expose rien.
    """
    found: dict[str, str] = {}
    broken: list[str] = []
    try:
        root = importlib.import_module(root_name)
    except Exception as exc:  # pragma: no cover - depend de l'environnement
        print(f"ERREUR import racine {root_name}: {exc}")
        return found
    # walk_packages + importlib.import_module, faits a la main pour capturer
    # les echecs d'import des sous-modules optionnels.
    modules = [root]
    for info in pkgutil.walk_packages(root.__path__, prefix=root_name + "."):
        try:
            modules.append(importlib.import_module(info.name))
        except Exception as exc:
            broken.append(f"{info.name}: {type(exc).__name__}")
    for mod in modules:
        for name in dir(mod):
            if name.startswith("_"):
                continue
            # `getattr` peut DECLENCHER un import paresseux (SK 1.46 expose
            # `semantic_kernel.agents.autogen` via `__getattr__`, qui reclame la
            # dependance optionnelle `autogen`). Une dependance optionnelle
            # absente ne doit pas faire tomber la sonde : le symbole est
            # alors note ABSENT, pas fatal.
            try:
                obj = getattr(mod, name, None)
            except Exception:
                continue
            if getattr(obj, "__module__", None) is None and not isinstance(obj, type):
                continue
            found.setdefault(name, mod.__name__)
    return found


def find(symbols: dict[str, str], *needles: str) -> list[str]:
    """Symboles dont le nom contient l'un des fragments (casse insensible)."""
    low = [(s, m) for s, m in symbols.items()]
    out = []
    for s, m in low:
        sl = s.lower()
        for n in needles:
            nl = n.lower()
            if nl in sl:
                out.append(f"{s} ({m})")
                break
    return sorted(set(out))


def importable(path: str) -> tuple[bool, str]:
    """Importe un symbole par chemin pointé. Retourne (ok, detail)."""
    try:
        module_path, _, attr = path.rpartition(".")
        mod = importlib.import_module(module_path)
        if not hasattr(mod, attr):
            return False, "module importe, attribut absent"
        return True, "ok"
    except Exception as exc:
        return False, f"{type(exc).__name__}: {exc}"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--engine", required=True, choices=["sk", "maf", "adk"])
    args = ap.parse_args()

    engine = args.engine
    root = {"sk": "semantic_kernel", "maf": "agent_framework", "adk": "google.adk"}[engine]

    # En-tete produit par la SONDE elle-meme. La trace commitee doit etre le
    # stdout BRUT : un en-tete ajoute a la main (echo, editeur) ferait de la
    # trace un fichier retouche apres coup, ce que la regle du `README.md`
    # interdit ("une trace retouchée n'est plus une trace"). La date est donc
    # calculee au RUNTIME -- une re-execution ne peut pas mentir sur sa
    # datation -- et aucun chemin local n'y figure (un chemin machine dans une
    # trace commitee est interdit).
    print(f"# Sonde d'API courante -- moteur {engine}")
    print(f"# generee le {date.today().isoformat()} par current_api_probe.py --engine {engine}")
    print("# aucune requete LLM, aucune cle API ; environnement de mesure dedie")

    # --- 1. version installee -------------------------------------------------
    version = "?"
    for dist in {
        "sk": ["semantic-kernel"],
        "maf": ["agent-framework-core", "agent-framework-orchestrations", "agent-framework-openai"],
        "adk": ["google-adk", "google-genai"],
    }[engine]:
        try:
            from importlib.metadata import version as _v

            print(f"VERSION {dist}={_v(dist)}")
        except Exception as exc:
            print(f"VERSION {dist}=ABSENT ({type(exc).__name__})")

    # --- 2. DeprecationWarning emises a l'import -----------------------------
    # On capture l'import RACINE dans un contexte de warnings : c'est la seule
    # source qui atteste qu'une API est deprecnee DANS CE CODE-LA.
    with warnings.catch_warnings(record=True) as caught:
        warnings.simplefilter("always")
        try:
            with redirect_stdout(io.StringIO()):
                importlib.import_module(root)
        except Exception as exc:
            print(f"ERREUR import {root}: {exc}")
            return 2
        deprecations = [str(w.message) for w in caught if issubclass(w.category, DeprecationWarning)]
    print(f"DEPRECATIONS_A_L_IMPORT {len(deprecations)}")
    for d in sorted(set(deprecations)):
        print(f"  DEPRECATION {d[:200]}")

    # --- 3. symboles publics -------------------------------------------------
    symbols = walk_public_symbols(root)
    print(f"SYMBOLES_PUBLICS {len(symbols)}")

    # --- 3bis. CONTROLE NEGATIF INTER-MOTEURS ------------------------------
    # Les trois moteurs sont dans des environnements SEPARES (versions
    # incompatibles). Ce controle prouve que l'environnement mesure n'est pas
    # contamine : si le moteur d'a cote etait importable, un « ABSENT » de la
    # sonde pourrait venir d'une confusion de paquet plutot que d'une absence
    # reelle de l'API. C'est le controle qui rend les verdicts ABSENT
    # interpretables.
    others = {
        "sk": ["agent_framework", "google.adk"],
        "maf": ["semantic_kernel", "google.adk"],
        "adk": ["semantic_kernel", "agent_framework"],
    }[engine]
    print("CONTROLE NEGATIF INTER-MOTEURS (doivent etre NON importables)")
    env_clean = True
    for other in others:
        try:
            importlib.import_module(other)
            print(f"  NEGATIF PRESENT !! (env contamine)  {other}")
            env_clean = False
        except Exception:
            print(f"  NEGATIF absent OK  {other}")

    # --- 4. controles par capacite ------------------------------------------
    # Chaque capacite porte un CONTROLE POSITIF (ce qui doit etre la) et un
    # CONTROLE NEGATIF (ce qui doit etre absent). L'absence de controle negatif
    # rendrait « 0 hit » indiscernable d'une sonde cassee.
    caps = {
        "sk": {
            "topologies_orchestration": {
                # Chemins REELS des sous-modules. Interroger le chemin
                # *package* (`semantic_kernel.agents.orchestration.X`) rend
                # un faux « absent » : le `__init__` du paquet ne re-exporte
                # PAS les classes (il ne re-exporte que ce que le pilote
                # importe depuis `semantic_kernel.agents`). Le faux negatif a
                # ete observe puis corrige -- d'ou la forme « sous-module »
                # ci-dessous, et le controle de convention dans CAPACITE
                # `agents`.
                "positif": [
                    "semantic_kernel.agents.orchestration.sequential.SequentialOrchestration",
                    "semantic_kernel.agents.orchestration.concurrent.ConcurrentOrchestration",
                    "semantic_kernel.agents.orchestration.group_chat.GroupChatOrchestration",
                    "semantic_kernel.agents.orchestration.magentic.MagenticOrchestration",
                    "semantic_kernel.agents.orchestration.handoffs.HandoffOrchestration",
                ],
                "negatif": [],
                "noms": ["Orchestration"],
            },
            "agents": {
                "positif": [
                    "semantic_kernel.agents.ChatCompletionAgent",
                    "semantic_kernel.agents.runtime.InProcessRuntime",
                    # re-export depuis le PAQUET `agents` (le pilote importe
                    # `GroupChatOrchestration` par ce chemin-la) ;
                    "semantic_kernel.agents.GroupChatOrchestration",
                ],
                # CONTROLE NEGATIF DE CONVENTION : le paquet
                # `semantic_kernel.agents.orchestration` ne re-exporte PAS ses
                # classes. Un « absent » a cet endroit est une CONVENTION
                # d'import, pas une suppression -- le signaler empeche de
                # lire une absence de re-export comme une API retiree.
                "negatif": [
                    "semantic_kernel.agents.orchestration.SequentialOrchestration",
                ],
                "noms": ["AgentGroupChat", "AgentGroupChatSettings", "ProcessBuilder", "ChatCompletionAgent"],
            },
            "checkpoint_reprise": {"positif": [], "negatif": [], "noms": ["checkpoint", "resume", "restore", "snapshot"]},
            "observabilite": {"positif": [], "negatif": [], "noms": ["opentelemetry", "observability", "tracer"]},
            "comptage_tokens": {"positif": [], "negatif": [], "noms": ["tokencount", "counttokens", "tokenusage", "usagedetails", "completionusage"]},
            "endpoint_local": {
                "positif": [],
                "negatif": [],
                "noms": ["OpenAIChatCompletion", "AsyncOpenAI"],
            },
        },
        "maf": {
            "topologies_orchestration": {
                "positif": [
                    "agent_framework.orchestrations.SequentialBuilder",
                    "agent_framework.orchestrations.ConcurrentBuilder",
                    "agent_framework.orchestrations.GroupChatBuilder",
                    "agent_framework.orchestrations.MagenticBuilder",
                    "agent_framework.orchestrations.HandoffBuilder",
                ],
                "negatif": [],
                "noms": [],
            },
            "graphe_workflow": {
                "positif": ["agent_framework.WorkflowBuilder", "agent_framework.Agent"],
                "negatif": [],
                "noms": ["WorkflowBuilder", "Executor", "WorkflowContext"],
            },
            "checkpoint_reprise": {
                "positif": [],
                "negatif": [],
                "noms": ["checkpoint", "resume", "recovery"],
            },
            "observabilite": {"positif": [], "negatif": [], "noms": ["opentelemetry", "telemetry", "tracer"]},
            "comptage_tokens": {"positif": [], "negatif": [], "noms": ["tokenusage", "usagedetails", "usagecontent", "addusagedetails"]},
            "endpoint_local": {
                "positif": [],
                "negatif": [],
                "noms": ["OpenAIChatCompletionClient", "OpenAIClient"],
            },
            "magentic_ledger": {"positif": [], "negatif": [], "noms": ["MagenticProgressLedger", "ProgressLedger"]},
        },
        "adk": {
            "runner_session": {
                "positif": [
                    "google.adk.runners.Runner",
                    "google.adk.sessions.InMemorySessionService",
                ],
                "negatif": [],
                "noms": ["DatabaseSessionService", "VertexAiSessionService", "BaseSessionService"],
            },
            "agents_outils": {
                "positif": [],
                "negatif": [],
                "noms": ["LlmAgent", "AgentTool", "FunctionTool", "SequentialAgent", "LoopAgent", "ParallelAgent"],
            },
            "reprise_app": {"positif": [], "negatif": [], "noms": ["Resumability", "App", "resumable"]},
            "observabilite": {"positif": [], "negatif": [], "noms": ["opentelemetry", "trace", "callback"]},
            "comptage_tokens": {
                "positif": [],
                "negatif": [],
                "noms": ["usage_metadata", "UsageMetadata", "UsageContent"],
            },
            "endpoint_local": {"positif": [], "negatif": [], "noms": ["LiteLlm", "lite_llm", "OpenAI"]},
        },
    }[engine]

    for cap, spec in caps.items():
        print(f"CAPACITE {cap}")
        for path in spec["positif"]:
            ok, detail = importable(path)
            print(f"  POSITIF {'PRESENT OK' if ok else 'ABSENT !!'}  {path}  ({detail})")
        for path in spec["negatif"]:
            ok, _ = importable(path)
            print(f"  NEGATIF {'PRESENT !! (hypothese fausse)' if ok else 'absent OK'}  {path}")
        hits = find(symbols, *spec["noms"]) if spec["noms"] else []
        if spec["noms"]:
            if hits:
                for h in hits[:12]:
                    print(f"  SYMBOLE {h}")
                if len(hits) > 12:
                    print(f"  SYMBOLE ... (+{len(hits) - 12} autres)")
            else:
                print(f"  SYMBOLE aucun pour {spec['noms']} -- ABSENT")

    # --- 5. construction reelle, sans requete --------------------------------
    # La forme de l'appel est la preuve : on CONSTRUIT l'objet, on n'envoie
    # rien. Une exception ici = la construction a change au version courante.
    # --- 4bis. CONTROLE DE CHAMP : le comptage de tokens est un CHAMP, pas un
    # symbole. Une recherche par nom de symbole ne peut donc pas le voir -- et
    # « aucun symbole trouve » se lirait alors comme « API absente » alors que
    # la surface existe, sur un autre forme. On interroge la STRUCTURE des
    # classes porteuses.
    field_probes = {
        # SK : le compte n'est PAS un champ du message -- il atterrit dans
        # `ChatMessageContent.metadata["usage"]`, sous la forme d'un modele
        # `CompletionUsage`. On interroge donc le MODELE, et le message, pour
        # distinguer « API absente » de « API presente mais hors du message ».
        "sk": [
            ("semantic_kernel.connectors.ai.completion_usage.CompletionUsage", ("prompt_tokens", "completion_tokens")),
            ("semantic_kernel.contents.chat_message_content.ChatMessageContent", ("usage", "token")),
        ],
        # MAF : le compte est un CONTENU de message (`Content` de type
        # "usage"), construit par `Content.from_usage(...)` et agrege par
        # `add_usage_details(...)`. Le type public est `UsageDetails`.
        "maf": [
            ("agent_framework.UsageDetails", ("token_count",)),
            ("agent_framework.Content", ("usage", "token")),
        ],
        # ADK : le compte est un CHAMP de l'evenement (`Event.usage_metadata`),
        # type `GenerateContentResponseUsageMetadata`, avec le detail cache /
        # raisonnement / tools.
        "adk": [
            ("google.adk.events.Event", ("usage", "token")),
            ("google.genai.types.GenerateContentResponseUsageMetadata", ("token", "prompt", "candidates")),
        ],
    }[engine]
    print("CAPACITE comptage_tokens (CHAMPS de classe, pas symboles)")
    for path, needles in field_probes:
        ok, detail = importable(path)
        if not ok:
            print(f"  CHAMPS ABSENT !!  {path}  ({detail})")
            continue
        module_path, _, attr = path.rpartition(".")
        cls = getattr(importlib.import_module(module_path), attr)
        # Les classes du SDK sont tantôt des modeles pydantic
        # (`model_fields`), tantôt des dataclasses (`dataclasses.fields`), tantôt
        # des classes Python ordinaires (`__annotations__`). Les trois formes
        # sont interrogees : ne lire qu'une seule rendrait « absent » sur les
        # deux autres.
        fields = list(getattr(cls, "model_fields", {}) or {})
        if not fields:
            try:
                import dataclasses

                fields = [f.name for f in dataclasses.fields(cls)]
            except Exception:
                fields = []
        if not fields:
            fields = list(getattr(cls, "__annotations__", {}) or {})
        if not fields:
            fields = [a for a in dir(cls) if not a.startswith("_")]
        hits = [f for f in fields if any(n in f.lower() for n in needles)]
        print(f"  CHAMPS {'PRESENT OK' if hits else 'ABSENT'}  {path}")
        for h in hits:
            print(f"      champ {h}")

    print("CONSTRUCTION (sans requete)")
    if engine == "sk":
        # La forme reelle du branchement local est passee par le CLIENT
        # (`AsyncOpenAI(base_url=...)`), pas par un `base_url` du service : la
        # signature du service a change, et c'est exactement le genre de
        # derive que le pilote doit signaler. Les parametres acceptes sont
        # affiches pour que la lecture ne repose pas sur une convention.
        import inspect

        from semantic_kernel.connectors.ai.open_ai import OpenAIChatCompletion

        params = [p for p in inspect.signature(OpenAIChatCompletion.__init__).parameters]
        print(f"  SIGNATURE OpenAIChatCompletion.__init__ params={params}")
        print(f"  ACCEPTE base_url={'base_url' in params}")
        try:
            from openai import AsyncOpenAI

            client = AsyncOpenAI(
                api_key=os.environ.get("OPENAI_API_KEY") or "unset",
                base_url="http://127.0.0.1:8000/v1",
                max_retries=1,
            )
            svc = OpenAIChatCompletion(ai_model_id="gpt-4o-mini", async_client=client)
            print(f"  CONSTRUCTION OK OpenAIChatCompletion(async_client=AsyncOpenAI(base_url=...)) service_id={svc.service_id}")
        except Exception as exc:
            print(f"  CONSTRUCTION ECHEC : {type(exc).__name__}: {exc}")
    elif engine == "maf":
        import inspect

        from agent_framework_openai import OpenAIChatCompletionClient

        params = [p for p in inspect.signature(OpenAIChatCompletionClient.__init__).parameters]
        print(f"  SIGNATURE OpenAIChatCompletionClient.__init__ params={params}")
        print(f"  ACCEPTE base_url={'base_url' in params}")
        try:
            cli = OpenAIChatCompletionClient(
                model="gpt-4o-mini",
                api_key=os.environ.get("OPENAI_API_KEY") or "unset",
                base_url="http://127.0.0.1:8000/v1",
            )
            print("  CONSTRUCTION OK OpenAIChatCompletionClient(base_url=...)")
        except Exception as exc:
            print(f"  CONSTRUCTION ECHEC : {type(exc).__name__}: {exc}")
    else:
        try:
            from google.adk.sessions import InMemorySessionService

            svc = InMemorySessionService()
            print("  CONSTRUCTION OK InMemorySessionService()")
        except Exception as exc:
            print(f"  CONSTRUCTION ECHEC InMemorySessionService() : {type(exc).__name__}: {exc}")

    print(f"SONDE FIN {engine}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
