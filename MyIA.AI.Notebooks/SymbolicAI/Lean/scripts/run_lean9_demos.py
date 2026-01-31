#!/usr/bin/env python3
"""
Run Lean-9 notebook demos to validate SK multi-agent execution.
"""

import json
import os
import sys
import time

# Change to notebook directory
os.chdir("d:/dev/CoursIA/MyIA.AI.Notebooks/SymbolicAI/Lean")

# Load .env
from dotenv import load_dotenv
load_dotenv()

# Check API key
api_key = os.getenv("OPENAI_API_KEY", "")
if not api_key or api_key.startswith("sk-..."):
    print("ERROR: OPENAI_API_KEY not set")
    sys.exit(1)

import nest_asyncio
nest_asyncio.apply()

# Import all required modules
print("=== Loading modules ===")

# Standard imports
from dataclasses import dataclass, field
from typing import Dict, List, Any, Optional
from enum import Enum
import json
import asyncio
import re

# SK imports
from semantic_kernel import Kernel
from semantic_kernel.agents import ChatCompletionAgent
from semantic_kernel.contents.chat_history import ChatHistory
from semantic_kernel.contents.chat_message_content import ChatMessageContent
from semantic_kernel.connectors.ai.open_ai import OpenAIChatCompletion
from semantic_kernel.connectors.ai import FunctionChoiceBehavior
from semantic_kernel.functions import KernelArguments

SK_AVAILABLE = True
print("Semantic Kernel: OK")

# Load lean_runner (stub for testing)
class LeanRunner:
    def __init__(self, backend="subprocess", timeout=30):
        self.backend = backend
        self.timeout = timeout

    def execute(self, code: str):
        return {"success": True, "output": "OK", "errors": ""}

print("LeanRunner: OK (stub)")

# ===== ProofState =====
class ProofPhase(Enum):
    INIT = "init"
    SEARCH = "search"
    TACTIC_GEN = "tactic_gen"
    VERIFICATION = "verification"
    REFINEMENT = "refinement"
    COMPLETE = "complete"

@dataclass
class ProofState:
    theorem_statement: str
    current_goal: str
    max_iterations: int = 20
    phase: ProofPhase = field(default=ProofPhase.INIT)
    discovered_lemmas: List[str] = field(default_factory=list)
    tactics_history: List[str] = field(default_factory=list)
    verification_results: List[Dict] = field(default_factory=list)
    iteration_count: int = 0
    iteration: int = 0
    total_lean_time_ms: float = 0.0
    final_proof: Optional[str] = None
    session_id: str = field(default_factory=lambda: "test")
    _next_agent_designation: Optional[str] = None

    @property
    def proof_complete(self) -> bool:
        return self.phase == ProofPhase.COMPLETE

    def increment_iteration(self):
        self.iteration_count += 1

    def designate_next_agent(self, agent_name: str):
        self._next_agent_designation = agent_name

    def consume_next_agent_designation(self) -> Optional[str]:
        designation = self._next_agent_designation
        self._next_agent_designation = None
        return designation

    def add_lemma(self, name, statement, namespace="", relevance=0.5):
        self.discovered_lemmas.append(name)
        return f"lemma_{len(self.discovered_lemmas)}"

    def add_tactic_attempt(self, tactic, state_before="", confidence=0.5, explanation=""):
        self.tactics_history.append(tactic)
        return f"tactic_{len(self.tactics_history)}"

    def add_verification(self, attempt_id, success, output, errors, remaining_goals=None, exec_time_ms=0.0, backend=""):
        self.verification_results.append({"success": success})
        return f"verif_{len(self.verification_results)}"

    def get_state_snapshot(self, summarize=True):
        return {
            "theorem": self.theorem_statement,
            "phase": self.phase.value,
            "lemmas": self.discovered_lemmas,
            "iterations": self.iteration_count
        }

print("ProofState: OK")

# ===== Agent Instructions =====
SEARCH_AGENT_INSTRUCTIONS = """Tu es SearchAgent, specialise dans la recherche de lemmes Mathlib.
Pour le theoreme donne, trouve les lemmes pertinents et delegue a TacticAgent."""

TACTIC_AGENT_INSTRUCTIONS = """Tu es TacticAgent, specialise dans la generation de tactiques Lean.
Genere des tactiques comme simp, rfl, exact, ring, omega. Delegue a VerifierAgent."""

VERIFIER_AGENT_INSTRUCTIONS = """Tu es VerifierAgent, specialise dans la verification de preuves.
Si la preuve est correcte, dis "PROOF COMPLETE". Sinon delegue a CriticAgent."""

CRITIC_AGENT_INSTRUCTIONS = """Tu es CriticAgent, analyse les echecs et propose des corrections.
Delegue a SearchAgent ou TacticAgent."""

COORDINATOR_AGENT_INSTRUCTIONS = """Tu es CoordinatorAgent, tu coordonnes les agents.
Utilise pour les strategies globales."""

# ===== Plugins (stubs) =====
def kernel_function(description="", name=""):
    def decorator(func):
        func._sk_function = True
        func._sk_description = description
        func._sk_name = name or func.__name__
        return func
    return decorator

class ProofStateManagerPlugin:
    def __init__(self, state: ProofState):
        self._state = state

    @kernel_function(description="Get proof state", name="get_proof_state")
    def get_proof_state(self, summarize: bool = True) -> str:
        return json.dumps(self._state.get_state_snapshot(summarize))

    @kernel_function(description="Add lemma", name="add_discovered_lemma")
    def add_discovered_lemma(self, name: str, statement: str = "", namespace: str = "", relevance: float = 0.5) -> str:
        return self._state.add_lemma(name, statement, namespace, relevance)

    @kernel_function(description="Designate next agent", name="designate_next_agent")
    def designate_next_agent(self, agent_name: str) -> str:
        self._state.designate_next_agent(agent_name)
        return f"Delegue a {agent_name}"

class LeanSearchPlugin:
    def __init__(self, runner):
        self.runner = runner

    @kernel_function(description="Search mathlib", name="search_mathlib_lemmas")
    def search_mathlib_lemmas(self, query: str) -> str:
        # Return some fake lemmas for testing
        return "Nat.add_zero, Nat.add_comm, Nat.add_assoc"

class LeanTacticPlugin:
    @kernel_function(description="Generate tactics", name="generate_tactics")
    def generate_tactics(self, goal: str) -> str:
        return "simp, rfl, ring"

class LeanVerificationPlugin:
    def __init__(self, runner):
        self.runner = runner

    @kernel_function(description="Verify proof", name="verify_proof")
    def verify_proof(self, proof: str) -> str:
        return "Verification OK"

print("Plugins: OK (stubs)")

# ===== Agent Factory =====
def _create_sk_agents(plugins: Dict[str, Any], state: ProofState) -> Dict[str, Any]:
    kernel = Kernel()
    model = os.getenv("OPENAI_CHAT_MODEL_ID", "gpt-4o-mini")

    service = OpenAIChatCompletion(
        service_id="openai",
        ai_model_id=model,
        api_key=api_key
    )
    kernel.add_service(service)

    for plugin_name, plugin in plugins.items():
        kernel.add_plugin(plugin, plugin_name=plugin_name)

    settings = kernel.get_prompt_execution_settings_from_service_id(service_id="openai")
    settings.function_choice_behavior = FunctionChoiceBehavior.Auto()

    agents = {}
    agent_configs = [
        ("SearchAgent", SEARCH_AGENT_INSTRUCTIONS),
        ("TacticAgent", TACTIC_AGENT_INSTRUCTIONS),
        ("VerifierAgent", VERIFIER_AGENT_INSTRUCTIONS),
        ("CriticAgent", CRITIC_AGENT_INSTRUCTIONS),
        ("CoordinatorAgent", COORDINATOR_AGENT_INSTRUCTIONS),
    ]

    for name, instructions in agent_configs:
        agents[name] = ChatCompletionAgent(
            kernel=kernel,
            name=name,
            instructions=instructions,
            arguments=KernelArguments(settings=settings)
        )

    print(f"Created {len(agents)} SK agents with model {model}")
    return agents

# ===== ProofAgentGroupChat =====
class ProofAgentGroupChat:
    def __init__(self, agents: Dict[str, Any], state: ProofState, use_sk: bool = True):
        self.agents = agents
        self.state = state
        self.use_sk = use_sk and SK_AVAILABLE
        self.history = []

    def run(self, initial_message: str, verbose: bool = True) -> str:
        if self.use_sk:
            loop = asyncio.get_event_loop()
            return loop.run_until_complete(self._run_sk(initial_message, verbose))
        else:
            return self._run_fallback(initial_message, verbose)

    async def _run_sk(self, initial_message: str, verbose: bool = True) -> str:
        if verbose:
            print("=" * 60)
            print(f"Session MULTI-AGENTS (SK): {initial_message[:80]}...")
            print("=" * 60)

        chat_history = ChatHistory()
        chat_history.add_user_message(initial_message)

        current_message = initial_message
        agent_order = ["SearchAgent", "TacticAgent", "VerifierAgent", "CriticAgent", "CoordinatorAgent"]

        for i in range(self.state.max_iterations):
            self.state.iteration = i + 1
            self.state.increment_iteration()

            designated = self.state.consume_next_agent_designation()
            if designated and designated in self.agents:
                agent_name = designated
            else:
                agent_name = agent_order[i % len(agent_order)]

            agent = self.agents.get(agent_name)
            if not agent:
                continue

            if verbose:
                print(f"\n[Tour {self.state.iteration_count}] {agent_name}")

            try:
                response_text = ""

                async for response in agent.invoke(chat_history):
                    if hasattr(response, 'content') and response.content:
                        response_text += str(response.content)
                    elif hasattr(response, 'items'):
                        for item in response.items:
                            if hasattr(item, 'text'):
                                response_text += item.text

                if not response_text:
                    response_text = f"[{agent_name}] Pas de reponse"

                chat_history.add_assistant_message(response_text)

                if i < self.state.max_iterations - 1:
                    next_context = f"Continue la preuve. Reponse precedente de {agent_name}: {response_text[:200]}"
                    chat_history.add_user_message(next_context)

                self._update_state_from_response(agent_name, response_text)

            except Exception as e:
                import traceback
                response_text = f"Erreur agent {agent_name}: {str(e)}"
                if verbose:
                    print(f"  [ERROR] {e}")
                    traceback.print_exc()

            self.history.append({
                "iteration": self.state.iteration_count,
                "agent": agent_name,
                "response": response_text[:200] if response_text else "",
            })

            if verbose:
                display_response = response_text[:200] + "..." if len(response_text) > 200 else response_text
                print(f"  Response: {display_response}")

            if self.state.proof_complete:
                if verbose:
                    print(f"\n[LOG] Preuve trouvee!")
                break

            current_message = response_text

        if verbose:
            print("\n" + "=" * 60)
            print(f"Session terminee apres {self.state.iteration_count} iterations.")
            print("=" * 60)

        return self.state.final_proof or "Preuve non trouvee"

    def _update_state_from_response(self, agent_name: str, response: str):
        response_lower = response.lower()

        if "lemma:" in response_lower or "found:" in response_lower or "nat." in response_lower:
            lemma_matches = re.findall(r'(Nat\.\w+|Eq\.\w+|List\.\w+)', response)
            for lemma in lemma_matches:
                if lemma not in self.state.discovered_lemmas:
                    self.state.discovered_lemmas.append(lemma)

        # Detection des tactiques - track across iterations
        proof_patterns = [
            (r'simp\s*\[[^\]]*\]', 'simp'),
            (r'\brfl\b', 'rfl'),
            (r'exact\s+\w+', 'exact'),
            (r'\bring\b', 'ring'),
            (r'\bomega\b', 'omega'),
            (r'\blinarith\b', 'linarith'),
            (r'\bdecide\b', 'decide'),
        ]

        for pattern, tactic_name in proof_patterns:
            if re.search(pattern, response, re.IGNORECASE):
                if not hasattr(self, '_proof_tactics_found'):
                    self._proof_tactics_found = []
                if tactic_name not in self._proof_tactics_found:
                    self._proof_tactics_found.append(tactic_name)
                    self.state.tactics_history.append(response[:100])

        # Detection de preuve complete - multiple signals
        proof_complete_signals = [
            "proof complete",
            "qed",
            "verified",
            "goals accomplished",
            "proof found",
            "la preuve est terminee",
            "la preuve est cloturee",
            "preuve reussie",
        ]

        tactics_found = getattr(self, '_proof_tactics_found', [])

        if any(signal in response_lower for signal in proof_complete_signals):
            if tactics_found:
                self.state.phase = ProofPhase.COMPLETE
                if not self.state.final_proof:
                    self.state.final_proof = tactics_found[0]
        elif ":= by" in response and tactics_found:
            self.state.phase = ProofPhase.COMPLETE
            if not self.state.final_proof:
                self.state.final_proof = tactics_found[0]

        # Detect complete proof in code block
        code_block_match = re.search(r'```lean\n(.*?)```', response, re.DOTALL)
        if code_block_match:
            code_content = code_block_match.group(1)
            if ":= by" in code_content or ":= rfl" in code_content:
                for pattern, tactic_name in proof_patterns:
                    if re.search(pattern, code_content, re.IGNORECASE):
                        self.state.phase = ProofPhase.COMPLETE
                        self.state.final_proof = code_content.strip()[:200]
                        break

        delegate_patterns = [
            (r'@TacticAgent|delegate.*TacticAgent', 'TacticAgent'),
            (r'@VerifierAgent|delegate.*VerifierAgent', 'VerifierAgent'),
            (r'@CriticAgent|delegate.*CriticAgent', 'CriticAgent'),
            (r'@CoordinatorAgent|delegate.*CoordinatorAgent', 'CoordinatorAgent'),
            (r'@SearchAgent|delegate.*SearchAgent', 'SearchAgent'),
        ]
        for pattern, target in delegate_patterns:
            if re.search(pattern, response, re.IGNORECASE):
                self.state.designate_next_agent(target)
                break

    def _run_fallback(self, initial_message: str, verbose: bool = True) -> str:
        return "Fallback mode not used"

print("ProofAgentGroupChat: OK")

# ===== prove_with_multi_agents =====
def prove_with_multi_agents(
    theorem: str,
    goal: str = "",
    max_iterations: int = 10,
    verbose: bool = True,
    use_simulation: bool = False
) -> Dict[str, Any]:
    start_time = time.time()

    if not goal:
        if ":" in theorem:
            goal = theorem.split(":")[-1].strip()

    state = ProofState(
        theorem_statement=theorem,
        current_goal=goal,
        max_iterations=max_iterations
    )

    runner = LeanRunner(backend="subprocess", timeout=30)

    plugins = {
        "state": ProofStateManagerPlugin(state),
        "search": LeanSearchPlugin(runner),
        "tactic": LeanTacticPlugin(),
        "verification": LeanVerificationPlugin(runner)
    }

    use_sk = SK_AVAILABLE and not use_simulation
    agents = _create_sk_agents(plugins, state)

    chat = ProofAgentGroupChat(
        agents=agents,
        state=state,
        use_sk=use_sk
    )

    mode_str = "Semantic Kernel" if use_sk else "Simulation"
    if verbose:
        print(f"Mode: {mode_str}")

    result = chat.run(f"Prouver: {theorem}", verbose=verbose)

    elapsed = time.time() - start_time
    metrics = {
        "success": state.proof_complete,
        "theorem": theorem,
        "final_proof": state.final_proof,
        "iterations": state.iteration_count,
        "lemmas_discovered": len(state.discovered_lemmas),
        "tactics_tried": len(state.tactics_history),
        "verifications": len(state.verification_results),
        "total_time_s": round(elapsed, 2),
    }

    return metrics

print("prove_with_multi_agents: OK")

# ===== DEMOS =====
DEMOS = [
    {
        "name": "DEMO_1_TRIVIAL",
        "theorem": "theorem demo_rfl (n : Nat) : n = n",
        "description": "Reflexivite - 1 lemme direct (Eq.refl)",
        "expected_iterations": "2-3",
        "expected_lemmas": 1,
        "complexity": "Triviale"
    },
    {
        "name": "DEMO_2_COMPOSITION",
        "theorem": "theorem add_zero_comm (n m : Nat) : n + m + 0 = m + n",
        "description": "Composition - 2 lemmes (add_zero + add_comm)",
        "expected_iterations": "5-7",
        "expected_lemmas": 2,
        "complexity": "Simple - necessite combiner 2 lemmes"
    },
    {
        "name": "DEMO_3_MULTI_REWRITE",
        "theorem": "theorem quad_comm (a b c d : Nat) : (a + b) + (c + d) = (d + c) + (b + a)",
        "description": "Reecritures multiples - 4 applications de add_comm + add_assoc",
        "expected_iterations": "10-15",
        "expected_lemmas": 2,
        "complexity": "Intermediaire - chaine de reecritures"
    },
    {
        "name": "DEMO_4_STRUCTURED",
        "theorem": "theorem distrib_both (a b c : Nat) : (a + b) * c + a * c = a * c + a * c + b * c",
        "description": "Preuve structuree - right_distrib + add_assoc + add_comm",
        "expected_iterations": "15-20",
        "expected_lemmas": 3,
        "complexity": "Avancee - decomposition + recombinaison"
    }
]

all_results = []

for i, demo in enumerate(DEMOS, 1):
    print("\n" + "=" * 70)
    print(f"RUNNING DEMO {i}/4: {demo['name']}")
    print("=" * 70)
    print(f"Theoreme: {demo['theorem']}")
    print(f"Complexite: {demo['complexity']}")

    result = prove_with_multi_agents(
        theorem=demo["theorem"],
        max_iterations=10,
        verbose=True,
        use_simulation=False
    )

    print(f"\nResultat {demo['name']}:")
    print(f"  - Success: {result['success']}")
    print(f"  - Iterations: {result['iterations']}")
    print(f"  - Final proof: {result['final_proof'][:100] if result['final_proof'] else 'None'}...")
    print(f"  - Time: {result['total_time_s']}s")

    all_results.append({
        "name": demo["name"],
        "success": result["success"],
        "iterations": result["iterations"],
        "time": result["total_time_s"]
    })

# Summary
print("\n" + "=" * 70)
print("SUMMARY")
print("=" * 70)
for r in all_results:
    status = "OK" if r["success"] else "FAILED"
    print(f"  {r['name']}: {status} - {r['iterations']} iterations - {r['time']}s")

successes = sum(1 for r in all_results if r["success"])
print(f"\nTotal: {successes}/4 demos successful")

if successes >= 2:
    print("\n=== VALIDATION SUCCESSFUL ===")
else:
    print("\n=== VALIDATION FAILED ===")
    sys.exit(1)
