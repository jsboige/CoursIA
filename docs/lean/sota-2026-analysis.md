# SOTA in Automated Lean 4 Proving (May 2026)

Synthesis of the current landscape in automated theorem proving for Lean 4, with focus on actionable insights for our multi-agent prover harness.

---

## 1. DeepSeek-Prover-V2 (April 2025)

**Paper**: [arXiv:2504.21801](https://arxiv.org/abs/2504.21801) | **Models**: 7B and 671B (MoE) | **License**: Open-source

**Architecture**: Built on DeepSeek-V3 (671B MoE). Uses a recursive cold-start pipeline where DeepSeek-V3 decomposes theorems into subgoals, a 7B prover attempts each subgoal, and completed proofs are synthesized back into chain-of-thought training data. RL via GRPO (Group Relative Policy Optimization) refines the model.

**Key innovation**: Subgoal decomposition bridges informal and formal reasoning. The model produces both CoT reasoning traces (informal) and verified Lean 4 proofs (formal) in a unified training loop.

**Results**:
| Benchmark | Score | Notes |
|-----------|-------|-------|
| miniF2F-test | 88.9% pass ratio | Whole-proof generation |
| PutnamBench | 49/658 | University-level problems |
| AIME 2024-25 | 6/15 formal | vs 8/15 informal (DeepSeek-V3) |

**Relevance to us**: Their subgoal decomposition is conceptually similar to our Coordinator agent's role. The gap between formal (6) and informal (8) on AIME highlights the remaining difficulty of formalizing combinatorial arguments -- exactly our challenge with Knuth rotation sub-cases.

---

## 2. LeanCopilot / LLMLean

### LeanCopilot (LeanDojo)

**Paper**: [arXiv:2404.12534](https://arxiv.org/abs/2404.12534) | **GitHub**: [lean-dojo/LeanCopilot](https://github.com/lean-dojo/LeanCopilot) | Published at ICML 2025

In-framework integration of LLMs into Lean 4. Provides three native tactics:
- `suggest_tactics`: LLM-generated tactic suggestions given current proof state
- `search_proof`: Automated proof search via tree search with LLM-guided expansion
- `select_premises`: Retrieval-augmented premise selection from Mathlib

Runs models locally (ONNX) or via API server. Built on LeanDojo's tracing infrastructure for extracting proof states and interaction data.

### LLMLean (CMU L3)

**GitHub**: [cmu-l3/llmlean](https://github.com/cmu-l3/llmlean)

Lightweight alternative: integrates LLMs (local or cloud) directly into Lean for tactic suggestions and proof completion. Version 2.0 adds improved context understanding and multi-provider support (OpenAI, Anthropic, local models).

### ReProver (LeanDojo v2)

Retrieval-Augmented Prover: extracts premises from Mathlib via embedding similarity, then generates tactics conditioned on retrieved context. Part of the LeanDojo-v2 framework for training, evaluating, and deploying provers.

**Key insight for us**: LeanCopilot's in-framework approach (running inside the Lean tactic monad) gets precise proof states, unlike our external harness that parses error messages. Premise selection via embedding retrieval could significantly improve our TacticAgent's success rate on Mathlib-heavy proofs.

---

## 3. ATP Landscape for Lean 4 (2025-2026)

### BFS-Prover / BFS-Prover-V2 (ByteDance Seed)

**V1** ([arXiv:2502.03438](https://arxiv.org/abs/2502.03438), ACL 2025): Best-first search with LLM step-prover. 72.95% on miniF2F-test. Demonstrated that simple BFS with good value estimation outperforms complex tree search (MCTS).

**V2** ([arXiv:2509.06493](https://arxiv.org/abs/2509.06493), NeurIPS 2025): Multi-turn off-policy RL + multi-agent tree search. **95.08% miniF2F, 41.4% ProofNet**. Step-level tactic generation with hierarchical search. 7B and 32B variants.

### Kimina-Prover Preview (Moonshot AI, April 2025)

**Paper**: [arXiv:2504.11354](https://arxiv.org/abs/2504.11354)

72B reasoning model with "formal reasoning pattern": interleaves informal CoT thinking with formal Lean 4 code. 80.7% on miniF2F (pass@8192). Key contribution: structured thinking tags (`<thinkormal>` blocks) that bridge reasoning and formalization.

### Goedel-Prover / V2

**V1** ([arXiv:2502.07640](https://arxiv.org/abs/2502.07640)): Iterative expert self-training. NL-to-Lean formalization of 1.64M statements (Numina dataset), self-bootstrapping prover pipeline. 57.6% miniF2F (SOTA at time, April 2025). Open-sourced training data (Goedel-Pset-v1, 800K+ solved).

**V2**: Higher pass@32 with dramatically improved sample efficiency. Surpasses all prior models on miniF2F including DeepSeek-Prover-V1.5.

### Seed-Prover / 1.5 (ByteDance Seed)

**Seed-Prover 1.0**: Lemma-style whole-proof reasoning. Iterative refinement via Lean feedback + proved lemmas + self-summarization. Saturated miniF2F. 5/6 IMO 2025 problems proved.

**Seed-Prover 1.5** ([arXiv:2512.17260](https://arxiv.org/abs/2512.17260), Dec 2025): Large-scale agentic RL. First five IMO 2025 problems with complete Lean proofs. Agentic architecture with self-reflection loop.

### Delta Prover (July 2025)

**Paper**: [arXiv:2507.15225](https://arxiv.org/abs/2507.15225)

Agent-based framework using general-purpose LLMs (no specialized fine-tuning). Reflection + decomposition algorithm. **95.9% miniF2F-test**. Demonstrates that frontier LLMs + smart orchestration can match specialized provers.

### Leanabell-Prover / V2 (July 2025)

**Paper**: [arXiv:2507.08649](https://arxiv.org/abs/2507.08649)

7B model with verifier-integrated long CoT. RL with Lean feedback during training, producing self-aware reasoning that anticipates verification failures. Post-training scaling approach -- improved performance without increasing model size.

### AlphaProof (Google DeepMind, July 2024; Nature Nov 2025)

**Paper**: [Nature, Nov 2025](https://www.nature.com/articles/s41586-025-09833-y)

AlphaZero-style RL paired with a pre-trained LM. Autoformalizes problems into Lean 4, searches for verified proof steps. IMO 2024 silver medal (4/6 problems, 28 points). **Gemini + Deep Think achieved IMO 2025 gold** (35/42 points).

Not open-source. Key lesson: the RL + formal verification loop (train on verified proofs, not just generated ones) is essential for scaling.

---

## 4. Multi-Agent Proving Architectures

### MA-LoT (March 2025)

**Paper**: [arXiv:2503.03205](https://arxiv.org/abs/2503.03205)

**The most directly comparable published work to our harness.** Two-agent framework:
- **Prover Agent**: Generates Lean 4 proofs with long CoT reasoning
- **Corrector Agent**: Analyzes failures and suggests corrections

Uses "LoT-Transfer Learning" pipeline: SFT data from successful proofs -> NL Long CoT training -> field-specific alignment.

**Results**: 61.07% on miniF2F-test (Lean 4), outperforming single-agent baselines (GPT-4: 22.95%, InternLM-Step-Prover: 50.70%, Goedel-Prover: 55.33%).

**Comparison to our harness**: Our 5-agent design (Search, Tactic, Critic, Coordinator, Director) is more decomposed than MA-LoT's 2-agent setup. Their Corrector is analogous to our Critic+Director. Their Prover combines our Tactic+Search. We lack the specialized SFT/alignment training that makes their agents effective.

### APOLLO (NeurIPS 2025)

**Paper**: [arXiv:2505.05758](https://arxiv.org/abs/2505.05758)

Model-agnostic agentic framework combining LLM + Lean compiler + automated solvers. Focuses on proof *repair* rather than generation from scratch. 75% on miniF2F. Modular pipeline: generate -> verify -> repair -> iterate.

**Relevance**: Proof repair is a capability our harness lacks. When our TacticAgent produces a near-miss proof, we discard and retry rather than repairing.

### BFS-Prover-V2 Multi-Agent Search

The multi-agent variant in BFS-Prover-V2 uses separate agents for: (1) tactic generation, (2) value estimation for search node priority, (3) proof state evaluation. Published results show multi-agent tree search significantly outperforms single-agent at fixed compute budgets.

---

## 5. Comparison Matrix

| System | Date | Size | miniF2F | ProofNet | Putnam | Strategy | Mathlib | Open |
|--------|------|------|---------|----------|--------|----------|---------|------|
| **DeepSeek-Prover-V2** | Apr 2025 | 671B | 88.9% | - | 49/658 | Whole-proof, subgoal RL | Partial | Yes |
| **BFS-Prover-V2** | Sep 2025 | 7B/32B | **95.1%** | **41.4%** | - | Step BFS + multi-agent RL | Yes | Yes |
| **Seed-Prover 1.5** | Dec 2025 | Proprietary | ~99% | >50% | SOTA | Lemma-style + agentic RL | Yes | No |
| **Delta Prover** | Jul 2025 | API-only | **95.9%** | - | - | Agent + reflection, no fine-tune | No | Yes |
| **Kimina-Prover** | Apr 2025 | 72B | 80.7%@8192 | - | - | Whole-proof CoT | Partial | Yes |
| **Goedel-Prover V2** | Aug 2025 | - | >60%@32 | - | - | Whole-proof, iterative self-train | Partial | Yes |
| **AlphaProof** | Jul 2024 | Proprietary | - | - | IMO silver | AlphaZero RL + Lean | Yes | No |
| **MA-LoT** | Mar 2025 | 7B | 61.1% | - | - | 2-agent (Prover+Corrector) | Partial | Yes |
| **Leanabell-V2** | Jul 2025 | 7B | - | - | - | Verifier-integrated CoT | Partial | Yes |
| **APOLLO** | May 2025 | Model-agnostic | 75% | - | - | LLM + Lean + repair loop | Yes | Yes |
| **Our harness** | 2025-26 | API (GPT-5.5) | - | - | - | 5-agent (Search/Tactic/Critic/Coord/Director) | Via context | N/A |

**Key observations**:
- miniF2F is nearly saturated (95%+). Real frontier is ProofNet, PutnamBench, and IMO-level.
- Step-level proving (BFS-Prover-V2) outperforms whole-proof generation at smaller model sizes.
- Multi-agent approaches (MA-LoT, BFS-Prover-V2, APOLLO) consistently beat single-agent at same model size.
- Open-source 7B models with RL can match or beat proprietary 671B models on standard benchmarks.

---

## 6. Actionable Insights for Our Harness

### 6.1 Architecture improvements

1. **Proof repair agent** (inspired by APOLLO): Instead of discarding near-miss proofs, add a RepairAgent that takes (failed proof, error message) and produces a corrected version. Our near-miss rate on intractable proofs is high -- repair could convert more of these.

2. **Premise retrieval** (inspired by LeanCopilot/ReProver): Add embedding-based Mathlib premise selection before TacticAgent invocation. Currently our TacticAgent operates blind to Mathlib content. A retrieval step could provide relevant lemmas as context.

3. **Step-level mode** (inspired by BFS-Prover-V2): Our whole-proof mode sometimes generates 20+ line proofs that fail at line 3. A step-level fallback (generate one tactic at a time, verify, continue) would be more robust for complex proofs.

### 6.2 Training data opportunities

4. **Self-play data** (inspired by Goedel-Prover): Our successful proofs (gale_shapley_stable, man_optimal, meetSpouse_injective, etc.) are unique training data. Fine-tuning a small model on our proven theorems could create a domain-specific prover.

5. **Subgoal decomposition training** (inspired by DeepSeek-Prover-V2): Train the CoordinatorAgent to decompose hard goals into lemmas. Our current Coordinator plans at the file level; subgoal-level decomposition could unlock harder proofs.

### 6.3 Benchmark gaps

6. **We don't compete on standard benchmarks**: Our harness targets specific theorems (stable marriage, voting, cooperative games). This is a different regime than miniF2F/ProofNet. Our intractability findings (Knuth rotation sub-cases) reveal that even SOTA systems would likely fail on these -- they require domain-specific mathematical insight that current LLMs lack.

7. **The frontier has moved to IMO/Putnam**: Standard benchmarks are saturated. Our niche (research-level combinatorics in specific domains) remains underserved by SOTA systems.

---

## References

- DeepSeek-Prover-V2: https://arxiv.org/abs/2504.21801
- LeanCopilot: https://arxiv.org/abs/2404.12534 | https://github.com/lean-dojo/LeanCopilot
- LLMLean: https://github.com/cmu-l3/llmlean
- LeanDojo v2 / ReProver: https://leandojo.org/
- BFS-Prover: https://arxiv.org/abs/2502.03438
- BFS-Prover-V2: https://arxiv.org/abs/2509.06493 | https://github.com/ByteDance-Seed/BFS-Prover-V2
- Kimina-Prover: https://arxiv.org/abs/2504.11354
- Goedel-Prover: https://arxiv.org/abs/2502.07640 | https://goedel-lm.github.io/
- Seed-Prover 1.5: https://arxiv.org/abs/2512.17260
- Delta Prover: https://arxiv.org/abs/2507.15225
- Leanabell-Prover-V2: https://arxiv.org/abs/2507.08649
- AlphaProof (Nature): https://www.nature.com/articles/s41586-025-09833-y
- MA-LoT: https://arxiv.org/abs/2503.03205
- APOLLO: https://arxiv.org/abs/2505.05758
- AlphaProof IMO 2025 Gold: https://deepmind.google/blog/advanced-version-of-gemini-with-deep-think-officially-achieves-gold-medal-standard-at-the-international-mathematical-olympiad/
