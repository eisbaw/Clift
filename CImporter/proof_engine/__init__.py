# Proof engine: extract sorry goals, build prompts, apply proofs, check results.
# LLM-agnostic: prompt construction is model-independent, only the API call differs.
# Trust anchor: Lean kernel checks ALL accepted proofs. LLM output is UNTRUSTED.
