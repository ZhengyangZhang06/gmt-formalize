# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.weyl_lemma-a1.conv_swap-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-73a7e5f57f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.weyl_lemma-a1`
- Child key: `conv_swap`
- Declaration: `Submission.dorag_ha_weyl_conv_swap`
- Exact Lean type: `∀ (n : ℕ) (f φ ψ : Euclid n → ℝ) (x : Euclid n), Integrable f → Continuous φ → HasCompactSupport φ → Continuous ψ → HasCompactSupport ψ → ∫ z, (∫ y, f y * φ (x - z - y)) * ψ z = ∫ z, (∫ y, f y * ψ (x - z - y)) * φ z`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
