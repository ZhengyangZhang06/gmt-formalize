# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.rellich_ball-a1.line_ftc-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-c14fae9d0b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.rellich_ball-a1`
- Child key: `line_ftc`
- Declaration: `Submission.dorag_ha_rb_line_ftc`
- Exact Lean type: `∀ (n : ℕ) (u : Euclid n → ℝ) (L : NNReal) (p v : Euclid n) (a b : ℝ), LipschitzWith L u → (∀ᵐ τ : ℝ, τ ∈ Set.uIcc a b → DifferentiableAt ℝ u (p + τ • v)) → u (p + b • v) - u (p + a • v) = ∫ τ in a..b, fderiv ℝ u (p + τ • v) v`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
