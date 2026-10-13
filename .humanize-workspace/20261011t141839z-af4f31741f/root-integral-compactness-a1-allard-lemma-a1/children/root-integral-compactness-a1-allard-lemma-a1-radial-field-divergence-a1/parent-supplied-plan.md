# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.allard_lemma-a1.radial_field_divergence-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-allard-lemma-a1-radial-field-divergence-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.allard_lemma-a1`
- Child key: `radial_field_divergence`
- Declaration: `Submission.intcpt_allard_radial_field_divergence`
- Exact Lean type: `∀ (N n : ℕ) (a : Euclidean N → ℝ) (y z : Euclidean N) (S : Grassmannian N n), DifferentiableAt ℝ a z → Varifold.tangentialDivergence (fun w ↦ a w • (w - y)) z S = n * a z + fderiv ℝ a z (Grassmannian.project S (z - y))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
