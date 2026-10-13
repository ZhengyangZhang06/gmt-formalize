# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.mean_value-a1.affine_comp_deriv-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-831ebcc444/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.mean_value-a1`
- Child key: `affine_comp_deriv`
- Declaration: `Submission.dorag_ha_mv_affine_comp_deriv`
- Exact Lean type: `∀ (n : ℕ) (h : Euclid n → ℝ) (x : Euclid n) (s : ℝ) (y a b : Euclid n), fderiv ℝ (fun z : Euclid n => h (x - s • z)) y a = -(s * fderiv ℝ h (x - s • y) a) ∧ iteratedFDeriv ℝ 2 (fun z : Euclid n => h (x - s • z)) y ![a, b] = s ^ 2 * iteratedFDeriv ℝ 2 h (x - s • y) ![a, b]`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
