# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.mean_value-a1.deriv_under_integral-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-9d42229933/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.mean_value-a1`
- Child key: `deriv_under_integral`
- Declaration: `Submission.dorag_ha_mv_deriv_under_integral`
- Exact Lean type: `∀ (n : ℕ) (U : Set (Euclid n)) (h : Euclid n → ℝ) (x : Euclid n) (r R : ℝ) (g : ℝ → ℝ), IsOpen U → ContDiffOn ℝ 1 h U → closedBall x R ⊆ U → 0 < r → Continuous g → (∀ t : ℝ, r ^ 2 ≤ t → g t = 0) → ∀ s : ℝ, |s| * r < R → HasDerivAt (fun σ : ℝ => ∫ y : Euclid n, h (x - σ • y) * g (‖y‖ ^ 2)) (-∫ y : Euclid n, fderiv ℝ h (x - s • y) y * g (‖y‖ ^ 2)) s`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
