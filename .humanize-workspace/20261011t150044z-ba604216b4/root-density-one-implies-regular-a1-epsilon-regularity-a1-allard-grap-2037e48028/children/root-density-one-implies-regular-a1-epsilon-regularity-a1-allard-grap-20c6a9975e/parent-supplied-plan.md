# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_variation-a1.cutoff_extension-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-20c6a9975e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_variation-a1`
- Child key: `cutoff_extension`
- Declaration: `Submission.dorag_tes_gv_cutoff_extension`
- Exact Lean type: `∀ (n m : ℕ), 0 < n → ∀ (ξ : Euclid m) (r : ℝ) (P : Euclid m →L[ℝ] Euclid n) (ζ : Euclid n → ℝ) (G : ℝ), 0 < r → ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Euclid n) (r / 2) → (∀ v, ‖fderiv ℝ ζ v‖ ≤ G) → ∃ ψ : Euclid m → ℝ, ContDiff ℝ 1 ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ closedBall ξ r ∧ (∀ x, |ψ x| ≤ G * (r / 2)) ∧ ∀ x, ‖x - ξ‖ ^ 2 ≤ ‖P (x - ξ)‖ ^ 2 + r ^ 2 / 16 → fderiv ℝ ψ x = (fderiv ℝ ζ (P (x - ξ))).comp P`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
