# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.bv_results-a1.extension-a1.boundary_direction-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-bv-results-a1-extension-a1-boundary-direction-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.bv_results-a1.extension-a1`
- Child key: `boundary_direction`
- Declaration: `Submission.bv_ext_infDist_compl_fderiv_lt`
- Exact Lean type: `∀ (n : ℕ) (U : Set (Rn n)) (ξ : Rn n) (r : ℝ), IsOpen U → Convex ℝ U → Uᶜ.Nonempty → 0 < r → closedBall ξ r ⊆ U → ∃ η : ℝ, 0 < η ∧ ∀ x ∈ U, infDist x Uᶜ < η → DifferentiableAt ℝ (fun y ↦ infDist y Uᶜ) x → r < -fderiv ℝ (fun y ↦ infDist y Uᶜ) x (x - ξ)`

## Sibling prerequisites

- `root.bv_results-a1.extension-a1.distance_concave-a1`
- `root.bv_results-a1.extension-a1.distance_gradient-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
