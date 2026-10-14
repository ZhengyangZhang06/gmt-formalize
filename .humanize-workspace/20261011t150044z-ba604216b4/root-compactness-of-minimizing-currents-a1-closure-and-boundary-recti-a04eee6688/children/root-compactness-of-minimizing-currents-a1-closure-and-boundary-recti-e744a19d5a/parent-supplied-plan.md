# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1.product-a1.subspace_haar-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-e744a19d5a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1.product-a1`
- Child key: `subspace_haar`
- Declaration: `Submission.cbr_ci_cp_prod_subspace_haar`
- Exact Lean type: `∀ (P n : ℕ) (m : Measure (Euclid P)) (V : Submodule ℝ (Euclid P)), Module.finrank ℝ V = n → m (V : Set (Euclid P))ᶜ = 0 → (∀ K : Set (Euclid P), IsCompact K → m K < ∞) → (∀ v ∈ V, ∀ A : Set (Euclid P), MeasurableSet A → m ((fun x => v + x) ⁻¹' A) = m A) → ∃ c : ℝ≥0∞, m = c • (μHE[n]).restrict (V : Set (Euclid P))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
