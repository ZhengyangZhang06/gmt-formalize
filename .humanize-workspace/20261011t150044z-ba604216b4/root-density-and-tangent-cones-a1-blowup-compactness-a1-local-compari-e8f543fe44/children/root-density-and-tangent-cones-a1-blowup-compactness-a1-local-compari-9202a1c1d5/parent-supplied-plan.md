# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1.localize-a1.cutoff_estimate-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-9202a1c1d5/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1.localize-a1`
- Child key: `cutoff_estimate`
- Declaration: `Submission.dtc_bc_lc_fd_lz_cutoff_estimate`
- Exact Lean type: `∀ (P m : ℕ) (U V S : Set (Euclid P)) (T : GeometricCurrentOn U (m + 1)) (R : IMRep U (m + 1)) (g : Euclid P → ℝ) (η : TestFormOn U m) (a c : ℝ), R.Represents T → ContDiff ℝ (⊤ : ℕ∞) g → tsupport g ⊆ V → (∀ x, |g x| ≤ a) → (∀ x, ‖fderiv ℝ g x‖ ≤ c) → (∀ x, fderiv ℝ g x ≠ 0 → x ∈ S) → (∀ x, covectorEuclideanNorm ((η : DifferentialForm (Euclid P) m) x) ≤ 1) → ENNReal.ofReal |R.action (fun x => g x • exteriorDerivative (η : DifferentialForm (Euclid P) m) x)| ≤ ENNReal.ofReal a * T.boundary.massOn V + ENNReal.ofReal c * R.measure S`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1.localize-a1.action_bound-a1`
- `root.compactness_of_minimizing_currents-a1.slicing-a1.cutoff_defect-a1.leibniz-a1`
- `root.compactness_of_minimizing_currents-a1.slicing-a1.wedge_norm-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
