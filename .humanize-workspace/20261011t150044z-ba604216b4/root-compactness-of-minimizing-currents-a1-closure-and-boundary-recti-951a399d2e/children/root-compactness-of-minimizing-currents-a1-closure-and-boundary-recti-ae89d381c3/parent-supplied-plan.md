# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.l1_constant-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-ae89d381c3/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1`
- Child key: `l1_constant`
- Declaration: `Submission.cbr_ci_pw_density_l1_tendsto_const`
- Exact Lean type: `∀ (d : ℕ) (R c Λ : ℝ) (Y : ℕ → GeometricCurrentOn (ball (0 : Euclid (d + 1)) (2 * R)) (d + 1)) (u : ℕ → Euclid (d + 1) → ℝ), 0 < R → (∀ k, IntegrableOn (u k) (ball 0 (2 * R))) → (∀ᶠ k in atTop, ∫ y in ball 0 (2 * R), |u k y| ≤ Λ) → (∀ (k : ℕ) (ω : TestFormOn (ball (0 : Euclid (d + 1)) (2 * R)) (d + 1)), Y k ω = ∫ y in ball 0 (2 * R), u k y * (ω : DifferentialForm (Euclid (d + 1)) (d + 1)) y (fun i => EuclideanSpace.single i (1 : ℝ))) → Tendsto (fun k => (Y k).boundary.massOn (ball 0 (2 * R))) atTop (𝓝 0) → (∀ ω : TestFormOn (ball (0 : Euclid (d + 1)) (2 * R)) (d + 1), Tendsto (fun k => Y k ω) atTop (𝓝 (c * ∫ y, (ω : DifferentialForm (Euclid (d + 1)) (d + 1)) y (fun i => EuclideanSpace.single i (1 : ℝ))))) → Tendsto (fun k => ∫ y in ball 0 R, |u k y - c|) atTop (𝓝 0)`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.interior_form-a1`
- `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.mollified_uniform-a1`
- `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.bv_estimate-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
