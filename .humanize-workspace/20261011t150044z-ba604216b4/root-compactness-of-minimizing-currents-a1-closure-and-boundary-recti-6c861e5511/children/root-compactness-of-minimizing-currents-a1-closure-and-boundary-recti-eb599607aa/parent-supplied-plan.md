# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1.directional-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-eb599607aa/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1`
- Child key: `directional`
- Declaration: `Submission.cbr_ci_cp_wedge_annihilator_subspace`
- Exact Lean type: `∀ (P d : ℕ) (ν : Measure (Euclid P)) (ζ₀ : MultiVector P (d + 1)), (∀ K : Set (Euclid P), IsCompact K → ν K < ∞) → (∀ φ : TestFormOn (univ : Set (Euclid P)) d, ∫ y, ζ₀ (exteriorDerivative (φ : DifferentialForm (Euclid P) d) y) ∂ν = 0) → ∃ V : Submodule ℝ (Euclid P), (∀ v ∈ V, ∀ φ : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → ∫ y, fderiv ℝ φ y v ∂ν = 0) ∧ ∀ w ∈ Vᗮ, ∀ (α : Covector (Euclid P) d) (γ : Covector (Euclid P) (d + 1)), (∀ u : Fin (d + 1) → Euclid P, γ u = ∑ i : Fin (d + 1), (-1 : ℝ) ^ (i : ℕ) * (inner ℝ w (u i) * α (i.removeNth u))) → ζ₀ γ = 0`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.boundary_weak_derivatives-a1.extderiv_smul_const-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
