# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.isolate_plane-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-276085ade4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1`
- Child key: `isolate_plane`
- Declaration: `Submission.cbr_ci_pw_isolate_plane`
- Exact Lean type: `∀ (P n N : ℕ) (v : Fin n → Euclid P) (w : Fin N → Euclid P) (α : Fin N → ℝ) (ν : Measure (Euclid P)) (pL : Euclid P →L[ℝ] Euclid n) (i₀ : Fin N), Orthonormal ℝ v → Injective w → (∀ (i : Fin N) (j : Fin n), inner ℝ (w i) (v j) = 0) → ν = ∑ i, ENNReal.ofReal (α i) • (μHE[n]).restrict {y : Euclid P | y - w i ∈ Submodule.span ℝ (Set.range v)} → (∀ (x : Euclid P) (i : Fin n), pL x i = inner ℝ (v i) x) → ∃ (g : Euclid P → ℝ) (δ : ℝ), 0 < δ ∧ LipschitzWith 1 g ∧ (∀ y : Euclid P, y - w i₀ ∈ Submodule.span ℝ (Set.range v) → g y = 0) ∧ ν.restrict {x | g x < 3 * δ} = ENNReal.ofReal (α i₀) • (μHE[n]).restrict {y : Euclid P | y - w i₀ ∈ Submodule.span ℝ (Set.range v)} ∧ ∀ t r : ℝ, IsCompact ({x | g x ≤ t} ∩ pL ⁻¹' closedBall 0 r)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
