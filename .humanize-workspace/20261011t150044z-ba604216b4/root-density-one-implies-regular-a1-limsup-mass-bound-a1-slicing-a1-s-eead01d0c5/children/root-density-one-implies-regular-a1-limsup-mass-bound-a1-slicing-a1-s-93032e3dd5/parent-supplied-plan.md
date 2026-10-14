# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_weak_limit-a1.localize-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-93032e3dd5/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_weak_limit-a1`
- Child key: `localize`
- Declaration: `Submission.dor_lmbsf_pwl_chart_cutoff_localize`
- Exact Lean type: `∀ (P d : ℕ) (V C : Set (Euclid d)) (ψ : Euclid d → Euclid P) (hs : ℕ → Euclid P → ℝ) (h : Euclid P → ℝ) (c : ℝ), IsOpen V → ContDiffOn ℝ 1 ψ V → IsCompact C → C ⊆ V → (∀ k, ContDiff ℝ 1 (hs k)) → (∀ k x, ‖fderiv ℝ (hs k) x‖ ≤ c) → TendstoUniformly hs h atTop → ∃ (O : Set (Euclid d)) (K : NNReal) (us : ℕ → Euclid d → ℝ) (u : Euclid d → ℝ), IsOpen O ∧ C ⊆ O ∧ (∀ k, LipschitzWith K (us k)) ∧ LipschitzWith K u ∧ TendstoUniformly us u atTop ∧ (∀ k, ∀ y ∈ O, us k y = hs k (ψ y)) ∧ ∀ y ∈ O, u y = h (ψ y)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
