# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_mass_bound-a1.smooth_approx-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-smooth-approx-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_mass_bound-a1`
- Child key: `smooth_approx`
- Declaration: `Submission.slicing_mb_smooth_approx`
- Exact Lean type: `∀ (P : ℕ) (W : Set (Eucl P)), IsOpen W → ∀ (f : Eucl P → ℝ) (L : ℝ≥0), LipschitzOnWith L f W → ∀ LW : ℝ≥0, (∀ᵐ x ∂(volume : Measure (Eucl P)), x ∈ W → ‖fderiv ℝ f x‖₊ ≤ LW) → ∀ K : Set (Eucl P), IsCompact K → K ⊆ W → ∀ δ : ℝ, 0 < δ → ∃ g : Eucl P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ (∀ x ∈ K, |g x - f x| ≤ δ) ∧ (∀ x ∈ K, ‖fderiv ℝ g x‖₊ ≤ LW)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
