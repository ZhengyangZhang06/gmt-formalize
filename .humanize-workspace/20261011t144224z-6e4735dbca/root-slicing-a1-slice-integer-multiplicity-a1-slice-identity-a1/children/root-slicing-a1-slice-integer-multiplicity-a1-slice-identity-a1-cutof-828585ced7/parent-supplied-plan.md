# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.slice_identity-a1.cutoff_gradient-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-identity-a1-cutof-828585ced7/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1.slice_identity-a1`
- Child key: `cutoff_gradient`
- Declaration: `Submission.slicing_im_si_cutoff_tangential_gradient`
- Exact Lean type: `∀ (P : ℕ) (μ : Measure (Eucl P)) (Tan : Eucl P → Submodule ℝ (Eucl P) → Prop) (f : Eucl P → ℝ) (L : ℝ≥0) (G : Eucl P → Eucl P) (t ε : ℝ), 0 < ε → LipschitzWith L f → Measurable G → (∀ x, ‖G x‖ ≤ L) → (∀ᵐ x ∂μ, ∀ Q : Submodule ℝ (Eucl P), Tan x Q → G x ∈ Q ∧ ∀ u ∈ Q, HasDerivAt (fun s : ℝ => f (x + s • u)) (inner ℝ (G x) u) 0) → (∀ᵐ x ∂μ, f x = t - ε → G x = 0) → (∀ᵐ x ∂μ, f x = t → G x = 0) → ∃ K : ℝ≥0, LipschitzWith K (fun x => max 0 (min 1 ((t - f x) / ε))) ∧ Measurable ((f ⁻¹' Ioo (t - ε) t).indicator (fun y => (-ε⁻¹) • G y)) ∧ (∀ x, ‖(f ⁻¹' Ioo (t - ε) t).indicator (fun y => (-ε⁻¹) • G y) x‖ ≤ K) ∧ ∀ᵐ x ∂μ, ∀ Q : Submodule ℝ (Eucl P), Tan x Q → (f ⁻¹' Ioo (t - ε) t).indicator (fun y => (-ε⁻¹) • G y) x ∈ Q ∧ ∀ u ∈ Q, HasDerivAt (fun s : ℝ => max 0 (min 1 ((t - f (x + s • u)) / ε))) (inner ℝ ((f ⁻¹' Ioo (t - ε) t).indicator (fun y => (-ε⁻¹) • G y) x) u) 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
