# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.holder_bilinear-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-holder-bilinear-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1`
- Child key: `holder_bilinear`
- Declaration: `Submission.dohr_eb_holder_bilinear`
- Exact Lean type: `∀ (E₁ E₂ E₃ E₄ : Type) [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [NormedAddCommGroup E₃] [NormedSpace ℝ E₃] [NormedAddCommGroup E₄] [NormedSpace ℝ E₄] (m : ℕ) (α : ℝ) (B : E₂ →L[ℝ] E₃ →L[ℝ] E₄) (f : E₁ → E₂) (g : E₁ → E₃) (U : Set E₁), 0 < α → α ≤ 1 → IsOpen U → ContDiffOn ℝ m f U → (∀ K : Set E₁, IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ m f x - iteratedFDeriv ℝ m f y‖ ≤ C * ‖x - y‖ ^ α) → ContDiffOn ℝ m g U → (∀ K : Set E₁, IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ m g x - iteratedFDeriv ℝ m g y‖ ≤ C * ‖x - y‖ ^ α) → ContDiffOn ℝ m (fun x => B (f x) (g x)) U ∧ ∀ K : Set E₁, IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ m (fun x => B (f x) (g x)) x - iteratedFDeriv ℝ m (fun x => B (f x) (g x)) y‖ ≤ C * ‖x - y‖ ^ α`

## Sibling prerequisites

- `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.holder_comp-a1`
- `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.holder_of_contdiff_succ-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
