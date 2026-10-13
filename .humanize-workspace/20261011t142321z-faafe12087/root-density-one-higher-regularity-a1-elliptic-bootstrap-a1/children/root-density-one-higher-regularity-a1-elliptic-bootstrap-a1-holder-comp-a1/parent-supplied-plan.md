# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.holder_comp-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-holder-comp-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1`
- Child key: `holder_comp`
- Declaration: `Submission.dohr_eb_holder_comp`
- Exact Lean type: `∀ (E₁ E₂ E₃ : Type) [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [NormedAddCommGroup E₃] [NormedSpace ℝ E₃] (m : ℕ) (α : ℝ) (f : E₁ → E₂) (h : E₂ → E₃) (U : Set E₁) (V : Set E₂), 0 < α → α ≤ 1 → IsOpen U → IsOpen V → MapsTo f U V → (1 ≤ m ∨ ContDiffOn ℝ 1 f U ∨ ContDiffOn ℝ 1 h V) → ContDiffOn ℝ m f U → (∀ K : Set E₁, IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ m f x - iteratedFDeriv ℝ m f y‖ ≤ C * ‖x - y‖ ^ α) → ContDiffOn ℝ m h V → (∀ K : Set E₂, IsCompact K → K ⊆ V → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ m h x - iteratedFDeriv ℝ m h y‖ ≤ C * ‖x - y‖ ^ α) → ContDiffOn ℝ m (h ∘ f) U ∧ ∀ K : Set E₁, IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ m (h ∘ f) x - iteratedFDeriv ℝ m (h ∘ f) y‖ ≤ C * ‖x - y‖ ^ α`

## Sibling prerequisites

- `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.holder_of_contdiff_succ-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
