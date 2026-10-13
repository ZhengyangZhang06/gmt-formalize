# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.linear_higher_regularity-a1.coeff_uniform_bounds-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-linear-hi-a5168fec76/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.linear_higher_regularity-a1`
- Child key: `coeff_uniform_bounds`
- Declaration: `Submission.dohr_eb_lhr_coeff_uniform_bounds`
- Exact Lean type: `∀ (n ℓ : ℕ) (α : ℝ) (U K : Set (Rn n)) (a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ), 0 < α → α ≤ 1 → IsOpen U → IsCompact K → Convex ℝ K → K ⊆ U → (∀ P Q : Rn n →L[ℝ] Rn ℓ, ContDiffOn ℝ 1 (fun x => a x P Q) U) → ∃ M : ℝ, ∀ x ∈ K, ∀ y ∈ K, ∀ P Q : Rn n →L[ℝ] Rn ℓ, |a x P Q| ≤ M * ‖P‖ * ‖Q‖ ∧ |a x P Q - a y P Q| ≤ M * ‖x - y‖ ^ α * ‖P‖ * ‖Q‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
