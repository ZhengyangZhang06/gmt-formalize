# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1.frame_geometry-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-integer-density-a1-plane-integer-a1-f-fe9aa3c949/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1`
- Child key: `frame_geometry`
- Declaration: `Submission.ind_pi_frame_geometry`
- Exact Lean type: `∀ (P n : ℕ) (τ : Fin n → Eucl P) (p : Eucl P →L[ℝ] Eucl n) (d : Eucl P → ℝ), Orthonormal ℝ τ → (∀ y i, p y i = inner ℝ (τ i) y) → (∀ y, d y = ‖y - ∑ i, inner ℝ (τ i) y • τ i‖) → LipschitzWith 1 d ∧ (∀ y, ‖y‖ ^ 2 = ‖p y‖ ^ 2 + d y ^ 2) ∧ ‖p‖ ≤ 1 ∧ (∀ a : Eucl n, p (∑ i, a i • τ i) = a) ∧ (∀ i, p (τ i) = EuclideanSpace.single i (1 : ℝ)) ∧ (∀ z ∈ Submodule.span ℝ (Set.range τ), d z = 0) ∧ CompactlyContainedOpen {y : Eucl P | ‖p y‖ < 1 ∧ d y < 3 / 4} (ball (0 : Eucl P) 2) ∧ ∀ γ : ℝ, γ < 3 / 4 → ∀ K : Set (Eucl n), IsCompact K → K ⊆ ball (0 : Eucl n) 1 → IsCompact (p ⁻¹' K ∩ {y | d y ≤ γ}) ∧ p ⁻¹' K ∩ {y | d y ≤ γ} ⊆ {y : Eucl P | ‖p y‖ < 1 ∧ d y < 3 / 4}`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
