# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_slice_tangent-a1.patch_tangent_transfer-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-1230672507/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_slice_tangent-a1`
- Child key: `patch_tangent_transfer`
- Declaration: `Submission.dor_lmbsf_pst_patch_tangent_transfer`
- Exact Lean type: `(∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q) → ∀ (P n : ℕ) (S : Set (Euclid P)) (D : ℕ → Set (Euclid n)) (χ : ℕ → Euclid n → Euclid P) (c : ℕ → Euclid n) (ρ : ℕ → ℝ), MeasurableSet S → μHE[n] S ≠ ∞ → (∀ k, IsOpen (D k)) → (∀ k, ContDiffOn ℝ 1 (χ k) (D k)) → (∀ k, closedBall (c k) (ρ k) ⊆ D k) → (∀ k, InjOn (χ k) (closedBall (c k) (ρ k))) → ∀ᵐ x ∂(μHE[n].restrict S), ∀ k, ∀ z ∈ ball (c k) (ρ k), χ k z = x → ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n (χ k '' closedBall (c k) (ρ k)) x Q → HasApproximateTangentSpaceAt n S x Q`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
