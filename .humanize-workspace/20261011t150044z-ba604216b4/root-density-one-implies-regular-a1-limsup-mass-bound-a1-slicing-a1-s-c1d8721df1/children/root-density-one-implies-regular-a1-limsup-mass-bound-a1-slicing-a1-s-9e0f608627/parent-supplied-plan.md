# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.tangential_gradient-a1.tangent_gluing-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-9e0f608627/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.tangential_gradient-a1`
- Child key: `tangent_gluing`
- Declaration: `Submission.dor_lmbsf_tg_tangent_gluing`
- Exact Lean type: `(∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q) → ∀ (P n : ℕ) (U B : Set (Euclid P)) (S : ℕ → Set (Euclid P)) (Q : Euclid P → Submodule ℝ (Euclid P)), IsOpen U → MeasurableSet B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → (∀ j, MeasurableSet (S j)) → (∀ j, S j ⊆ B) → B ⊆ ⋃ j, S j → (∀ j, ∀ᵐ x ∂(μHE[n].restrict (S j)), HasApproximateTangentSpaceAt n (S j) x (Q x)) → ∀ᵐ x ∂(μHE[n].restrict B), HasApproximateTangentSpaceAt n B x (Q x)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
