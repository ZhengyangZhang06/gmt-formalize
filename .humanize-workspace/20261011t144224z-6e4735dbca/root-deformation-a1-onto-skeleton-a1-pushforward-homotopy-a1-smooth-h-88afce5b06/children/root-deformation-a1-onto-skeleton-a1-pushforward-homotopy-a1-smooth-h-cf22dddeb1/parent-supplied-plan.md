# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_homotopy-a1.affine_estimate-a1.affine_homotopy_proper-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-h-cf22dddeb1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_homotopy-a1.affine_estimate-a1`
- Child key: `affine_homotopy_proper`
- Declaration: `Submission.dph_sh_ae_affine_homotopy_isCompact_preimage_cyl`
- Exact Lean type: `∀ (m m' : ℕ) (F₀ F₁ : Eucl m → Eucl m') (S : Set (Eucl m)) (s : ℝ), Continuous F₀ → Continuous F₁ → IsClosed S → (∀ x ∈ S, dist (F₁ x) (F₀ x) ≤ s) → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (F₀ ⁻¹' K ∩ S)) → ∀ K : Set (Eucl m'), IsCompact K → IsCompact ((fun y : Eucl (m + 1) => F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) + (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) • (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) - F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))))) ⁻¹' K ∩ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ S})`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
