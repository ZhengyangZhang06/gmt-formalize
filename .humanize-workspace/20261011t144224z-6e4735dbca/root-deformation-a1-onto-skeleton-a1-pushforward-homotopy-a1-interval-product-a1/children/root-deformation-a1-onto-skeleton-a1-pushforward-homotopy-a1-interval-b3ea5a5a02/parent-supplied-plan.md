# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.interval_product-a1.horizontal_slices-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-interval-b3ea5a5a02/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.interval_product-a1`
- Child key: `horizontal_slices`
- Declaration: `Submission.dph_iprod_horizontal_slices`
- Exact Lean type: `∀ (m q : ℕ) (ψ : TestFormOn (univ : Set (Eucl (m + 1))) q), ∃ Ψ Ψ' : ℝ → TestFormOn (univ : Set (Eucl m)) q, (∀ (s : ℝ) (x : Eucl m) (v : Fin q → Eucl m), (Ψ s : DifferentialForm (Eucl m) q) x v = (ψ : DifferentialForm (Eucl (m + 1)) q) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) ∧ ∀ (s : ℝ) (x : Eucl m) (v : Fin q → Eucl m), (Ψ' s : DifferentialForm (Eucl m) q) x v = fderiv ℝ (ψ : DifferentialForm (Eucl (m + 1)) q) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (EuclideanSpace.single 0 1) (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))`

## Sibling prerequisites

- `root.integrality_weak_limits-a1.smooth_pushforward-a1.compatible_form-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
