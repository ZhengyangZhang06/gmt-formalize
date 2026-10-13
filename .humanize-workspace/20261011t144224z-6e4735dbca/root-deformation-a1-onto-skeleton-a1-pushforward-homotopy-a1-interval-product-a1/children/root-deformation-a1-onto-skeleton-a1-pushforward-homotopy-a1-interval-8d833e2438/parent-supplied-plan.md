# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.interval_product-a1.slice_ext_deriv-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-interval-8d833e2438/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.interval_product-a1`
- Child key: `slice_ext_deriv`
- Declaration: `Submission.dph_iprod_slice_extDeriv`
- Exact Lean type: `(∀ (m : ℕ) (ψ : TestFormOn (univ : Set (Eucl (m + 1))) 0) (y : Eucl (m + 1)) (v : Fin 0 → Eucl m), ((exteriorDerivativeTestOn (univ : Set (Eucl (m + 1))) 0 ψ : TestFormOn (univ : Set (Eucl (m + 1))) (0 + 1)) : DifferentialForm (Eucl (m + 1)) (0 + 1)) y (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i)))) = fderiv ℝ (ψ : DifferentialForm (Eucl (m + 1)) 0) y (EuclideanSpace.single 0 1) (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) ∧ (∀ (m j : ℕ) (ψ : TestFormOn (univ : Set (Eucl (m + 1))) (j + 1)) (φ : TestFormOn (univ : Set (Eucl m)) j) (s : ℝ), (∀ (x : Eucl m) (w : Fin j → Eucl m), (φ : DifferentialForm (Eucl m) j) x w = (ψ : DifferentialForm (Eucl (m + 1)) (j + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (w i))))) → ∀ (x : Eucl m) (v : Fin (j + 1) → Eucl m), ((exteriorDerivativeTestOn (univ : Set (Eucl (m + 1))) (j + 1) ψ : TestFormOn (univ : Set (Eucl (m + 1))) (j + 1 + 1)) : DifferentialForm (Eucl (m + 1)) (j + 1 + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i)))) = fderiv ℝ (ψ : DifferentialForm (Eucl (m + 1)) (j + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (EuclideanSpace.single 0 1) (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i)))) - ((exteriorDerivativeTestOn (univ : Set (Eucl m)) j φ : TestFormOn (univ : Set (Eucl m)) (j + 1)) : DifferentialForm (Eucl m) (j + 1)) x v)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
