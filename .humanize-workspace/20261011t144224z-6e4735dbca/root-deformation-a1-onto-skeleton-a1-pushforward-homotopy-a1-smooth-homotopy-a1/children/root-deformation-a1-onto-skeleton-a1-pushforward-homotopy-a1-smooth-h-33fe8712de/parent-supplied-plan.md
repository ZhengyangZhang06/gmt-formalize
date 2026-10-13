# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_homotopy-a1.slice_comparison-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-h-33fe8712de/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_homotopy-a1`
- Child key: `slice_comparison`
- Declaration: `Submission.dph_sh_apply_eq_of_eqOn_nhds_cyl`
- Exact Lean type: `∀ (m q : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) q) (Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (q + 1)), (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (q + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) q), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin q → Eucl m), (φ s : DifferentialForm (Eucl m) q) x v = (η : DifferentialForm (Eucl (m + 1)) (q + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z η = ∫ s in (0 : ℝ)..1, X (φ s)) → ∀ (η η' : TestFormOn (univ : Set (Eucl (m + 1))) (q + 1)) (N : Set (Eucl (m + 1))), IsOpen N → {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support} ⊆ N → (∀ y ∈ N, (η : DifferentialForm (Eucl (m + 1)) (q + 1)) y = (η' : DifferentialForm (Eucl (m + 1)) (q + 1)) y) → Z η = Z η'`

## Sibling prerequisites

- `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_im-a1.slice_forms-a1`
- `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_exists-a1.locality-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
