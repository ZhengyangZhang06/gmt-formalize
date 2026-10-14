# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_homotopy-a1.slice_compatible-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-h-a2a415b3c0/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_homotopy-a1`
- Child key: `slice_compatible`
- Declaration: `Submission.dph_sh_slice_compatible_testForm`
- Exact Lean type: `∀ (m m' q : ℕ) (G : Eucl (m + 1) → Eucl m') (ω : DifferentialForm (Eucl m') q) (θ : TestFormOn (univ : Set (Eucl (m + 1))) q) (N : Set (Eucl (m + 1))) (s : ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G → (∀ y ∈ N, (θ : DifferentialForm (Eucl (m + 1)) q) y = (ω (G y)).compContinuousLinearMap (fderiv ℝ G y)) → ∃ θs : TestFormOn (univ : Set (Eucl m)) q, (∀ (x : Eucl m) (v : Fin q → Eucl m), (θs : DifferentialForm (Eucl m) q) x v = (θ : DifferentialForm (Eucl (m + 1)) q) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) ∧ ∀ x : Eucl m, (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)) ∈ N → (θs : DifferentialForm (Eucl m) q) x = (ω ((fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))) x)).compContinuousLinearMap (fderiv ℝ (fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))) x)`

## Sibling prerequisites

- `root.integrality_weak_limits-a1.smooth_pushforward-a1.compatible_form-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
