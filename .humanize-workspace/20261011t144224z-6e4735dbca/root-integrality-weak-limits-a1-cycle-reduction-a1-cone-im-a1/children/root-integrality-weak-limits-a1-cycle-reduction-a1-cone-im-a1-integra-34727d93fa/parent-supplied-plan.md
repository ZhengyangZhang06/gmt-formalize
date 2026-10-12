# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.cycle_reduction-a1.cone_im-a1.integral_exchange-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-im-a1-integra-34727d93fa/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_im-a1`
- Child key: `integral_exchange`
- Declaration: `Submission.iwl_cr_ci_integral_exchange`
- Exact Lean type: `∀ (P m : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl P)) m) (K : Set (Eucl P)) (φ : ℝ → TestFormOn (univ : Set (Eucl P)) m) (ψ : TestFormOn (univ : Set (Eucl P)) m), IsIntegerMultiplicity X → IsCompact K → Continuous (fun p : ℝ × Eucl P => (φ p.1 : DifferentialForm (Eucl P) m) p.2) → (∀ s ∈ Icc (0 : ℝ) 1, tsupport (φ s : DifferentialForm (Eucl P) m) ⊆ K) → (∀ (x : Eucl P) (v : Fin m → Eucl P), (ψ : DifferentialForm (Eucl P) m) x v = ∫ s in (0 : ℝ)..1, (φ s : DifferentialForm (Eucl P) m) x v) → ∫ s in (0 : ℝ)..1, X (φ s) = X ψ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
