# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.cycle_reduction-a1.cone_im-a1.cutoff_pullback-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-im-a1-cutoff-pullback-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_im-a1`
- Child key: `cutoff_pullback`
- Declaration: `Submission.iwl_cr_ci_cutoff_pullback_testForm`
- Exact Lean type: `∀ (P Q k : ℕ) (f : Eucl P → Eucl Q) (χ : Eucl P → ℝ) (ω : DifferentialForm (Eucl Q) k), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ → HasCompactSupport χ → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω → ∃ η : TestFormOn (univ : Set (Eucl P)) k, ∀ y, (η : DifferentialForm (Eucl P) k) y = χ y • (ω (f y)).compContinuousLinearMap (fderiv ℝ f y)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
