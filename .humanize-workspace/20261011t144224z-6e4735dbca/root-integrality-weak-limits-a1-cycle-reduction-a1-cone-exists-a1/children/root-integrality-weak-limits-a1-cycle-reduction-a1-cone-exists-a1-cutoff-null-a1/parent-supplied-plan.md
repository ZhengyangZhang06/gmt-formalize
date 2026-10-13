# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.cycle_reduction-a1.cone_exists-a1.cutoff_null-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-exists-a1-cutoff-null-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_exists-a1`
- Child key: `cutoff_null`
- Declaration: `Submission.iwl_cr_ce_cutoff_converges_zero`
- Exact Lean type: `∀ (P k : ℕ) (U : Set (Eucl P)) (ζ : Eucl P → ℝ) (ψs : ℕ → DifferentialForm (Eucl P) k) (φs : ℕ → TestFormOn U k), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ζ → HasCompactSupport ζ → tsupport ζ ⊆ U → (∀ l, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ψs l)) → (∀ l x, (φs l : DifferentialForm (Eucl P) k) x = ζ x • ψs l x) → (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ᶠ l in atTop, ∀ x ∈ tsupport ζ, ‖iteratedFDeriv ℝ j (ψs l) x‖ ≤ ε) → TestFormOnConverges φs 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
