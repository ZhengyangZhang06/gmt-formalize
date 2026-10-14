# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.cycle_reduction-a1.radial_operator-a1.parametric_integral-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-radial-operator-a1-04239efcb3/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.cycle_reduction-a1.radial_operator-a1`
- Child key: `parametric_integral`
- Declaration: `Submission.iwl_cr_ro_intervalIntegral_contDiff`
- Exact Lean type: `∀ (P : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (G : ℝ × Eucl P → V) (a b : ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Eucl P => ∫ t in a..b, G (t, x)) ∧ (∀ j : ℕ, Continuous (fun p : ℝ × Eucl P => iteratedFDeriv ℝ j (fun z : Eucl P => G (p.1, z)) p.2)) ∧ ∀ (j : ℕ) (x : Eucl P), iteratedFDeriv ℝ j (fun y : Eucl P => ∫ t in a..b, G (t, y)) x = ∫ t in a..b, iteratedFDeriv ℝ j (fun z : Eucl P => G (t, z)) x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
