# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.cycle_reduction-a1.cone_im-a1.integral_exchange-a1.nvector_integral-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-im-a1-integra-5b296a6678/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_im-a1.integral_exchange-a1`
- Child key: `nvector_integral`
- Declaration: `Submission.iwl_cr_ci_ie_nvector_intervalIntegral`
- Exact Lean type: `∀ (P m : ℕ) (a b : ℝ) (f : ℝ → Covector (Eucl P) m) (c : Covector (Eucl P) m) (w : NVector (Eucl P) m), Continuous f → (∀ v : Fin m → Eucl P, c v = ∫ s in a..b, f s v) → ∫ s in a..b, w (f s) = w c`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
