# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.cone-a1.cone_lemma-a1.dilation_invariance-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1-cone-lemma-a1-dilation-invariance-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.cone-a1.cone_lemma-a1`
- Child key: `dilation_invariance`
- Declaration: `Submission.dtc_cwv_action_dilation_invariant`
- Exact Lean type: `∀ (P n : ℕ) (R : IMRep (univ : Set (Euclid P)) n), (∀ β γ : TestFormOn (univ : Set (Euclid P)) n, (∀ y, (γ : DifferentialForm (Euclid P) n) y = (n : ℝ) • (β : DifferentialForm (Euclid P) n) y + fderiv ℝ (β : DifferentialForm (Euclid P) n) y y) → R.action (γ : DifferentialForm (Euclid P) n) = 0) → ∀ lam : ℝ, 0 < lam → ∀ ω ω' : TestFormOn (univ : Set (Euclid P)) n, (∀ y, (ω' : DifferentialForm (Euclid P) n) y = (lam⁻¹ ^ n) • (ω : DifferentialForm (Euclid P) n) (lam⁻¹ • y)) → R.action (ω' : DifferentialForm (Euclid P) n) = R.action (ω : DifferentialForm (Euclid P) n)`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.cone-a1.cone_lemma-a1.scaled_derivative-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
