# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.cone-a1.cone_lemma-a1.cone_criterion-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1-cone-lemma-a1-cone-criterion-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.cone-a1.cone_lemma-a1`
- Child key: `cone_criterion`
- Declaration: `Submission.dtc_cwv_isConeCurrent_of_pullback_invariant`
- Exact Lean type: `∀ (P n : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) n), (∀ lam : ℝ, 0 < lam → ∀ ω ω' : TestFormOn (univ : Set (Euclid P)) n, (∀ y, (ω' : DifferentialForm (Euclid P) n) y = (lam⁻¹ ^ n) • (ω : DifferentialForm (Euclid P) n) (lam⁻¹ • y)) → C ω' = C ω) → IsConeCurrent C`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
