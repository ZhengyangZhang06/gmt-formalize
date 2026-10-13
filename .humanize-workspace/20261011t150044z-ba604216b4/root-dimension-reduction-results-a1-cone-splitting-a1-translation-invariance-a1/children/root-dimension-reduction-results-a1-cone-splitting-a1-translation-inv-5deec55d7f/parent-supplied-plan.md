# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.translation_invariance-a1.directional_annihilation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-translation-inv-5deec55d7f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.translation_invariance-a1`
- Child key: `directional_annihilation`
- Declaration: `Submission.dimred_cs_ti_directional_annihilated`
- Exact Lean type: `∀ (P n : ℕ) (S : GeometricCurrentOn (univ : Set (Euclid P)) n) (R : IMRep (univ : Set (Euclid P)) n) (v : Euclid P), 0 < n → R.Represents S → BoundaryVanishes S → (∀ᵐ x ∂R.measure, ∀ β : Covector (Euclid P) (n + 1), R.orient x (ContinuousAlternatingMap.curryLeft β v) = 0) → ∀ β γ : TestFormOn (univ : Set (Euclid P)) n, (∀ y, (γ : DifferentialForm (Euclid P) n) y = fderiv ℝ (β : DifferentialForm (Euclid P) n) y v) → S γ = 0`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.cone_splitting-a1.translation_invariance-a1.const_cartan-a1`
- `root.dimension_reduction_results-a1.cone_splitting-a1.translation_invariance-a1.const_contraction-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
