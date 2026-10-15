# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.measure_invariance-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-measure-invariance-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1`
- Child key: `measure_invariance`
- Declaration: `Submission.dimred_cs_measure_invariant_of_density_invariant`
- Exact Lean type: `∀ (P n : ℕ) (S : GeometricCurrentOn (univ : Set (Euclid P)) n) (R : IMRep (univ : Set (Euclid P)) n) (L : Submodule ℝ (Euclid P)), 0 < n → R.Represents S → (∀ x : Euclid P, ∃ θ : ℝ, HasMassDensity S x θ) → (∀ y ∈ L, ∀ lam : ℝ, 0 < lam → ∀ (w : Euclid P) (θ : ℝ), HasMassDensity S w θ → HasMassDensity S (y + lam • w) θ) → (∀ y ∈ L, ∀ A : Set (Euclid P), MeasurableSet A → R.measure ((fun x => y + x) ⁻¹' A) = R.measure A) ∧ ∀ lam : ℝ, 0 < lam → ∀ A : Set (Euclid P), MeasurableSet A → R.measure ((fun x => lam • x) '' A) = ENNReal.ofReal (lam ^ n) * R.measure A`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
