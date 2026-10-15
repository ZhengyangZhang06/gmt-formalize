# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.high_degree_case-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-high-degree-case-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1`
- Child key: `high_degree_case`
- Declaration: `Submission.dimred_cs_high_degree_case`
- Exact Lean type: `∀ (P n : ℕ) (S : GeometricCurrentOn (univ : Set (Euclid P)) n) (L : Submodule ℝ (Euclid P)), P < n → IsConeCurrent S ∧ (∀ v ∈ L, ∀ ω : TestFormOn (univ : Set (Euclid P)) n, currentEval (blowUp S (-v) 1 one_ne_zero) (ω : DifferentialForm (Euclid P) n) = S ω) ∧ ∃ S₀ : GeometricCurrentOn (univ : Set (Euclid P)) (n - Module.finrank ℝ L), IsMinimizingIn S₀ univ ∧ BoundaryVanishes S₀ ∧ IsConeCurrent S₀ ∧ S₀.support ⊆ (Lᗮ : Set (Euclid P)) ∧ (∀ t ∈ L, ∀ y ∈ Lᗮ, (t + y ∈ S.support ↔ y ∈ S₀.support)) ∧ ∀ t ∈ L, ∀ y ∈ Lᗮ, ∀ θ : ℝ, (HasMassDensity S (t + y) θ ↔ HasMassDensity S₀ y θ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
