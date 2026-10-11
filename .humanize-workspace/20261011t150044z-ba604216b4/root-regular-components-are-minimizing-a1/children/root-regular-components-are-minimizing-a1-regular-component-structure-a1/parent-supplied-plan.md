# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_components_are_minimizing-a1.regular_component_structure-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-regular-component-structure-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_components_are_minimizing-a1`
- Child key: `regular_component_structure`
- Declaration: `Submission.regcomp_regular_component_structure`
- Exact Lean type: `∀ (P m : ℕ) (U : Set (Euclid P)) (T T₁ : GeometricCurrentOn U (m + 1)) (R : IMRep U (m + 1)) (y : Euclid P), IsOpen U → R.Represents T → y ∈ regularSet T → (∀ ω : TestFormOn U (m + 1), T₁ ω = ∫ x in connectedComponentIn (regularSet T) y, R.orient x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 1]) → MeasurableSet (connectedComponentIn (regularSet T) y) ∧ μHE[m + 1] (connectedComponentIn (regularSet T) y \ R.carrier) = 0 ∧ closure (connectedComponentIn (regularSet T) y) ∩ U ⊆ connectedComponentIn (regularSet T) y ∪ singularSet T ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → IsCompact (singularSet T ∩ K)) ∧ ∀ z ∈ connectedComponentIn (regularSet T) y, ∃ G : Set (Euclid P), IsOpen G ∧ z ∈ G ∧ ∃ c : ℝ, ∀ ω : TestFormOn U (m + 1), tsupport (ω : DifferentialForm (Euclid P) (m + 1)) ⊆ G → T₁ ω = c * T ω`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
