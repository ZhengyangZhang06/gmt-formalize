# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.minimizing_implies_stationary-a1.tangential_deformation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-tangential-deformation-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.minimizing_implies_stationary-a1`
- Child key: `tangential_deformation`
- Declaration: `Submission.tangential_c1_deformation_exists`
- Exact Lean type: `∀ (P d : ℕ) (U N : Set (Euclid P)) (X : Euclid P → Euclid P), IsOpen U → IsEmbeddedSubmanifold 2 d N → (closure N \ N) ∩ U = ∅ → ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U → (∀ x ∈ N ∩ U, X x ∈ tangentSpace N x) → ∃ φ : ℝ → Euclid P → Euclid P, (∀ t, ContDiff ℝ 1 (φ t) ∧ Bijective (φ t) ∧ (∀ x, Injective (fderiv ℝ (φ t) x)) ∧ (∀ x, x ∉ tsupport X → φ t x = x) ∧ MapsTo (φ t) (N ∩ U) (N ∩ U)) ∧ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → ∀ x, ‖fderiv ℝ (φ t) x - ContinuousLinearMap.id ℝ (Euclid P) - t • fderiv ℝ X x‖ ≤ ε * |t|`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.chart_tangent_space-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
