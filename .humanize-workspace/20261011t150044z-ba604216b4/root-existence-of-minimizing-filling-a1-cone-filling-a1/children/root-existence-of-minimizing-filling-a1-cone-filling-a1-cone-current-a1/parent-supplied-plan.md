# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.existence_of_minimizing_filling-a1.cone_filling-a1.cone_current-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-existence-of-minimizing-filling-a1-cone-filling-a1-cone-current-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.existence_of_minimizing_filling-a1.cone_filling-a1`
- Child key: `cone_current`
- Declaration: `Submission.ecf_cone_current`
- Exact Lean type: `∀ (n P : ℕ) (S : GeometricCurrentOn (univ : Set (Euclid P)) (n + 1)), S.mass ≠ ∞ → IsCompact S.support → S.boundary = 0 → ∃ R : GeometricCurrentOn (univ : Set (Euclid P)) (n + 2), IsCompact R.support ∧ R.boundary = S ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) (n + 2), ∃ γ : TestFormOn (univ : Set (Euclid P)) (n + 1), R ω = S γ ∧ ∀ x ∈ S.support, ∀ v : Fin (n + 1) → Euclid P, (γ : DifferentialForm (Euclid P) (n + 1)) x v = ∫ t in (0 : ℝ)..1, t ^ (n + 1) * (ω : DifferentialForm (Euclid P) (n + 2)) (t • x) (Fin.cons x v)`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.vanish_off_support-a1`
- `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.slice-a1.param_integral-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
