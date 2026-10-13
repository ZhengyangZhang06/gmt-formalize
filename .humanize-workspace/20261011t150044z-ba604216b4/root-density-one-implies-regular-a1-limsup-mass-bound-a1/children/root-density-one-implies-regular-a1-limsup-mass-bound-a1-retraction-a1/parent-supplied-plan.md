# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.retraction-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-retraction-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1`
- Child key: `retraction`
- Declaration: `Submission.dor_lmb_c1_retraction`
- Exact Lean type: `∀ (P d : ℕ) (U N : Set (Euclid P)) (y : Euclid P), IsOpen U → IsEmbeddedSubmanifold 2 d N → (closure N \ N) ∩ U = ∅ → y ∈ N ∩ U → ∃ (r c : ℝ) (proj : Euclid P → Euclid P), 0 < r ∧ 0 ≤ c ∧ closedBall y r ⊆ U ∧ ContDiffOn ℝ 1 proj (ball y r) ∧ MapsTo proj (ball y r) N ∧ (∀ x ∈ N ∩ ball y r, proj x = x) ∧ (∀ x ∈ N ∩ ball y r, ∀ v ∈ tangentSpace N x, fderiv ℝ proj x v = v) ∧ ∀ x ∈ ball y r, ‖fderiv ℝ proj x‖ ≤ 1 + c * dist x y`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
