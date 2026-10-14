# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.dilation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-dilation-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1`
- Child key: `dilation`
- Declaration: `Submission.cmcdt_dilation_pushforward`
- Exact Lean type: `∀ P : ℕ, ∃ dil : ∀ k : ℕ, ℝ → GeometricCurrentOn (univ : Set (Euclid P)) k → GeometricCurrentOn (univ : Set (Euclid P)) k, ∀ (k : ℕ) (lam : ℝ), 0 < lam → (∀ X Y : GeometricCurrentOn (univ : Set (Euclid P)) k, dil k lam (X - Y) = dil k lam X - dil k lam Y) ∧ (∀ X : GeometricCurrentOn (univ : Set (Euclid P)) k, dil k lam⁻¹ (dil k lam X) = X) ∧ (∀ X : GeometricCurrentOn (univ : Set (Euclid P)) k, (dil k lam X).mass = ENNReal.ofReal (lam ^ k) * X.mass) ∧ (∀ X : GeometricCurrentOn (univ : Set (Euclid P)) k, (dil k lam X).support = (fun x => lam • x) '' X.support) ∧ (∀ X : GeometricCurrentOn (univ : Set (Euclid P)) k, IsIntegerMultiplicity X → IsIntegerMultiplicity (dil k lam X)) ∧ ∀ X : GeometricCurrentOn (univ : Set (Euclid P)) (k + 1), (dil (k + 1) lam X).boundary = dil k lam X.boundary`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
