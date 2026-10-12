# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.interior_estimates-a1.fderiv_apply_harmonic-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-79bf416985/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.interior_estimates-a1`
- Child key: `fderiv_apply_harmonic`
- Declaration: `Submission.dorag_ha_ie_fderiv_apply_harmonic`
- Exact Lean type: `∀ (n : ℕ) (U : Set (Euclid n)) (h : Euclid n → ℝ) (e : Euclid n), IsOpen U → (∀ m : ℕ, ContDiffOn ℝ m h U) → (∀ y ∈ U, ∑ i : Fin n, iteratedFDeriv ℝ 2 h y ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0) → (∀ m : ℕ, ContDiffOn ℝ m (fun y => fderiv ℝ h y e) U) ∧ ∀ y ∈ U, ∑ i : Fin n, iteratedFDeriv ℝ 2 (fun z => fderiv ℝ h z e) y ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
