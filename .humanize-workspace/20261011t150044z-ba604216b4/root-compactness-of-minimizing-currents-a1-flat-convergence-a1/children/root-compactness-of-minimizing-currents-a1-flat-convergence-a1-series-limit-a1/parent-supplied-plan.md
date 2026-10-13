# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.flat_convergence-a1.series_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-series-limit-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.flat_convergence-a1`
- Child key: `series_limit`
- Declaration: `Submission.cmc_fc_series_limit`
- Exact Lean type: `(∀ (P d : ℕ) (U : Set (Euclid P)) (Ts : ℕ → GeometricCurrentOn U d) (T : GeometricCurrentOn U d), IsOpen U → (∀ j, IsIntegerMultiplicity (Ts j)) → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → ⨆ j, ((Ts j).massOn W + boundaryMassOn (Ts j) W) < ∞) → WeaklyConvergesOn Ts T → IsIntegerMultiplicity T) → (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) → ∀ (P m : ℕ) (U : Set (Euclid P)) (X : ℕ → GeometricCurrentOn U (m + 1)) (Xlim : GeometricCurrentOn U (m + 1)) (Λ : NNReal) (R : ℕ → GeometricCurrentOn U (m + 2)) (S : ℕ → GeometricCurrentOn U (m + 1)), IsOpen U → WeaklyConvergesOn X Xlim → (∀ r, (X r).mass ≤ Λ ∧ (X r).boundary.mass ≤ Λ) → (∀ r, IsIntegerMultiplicity (R r) ∧ IsIntegerMultiplicity (S r) ∧ X (r + 1) - X r - S r = (R r).boundary ∧ (R r).mass + (S r).mass ≤ (2⁻¹ : ℝ≥0∞) ^ r) → ∀ ℓ : ℕ, ∃ (R' : GeometricCurrentOn U (m + 2)) (S' : GeometricCurrentOn U (m + 1)), IsIntegerMultiplicity R' ∧ IsIntegerMultiplicity S' ∧ Xlim - X ℓ - S' = R'.boundary ∧ R'.mass + S'.mass ≤ 2 * (2⁻¹ : ℝ≥0∞) ^ ℓ`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.series_current-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
