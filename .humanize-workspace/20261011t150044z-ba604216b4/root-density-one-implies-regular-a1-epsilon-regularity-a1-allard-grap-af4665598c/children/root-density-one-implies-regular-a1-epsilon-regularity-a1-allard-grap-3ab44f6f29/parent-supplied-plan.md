# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.affine_assembly-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-3ab44f6f29/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1`
- Child key: `affine_assembly`
- Declaration: `Submission.dorag_tes_componentwise_affine_assembly`
- Exact Lean type: `∀ (n k : ℕ) (f : Euclid n → Euclid k) (s A B Q t : ℝ), Continuous f → 0 < s → (∀ j : Fin k, ∃ (a : ℝ) (b : Euclid n →L[ℝ] ℝ), ‖b‖ ≤ B ∧ |a| ≤ A ∧ ∫ v in ball (0 : Euclid n) t, (s⁻¹ * EuclideanSpace.proj j (f v) - a - b v) ^ 2 ≤ Q) → ∃ (c : Euclid k) (Λ : Euclid n →L[ℝ] Euclid k), ‖c‖ ≤ k * s * A ∧ ‖Λ‖ ≤ k * s * B ∧ ∫⁻ v in ball (0 : Euclid n) t, ENNReal.ofReal (‖f v - c - Λ v‖ ^ 2) ≤ ENNReal.ofReal (k * s ^ 2 * Q)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
