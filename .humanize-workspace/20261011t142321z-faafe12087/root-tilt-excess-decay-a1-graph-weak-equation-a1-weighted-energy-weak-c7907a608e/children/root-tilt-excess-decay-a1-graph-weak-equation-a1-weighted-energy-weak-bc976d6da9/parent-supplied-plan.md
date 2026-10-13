# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.graph_weak_equation-a1.weighted_energy_weak_equation-a1.weight_error_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1-weighted-energy-weak-bc976d6da9/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.graph_weak_equation-a1.weighted_energy_weak_equation-a1`
- Child key: `weight_error_bound`
- Declaration: `Submission.gwe_wewe_weight_error_bound`
- Exact Lean type: `∀ (n ℓ : ℕ) (cJ σ κ M : ℝ) (f : Rn n → Rn ℓ) (W ζ : Rn n → ℝ) (j : Fin ℓ), 0 ≤ cJ → 0 < σ → 0 ≤ κ → κ ≤ 1 → LipschitzOnWith 1 f (closedBall 0 (σ / 2)) → Measurable W → (∀ᵐ x ∂(volume : Measure (Rn n)), x ∈ ball 0 (3 * σ / 8) → W x = 0 ∨ (1 ≤ W x ∧ W x ≤ (1 + κ) * (1 + cJ * hsNormSq (fderiv ℝ f x)))) → (∀ x, ‖gradient ζ x‖ ≤ M) → |(∫ x in ball (0 : Rn n) (σ / 4), inner ℝ (gradient (fun y => f y j) x) (gradient ζ x)) - ∫ x in ball (0 : Rn n) (σ / 4), inner ℝ (gradient (fun y => f y j) x) (gradient ζ x) * W x| ≤ M * (volume (ball (0 : Rn n) (3 * σ / 8) ∩ {x | W x = 0})).toReal + M * κ * (∫ x in ball (0 : Rn n) (σ / 4), ‖gradient (fun y => f y j) x‖) + 2 * cJ * M * ∫ x in ball (0 : Rn n) (σ / 4), hsNormSq (fderiv ℝ f x)`

## Sibling prerequisites

- `root.tilt_excess_decay-a1.graph_weak_equation-a1.weighted_energy_weak_equation-a1.lipschitz_fderiv_facts-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
