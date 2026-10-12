# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.graph_weak_equation-a1.weighted_energy_weak_equation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1-weighted-energy-weak-c7907a608e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.graph_weak_equation-a1`
- Child key: `weighted_energy_weak_equation`
- Declaration: `Submission.gwe_weighted_energy_weak_equation`
- Exact Lean type: `∀ n ℓ : ℕ, 1 ≤ n → ∀ K0 cJ : ℝ, 0 ≤ K0 → 0 ≤ cJ → ∃ C : ℝ, 0 < C ∧ ∀ (σ κ E h : ℝ) (f : Rn n → Rn ℓ) (W : Rn n → ℝ), 0 < σ → 0 ≤ κ → κ ≤ 1 → 0 ≤ E → 0 ≤ h → LipschitzOnWith 1 f (closedBall 0 (σ / 2)) → Measurable W → (∀ᵐ x ∂(volume : Measure (Rn n)), x ∈ ball 0 (3 * σ / 8) → W x = 0 ∨ (1 ≤ W x ∧ W x ≤ (1 + κ) * (1 + cJ * hsNormSq (fderiv ℝ f x)))) → volume (ball (0 : Rn n) (3 * σ / 8) ∩ {x | W x = 0}) ≤ ENNReal.ofReal (K0 * E * σ ^ n) → ∫⁻ x in ball (0 : Rn n) (3 * σ / 8), ENNReal.ofReal (hsNormSq (fderiv ℝ f x) * W x) ≤ ENNReal.ofReal (K0 * E * σ ^ n) → (∫ x in ball (0 : Rn n) (3 * σ / 8), hsNormSq (fderiv ℝ f x) ≤ C * E * σ ^ n) ∧ ∀ ζ : Rn n → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball 0 (σ / 4) → ∀ M : ℝ, (∀ x, ‖gradient ζ x‖ ≤ M) → ∀ j : Fin ℓ, |∫ x in ball (0 : Rn n) (σ / 4), inner ℝ (gradient (fun y => f y j) x) (gradient ζ x) * W x| ≤ K0 * (E + h) * M * σ ^ n → |∫ x in ball (0 : Rn n) (σ / 4), inner ℝ (gradient (fun y => f y j) x) (gradient ζ x)| ≤ C * (E + h + κ * Real.sqrt E) * M * σ ^ n`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
