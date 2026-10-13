# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.graph_weak_equation-a1.weighted_energy_weak_equation-a1.energy_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1-weighted-energy-weak-1b3d0b2dbe/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.graph_weak_equation-a1.weighted_energy_weak_equation-a1`
- Child key: `energy_bound`
- Declaration: `Submission.gwe_wewe_energy_bound`
- Exact Lean type: `∀ (n ℓ : ℕ) (K0 σ E : ℝ) (f : Rn n → Rn ℓ) (W : Rn n → ℝ), 0 ≤ K0 → 0 < σ → 0 ≤ E → LipschitzOnWith 1 f (closedBall 0 (σ / 2)) → Measurable W → (∀ᵐ x ∂(volume : Measure (Rn n)), x ∈ ball 0 (3 * σ / 8) → W x = 0 ∨ 1 ≤ W x) → volume (ball (0 : Rn n) (3 * σ / 8) ∩ {x | W x = 0}) ≤ ENNReal.ofReal (K0 * E * σ ^ n) → ∫⁻ x in ball (0 : Rn n) (3 * σ / 8), ENNReal.ofReal (hsNormSq (fderiv ℝ f x) * W x) ≤ ENNReal.ofReal (K0 * E * σ ^ n) → IntegrableOn (fun x => hsNormSq (fderiv ℝ f x)) (ball (0 : Rn n) (3 * σ / 8)) ∧ ∫ x in ball (0 : Rn n) (3 * σ / 8), hsNormSq (fderiv ℝ f x) ≤ (1 + n) * K0 * E * σ ^ n`

## Sibling prerequisites

- `root.tilt_excess_decay-a1.graph_weak_equation-a1.weighted_energy_weak_equation-a1.lipschitz_fderiv_facts-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
