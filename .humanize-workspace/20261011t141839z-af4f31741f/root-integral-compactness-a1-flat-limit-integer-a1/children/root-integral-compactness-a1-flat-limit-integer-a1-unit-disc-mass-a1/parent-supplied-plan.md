# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.flat_limit_integer-a1.unit_disc_mass-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-flat-limit-integer-a1-unit-disc-mass-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.flat_limit_integer-a1`
- Child key: `unit_disc_mass`
- Declaration: `Submission.intcpt_fli_unit_disc_mass_eventually`
- Exact Lean type: `∀ (N n : ℕ) (P : Grassmannian N n) (θ₀ : ℝ) (W : ℕ → Varifold N n (ball (0 : Euclidean N) 5)), 0 < θ₀ → (∀ f : C_c(Euclidean N × Grassmannian N n, ℝ), tsupport f ⊆ ball (0 : Euclidean N) 5 ×ˢ (univ : Set (Grassmannian N n)) → Tendsto (fun k ↦ ∫ z, f z ∂(W k).measure) atTop (𝓝 (θ₀ * ∫ z, f z ∂(planeVarifoldMeasure P)))) → ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ a ∈ (P.plane : Set (Euclidean N)), ‖a‖ ≤ 1 → (W k).weight (closedBall a 1) ≤ ENNReal.ofReal ((θ₀ + η) * (unitBallVolume n).toReal)`

## Sibling prerequisites

- `root.integral_compactness-a1.flat_limit_integer-a1.plane_ball_measure-a1`
- `root.integral_compactness-a1.flat_limit_integer-a1.compact_mass_eventually-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
