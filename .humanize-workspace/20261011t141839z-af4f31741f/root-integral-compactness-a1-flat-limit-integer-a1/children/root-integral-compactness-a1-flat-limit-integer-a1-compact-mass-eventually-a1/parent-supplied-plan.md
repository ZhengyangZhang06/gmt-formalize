# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.flat_limit_integer-a1.compact_mass_eventually-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-flat-limit-integer-a1-compact-mass-eventually-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.flat_limit_integer-a1`
- Child key: `compact_mass_eventually`
- Declaration: `Submission.intcpt_fli_weight_compact_eventually_lt`
- Exact Lean type: `∀ (N n : ℕ) (P : Grassmannian N n) (θ₀ : ℝ) (W : ℕ → Varifold N n (ball (0 : Euclidean N) 5)), 0 < θ₀ → (∀ f : C_c(Euclidean N × Grassmannian N n, ℝ), tsupport f ⊆ ball (0 : Euclidean N) 5 ×ˢ (univ : Set (Grassmannian N n)) → Tendsto (fun k ↦ ∫ z, f z ∂(W k).measure) atTop (𝓝 (θ₀ * ∫ z, f z ∂(planeVarifoldMeasure P)))) → ∀ (K O : Set (Euclidean N)) (c : ℝ≥0∞), IsCompact K → IsOpen O → K ⊆ O → O ⊆ ball (0 : Euclidean N) 5 → ENNReal.ofReal θ₀ * (μHE[n] : Measure (Euclidean N)) ((P.plane : Set (Euclidean N)) ∩ O) < c → ∀ᶠ k in atTop, (W k).weight K < c`

## Sibling prerequisites

- `root.integral_compactness-a1.flat_limit_integer-a1.weight_tendsto-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
