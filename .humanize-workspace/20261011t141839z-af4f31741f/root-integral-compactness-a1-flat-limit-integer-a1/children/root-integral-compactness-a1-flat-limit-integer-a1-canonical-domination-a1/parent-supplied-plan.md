# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.flat_limit_integer-a1.canonical_domination-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-flat-limit-integer-a1-canonical-domination-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.flat_limit_integer-a1`
- Child key: `canonical_domination`
- Declaration: `Submission.intcpt_fli_integral_canonical_domination`
- Exact Lean type: `(∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U), IsIntegral V → ∀ᵐ x ∂V.weight, ∃ k : ℕ, 1 ≤ k ∧ HasDensity n V.weight x (k : ℝ≥0∞)) → (∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U), V.HasLocallyBoundedFirstVariation → (∀ᵐ x ∂V.weight, ∃ θ : ℝ≥0∞, HasDensity n V.weight x θ ∧ 0 < θ) → ∃ θ : Euclidean N → ℝ, IsVarifoldOf V {x | x ∈ V.weight.support ∧ ∃ (T : Grassmannian N n) (θ' : ℝ), HasTangentPlane V x T θ'} θ ∧ (∀ x ∈ {x | x ∈ V.weight.support ∧ ∃ (T : Grassmannian N n) (θ' : ℝ), HasTangentPlane V x T θ'}, (∃ T : Grassmannian N n, HasTangentPlane V x T (θ x)) ∧ HasDensity n V.weight x (ENNReal.ofReal (θ x))) ∧ ∀ Z ⊆ {x | x ∈ V.weight.support ∧ ∃ (T : Grassmannian N n) (θ' : ℝ), HasTangentPlane V x T θ'}, V.weight Z = 0 → (μHE[n] : Measure (Euclidean N)) Z = 0) → ∀ (N n : ℕ) (U : Set (Euclidean N)) (W : Varifold N n U), IsIntegral W → W.HasLocallyBoundedFirstVariation → ∃ θ : Euclidean N → ℝ, IsVarifoldOf W {x | x ∈ W.weight.support ∧ ∃ (T : Grassmannian N n) (θ' : ℝ), HasTangentPlane W x T θ'} θ ∧ (∀ x ∈ {x | x ∈ W.weight.support ∧ ∃ (T : Grassmannian N n) (θ' : ℝ), HasTangentPlane W x T θ'}, (∃ T : Grassmannian N n, HasTangentPlane W x T (θ x)) ∧ HasDensity n W.weight x (ENNReal.ofReal (θ x))) ∧ (μHE[n] : Measure (Euclidean N)) {x | x ∈ {x | x ∈ W.weight.support ∧ ∃ (T : Grassmannian N n) (θ' : ℝ), HasTangentPlane W x T θ'} ∧ ¬ ∃ m : ℕ, 1 ≤ m ∧ θ x = m} = 0 ∧ ∀ (K : Set (Euclidean N)) (u : Euclidean N → ℝ≥0∞), IsCompact K → K ⊆ U → Measurable u → (∀ x, x ∉ K → u x = 0) → ∫⁻ x, u x ∂W.weight ≤ ∫⁻ x in {x | x ∈ W.weight.support ∧ ∃ (T : Grassmannian N n) (θ' : ℝ), HasTangentPlane W x T θ'} ∩ K, u x * ENNReal.ofReal (θ x) ∂(μHE[n] : Measure (Euclidean N))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
