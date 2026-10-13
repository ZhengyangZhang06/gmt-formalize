# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.canonical_representation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-canonical-representation-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1`
- Child key: `canonical_representation`
- Declaration: `Submission.intcpt_canonical_tangent_representation`
- Exact Lean type: `AllardRectifiabilityTheorem → FirstRectifiabilityTheorem → ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U), V.HasLocallyBoundedFirstVariation → (∀ᵐ x ∂V.weight, ∃ θ : ℝ≥0∞, HasDensity n V.weight x θ ∧ 0 < θ) → ∃ θ : Euclidean N → ℝ, IsVarifoldOf V {x | x ∈ V.weight.support ∧ ∃ (T : Grassmannian N n) (θ' : ℝ), HasTangentPlane V x T θ'} θ ∧ (∀ x ∈ {x | x ∈ V.weight.support ∧ ∃ (T : Grassmannian N n) (θ' : ℝ), HasTangentPlane V x T θ'}, (∃ T : Grassmannian N n, HasTangentPlane V x T (θ x)) ∧ HasDensity n V.weight x (ENNReal.ofReal (θ x))) ∧ ∀ Z ⊆ {x | x ∈ V.weight.support ∧ ∃ (T : Grassmannian N n) (θ' : ℝ), HasTangentPlane V x T θ'}, V.weight Z = 0 → (μHE[n] : Measure (Euclidean N)) Z = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
