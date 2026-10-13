# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.rectifiability-a1.bf_trichotomy-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-bf-trichotomy-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.rectifiability-a1`
- Child key: `bf_trichotomy`
- Declaration: `Submission.rectifiability_bf_trichotomy`
- Exact Lean type: `∀ (N m : ℕ) (E : Set (Eucl N)) (δ : ℝ), IsSigmaCompact E → (μHE[m + 1] : Measure (Eucl N)) E < ∞ → 0 < δ → ∀ᵐ v ∂(volume : Measure (Fin (m + 1) → Eucl N)), ∀ᵐ a ∂((μHE[m + 1] : Measure (Eucl N)).restrict E), (∀ η : ℝ, 0 < η → ∃ s ∈ Ioo (0 : ℝ) 1, ∀ r ∈ Ioo (0 : ℝ) δ, (μHE[m + 1] : Measure (Eucl N)) (E ∩ {x | dist x a < r ∧ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ < s * ‖x - a‖}) ≤ ENNReal.ofReal (η * (r * s) ^ (m + 1))) ∨ dimensionalUpperDensity (Measure.map (fun x : Eucl N => (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) x) : Eucl (m + 1))) ((μHE[m + 1] : Measure (Eucl N)).restrict E)).toOuterMeasure ((m + 1 : ℕ) : ℝ) univ (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) a) : Eucl (m + 1)) = ⊤ ∨ ∃ x ∈ E, x ≠ a ∧ dist x a < δ ∧ (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) x) : Eucl (m + 1)) = (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) a) : Eucl (m + 1))`

## Sibling prerequisites

- `root.rectifiability-a1.mickle_rado-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
