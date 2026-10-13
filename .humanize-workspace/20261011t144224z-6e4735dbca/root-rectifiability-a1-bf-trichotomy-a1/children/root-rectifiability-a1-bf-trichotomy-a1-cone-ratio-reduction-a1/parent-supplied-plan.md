# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.rectifiability-a1.bf_trichotomy-a1.cone_ratio_reduction-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-bf-trichotomy-a1-cone-ratio-reduction-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.rectifiability-a1.bf_trichotomy-a1`
- Child key: `cone_ratio_reduction`
- Declaration: `Submission.rectifiability_bf_cone_ratio_reduction`
- Exact Lean type: `∀ (N m : ℕ) (μ : Measure (Eucl N)) (δ : ℝ) (a : Eucl N) (v : Fin (m + 1) → Eucl N), (limsup (fun s : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ, μ {x | dist x a < r ∧ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ < s * ‖x - a‖} / ENNReal.ofReal ((r * s) ^ (m + 1))) (𝓝[>] 0) = 0 → ∀ η : ℝ, 0 < η → ∃ s ∈ Ioo (0 : ℝ) 1, ∀ r ∈ Ioo (0 : ℝ) δ, μ {x | dist x a < r ∧ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ < s * ‖x - a‖} ≤ ENNReal.ofReal (η * (r * s) ^ (m + 1))) ∧ (limsup (fun s : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ, μ {x | dist x a < r ∧ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ < s * ‖x - a‖} / ENNReal.ofReal ((r * s) ^ (m + 1))) (𝓝[>] 0) = ⊤ → dimensionalUpperDensity (Measure.map (fun x : Eucl N => (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) x) : Eucl (m + 1))) μ).toOuterMeasure ((m + 1 : ℕ) : ℝ) univ (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) a) : Eucl (m + 1)) = ⊤)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
