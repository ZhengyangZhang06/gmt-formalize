# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1.slice_selection-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-integer-density-a1-plane-integer-a1-s-253346ea31/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1`
- Child key: `slice_selection`
- Declaration: `Submission.ind_pi_good_slice_selection`
- Exact Lean type: `SlicingTheorem → (∀ (P k : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (Xj : ℕ → GeometricCurrentOn U k) (X : GeometricCurrentOn U k) (W : Set (Eucl P)) (φ : Eucl P → ℝ), WeaklyConvergesOn Xj X → IsOpen W → W ⊆ U → (⨆ j, (Xj j).massOn W) < ∞ → ContinuousOn φ U → ∃ (ψ : ℕ → ℕ) (E : Set ℝ), StrictMono ψ ∧ E.Countable ∧ ∀ s ∉ E, ∀ (Rj : ℕ → GeometricCurrentOn U k) (R : GeometricCurrentOn U k), (∀ j, IsRestriction (Xj (ψ j)) {x | x ∈ U ∧ φ x < s} (Rj j)) → IsRestriction X {x | x ∈ U ∧ φ x < s} R → (∀ ω : TestFormOn U k, tsupport (ω : DifferentialForm (Eucl P) k) ⊆ W → Tendsto (fun j => Rj j ω) atTop (𝓝 (R ω))) ∧ (∀ K : Set (Eucl P), IsCompact K → K ⊆ W → {x | x ∈ U ∧ φ x ≤ s} ⊆ K → WeaklyConvergesOn Rj R)) → ∀ (P m : ℕ) (U W : Set (Eucl P)) (Xk : ℕ → GeometricCurrentOn U (m + 1)) (X : GeometricCurrentOn U (m + 1)) (d : Eucl P → ℝ) (L : ℝ≥0) (a b : ℝ), IsOpen U → CompactlyContainedOpen W U → LipschitzWith L d → a < b → (∀ k, (Xk k).boundary = 0) → (∀ k V, CompactlyContainedOpen V U → (Xk k).massOn V < ∞) → (⨆ k, (Xk k).massOn W) < ∞ → WeaklyConvergesOn Xk X → ∃ (γ : ℝ) (κ : ℕ → ℕ) (Rk : ℕ → GeometricCurrentOn U (m + 1)) (G : ℝ≥0∞), γ ∈ Ioo a b ∧ StrictMono κ ∧ G < ∞ ∧ (∀ k, IsRestriction (Xk (κ k)) {x | x ∈ U ∧ d x < γ} (Rk k)) ∧ (∀ k, (Rk k).massOn W ≤ (Xk (κ k)).massOn W) ∧ (∀ k, (Rk k).boundary.massOn W ≤ G) ∧ ∀ R : GeometricCurrentOn U (m + 1), IsRestriction X {x | x ∈ U ∧ d x < γ} R → ∀ ω : TestFormOn U (m + 1), tsupport (ω : DifferentialForm (Eucl P) (m + 1)) ⊆ W → Tendsto (fun k => Rk k ω) atTop (𝓝 (R ω))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
