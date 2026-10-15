# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.threshold_reduction-a1.iterated_blowup_limit-a1.diagonal_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1-iterated-b-1feeb48ffd/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.threshold_reduction-a1.iterated_blowup_limit-a1`
- Child key: `diagonal_limit`
- Declaration: `Submission.dimred_tr_ibl_diagonal_limit`
- Exact Lean type: `∀ (P n : ℕ) (Vs : ℕ → ℕ → Set (Euclid P)) (As : (k i : ℕ) → GeometricCurrentOn (Vs k i) n) (Ws : ℕ → Set (Euclid P)) (Zs : (k : ℕ) → GeometricCurrentOn (Ws k) n) (C : GeometricCurrentOn (univ : Set (Euclid P)) n), (∀ (k : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) n), Tendsto (fun i => currentEval (As k i) (ω : DifferentialForm (Euclid P) n)) atTop (𝓝 (currentEval (Zs k) (ω : DifferentialForm (Euclid P) n)))) → ConvergesWeakly Zs C → (∀ R : ℕ, ∃ (k₀ : ℕ) (Γ : ℝ≥0∞), Γ ≠ ∞ ∧ C.massOn (ball 0 ((R : ℝ) + 1)) ≤ Γ ∧ ∀ k, k₀ ≤ k → ∀ᶠ i in atTop, ball (0 : Euclid P) ((R : ℝ) + 1) ⊆ Vs k i ∧ (As k i).massOn (ball 0 ((R : ℝ) + 1)) ≤ Γ) → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ConvergesWeakly (fun k => As k (φ k)) C`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.threshold_reduction-a1.iterated_blowup_limit-a1.countable_tests-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
