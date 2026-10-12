# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.graph_c1-a1.campanato_continuous-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-b60df69aaa/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.graph_c1-a1`
- Child key: `campanato_continuous`
- Declaration: `Submission.dorag_gc_campanato_continuous_deriv`
- Exact Lean type: `∀ (n k : ℕ) (f : Euclid n → Euclid k) (Ω : Set (Euclid n)) (C s₁ : ℝ), 0 < n → IsOpen Ω → 0 ≤ C → 0 < s₁ → (∀ᵐ v ∂volume, v ∈ Ω → DifferentiableAt ℝ f v ∧ ∀ s : ℝ, 0 < s → s ≤ s₁ → ∫⁻ w in ball v s, ENNReal.ofReal (∑ i : Fin n, ‖(fderiv ℝ f w - fderiv ℝ f v) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ≤ ENNReal.ofReal (C * s ^ (n + 1))) → ∃ g : Euclid n → (Euclid n →L[ℝ] Euclid k), ContinuousOn g Ω ∧ ∀ᵐ v ∂volume, v ∈ Ω → HasFDerivAt f (g v) v`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
