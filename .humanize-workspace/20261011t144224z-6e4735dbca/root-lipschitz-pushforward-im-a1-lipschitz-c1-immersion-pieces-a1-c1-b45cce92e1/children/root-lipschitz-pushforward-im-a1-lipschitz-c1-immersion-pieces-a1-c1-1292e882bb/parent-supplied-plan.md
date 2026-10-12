# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1.c1_approximation_real-a1.egoroff_closed-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1-c1-1292e882bb/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1.c1_approximation_real-a1`
- Child key: `egoroff_closed`
- Declaration: `Submission.lpf_c1r_egoroff_closed`
- Exact Lean type: `∀ (n : ℕ) (C : Set (Eucl n)) (f : ℕ → Eucl n → ℝ) (g : Eucl n → ℝ), MeasurableSet C → (∀ k, Measurable (f k)) → Measurable g → (∀ x ∈ C, Tendsto (fun k => f k x) atTop (𝓝 (g x))) → ∀ ε : ℝ≥0∞, 0 < ε → ∃ A : Set (Eucl n), IsClosed A ∧ A ⊆ C ∧ (volume : Measure (Eucl n)) (C \ A) < ε ∧ ∀ R : ℝ, TendstoUniformlyOn f g atTop (A ∩ closedBall 0 R)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
