# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_pushforward_im-a1.pushforward_integrality-a1.induced_orientation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-pushforward-integrality-a1-induced-o-eb73d1c7d5/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1`
- Child key: `induced_orientation`
- Declaration: `Submission.lpf_pi_induced_orientation`
- Exact Lean type: `((∀ (P n : ℕ) (v : Fin n → Eucl P), ‖simpleNVector v‖ ^ 2 = (Matrix.of fun i j => inner ℝ (v i) (v j)).det) ∧ ∀ (P n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (τ : Fin n → Eucl P), simpleNVector (fun i => ∑ j, B i j • τ j) = B.det • simpleNVector τ) → ∀ (P Q n : ℕ) (τ : Fin n → Eucl P) (A : Eucl P →L[ℝ] Eucl Q) (w : NVector (Eucl P) n), Orthonormal ℝ τ → (w = simpleNVector τ ∨ w = -simpleNVector τ) → nVectorPushforward n A w ≠ 0 → LinearIndependent ℝ (fun i => A (τ i)) ∧ ∃ σ : Fin n → Eucl Q, Orthonormal ℝ σ ∧ Submodule.span ℝ (range σ) = Submodule.span ℝ (range (fun i => A (τ i))) ∧ (nVectorPushforward n A w = ‖nVectorPushforward n A w‖ • simpleNVector σ ∨ nVectorPushforward n A w = -(‖nVectorPushforward n A w‖ • simpleNVector σ))`

## Sibling prerequisites

- `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1.simple_unit_facts-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
