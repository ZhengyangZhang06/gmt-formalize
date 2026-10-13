# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.besicovitch_federer-a1.cone_trichotomy-a1.slab_to_cone-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-besicovitch-federer-a1-cone-trichotomy-a1-slab-to-cone-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.besicovitch_federer-a1.cone_trichotomy-a1`
- Child key: `slab_to_cone`
- Declaration: `Submission.bf_slabGood_imp_coneTrichotomy`
- Exact Lean type: `∀ (n ℓ : ℕ), 0 < n → 0 < ℓ → ∀ W : Submodule ℝ (Rn (n + ℓ)), finrank ℝ W = n → ∀ u : Fin ℓ → Rn (n + ℓ), Orthonormal ℝ u → (∀ j, u j ∈ Wᗮ) → ∀ (A : Set (Rn (n + ℓ))) (δ : ℝ) (a : Rn (n + ℓ)), (∀ j, ((∀ c : ℝ, 0 < c → ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s < ε → ∀ r : ℝ, 0 < r → r < δ → μHE[n] (A ∩ ({x | ‖(W ⊔ Submodule.span ℝ {u j}).starProjection (x - a) - inner ℝ ((W ⊔ Submodule.span ℝ {u j}).starProjection (x - a)) (u j) • u j‖ < s * ‖(W ⊔ Submodule.span ℝ {u j}).starProjection (x - a)‖} ∩ Metric.ball a r)) ≤ ENNReal.ofReal (c * (r * s) ^ n)) ∨ (∀ K : ℝ, ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 < s ∧ s < ε ∧ ∃ r : ℝ, 0 < r ∧ r < δ ∧ ENNReal.ofReal (K * (r * s) ^ n) ≤ μHE[n] (A ∩ ({x | ‖(W ⊔ Submodule.span ℝ {u j}).starProjection (x - a) - inner ℝ ((W ⊔ Submodule.span ℝ {u j}).starProjection (x - a)) (u j) • u j‖ < s * ‖(W ⊔ Submodule.span ℝ {u j}).starProjection (x - a)‖} ∩ Metric.ball a r))) ∨ ∃ b ∈ A, b ≠ a ∧ dist b a < δ ∧ (W ⊔ Submodule.span ℝ {u j}).starProjection (b - a) - inner ℝ ((W ⊔ Submodule.span ℝ {u j}).starProjection (b - a)) (u j) • u j = 0)) → ((∀ c : ℝ, 0 < c → ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s < ε → ∀ r : ℝ, 0 < r → r < δ → μHE[n] (A ∩ ({x | ‖W.starProjection (x - a)‖ < s * ‖x - a‖} ∩ Metric.ball a r)) ≤ ENNReal.ofReal (c * (r * s) ^ n)) ∨ (∀ K : ℝ, ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 < s ∧ s < ε ∧ ∃ r : ℝ, 0 < r ∧ r < δ ∧ ENNReal.ofReal (K * (r * s) ^ n) ≤ μHE[n] (A ∩ ({x | ‖W.starProjection (x - a)‖ < s * ‖x - a‖} ∩ Metric.ball a r))) ∨ ∃ b ∈ A, b ≠ a ∧ dist b a < δ ∧ W.starProjection (b - a) = 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
