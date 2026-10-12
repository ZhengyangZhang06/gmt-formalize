# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.besicovitch_federer-a1.cone_trichotomy-a1.slab_to_cone-a1.trichotomy_transfer-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-besicovitch-federer-a1-cone-trichotomy-a1-slab-to-cone-a1-tricho-60da978f98/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.besicovitch_federer-a1.cone_trichotomy-a1.slab_to_cone-a1`
- Child key: `trichotomy_transfer`
- Declaration: `Submission.bf_coneTrichotomy_of_slabCover`
- Exact Lean type: `∀ (N n : ℕ) (ι : Type) [Fintype ι] [Nonempty ι] (μ : Measure (Rn N)) (A : Set (Rn N)) (δ κ : ℝ) (a : Rn N) (X : ℝ → Set (Rn N)) (Z : ι → ℝ → Set (Rn N)) (Ax : Prop) (Ax' : ι → Prop), 0 < κ → (∀ j (s : ℝ), 0 < s → Z j s ⊆ X s) → (∀ s : ℝ, 0 < s → X s ⊆ ⋃ j, Z j (κ * s)) → (∀ j, Ax' j → Ax) → (∀ j, ((∀ c : ℝ, 0 < c → ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s < ε → ∀ r : ℝ, 0 < r → r < δ → μ (A ∩ (Z j s ∩ Metric.ball a r)) ≤ ENNReal.ofReal (c * (r * s) ^ n)) ∨ (∀ K : ℝ, ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 < s ∧ s < ε ∧ ∃ r : ℝ, 0 < r ∧ r < δ ∧ ENNReal.ofReal (K * (r * s) ^ n) ≤ μ (A ∩ (Z j s ∩ Metric.ball a r))) ∨ Ax' j)) → ((∀ c : ℝ, 0 < c → ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s < ε → ∀ r : ℝ, 0 < r → r < δ → μ (A ∩ (X s ∩ Metric.ball a r)) ≤ ENNReal.ofReal (c * (r * s) ^ n)) ∨ (∀ K : ℝ, ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 < s ∧ s < ε ∧ ∃ r : ℝ, 0 < r ∧ r < δ ∧ ENNReal.ofReal (K * (r * s) ^ n) ≤ μ (A ∩ (X s ∩ Metric.ball a r))) ∨ Ax)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
