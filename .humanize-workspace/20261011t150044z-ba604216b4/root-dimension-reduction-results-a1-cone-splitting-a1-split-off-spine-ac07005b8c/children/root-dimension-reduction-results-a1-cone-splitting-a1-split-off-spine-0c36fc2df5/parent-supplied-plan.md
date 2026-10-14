# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.spine_coarea-a1.coarea_of_pieces-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-0c36fc2df5/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.spine_coarea-a1`
- Child key: `coarea_of_pieces`
- Declaration: `Submission.dimred_cs_sos_sc_coarea_of_pieces`
- Exact Lean type: `∀ (P n : ℕ) (L : Submodule ℝ (Euclid P)) (M : Set (Euclid P)), Module.finrank ℝ L < n → MeasurableSet M → (∃ (F : ℕ → Euclid n → Euclid P) (B : ℕ → Set (Euclid n)) (m : ℕ → ℝ), (∀ i, ∃ K : NNReal, LipschitzWith K (F i)) ∧ (∀ i, MeasurableSet (B i)) ∧ (∀ i, 0 < m i) ∧ (∀ i, ∀ a ∈ B i, ∀ a' ∈ B i, m i * ‖a - a'‖ ≤ ‖F i a - F i a'‖) ∧ (∀ i, ∀ a ∈ B i, DifferentiableAt ℝ (F i) a ∧ Injective (fderiv ℝ (F i) a)) ∧ (∀ i, MeasurableSet (F i '' B i)) ∧ (∀ i, F i '' B i ⊆ M) ∧ Pairwise (fun i j => Disjoint (F i '' B i) (F j '' B j)) ∧ μHE[n] (M \ ⋃ i, F i '' B i) = 0) → (∀ K : Set (Euclid P), IsCompact K → μHE[n] (M ∩ K) ≠ ∞) → (∀ᵐ x ∂(μHE[n].restrict M), ∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ∧ L ≤ Q) → (∀ᵐ t ∂(μHE[Module.finrank ℝ L].restrict (L : Set (Euclid P))), CountablyRectifiable (n - Module.finrank ℝ L) (M ∩ {x | L.starProjection x = t}) ∧ ∀ᵐ x ∂(μHE[n - Module.finrank ℝ L].restrict (M ∩ {x | L.starProjection x = t})), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q → HasApproximateTangentSpaceAt (n - Module.finrank ℝ L) (M ∩ {x | L.starProjection x = t}) x (Q ⊓ Lᗮ)) ∧ ∀ g : Euclid P → ℝ≥0∞, Measurable g → AEMeasurable (fun t => ∫⁻ x in M ∩ {x | L.starProjection x = t}, g x ∂μHE[n - Module.finrank ℝ L]) (μHE[Module.finrank ℝ L].restrict (L : Set (Euclid P))) ∧ ∫⁻ x in M, g x ∂μHE[n] = ∫⁻ t in (L : Set (Euclid P)), ∫⁻ x in M ∩ {x | L.starProjection x = t}, g x ∂μHE[n - Module.finrank ℝ L] ∂μHE[Module.finrank ℝ L]`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.piece_tangent_density-a1.piece_pullback-a1`
- `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.image_tangent_transport-a1.ae_transfer-a1`
- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_splitting-a1.split_off_spine-a1.lipschitz_tangent-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
