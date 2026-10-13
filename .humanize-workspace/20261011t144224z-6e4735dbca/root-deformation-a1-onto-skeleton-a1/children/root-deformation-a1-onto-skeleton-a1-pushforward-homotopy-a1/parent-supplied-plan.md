# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.onto_skeleton-a1`
- Child key: `pushforward_homotopy`
- Declaration: `Submission.deformation_pushforward_homotopy`
- Exact Lean type: `(∀ (P Q k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl P)) k) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) k), IsRectifiableTriple (univ : Set (Eucl P)) k M θ ξ → (∀ x ∈ M, ∃ j : ℕ, θ x = j) → (∀ ω : TestFormOn (univ : Set (Eucl P)) k, X ω = tauAction k M θ ξ ω) → ∀ (g : Eucl P → Eucl Q) (Λ : ℝ≥0), LipschitzWith Λ g → (∀ K : Set (Eucl Q), IsCompact K → IsCompact (g ⁻¹' K ∩ X.support)) → ∃ S : GeometricCurrentOn (univ : Set (Eucl Q)) k, IsLipschitzPushforward X g S ∧ IsIntegerMultiplicity S ∧ ∀ (gj : ℕ → Eucl P → Eucl Q) (Λ' : ℝ≥0), (∀ j, ContDiff ℝ 1 (gj j)) → (∀ j, LipschitzWith Λ' (gj j)) → TendstoUniformly gj g atTop → ∀ ω : TestFormOn (univ : Set (Eucl Q)) k, Tendsto (fun j => ∫ x in M, θ x * nVectorPushforward k (fderiv ℝ (gj j) x) (ξ x) ((ω : DifferentialForm (Eucl Q) k) (gj j x)) ∂(μHE[k] : Measure (Eucl P))) atTop (𝓝 (S ω))) → ∀ D : ℕ, ∃ c : ℕ → ℝ≥0, ∀ f : Eucl D → Eucl D, ∃ (Pf : (k : ℕ) → GeometricCurrentOn (univ : Set (Eucl D)) k → GeometricCurrentOn (univ : Set (Eucl D)) k) (Hf : (k : ℕ) → GeometricCurrentOn (univ : Set (Eucl D)) k → GeometricCurrentOn (univ : Set (Eucl D)) (k + 1)), (∀ (k : ℕ) (E : Set (Eucl D)) (Λ : ℝ≥0) (δ b : ℝ) (X : GeometricCurrentOn (univ : Set (Eucl D)) k), IsClosed E → 0 < δ → LipschitzOnWith Λ f (thickening δ E) → (∀ x ∈ E, dist (f x) x ≤ b) → X.mass < ∞ → (∀ (j : ℕ) (Y : GeometricCurrentOn (univ : Set (Eucl D)) (j + 1)), k = j + 1 → HEq Y X → Y.boundary.mass < ∞) → X.support ⊆ E → (Pf k X).mass ≤ (c k : ℝ≥0∞) * (Λ : ℝ≥0∞) ^ k * X.mass ∧ (Hf k X).mass ≤ (c k : ℝ≥0∞) * ENNReal.ofReal b * (1 + (Λ : ℝ≥0∞)) ^ k * X.mass ∧ (Pf k X).support ⊆ closure (f '' X.support) ∧ (Hf k X).support ⊆ cthickening b X.support ∧ (IsIntegerMultiplicity X → IsIntegerMultiplicity (Pf k X) ∧ IsIntegerMultiplicity (Hf k X)) ∧ (∀ (α : SimonMultiIndex k D) (z : Eucl D) (ω : TestFormOn (univ : Set (Eucl D)) k) (ε : ℝ), 0 < ε → (∀ x ∈ thickening ε X.support, f x ∈ thickening ε (tsupport (ω : DifferentialForm (Eucl D) k)) → ∀ i, i ∉ range α → f x i = z i) → (∀ y, (ω : DifferentialForm (Eucl D) k) y (fun j => EuclideanSpace.single (α j) (1 : ℝ)) = 0) → Pf k X ω = 0) ∧ ∀ (X₁ X₂ : GeometricCurrentOn (univ : Set (Eucl D)) k) (a a₁ : ℝ), X₁.mass < ∞ → (∀ (j : ℕ) (Y : GeometricCurrentOn (univ : Set (Eucl D)) (j + 1)), k = j + 1 → HEq Y X₁ → Y.boundary.mass < ∞) → X₁.support ⊆ E → (∀ ω, X₂ ω = a * X ω + a₁ * X₁ ω) → (∀ ω, Pf k X₂ ω = a * Pf k X ω + a₁ * Pf k X₁ ω) ∧ ∀ ω, Hf k X₂ ω = a * Hf k X ω + a₁ * Hf k X₁ ω) ∧ ∀ (j : ℕ) (E : Set (Eucl D)) (Λ : ℝ≥0) (δ b : ℝ) (X : GeometricCurrentOn (univ : Set (Eucl D)) (j + 1)), IsClosed E → 0 < δ → LipschitzOnWith Λ f (thickening δ E) → (∀ x ∈ E, dist (f x) x ≤ b) → X.mass < ∞ → X.boundary.mass < ∞ → X.support ⊆ E → (Pf (j + 1) X).boundary = Pf j X.boundary ∧ ∀ ω, X ω - Pf (j + 1) X ω = (Hf (j + 1) X).boundary ω + Hf j X.boundary ω`

## Sibling prerequisites

- `root.compactness_mass_bounds-a1.mass_bound-a1`
- `root.isoperimetric-a1.vanish_off_support-a1`
- `root.integrality_weak_limits-a1.cycle_reduction-a1.support_lemmas-a1`
- `root.lipschitz_pushforward_im-a1.rectifiable_support_null-a1`
- `root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1.local_lipschitz_area-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
