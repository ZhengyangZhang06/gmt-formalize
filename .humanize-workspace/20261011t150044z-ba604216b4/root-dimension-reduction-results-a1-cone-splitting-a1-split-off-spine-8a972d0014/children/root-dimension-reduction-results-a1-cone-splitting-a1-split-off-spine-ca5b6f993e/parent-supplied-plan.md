# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.competitor_mass-a1.split_mass-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-ca5b6f993e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.competitor_mass-a1`
- Child key: `split_mass`
- Declaration: `Submission.dimred_cs_sos_mt_cm_split_mass`
- Exact Lean type: `∀ (P k m n : ℕ) (g : Fin k → Euclid P) (h : n = k + m) (S₀ S₀' : GeometricCurrentOn (univ : Set (Euclid P)) m) (R₀ R₀' : IMRep (univ : Set (Euclid P)) m) (S Z E' A₁ A₂ S' : GeometricCurrentOn (univ : Set (Euclid P)) n) (r : ℝ) (W : Set (Euclid P)), Orthonormal ℝ g → R₀.Represents S₀ → R₀'.Represents S₀' → R₀.measure ((Submodule.span ℝ (Set.range g))ᗮ : Set (Euclid P))ᶜ = 0 → R₀'.measure ((Submodule.span ℝ (Set.range g))ᗮ : Set (Euclid P))ᶜ = 0 → (∀ flat : Covector (Euclid P) n → Covector (Euclid P) m, (∀ (α : Covector (Euclid P) n) (v : Fin m → Euclid P), flat α v = α (Fin.append g v ∘ Fin.cast h)) → ∀ ω : TestFormOn (univ : Set (Euclid P)) n, S ω = ∫ t in (Submodule.span ℝ (Set.range g) : Set (Euclid P)), currentEval S₀ (fun y => flat ((ω : DifferentialForm (Euclid P) n) (t + y))) ∂μHE[k]) → (∀ flat : Covector (Euclid P) n → Covector (Euclid P) m, (∀ (α : Covector (Euclid P) n) (v : Fin m → Euclid P), flat α v = α (Fin.append g v ∘ Fin.cast h)) → ∀ ω : TestFormOn (univ : Set (Euclid P)) n, Z ω = (∫ t in {t | t ∈ Submodule.span ℝ (Set.range g) ∧ ∀ i, |inner ℝ (g i) t| ≤ r}, currentEval (S₀' - S₀) (fun y => flat ((ω : DifferentialForm (Euclid P) n) (t + y))) ∂μHE[k]) + E' ω) → (∀ flat : Covector (Euclid P) n → Covector (Euclid P) m, (∀ (α : Covector (Euclid P) n) (v : Fin m → Euclid P), flat α v = α (Fin.append g v ∘ Fin.cast h)) → ∀ ω : TestFormOn (univ : Set (Euclid P)) n, A₁ ω = ∫ t in (Submodule.span ℝ (Set.range g) : Set (Euclid P)) \ {t | t ∈ Submodule.span ℝ (Set.range g) ∧ ∀ i, |inner ℝ (g i) t| ≤ r}, currentEval S₀ (fun y => flat ((ω : DifferentialForm (Euclid P) n) (t + y))) ∂μHE[k]) → (∀ flat : Covector (Euclid P) n → Covector (Euclid P) m, (∀ (α : Covector (Euclid P) n) (v : Fin m → Euclid P), flat α v = α (Fin.append g v ∘ Fin.cast h)) → ∀ ω : TestFormOn (univ : Set (Euclid P)) n, A₂ ω = ∫ t in {t | t ∈ Submodule.span ℝ (Set.range g) ∧ ∀ i, |inner ℝ (g i) t| ≤ r}, currentEval S₀' (fun y => flat ((ω : DifferentialForm (Euclid P) n) (t + y))) ∂μHE[k]) → (∀ ω : TestFormOn (univ : Set (Euclid P)) n, S' ω = S ω + Z ω) → S'.massOn W ≤ A₁.massOn W + A₂.massOn W + E'.mass`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
