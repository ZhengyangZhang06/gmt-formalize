# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.face_replacement-a1.face_geometry-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-5d7afa5709/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.face_replacement-a1`
- Child key: `face_geometry`
- Declaration: `Submission.dor_lmb_fcd_fr_face_geometry`
- Exact Lean type: `∀ (P m : ℕ) (p : (Fin P → ℤ) × (Fin (m + 1) → Fin P)), StrictMono p.2 → volume {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} = 1 ∧ μHE[m + 1] {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)} = 1 ∧ (μHE[m + 1] : Measure (Euclid P)).restrict {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)} = Measure.map (fun y : Euclid (m + 1) => WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ)) (volume.restrict {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}) ∧ (∀ f : Euclid P → ℝ, ∫ x in {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)}, f x ∂μHE[m + 1] = ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, f (WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ))) ∧ (∀ y : Euclid (m + 1), (∀ i, 0 ≤ y i ∧ y i ≤ 1) → WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ) ∈ {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)}) ∧ (∀ y y' : Euclid (m + 1), dist (WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (p.2 j) (1 : ℝ)) = dist y y') ∧ (∀ x ∈ {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)}, ∀ x' ∈ {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)}, dist x x' ≤ Real.sqrt P) ∧ IsClosed {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)} ∧ ∀ q : (Fin P → ℤ) × (Fin (m + 1) → Fin P), StrictMono q.2 → q ≠ p → ∀ y : Euclid (m + 1), (∀ i, 0 < y i ∧ y i < 1) → WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ) ∉ {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range q.2 → (q.1 i : ℝ) ≤ x i ∧ x i ≤ q.1 i + 1) ∧ (i ∉ Set.range q.2 → x i = q.1 i)}`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
