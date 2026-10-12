# Parent-supplied natural-language proof

- Parent DAG node: `root.coarea_and_slices-a1.c1_level_slices_rectifiable-a1`
- Child DAG node: `root.coarea_and_slices-a1.c1_level_slices_rectifiable-a1.null_image-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the parent's supplied proof, step 3 (critical part): "ψ is locally Lipschitz on D (... by the mean value inequality; countably many ... cover D), so Hᵏ(ψ(...)) ≤ Σ_b Lip_bᵏ·Hᵏ(... ∩ b) = 0 (SimonGMT euclideanHausdorffMeasure_image_le_of_lipschitzOn)". It is extracted here as a standalone lemma about an arbitrary Hᵏ-null set Z ⊆ D. Background: the Lipschitz image inequality H^s(f(A)) ≤ Lip(f)^s·H^s(A) (Simon Ch. 2, Theorem 1.8(i), chapter-02.txt lines 270–286; Federer 2.10.11). Simon states it for an Hᵐ-measurable A of finite measure, but the covering argument in the first lines of his proof of (i) proves the inequality for an arbitrary A. That is the form used here, and it is SimonGMT's euclideanHausdorffMeasure_image_le_of_lipschitzOn, which has no measurability hypothesis.

Notation: ℝ^d = Rn d = EuclideanSpace ℝ (Fin d); Hᵏ = μHE[k], the k-dimensional Euclidean Hausdorff measure. Applied to arbitrary sets it is an outer measure, hence monotone and countably subadditive on all subsets. No measurability of Z, no finiteness, and no relation between k and n is needed.

1. (Local Lipschitz neighbourhoods.) Let u ∈ D. D is open and ψ is C¹ on D, so ψ is C¹ at u. By the mean value inequality (‖Dψ‖ is bounded near u; Mathlib ContDiffAt.exists_lipschitzOnWith), there are K_u ≥ 0 and a neighbourhood of u on which ψ is K_u-Lipschitz. Shrinking that neighbourhood, choose an open set t_u with u ∈ t_u on which ψ is K_u-Lipschitz.

2. (Countable subcover.) The sets t_u (u ∈ D) are open, and ℝⁿ is second countable. So there is a countable T ⊆ D with ⋃_{u∈T} t_u = ⋃_{u∈D} t_u (TopologicalSpace.isOpen_iUnion_countable, indexed by the subtype D). Since Z ⊆ D ⊆ ⋃_{u∈D} t_u, we get Z ⊆ ⋃_{u∈T} t_u, and hence ψ(Z) ⊆ ⋃_{u∈T} ψ(Z ∩ t_u).

3. (Each piece is null.) Fix u ∈ T. ψ is K_u-Lipschitz on Z ∩ t_u ⊆ t_u. The Lipschitz image inequality for Euclidean Hausdorff outer measure holds for arbitrary sets: a cover of Z ∩ t_u by sets C_i of diameter ≤ δ gives a cover of ψ(Z ∩ t_u) by the sets ψ(C_i ∩ Z ∩ t_u), of diameter ≤ K_u·diam C_i ≤ K_u·δ (SimonGMT Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn). It yields Hᵏ(ψ(Z ∩ t_u)) ≤ K_uᵏ·Hᵏ(Z ∩ t_u). By monotonicity Hᵏ(Z ∩ t_u) ≤ Hᵏ(Z) = 0, so Hᵏ(ψ(Z ∩ t_u)) ≤ K_uᵏ·0 = 0.

4. (Countable subadditivity.) T is countable, so Hᵏ(⋃_{u∈T} ψ(Z ∩ t_u)) ≤ Σ_{u∈T} Hᵏ(ψ(Z ∩ t_u)) = 0 (measure_biUnion_null_iff). By monotonicity and step 2, Hᵏ(ψ(Z)) = 0. ∎

Appendix: a complete Lean proof of exactly this statement. It was checked on the pinned toolchain lean 4.35.0-rc3 / Mathlib 25730c7c with only `import GMT.Ch03.Submission`, in the comparator's replayed Contract scope. It has no warnings and depends only on [propext, Classical.choice, Quot.sound]. Place it in GMT/Ch03/Submission.lean inside `namespace GMT.Ch03`, after the frozen definitions.

```lean
theorem Submission.contDiffOn_image_euclideanHausdorff_null : ∀ (n N k : ℕ) (D Z : Set (Rn n)) (ψ : Rn n → Rn N), IsOpen D → ContDiffOn ℝ 1 ψ D → Z ⊆ D → μHE[k] Z = 0 → μHE[k] (ψ '' Z) = 0 := by
  intro n N k D Z ψ hD hψ hZD hZ
  -- local Lipschitz neighbourhoods
  have hloc : ∀ u : D, ∃ K : ℝ≥0, ∃ t : Set (Rn n), IsOpen t ∧ (u : Rn n) ∈ t ∧ LipschitzOnWith K ψ t := by
    intro u
    obtain ⟨K, t, ht, hKt⟩ := (hψ.contDiffAt (hD.mem_nhds u.2)).exists_lipschitzOnWith
    obtain ⟨t', ht't, ht'o, hut'⟩ := mem_nhds_iff.mp ht
    exact ⟨K, t', ht'o, hut', hKt.mono ht't⟩
  choose K t ht hut hKt using hloc
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable t ht
  have hcover : Z ⊆ ⋃ i ∈ T, t i := by
    intro z hz
    rw [hTU]
    exact mem_iUnion.2 ⟨⟨z, hZD hz⟩, hut _⟩
  have himg : ψ '' Z ⊆ ⋃ i ∈ T, ψ '' (Z ∩ t i) := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨i, hiT, hzi⟩ := mem_iUnion₂.1 (hcover hz)
    exact mem_iUnion₂.2 ⟨i, hiT, ⟨z, ⟨hz, hzi⟩, rfl⟩⟩
  refine measure_mono_null himg ((measure_biUnion_null_iff hTc).2 fun i _ => ?_)
  refine le_antisymm ?_ bot_le
  calc μHE[k] (ψ '' (Z ∩ t i)) ≤ (K i : ℝ≥0∞) ^ k * μHE[k] (Z ∩ t i) :=
        Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn k
          ((hKt i).mono inter_subset_right)
    _ = 0 := by rw [measure_mono_null inter_subset_left hZ, mul_zero]
```

## Key steps

1. Each u ∈ D has an open neighbourhood t_u on which ψ is K_u-Lipschitz (ψ is C¹ at u; mean value inequality).
2. Lindelöf (second countability of ℝⁿ): countably many t_u (u ∈ T) cover Z, so ψ(Z) ⊆ ⋃_{u∈T} ψ(Z ∩ t_u).
3. Lipschitz image bound for arbitrary sets: Hᵏ(ψ(Z ∩ t_u)) ≤ K_uᵏ·Hᵏ(Z ∩ t_u) ≤ K_uᵏ·Hᵏ(Z) = 0.
4. Countable subadditivity and monotonicity of the outer measure Hᵏ give Hᵏ(ψ(Z)) = 0.

## Reference use

### local-project

Queries:
- `rg -n "theorem isOpen_iUnion_countable" mathlib/Mathlib/Topology/Bases.lean`
- `rg -n "theorem ContDiffAt.exists_lipschitzOnWith |lemma ContDiffOn.locallyLipschitzOn" mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `rg -n "theorem OpenPartialHomeomorph.contDiffAt_symm " mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `rg -n "protected theorem ContinuousLinearEquiv.isOpen" mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `rg -n "def toOpenPartialHomeomorph|theorem mem_toOpenPartialHomeomorph_source|theorem toOpenPartialHomeomorph_coe" mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `grep -n "theorem\|def \|lemma" mathlib/Mathlib/Analysis/Calculus/Implicit.lean`
- `rg -n "theorem finrank_range_add_finrank_ker|noncomputable def linearEquivOfInjective" mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`
- `rg -n "theorem FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq" mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `rg -n "theorem orthogonalProjectionOnto_mem_subspace_eq_self|def orthogonalProjectionOnto" mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `rg -l -i "countablyRectifiable" mathlib/Mathlib/MeasureTheory mathlib/Mathlib/Geometry mathlib/Mathlib/Analysis/Calculus  (no match)`
- `rg -n "hausdorffMeasure_image_null|image_null_of_locallyLipschitz|LocallyLipschitzOn.hausdorffMeasure" mathlib/Mathlib/MeasureTheory mathlib/Mathlib/Topology/MetricSpace  (no match)`
- `rg -n "theorem hausdorffMeasure_image_le \(h : LipschitzOnWith" mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean; rg -n 'notation "μHE\["' mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n "^open|^namespace|^abbrev Rn|^def SlicesAreRectifiable" project/GMT/Ch03/Contract.lean; rg -n "^import" project/GMT/Ch03/Contract.lean`
- `rg -n "^theorem countablyRectifiable_image_contDiffOn_open|^theorem countablyRectifiable_sUnion|^theorem countablyRectifiable_iUnion|^theorem countablyRectifiable_of_measure_zero|^theorem CountablyRectifiable.mono|^theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn" <pinned simongmt>/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean Chapter03/Rectifiable.lean Chapter02/Lipschitz.lean`
- `cmp GMT/Ch03/Submission.lean GMT/Ch03/Contract.lean; cmp GMT/Ch03/Contract.lean <snapshot>/project/GMT/Ch03/Contract.lean (both identical)`
- `lean Avail.lean / Avail2.lean: #check of the IFT, Lipschitz, Lindelöf and SimonGMT lemmas after only `import GMT.Ch03.Submission``
- `python3 -I: gmt-compare.py child_modules(contract mode) + lean_contract.validate_lean_statement on both child types, then `lean` on the generated NodeChallenge files`
- `lean /tmp/c1slices-decomp/Integration.lean (full child proofs + sibling stub + parent assembly + `exact Submission.X` comparator checks; #print axioms)`
- `python3 -I dag.json lean_name uniqueness (113 nodes) + grep of both names in all branches' GMT/Ch03/Submission.lean, simongmt and Mathlib (no match)`
- `sed -n 1440,1500p book/chapter-02.txt (Simon 6.2-6.4); sed -n 425,445p book/chapter-03.txt (Remark 2.10(2)); sed -n 268,290p book/chapter-02.txt (Thm 1.8)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/Implicit.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`

Snapshot: project d09bc8a, Mathlib 25730c7c, plus the pinned simongmt package. The workspace Submission.lean and Contract.lean are byte-identical to the snapshot Contract.

No-match results:
- Mathlib has no countable-rectifiability notion; rg 'countablyRectifiable' finds nothing in MeasureTheory, Geometry or Analysis/Calculus.
- Mathlib has no lemma 'locally Lipschitz images of Hausdorff-null sets are null'.
- Mathlib has no regular-level-set rectifiability result.

Available after only `import GMT.Ch03.Submission`, verified by #check:
- Inverse function theorem: HasStrictFDerivAt.toOpenPartialHomeomorph (+ mem_toOpenPartialHomeomorph_source), ContDiffAt.hasStrictFDerivAt', OpenPartialHomeomorph.contDiffAt_symm, ContinuousLinearEquiv.isOpen.
- Lindelöf: TopologicalSpace.isOpen_iUnion_countable.
- Lipschitz: ContDiffAt.exists_lipschitzOnWith, LipschitzOnWith.extend_finite_dimension, LocallyLipschitzOn.exists_lipschitzOnWith_of_compact.
- Linear algebra: LinearMap.finrank_range_add_finrank_ker, LinearMap.linearEquivOfInjective, FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self.
- SimonGMT: countablyRectifiable_range / _iUnion / _sUnion / _of_measure_zero, CountablyRectifiable.mono, Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn.

Not reachable without a new import:
- ContDiffAt.toOpenPartialHomeomorph.
- HasStrictFDerivAt.implicitToOpenPartialHomeomorph.
- SimonGMT Chapter03.countablyRectifiable_image_contDiffOn_open, which is in SubmanifoldCover. Child A therefore inlines its 25-line proof.

Both child types elaborate in the comparator's replayed Contract scope. Both have complete, warning-free Lean proofs using only standard axioms. The selected frozen type follows from them plus a stub of the frozen sibling type, which is the only sorryAx.

Simon Ch. 2 6.3–6.4 (chapter-02.txt lines 1476–1497) and Ch. 3 Remark 2.10(2) (chapter-03.txt lines 439–442) give exactly the regular-part / critical-part structure used.
