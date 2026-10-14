# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.planar_constancy-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.planar_constancy-a1.plane_test_extension-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 6 of the parent-supplied proof, construction of the ambient test function: "Since ι(spt ψ) is a compact subset of the open set V, there is δ > 0 with {y ∈ ℝ^P : ι^*(y) ∈ spt ψ, |y − p_Q(y)| ≤ δ} ⊆ V, where ι^*(y) := (⟨y, τ_1⟩, …, ⟨y, τ_n⟩) and p_Q is the orthogonal projection onto Q. With χ ∈ C^∞_c(ℝ^P), χ = 1 near 0, spt χ ⊆ B_δ(0), put f(y) := ψ(ι^*(y))·χ(y − p_Q(y)): f ∈ C^∞_c(V), f(ι(s)) = ψ(s) and D_{τ_i}f(ι(s)) = ∂_iψ(s)". Notation: ‖·‖ is the Euclidean norm; B(0, ρ), B̄(0, ρ) are open and closed balls; cthickening δ A := {y : inf_{a∈A}‖y − a‖ ≤ δ}.
1. (Linear maps.) ι is linear and ‖ι(s)‖ = ‖s‖ (orthonormality: ‖Σ s_iτ_i‖² = Σ s_i²). Let ι* : ℝ^P → ℝ^n, ι*(y) := (⟨τ_1, y⟩, …, ⟨τ_n, y⟩), a continuous linear map; let p := ι∘ι* (the orthogonal projection onto Q = span{τ_i}) and q := id − p, both continuous linear. By orthonormality, ι*(ι(s)) = s (⟨τ_k, Σ_i s_iτ_i⟩ = s_k) and ι*(τ_j) = e_j; consequently q(ι(s)) = ι(s) − ι(ι*(ι(s))) = 0, and every y satisfies y = p(y) + q(y) with ‖p(y)‖ = ‖ι*(y)‖.
2. (Margin.) K := tsupport ψ is compact (ψ has compact support) and K ⊆ Ω, so ι(K) is compact (ι continuous) and ι(K) ⊆ V. Since V is open, there is δ > 0 with cthickening δ (ι(K)) ⊆ V (IsCompact.exists_cthickening_subset_open). Let R ≥ 0 with K ⊆ B̄(0, R) (K is bounded).
3. (Cutoff.) Let χ : ℝ^P → ℝ be a smooth bump function centred at 0 with inner radius δ/2 and outer radius δ (Mathlib ContDiffBump with rIn = δ/2 < rOut = δ): χ is C^∞, χ = 1 on B̄(0, δ/2) (ContDiffBump.one_of_mem_closedBall), and the support of χ is B(0, δ) (ContDiffBump.support_eq).
4. (Definition.) f(y) := ψ(ι*(y))·χ(q(y)). f is C^∞: ψ∘ι* and χ∘q are compositions of C^∞ functions with continuous linear maps, and products of C^∞ functions are C^∞.
5. (Support.) If f(y) ≠ 0 then ψ(ι*(y)) ≠ 0, so ι*(y) ∈ K, and χ(q(y)) ≠ 0, so ‖q(y)‖ < δ. Hence support f ⊆ A := {y : ι*(y) ∈ K and ‖q(y)‖ ≤ δ}. A is closed (K is closed; ι*, q and the norm are continuous), so tsupport f ⊆ A. A is bounded: for y ∈ A, ‖y‖ ≤ ‖p(y)‖ + ‖q(y)‖ = ‖ι*(y)‖ + ‖q(y)‖ ≤ R + δ. So A is compact (closed and bounded in ℝ^P) and f has compact support (HasCompactSupport.of_support_subset_isCompact). For y ∈ A, p(y) = ι(ι*(y)) ∈ ι(K) and ‖y − p(y)‖ = ‖q(y)‖ ≤ δ, so y ∈ cthickening δ (ι(K)) ⊆ V. Hence tsupport f ⊆ A ⊆ V.
6. (Values on Q.) For s ∈ ℝ^n: ι*(ι(s)) = s and q(ι(s)) = 0, so f(ι(s)) = ψ(s)·χ(0) = ψ(s) (0 ∈ B̄(0, δ/2)).
7. (Derivatives on Q.) Fix s ∈ ℝ^n. Since q is continuous and q(ι(s)) = 0, the set N := {y : q(y) ∈ B̄(0, δ/2)} is a neighbourhood of ι(s), and on N, χ(q(y)) = 1, so f = ψ∘ι* on N. Functions that agree near a point have the same derivative there (Filter.EventuallyEq.fderiv_eq), so by the chain rule Df(ι(s)) = D(ψ∘ι*)(ι(s)) = Dψ(ι*(ι(s)))∘ι* = Dψ(s)∘ι*. Therefore Df(ι(s))(τ_j) = Dψ(s)(ι*(τ_j)) = Dψ(s)(e_j) for every j (step 1). ∎

Formalization note (verified during the decomposition check; not part of the mathematical argument). The following single theorem proves exactly this frozen statement. It was compiled with `lake env lean` (Lean v4.35.0-rc3, Mathlib 25730c7c, SimonGMT 2b36630) after `import GMT.Ch07.Submission` only, inside `namespace GMT.Ch07` with the contract opens. It uses no sibling declaration, no import and no helper declaration; `#print axioms` gives exactly propext, Classical.choice and Quot.sound. It follows the numbered steps above and may be used directly as the leaf candidate:
```lean
theorem Submission.idtp_pc_plane_test_extension : ∀ (P n : ℕ) (V : Set (Euclid P)) (τ : Fin n → Euclid P) (ψ : Euclid n → ℝ), IsOpen V → Orthonormal ℝ τ → ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ {s : Euclid n | ∑ i, s i • τ i ∈ V} → ∃ f : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧ tsupport f ⊆ V ∧ ∀ s : Euclid n, f (∑ i, s i • τ i) = ψ s ∧ ∀ j : Fin n, fderiv ℝ f (∑ i, s i • τ i) (τ j) = fderiv ℝ ψ s (EuclideanSpace.single j (1 : ℝ)) := by
  intro P n V τ ψ hV hτ hψ hψc hψΩ
  -- the parametrization L and its left inverse Ls
  let L₀ : Euclid n →ₗ[ℝ] Euclid P :=
    { toFun := fun s => ∑ i, s i • τ i
      map_add' := fun s t => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c s => by simp [Finset.smul_sum, smul_smul] }
  let L : Euclid n →L[ℝ] Euclid P := LinearMap.toContinuousLinearMap L₀
  have hLapp : ∀ s, L s = ∑ i, s i • τ i := fun s => rfl
  have hnorm : ∀ s, ‖L s‖ = ‖s‖ := by
    intro s
    have h1 : ‖L s‖ ^ 2 = ‖s‖ ^ 2 := by
      rw [hLapp, ← real_inner_self_eq_norm_sq, hτ.inner_sum, EuclideanSpace.norm_eq,
        Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
      simp [sq]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h1
  let Ls₀ : Euclid P →ₗ[ℝ] Euclid n :=
    { toFun := fun y => (WithLp.equiv 2 (Fin n → ℝ)).symm (fun k => inner ℝ (τ k) y)
      map_add' := fun y z => by ext k; simp [inner_add_right]
      map_smul' := fun c y => by ext k; simp [inner_smul_right] }
  let Ls : Euclid P →L[ℝ] Euclid n := LinearMap.toContinuousLinearMap Ls₀
  have hLsL : ∀ s, Ls (L s) = s := by
    intro s
    ext k
    simp [Ls, Ls₀, L, L₀, orthonormal_iff_ite.mp hτ]
  have hLsτ : ∀ j, Ls (τ j) = EuclideanSpace.single j (1 : ℝ) := by
    intro j
    ext k
    simp [Ls, Ls₀, orthonormal_iff_ite.mp hτ, eq_comm]
  -- the normal component q y = y - L (Ls y)
  let q : Euclid P →L[ℝ] Euclid P := ContinuousLinearMap.id ℝ (Euclid P) - L.comp Ls
  have hqapp : ∀ y, q y = y - L (Ls y) := fun y => rfl
  have hqL : ∀ s, q (L s) = 0 := by intro s; rw [hqapp, hLsL, sub_self]
  -- compactness and a margin δ
  set K := tsupport ψ with hKdef
  have hK : IsCompact K := hψc
  have hLK : IsCompact (L '' K) := hK.image L.continuous
  have hLKV : L '' K ⊆ V := by
    rintro _ ⟨s, hs, rfl⟩
    exact hψΩ hs
  obtain ⟨δ, hδ, hδV⟩ := hLK.exists_cthickening_subset_open hV hLKV
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  -- the bump function
  let χ : ContDiffBump (0 : Euclid P) := ⟨δ / 2, δ, by positivity, by linarith⟩
  let f : Euclid P → ℝ := fun y => ψ (Ls y) * χ (q y)
  have hfapp : ∀ y, f y = ψ (Ls y) * χ (q y) := fun y => rfl
  -- the set A
  let A : Set (Euclid P) := {y | Ls y ∈ K ∧ ‖q y‖ ≤ δ}
  have hAclosed : IsClosed A :=
    (isClosed_tsupport ψ |>.preimage Ls.continuous).inter
      (isClosed_le (continuous_norm.comp q.continuous) continuous_const)
  have hsuppA : support f ⊆ A := by
    intro y hy
    have hy' : ψ (Ls y) * χ (q y) ≠ 0 := hy
    refine ⟨subset_tsupport ψ (left_ne_zero_of_mul hy'), ?_⟩
    have hχ : χ (q y) ≠ 0 := right_ne_zero_of_mul hy'
    have : q y ∈ support χ := hχ
    rw [χ.support_eq] at this
    simpa [dist_eq_norm] using (mem_ball.mp this).le
  have htsuppA : tsupport f ⊆ A := closure_minimal hsuppA hAclosed
  have hAbdd : A ⊆ closedBall 0 (R + δ) := by
    intro y hy
    rw [mem_closedBall, dist_zero_right]
    have h1 : y = L (Ls y) + q y := by rw [hqapp]; abel
    have h2 : ‖Ls y‖ ≤ R := by simpa using hR hy.1
    calc ‖y‖ = ‖L (Ls y) + q y‖ := by rw [← h1]
      _ ≤ ‖L (Ls y)‖ + ‖q y‖ := norm_add_le _ _
      _ = ‖Ls y‖ + ‖q y‖ := by rw [hnorm]
      _ ≤ R + δ := add_le_add h2 hy.2
  have hAcpt : IsCompact A := (isCompact_closedBall 0 (R + δ)).of_isClosed_subset hAclosed hAbdd
  have hAV : A ⊆ V := by
    intro y hy
    apply hδV
    apply mem_cthickening_of_dist_le y (L (Ls y)) δ (L '' K) ⟨Ls y, hy.1, rfl⟩
    rw [dist_eq_norm, ← hqapp]
    exact hy.2
  refine ⟨f, ?_, ?_, htsuppA.trans hAV, fun s => ⟨?_, fun j => ?_⟩⟩
  · exact (hψ.comp Ls.contDiff).mul (χ.contDiff.comp q.contDiff)
  · exact HasCompactSupport.of_support_subset_isCompact hAcpt hsuppA
  · show ψ (Ls (L s)) * χ (q (L s)) = ψ s
    rw [hLsL, hqL, χ.one_of_mem_closedBall (by simp; positivity), mul_one]
  · -- near L s, f = ψ ∘ Ls
    have hev : f =ᶠ[𝓝 (L s)] fun y => ψ (Ls y) := by
      have hq : Tendsto q (𝓝 (L s)) (𝓝 0) := by
        have := q.continuous.tendsto (L s)
        rwa [hqL] at this
      filter_upwards [hq (closedBall_mem_nhds 0 (by positivity : (0:ℝ) < δ / 2))] with y hy
      rw [hfapp, χ.one_of_mem_closedBall hy, mul_one]
    show fderiv ℝ f (L s) (τ j) = _
    rw [hev.fderiv_eq]
    change fderiv ℝ (ψ ∘ Ls) (L s) (τ j) = _
    have hψd : DifferentiableAt ℝ ψ (Ls (L s)) := (hψ.differentiable (by simp)).differentiableAt
    rw [fderiv_comp (L s) hψd Ls.differentiableAt, ContinuousLinearMap.fderiv]
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, hLsτ, hLsL]
```

## Key steps

1. ι* (y) = (⟨τ_k, y⟩)_k, p = ι∘ι*, q = id − p: ι*ι = id, ι*(τ_j) = e_j, q(ι(s)) = 0, ‖y‖ ≤ ‖ι*y‖ + ‖q y‖.
2. ι(tsupport ψ) is a compact subset of V, so cthickening δ (ι(tsupport ψ)) ⊆ V for some δ > 0.
3. f(y) := ψ(ι*y)·χ(q y) with a smooth bump χ = 1 on B̄(0, δ/2), support B(0, δ).
4. support f ⊆ {ι*y ∈ tsupport ψ, ‖q y‖ ≤ δ}, a compact subset of cthickening δ (ι(tsupport ψ)) ⊆ V.
5. f = ψ∘ι* near ι(s), so f(ι(s)) = ψ(s) and Df(ι(s))(τ_j) = Dψ(s)(ι*τ_j) = Dψ(s)(e_j).

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD (against manifest.json)`
- `python3 scan of dag.json: accepted nodes (status, lean_name, lean_statement, candidate_commit) for dimred_*, imrep_*, atsm_*, dgcr_*, dgid_*, dgoj_*, rsdic_*, regcomp_*; duplicate lean_names; cross-branch reuse precedents (children whose parent field differs)`
- `rg -n 'idtp_pc_' over dag.json, nodes/, the snapshot and all git refs (no match)`
- `git show <candidate>:GMT/Ch07/Submission.lean for 01ae2c59, d15b5cf4, 038573e4, d5e029d5, c1d60848, dcc3f4b7, 8a6855aa; diff against the contract (added declarations, imports, removed lines)`
- `grep -n theorem/def in .lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean, Chapter03/Rectifiable.lean, Chapter06/{Forms,Currents,Mass,CurrentLocalEquality}.lean`
- `rg -n 'Isometry.map_euclideanHausdorffMeasure|EuclideanSpace.euclideanHausdorffMeasure_eq_volume|exists_cthickening_subset_open|eq_of_le_of_finrank_eq|one_of_mem_closedBall' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `lake env lean /tmp/pc-decomp-k7q2/check/Probe2.lean and Names.lean (#check of the cited Mathlib/SimonGMT names after import GMT.Ch07.Submission; Chapter08 names unknown)`
- `lake env lean /tmp/pc-decomp-k7q2/check/{Types,Parent,Children}.lean and /tmp/pc-decomp-k7q2/merged/Merged.lean (#print axioms)`
- `sed -n 560,640p book/chapter-06.txt (Simon 2.34, Constancy Theorem and proof); sed -n 1830,1880p book/chapter-06.txt (deformation theorem (26)–(27))`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-77d7be4677/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-77d7be4677/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-im-mass-measure-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-im-mass-measure-a1/rlcr-plan-v1.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-regular-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/pc-decomp-k7q2/check/Types.lean`
- `/tmp/pc-decomp-k7q2/check/Parent.lean`
- `/tmp/pc-decomp-k7q2/check/Children.lean`
- `/tmp/pc-decomp-k7q2/merged/Merged.lean`

The pins match. The snapshot is project b4d606d (equal to workspace HEAD) with mathlib 25730c7c, and SimonGMT is 2b36630. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

Reused accepted declarations. dimred_im_mass_measure, imrep_carrier_sdiff_support_null, atsm_approxTangent_le_of_flat, dgcr_unitOrientation_eq_or_neg, dgcr_smooth_tests_to_C1_tests and dgcr_bwd_coordinate_covector are comparator-accepted and are reused at byte-identical types. Their candidates only add pairwise-disjoint declarations to the contract.

Library support.
- Mathlib supplies Isometry.map_euclideanHausdorffMeasure and EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Geometry/Euclidean/Volume/Measure.lean:141,187).
- Mathlib also supplies IsCompact.exists_cthickening_subset_open, Submodule.eq_of_le_of_finrank_eq, the ContDiffBump API and the MeasurableEmbedding transfer lemmas, all inside the frozen import closure.
- SimonGMT supplies exteriorDerivative_apply (Chapter06/Forms.lean:119) and support_euclideanHausdorffMeasure_restrict_submodule (Chapter03).
- SimonGMT's ae_eq_const_of_weak_coordinate_derivatives_zero (Chapter08/DistributionalConstancy.lean) is outside the frozen import closure. It is applied in this node's parent proof with an added import, following the accepted precedent 8a6855aa.

Names. No idtp_pc_* name occurs anywhere.

Lean. All 12 child types elaborate. The exact parent type follows from three child types plus the SimonGMT theorem. Each new child has a verified single-theorem proof from its declared dependencies. A fully merged build with the reused accepted code has no sorry, and all seven new declarations depend only on propext, Classical.choice and Quot.sound.
