# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.planar_constancy-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.planar_constancy-a1.boundary_weak_derivative-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 6 ("Zero weak derivatives") of the parent-supplied proof, ambient part: "φ := f·α_i ∈ 𝒟^{n−1}(V). Then dφ = df ∧ α_i and ⟨dφ(x), ξ_Q⟩ = (−1)^{i−1}D_{τ_i}f(x). Since ∂S = 0 in V, 0 = ∂S(φ) = S(dφ) = (−1)^{i−1}∫_{V∩Q} g D_{τ_i}f dH^n"; Simon Ch. 6, proof of 2.34, formula (2) (d ω_j = (D_j a) dx^1 ∧ ⋯ ∧ dx^n). Here the sign (−1)^{i−1} is absorbed into the choice of the constant (n−1)-covector, so that dφ(x)(τ) = Df(x)(τ_j) exactly. Notation: H^n := μHE[n]; indices of τ run over Fin n = {0, …, n−1}; for a family w = (w_0, …, w_m), Fin.removeNth i w is the family with entry i deleted; α(τ) := α(τ_0, …, τ_{n−1}).
1. (Degree.) Since n ≥ 1, write n = m + 1. Then BoundaryVanishes S means S.boundary = 0, i.e. ∂S(φ) = S(dφ) = 0 for every φ ∈ 𝒟^m(V) (GeometricCurrentOn.boundary_apply: ∂S(φ) = S(dφ), where dφ = exteriorDerivative φ belongs to 𝒟^n(V) because d preserves smoothness and compact support and tsupport dφ ⊆ tsupport φ).
2. (A constant m-covector.) Let e_0, …, e_m be the standard basis of ℝ^{m+1}. By the accepted sibling coordinate_covector (dgcr_bwd_coordinate_covector) there is an m-covector β on ℝ^{m+1} with β(Fin.removeNth i e) = (−1)^j if i = j and = 0 if i ≠ j (explicitly β(w_1, …, w_m) = det[e_j, w_1, …, w_m]: if i ≠ j the family (e_j, Fin.removeNth i e) contains e_j twice; if i = j, moving e_j to position j costs j transpositions). Let ι* : ℝ^P → ℝ^{m+1}, ι*(y) := (⟨τ_0, y⟩, …, ⟨τ_m, y⟩), a continuous linear map; by orthonormality ι*(τ_k) = e_k. Define the m-covector α on ℝ^P by α(w_1, …, w_m) := β(ι*w_1, …, ι*w_m) (ContinuousAlternatingMap.compContinuousLinearMap). Then for every i, α(Fin.removeNth i τ) = β(Fin.removeNth i (ι*∘τ)) = β(Fin.removeNth i e) = (−1)^j if i = j, and 0 otherwise.
3. (Test form.) Let f be C^∞ with compact support and tsupport f ⊆ V, and put φ(y) := f(y)·α (a constant covector times a scalar function). φ is C^∞, has compact support, and tsupport φ ⊆ tsupport f ⊆ V; so φ ∈ 𝒟^m(V).
4. (Exterior derivative.) For every x ∈ ℝ^P and every family w = (w_0, …, w_m), since f is differentiable at x and α is constant,
 dφ(x)(w) = Σ_{i=0}^{m} (−1)^i·D[y ↦ f(y)α(Fin.removeNth i w)](x)(w_i) = Σ_{i=0}^{m} (−1)^i·Df(x)(w_i)·α(Fin.removeNth i w)
 (the alternating-sum formula for the exterior derivative, SimonGMT exteriorDerivative_apply in Chapter06/Forms.lean, dφ(x)(w) = Σ_i (−1)^i·D[y ↦ φ(y)(Fin.removeNth i w)](x)(w_i), applied to the form φ, which is differentiable at x; for each i the scalar function y ↦ φ(y)(Fin.removeNth i w) equals f(y)·c_i with the constant c_i := α(Fin.removeNth i w), whose derivative at x is c_i·Df(x) (fderiv_mul_const)). Taking w = τ and using step 2, only the term i = j survives: dφ(x)(τ) = (−1)^j·Df(x)(τ_j)·(−1)^j = Df(x)(τ_j).
5. (Conclusion.) By step 1 and the hypothesis on S applied to ω := dφ ∈ 𝒟^n(V):
 0 = ∂S(φ) = S(dφ) = ∫_{V∩Q} g(x)·dφ(x)(τ) dH^n(x) = ∫_{V∩Q} g(x)·Df(x)(τ_j) dH^n(x),
 the last equality because the two integrands agree at every point by step 4. ∎

Formalization note (verified during the decomposition check; not part of the mathematical argument). The following single theorem proves exactly this frozen statement. It was compiled with `lake env lean` (Lean v4.35.0-rc3, Mathlib 25730c7c, SimonGMT 2b36630) after `import GMT.Ch07.Submission` only, inside `namespace GMT.Ch07` with the contract opens. It uses exactly the declared dependencies Submission.dgcr_bwd_coordinate_covector (by these Submission.* names) and no import or helper declaration. In a build where those dependencies were sorry stubs, `#print axioms` showed only propext, Classical.choice and Quot.sound besides the stubs; in a fully merged build containing the dependencies' accepted code it gives exactly propext, Classical.choice and Quot.sound. It follows the numbered steps above and may be used directly as the leaf candidate:
```lean
theorem Submission.idtp_pc_boundary_weak_derivative : ∀ (P n : ℕ) (V : Set (Euclid P)) (S : GeometricCurrentOn V n) (τ : Fin n → Euclid P) (g : Euclid P → ℝ), 1 ≤ n → Orthonormal ℝ τ → BoundaryVanishes S → (∀ ω : TestFormOn V n, S ω = ∫ x in V ∩ (Submodule.span ℝ (Set.range τ) : Set (Euclid P)), g x * (ω : DifferentialForm (Euclid P) n) x τ ∂μHE[n]) → ∀ f : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → tsupport f ⊆ V → ∀ j : Fin n, ∫ x in V ∩ (Submodule.span ℝ (Set.range τ) : Set (Euclid P)), g x * fderiv ℝ f x (τ j) ∂μHE[n] = 0 := by
  intro P n V S τ g hn hτ hbd hrep f hf hfc hfV j
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hbd' : S.boundary = 0 := hbd
  obtain ⟨β, hβ⟩ := Submission.dgcr_bwd_coordinate_covector m j
  let Ls₀ : Euclid P →ₗ[ℝ] Euclid (m + 1) :=
    { toFun := fun y => (WithLp.equiv 2 (Fin (m + 1) → ℝ)).symm (fun k => inner ℝ (τ k) y)
      map_add' := fun y z => by ext k; simp [inner_add_right]
      map_smul' := fun c y => by ext k; simp [inner_smul_right] }
  let Ls : Euclid P →L[ℝ] Euclid (m + 1) := LinearMap.toContinuousLinearMap Ls₀
  have hLsτ : ∀ i, Ls (τ i) = EuclideanSpace.single i (1 : ℝ) := by
    intro i
    ext k
    simp [Ls, Ls₀, orthonormal_iff_ite.mp hτ, eq_comm]
  let α : Covector (Euclid P) m := β.compContinuousLinearMap Ls
  have hα : ∀ i : Fin (m + 1), α (i.removeNth τ) = if i = j then (-1 : ℝ) ^ (j : ℕ) else 0 := by
    intro i
    have : (fun l => Ls (i.removeNth τ l)) = i.removeNth (fun l : Fin (m + 1) => EuclideanSpace.single l (1 : ℝ)) := by
      funext l
      simp [Fin.removeNth_apply, hLsτ]
    show β (fun l => Ls (i.removeNth τ l)) = _
    rw [this, hβ i]
  let φ : DifferentialForm (Euclid P) m := fun y => f y • α
  have hφtest : IsTestForm φ ∧ tsupport φ ⊆ V := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact hf.smul contDiff_const
    · exact hfc.smul_right
    · exact (tsupport_smul_subset_left _ _).trans hfV
  let φt : TestFormOn V m := ⟨φ, hφtest⟩
  have hd : ∀ x, exteriorDerivative φ x τ = fderiv ℝ f x (τ j) := by
    intro x
    have hfd : DifferentiableAt ℝ f x := (hf.differentiable (by simp)).differentiableAt
    rw [exteriorDerivative_apply (hfd.smul_const α) τ]
    have h1 : ∀ i : Fin (m + 1), (fun y => (f y • α) (i.removeNth τ)) = fun y => f y * α (i.removeNth τ) := by
      intro i; funext y; simp [smul_eq_mul]
    simp only [h1]
    simp only [fderiv_mul_const hfd, hα]
    rw [Finset.sum_eq_single j]
    · simp only [ite_true]
      rw [zsmul_eq_mul]
      push_cast
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]
      simp
    · intro i _ hij
      simp [hij]
    · simp
  have h0 : S.boundary φt = 0 := by rw [hbd']; rfl
  rw [GeometricCurrentOn.boundary_apply] at h0
  have h2 := hrep (exteriorDerivativeTestOn V m φt)
  rw [h0] at h2
  rw [h2]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [← hd x]
  rfl
```

## Key steps

1. n = m + 1 and BoundaryVanishes S gives S(dφ) = ∂S(φ) = 0 for every φ ∈ 𝒟^m(V).
2. Pull back the coordinate covector β on ℝ^{m+1} (accepted dgcr_bwd_coordinate_covector) by ι*(y) = (⟨τ_k, y⟩)_k to get α with α(removeNth i τ) = (−1)^j δ_ij.
3. φ := f·α is a test form in V and dφ(x)(τ) = Σ_i (−1)^i Df(x)(τ_i) α(removeNth i τ) = Df(x)(τ_j).
4. 0 = S(dφ) = ∫_{V∩Q} g·dφ(τ) dH^n = ∫_{V∩Q} g·Df(τ_j) dH^n.

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
