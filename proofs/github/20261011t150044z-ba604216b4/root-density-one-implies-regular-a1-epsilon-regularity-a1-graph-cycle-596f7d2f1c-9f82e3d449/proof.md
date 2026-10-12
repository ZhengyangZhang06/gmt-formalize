# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.graph_orientation_jacobian-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.graph_orientation_jacobian-a1.covector_frame_det-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3(i) of the parent proof (the restriction α_L of α to L is a multiple of the basis determinant of L, evaluated at b), stated for an arbitrary orthonormal frame τ of the subspace L = span(range τ) containing b.
Notation: ℝᵐ means Euclid m = EuclideanSpace ℝ (Fin m); ⟨x, y⟩ is inner ℝ x y; e_j := EuclideanSpace.single j (1 : ℝ) is the j-th standard basis vector of ℝⁿ; an n-covector of ℝᴾ is an element of Covector (Euclid P) n = Euclid P [⋀^Fin n]→L[ℝ] ℝ (a continuous alternating n-linear map ℝᴾ × ⋯ × ℝᴾ → ℝ); MultiVector P n = Covector (Euclid P) n →L[ℝ] ℝ (continuous linear functionals on n-covectors); for a continuous linear map F, F* = F.adjoint and det of an endomorphism is ContinuousLinearMap.det (= LinearMap.det of the underlying linear map). L := span ℝ (range τ) ⊆ ℝᴾ, an n-family c in L has underlying ambient family ↑c.
1. A basis of L indexed by Fin n. An orthonormal family is linearly independent (Orthonormal.linearIndependent), so τ is a basis of its span: e := Module.Basis.span hτ.linearIndependent is a basis (e₁, …, eₙ) of L whose underlying vectors are ↑eᵢ = τᵢ (Module.Basis.span_apply).
2. Restriction of α to L. Let α_L := α.toAlternatingMap.compLinearMap L.subtype, i.e. α_L(c₁, …, cₙ) := α(↑c₁, …, ↑cₙ) for cᵢ ∈ L; it is an alternating n-linear form on L. Put b'ⱼ := ⟨bⱼ, hbⱼ⟩ ∈ L (hypothesis). Then α(b) = α_L(b') and α(τ) = α(↑e) = α_L(e) (both by unfolding, using ↑eᵢ = τᵢ).
3. Alternating n-forms on the n-dimensional space L with basis e are multiples of the basis determinant: α_L = α_L(e) • det_e (AlternatingMap.eq_smul_basis_det). Evaluating at b' gives α_L(b') = α_L(e)·det_e(b').
4. The coordinate matrix. det_e(b') = det M with Mᵢⱼ := e.repr(b'ⱼ)ᵢ (Module.Basis.det_apply, Module.Basis.toMatrix_apply). We claim Mᵢⱼ = ⟨τᵢ, bⱼ⟩. Indeed b'ⱼ = Σₗ Mₗⱼ • eₗ (Module.Basis.sum_repr); taking underlying vectors (Submodule.coe_sum, Submodule.coe_smul) gives bⱼ = Σₗ Mₗⱼ • τₗ, and taking the inner product with τᵢ and using orthonormality, ⟨τᵢ, Σₗ Mₗⱼ τₗ⟩ = Mᵢⱼ (Orthonormal.inner_right_fintype). Hence M = 𝒜.
5. Combining steps 2–4: α(b) = α_L(b') = α_L(e)·det_e(b') = α(τ)·det 𝒜 = det(𝒜)·α(τ). ∎
(The argument is uniform in n; for n = 0 both sides reduce to α of the empty family, det of the empty matrix being 1.)
Formalization note: unless split further this is a machine leaf: exactly one theorem `Submission.dgoj_covector_eq_det_mul_of_mem_span` appended to the frozen GMT/Ch07/Submission.lean inside `namespace GMT.Ch07` (before `main_theorem`), no new import, option or helper declaration. Every lemma cited is in the import closure of GMT.Ch07.Submission (pinned Mathlib 25730c7c). The following Lean proof was compiled by the parent decomposition session against that frozen import closure (lean 4.35.0-rc3; `#print axioms` = propext, Classical.choice, Quot.sound; no warnings) and passes the runtime leaf-delta check `check_source_delta`; it may be used verbatim:
theorem Submission.dgoj_covector_eq_det_mul_of_mem_span : ∀ (P n : ℕ) (τ b : Fin n → Euclid P), Orthonormal ℝ τ → (∀ j, b j ∈ Submodule.span ℝ (Set.range τ)) → ∀ α : Covector (Euclid P) n, α b = (Matrix.of fun i j => inner ℝ (τ i) (b j)).det * α τ := by
  intro P n τ b hτ hb α
  set L := Submodule.span ℝ (Set.range τ) with hLdef
  let e : Module.Basis (Fin n) ℝ L := Module.Basis.span hτ.linearIndependent
  have he : ∀ i, (e i : Euclid P) = τ i := fun i => by
    rw [Module.Basis.span_apply hτ.linearIndependent i]
  let αL : L [⋀^Fin n]→ₗ[ℝ] ℝ := α.toAlternatingMap.compLinearMap L.subtype
  let b' : Fin n → L := fun j => ⟨b j, hb j⟩
  have h1 : α b = αL b' := rfl
  have h2 : α τ = αL e := by
    show α τ = α (fun i => (e i : Euclid P))
    congr 1
    funext i
    exact (he i).symm
  -- coordinates of b' in e are the inner products with τ
  have hrepr : ∀ i j, e.repr (b' j) i = inner ℝ (τ i) (b j) := by
    intro i j
    have hs : (b j : Euclid P) = ∑ l, e.repr (b' j) l • τ l := by
      have := congrArg (Subtype.val) (e.sum_repr (b' j))
      simp only [Submodule.coe_sum, Submodule.coe_smul, he] at this
      exact this.symm
    rw [hs, hτ.inner_right_fintype]
  have hmat : e.toMatrix b' = Matrix.of fun i j => inner ℝ (τ i) (b j) := by
    ext i j
    rw [Module.Basis.toMatrix_apply, hrepr, Matrix.of_apply]
  have h3 : αL b' = αL e * e.det b' := by
    conv_lhs => rw [AlternatingMap.eq_smul_basis_det e αL]
    rfl
  rw [h1, h2, h3, Module.Basis.det_apply, hmat, mul_comm]

## Key steps

1. τ orthonormal ⇒ linearly independent ⇒ basis e := Module.Basis.span of L = span(range τ) with ↑eᵢ = τᵢ.
2. Restrict α to L: α_L := α.toAlternatingMap.compLinearMap L.subtype; α(b) = α_L(b') and α(τ) = α_L(e).
3. AlternatingMap.eq_smul_basis_det: α_L = α_L(e)·det_e, so α(b) = α(τ)·det_e(b').
4. det_e(b') = det of the coordinate matrix, whose (i,j) entry is ⟨τᵢ, bⱼ⟩ by expanding bⱼ = Σₗ cₗ τₗ and orthonormality.
5. Hence α(b) = det(⟨τᵢ, bⱼ⟩)·α(τ).

## Reference use

### local-project

Queries:
- `rg -n 'theorem AlternatingMap.eq_smul_basis_det' mathlib/Mathlib`
- `rg -n 'theorem volumeForm_robust\b|theorem abs_volumeForm_apply_le' mathlib/Mathlib`
- `rg -n 'theorem norm_image_sub_le' mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `rg -n 'theorem le_opNorm|theorem opNorm_le_bound' mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `rg -n 'finrank_range_of_inj' mathlib/Mathlib`
- `rg -n 'theorem det_eq_zero_iff_ker_ne_bot' mathlib/Mathlib`
- `rg -n 'theorem span_apply' mathlib/Mathlib/LinearAlgebra/Basis/Basic.lean`
- `rg -n 'theorem Orthonormal.inner_right_fintype' mathlib/Mathlib`
- `rg -n 'theorem Orthonormal.comp_linearIsometry' mathlib/Mathlib`
- `rg -n 'mem_span_range_iff_exists_fun' mathlib/Mathlib`
- `rg -n 'theorem toMatrix_self|theorem toMatrix_apply' mathlib/Mathlib/LinearAlgebra/Matrix/Basis.lean`
- `rg -n 'theorem det_toMatrix \(b' mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `rg -n 'theorem EuclideanSpace.inner_single_left' mathlib/Mathlib`
- `rg -n 'theorem adjoint_inner_right' mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `rg -n 'theorem ContDiffOn.continuousOn_fderiv_of_isOpen' mathlib/Mathlib`
- `rg -n 'theorem ContinuousLinearMap.continuous_det' mathlib/Mathlib`
- `rg -n 'def apply \(m : ι → E\)' mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `rg -n 'theorem posDef_gram_of_linearIndependent|theorem gram_eq_conjTranspose_mul' mathlib/Mathlib`
- `rg -n 'continuous_of_finiteDimensional' mathlib/Mathlib`
- `rg -n 'IsUnitOrientationOf|volumeForm|eq_smul_basis_det|ContinuousAlternatingMap.apply' project/GMT`
- `rg -n 'adjoint ∘L|\.det\)|Real.sqrt' project/GMT --glob '*.lean'`
- `rg -n 'mkContinuous|compContinuousLinearMap' project/GMT --glob '*.lean'`
- `lean #check probes after import GMT.Ch07.Submission: Matrix.gram, Matrix.posDef_gram_of_linearIndependent, Matrix.PosDef.det_pos, MultilinearMap.continuous_of_finiteDimensional, AlternatingMap.toContinuousAlternatingMap, ContinuousAlternatingMap.apply, ContinuousAlternatingMap.norm_image_sub_le, LinearMap.isUnit_iff_isUnit_det, Orientation.volumeForm_robust`
- `grep 'dgoj_' over dag.json, nodes/*/{decomposition-v*,parent-child-handoff}.json and git refs`
- `lean Stmts/Assembly/Full2/Check/Challenge.lean and in-situ OrientationJacobianFull.lean with #print axioms; python leaf_verification.check_source_delta on each child`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orientation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/Finrank.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Basis/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/Basis.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/GramMatrix.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch02/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-regular-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-7b72550114/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-07a3972eec1d/_recursive_lean/leaf_verification.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/graph_orientation_jacobian_decomposition/OrientationJacobianFull.lean`

The snapshot is project b4d606d with mathlib 25730c7c.

The project has no reusable frame, Gram or evaluation lemma for this node:
- It contains only the Ch07 definitions of MultiVector and IsUnitOrientationOf.
- The Ch02 Jacobian definitions (√det(L*∘L)) belong to another chapter's contract and are not imported.

Pinned Mathlib inside the frozen import closure supplies:
- linear algebra: AlternatingMap.eq_smul_basis_det, Module.Basis.span/span_apply, Module.Basis.det_apply/det_self, LinearMap.det_toMatrix, LinearMap.det_eq_zero_iff_ker_ne_bot, LinearMap.finrank_range_of_inj;
- inner products and orientation: Orthonormal.inner_right_fintype/comp_linearIsometry, stdOrthonormalBasis, Orientation.volumeForm_robust and abs_volumeForm_apply_le, ContinuousLinearMap.adjoint_inner_left/right;
- analysis: ContinuousAlternatingMap.le_opNorm and norm_image_sub_le, ContinuousLinearMap.continuous_det, ContDiffOn.continuousOn_fderiv_of_isOpen.

Unknown after `import GMT.Ch07.Submission`, so outside the closure:
- Matrix.gram and posDef_gram_of_linearIndependent (GramMatrix.lean);
- Matrix.PosDef.det_pos;
- MultilinearMap.continuous_of_finiteDimensional;
- AlternatingMap.toContinuousAlternatingMap.
The children therefore prove the Gram identity by hand, get positivity from the kernel of F*F, and build δ with the Hadamard bound.

Checks:
- All seven child types elaborate in the comparator contract scope.
- Each child was proved as a single theorem that passes check_source_delta.
- The frozen parent type assembles from the children in situ.
- Axioms are only propext, Classical.choice and Quot.sound.
- The prefix dgoj_ is unused, so there are no name collisions.
