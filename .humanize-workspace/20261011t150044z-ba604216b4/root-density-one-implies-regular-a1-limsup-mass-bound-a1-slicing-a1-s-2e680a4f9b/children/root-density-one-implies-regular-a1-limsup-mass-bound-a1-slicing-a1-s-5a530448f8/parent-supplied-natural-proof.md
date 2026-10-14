# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.lipschitz_leibniz-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.lipschitz_leibniz-a1.wedge_vector-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 4(a) and 4(b) of the parent proof (Simon Ch. 6, proof of Lemma 4.5(2), display (3): ⟨dh∧ω, ξ⟩ = ⟨dh, Ṽ⟩ with Ṽ tangent), stated pointwise for one multivector ζ and one covector α. Notation: Φ(β) := ζ(β∧α) = ζ(alternatizeUncurryFin(β.smulRight α)) for β : Euclid P →L[ℝ] ℝ; e_l := EuclideanSpace.single l 1; e_l♭ := innerSL ℝ e_l, so e_l♭(v) = ⟨e_l, v⟩; V := Σ_{l ∈ Fin P} Φ(e_l♭)·e_l.

1. (Φ is linear.) For β₁, β₂ and c ∈ ℝ: (β₁ + β₂).smulRight α = β₁.smulRight α + β₂.smulRight α and (c•β).smulRight α = c•(β.smulRight α) (check at each vector v: (β₁ v + β₂ v)•α = β₁ v•α + β₂ v•α by `add_smul`, and (c·β v)•α = c•(β v•α) by `mul_smul`). alternatizeUncurryFin is additive and ℝ-homogeneous (`ContinuousAlternatingMap.alternatizeUncurryFin_add`, `ContinuousAlternatingMap.alternatizeUncurryFin_smul`) and ζ is linear (`map_add`, `map_smul`). Hence Φ(β₁ + β₂) = Φ(β₁) + Φ(β₂) and Φ(c•β) = c·Φ(β), so Φ is an ℝ-linear map (Euclid P →L[ℝ] ℝ) →ₗ[ℝ] ℝ and commutes with finite sums (`map_sum`).
2. (Expansion of a 1-covector.) For every v ∈ ℝ^P, v = Σ_l v_l·e_l (`(EuclideanSpace.basisFun (Fin P) ℝ).sum_repr v`), so β(v) = Σ_l v_l·β(e_l) by linearity of β; and e_l♭(v) = ⟨e_l, v⟩ = v_l (`innerSL_apply_apply`, `EuclideanSpace.inner_single_left`). Hence β = Σ_l β(e_l)•e_l♭ as continuous linear functionals (ext at every v).
3. (Identity (1).) By steps 1 and 2, Φ(β) = Φ(Σ_l β(e_l)•e_l♭) = Σ_l β(e_l)·Φ(e_l♭). By linearity of β, β(V) = Σ_l Φ(e_l♭)·β(e_l). The two finite sums agree term by term (commutativity), so ζ(β∧α) = Φ(β) = β(V) for every β.
4. (Normal directions are annihilated.) Let ζ be a unit orientation of Q: there is an orthonormal family τ = (τ_0, …, τ_n) with span(range τ) = Q such that ζ(γ) = γ(τ) for all (n+1)-covectors γ, or ζ(γ) = −γ(τ) for all γ. Let v ∈ Q^⊥. Each τ_i lies in span(range τ) = Q (`Submodule.subset_span`), so ⟨v, τ_i⟩ = 0 (`Submodule.inner_left_of_mem_orthogonal`). By `ContinuousAlternatingMap.alternatizeUncurryFin_apply`, (v♭∧α)(τ) = Σ_i (−1)^i·((v♭.smulRight α)(τ_i))(τ with τ_i removed) = Σ_i (−1)^i·⟨v, τ_i⟩·α(τ with τ_i removed) = 0, every summand vanishing. Hence Φ(v♭) = ζ(v♭∧α) = ±0 = 0 in either sign case.
5. (Membership (2).) For every v ∈ Q^⊥, ⟨v, V⟩ = v♭(V) = Φ(v♭) = 0 by identity (1) with β := v♭ and step 4. So V ∈ (Q^⊥)^⊥ (`Submodule.mem_orthogonal`). Q is a subspace of the finite-dimensional space ℝ^P, hence complete, so it has an orthogonal projection and Q^⊥⊥ = Q (`Submodule.orthogonal_orthogonal`; the instance is found automatically). Therefore V ∈ Q. ∎

Lean reference implementation (kernel-checked during this decomposition against GMT.Ch07.Submission, Lean v4.35.0-rc3, Mathlib 25730c7c; no sibling is used; `#print axioms` gives propext, Classical.choice, Quot.sound). Place it after the contract's `noncomputable section … end`, inside `namespace GMT.Ch07`:

```lean
theorem Submission.dor_lmbsf_ll_wedge_representing_vector : ∀ (P n : ℕ) (ζ : MultiVector P (n + 1)) (α : Covector (Euclid P) n), (∀ β : Euclid P →L[ℝ] ℝ, ζ (ContinuousAlternatingMap.alternatizeUncurryFin (β.smulRight α)) = β (∑ l : Fin P, ζ (ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ (EuclideanSpace.single l (1 : ℝ))).smulRight α)) • EuclideanSpace.single l (1 : ℝ))) ∧ ∀ Q : Submodule ℝ (Euclid P), IsUnitOrientationOf ζ Q → (∑ l : Fin P, ζ (ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ (EuclideanSpace.single l (1 : ℝ))).smulRight α)) • EuclideanSpace.single l (1 : ℝ)) ∈ Q := by
  intro P n ζ α
  -- Φ(β) := ζ(β ∧ α) is linear in β
  let Φ : (Euclid P →L[ℝ] ℝ) → ℝ := fun β =>
    ζ (ContinuousAlternatingMap.alternatizeUncurryFin (β.smulRight α))
  have hΦadd : ∀ β₁ β₂ : Euclid P →L[ℝ] ℝ, Φ (β₁ + β₂) = Φ β₁ + Φ β₂ := by
    intro β₁ β₂
    have : (β₁ + β₂).smulRight α = β₁.smulRight α + β₂.smulRight α := by
      ext v; simp [add_smul]
    simp only [Φ, this, ContinuousAlternatingMap.alternatizeUncurryFin_add, map_add]
  have hΦsmul : ∀ (c : ℝ) (β : Euclid P →L[ℝ] ℝ), Φ (c • β) = c • Φ β := by
    intro c β
    have : (c • β).smulRight α = c • β.smulRight α := by
      ext v; simp [mul_smul]
    simp only [Φ, this, ContinuousAlternatingMap.alternatizeUncurryFin_smul, map_smul]
  let Φl : (Euclid P →L[ℝ] ℝ) →ₗ[ℝ] ℝ :=
    { toFun := Φ, map_add' := hΦadd, map_smul' := hΦsmul }
  -- expansion of a covector in the standard dual basis
  have hβexp : ∀ β : Euclid P →L[ℝ] ℝ,
      β = ∑ l : Fin P, β (EuclideanSpace.single l (1 : ℝ)) • innerSL ℝ (EuclideanSpace.single l (1 : ℝ)) := by
    intro β
    ext v
    have hv : v = ∑ l : Fin P, v l • EuclideanSpace.single l (1 : ℝ) := by
      conv_lhs => rw [← (EuclideanSpace.basisFun (Fin P) ℝ).sum_repr v]
      simp
    simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
      Pi.smul_apply, innerSL_apply_apply, EuclideanSpace.inner_single_left, map_one, one_mul,
      smul_eq_mul]
    conv_lhs => rw [hv]
    simp [map_sum, map_smul, mul_comm]
  have hid : ∀ β : Euclid P →L[ℝ] ℝ, Φ β = β (∑ l : Fin P, Φ (innerSL ℝ (EuclideanSpace.single l (1 : ℝ))) •
      EuclideanSpace.single l (1 : ℝ)) := by
    intro β
    have h1 : Φ β = Φl β := rfl
    rw [h1, hβexp β, map_sum]
    simp only [map_sum, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro l _
    simp only [Φl, LinearMap.coe_mk, AddHom.coe_mk]
    have := hβexp β
    rw [← this]
    ring
  refine ⟨hid, ?_⟩
  intro Q hQ
  obtain ⟨τ, hτ, hspan, hsign⟩ := hQ
  have hzero : ∀ v ∈ Qᗮ, Φ (innerSL ℝ v) = 0 := by
    intro v hv
    have hτQ : ∀ i, τ i ∈ Q := fun i => hspan ▸ Submodule.subset_span (Set.mem_range_self i)
    have hval : (ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ v).smulRight α)) τ = 0 := by
      rw [ContinuousAlternatingMap.alternatizeUncurryFin_apply]
      apply Finset.sum_eq_zero
      intro i _
      simp [Submodule.inner_left_of_mem_orthogonal (hτQ i) hv]
    rcases hsign with h | h
    · simp only [Φ, h, hval]
    · simp only [Φ, h, hval, neg_zero]
  rw [← Submodule.orthogonal_orthogonal Q, Submodule.mem_orthogonal]
  intro u hu
  have := hid (innerSL ℝ u)
  rw [hzero u hu, innerSL_apply_apply] at this
  exact this.symm
```

## Key steps

1. Φ(β) := ζ(β∧α) is ℝ-linear in β (smulRight, alternatizeUncurryFin and ζ are linear).
2. β = Σ_l β(e_l)e_l♭, so Φ(β) = Σ_l β(e_l)Φ(e_l♭) = β(V).
3. If ζ = ±(·)(τ) with τ an orthonormal basis of Q and v ⊥ Q, then (v♭∧α)(τ) = Σ_i (−1)^i⟨v, τ_i⟩α(…) = 0, so Φ(v♭) = 0.
4. ⟨v, V⟩ = Φ(v♭) = 0 for all v ∈ Q^⊥, hence V ∈ Q^⊥⊥ = Q.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606d, mathlib 25730c7c)`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical)`
- `rg -n 'theorem (extDeriv_smul|extDeriv_fun_smul|extDeriv_add)\b|lemma norm_alternatizeUncurryFin_le|theorem alternatizeUncurryFin_apply|theorem alternatizeUncurryFin_smul|theorem alternatizeUncurryFin_add' mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `rg -n 'extDeriv.*fun .* (•|\*) |extDeriv_mul|extDeriv_smul_fun|extDeriv.*smulRight' mathlib/Mathlib/Analysis/Calculus/DifferentialForm/`
- `rg -n 'theorem tendsto_integral_of_dominated_convergence|theorem isBoundedBilinearMap_apply|theorem isBoundedBilinearMap_smulRight|theorem orthogonal_orthogonal|theorem abs_max_sub_max_le_abs|theorem norm_smulRight_apply|theorem innerSL_apply_norm|theorem fderiv_fun_smul' mathlib/Mathlib`
- `rg -n 'dor_lmbsf_ll_|representing|tangent_wedge|cutoff_smooth|action_mul_tendsto' project/`
- `rg -ln 'mollif|LipschitzWith.*ContDiff|contDiff_convolution' simongmt/Poincare/SimonGMT`
- `grep -n '^def \|^abbrev \|^theorem ' simongmt Chapter06/Forms.lean and Chapter06/Currents.lean (exteriorDerivative = extDeriv, IsTestForm, TestFormOn, exteriorDerivativeTestOn, GeometricCurrentOn.boundary_apply)`
- `dag.json scans of statements for mollif|TendstoUniformly|smulRight|IsUnitOrientationOf|alternatizeUncurryFin|Leibniz|convolution, plus a lean_name collision check for dor_lmbsf_ll_*`
- `git show <candidate_commit>:GMT/Ch07/Submission.lean for 00c458d8, e32f0ad2, 5c54ddba, 533617d2, 0325970d (reused declarations and their exact types)`
- `git log --all -S'dor_lmbsf_ll_' (no match)`
- `lean GMT/Scratch/dor_lmbsf_ll_decomposition/{Assembly,ChildS,ChildN3,Childd1,Childd2,AllReal}.lean with #print axioms`
- `python3 -I verifier lean_contract.validate_lean_statement and gmt-compare contract_scope/child_modules on the 9 child types; lean challenges/*_Challenge.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/Bilinear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Submodule.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/LinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/Group/MinMax.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-2e680a4f9b/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-slicing-a1-lipschitz-smoothing-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-slicing-a1-cutoff-defect-a-11763512eb/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-constant-multiplicity-reduction-a1-imrep-cu-db12d15d12/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-first-variation-mass-bound-a1-o-90c59096a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-imrep-measure-unique-a1-orie-c3a822a8f5/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-15bd82d86f30/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/dor_lmbsf_ll_decomposition/Assembly.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/dor_lmbsf_ll_decomposition/AllReal.lean`

Snapshot: project b4d606d, mathlib 25730c7c. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

No match: Mathlib's DifferentialForm API has only constant-scalar rules (extDeriv_smul, extDeriv_fun_smul, extDerivWithin_fun_smul) and no Leibniz rule for a function times a form. SimonGMT has no Lipschitz mollifier in the frozen import closure; BV.lean and DistributionalConstancy.lean mention mollification only in docstrings and are not imported. The project has no representing-vector, tangent-field or cut-off-smoothing lemma, and no dor_lmbsf_ll_* name.

Relevant matches, now reused as children with byte-identical frozen types (all accepted with candidate commits):
- cmcs_lipschitz_smoothing (00c458d8);
- cmcs_cd_defect_identity (e32f0ad2);
- rsd_cmr_ic_action_integrable (5c54ddba);
- fvmb_imrep_ae_unitOrientation_approxTangentPlane (533617d2);
- unit_orientation_norm_le_one (0325970d).
The runtime (_existing_lean_name_problem, _accepted_checkpoint) allows this reuse.

Mathlib facts used by the new children, all present in the snapshot: alternatizeUncurryFin_apply/_add/_smul, norm_alternatizeUncurryFin_le, isBoundedBilinearMap_apply/_smulRight, norm_smulRight_apply, innerSL_apply_norm, Submodule.orthogonal_orthogonal, tendsto_integral_of_dominated_convergence, abs_max_sub_max_le_abs and fderiv_fun_smul.

Lean checks: the exact frozen parent type is proved from the 9 children. AllReal.lean, which splices in the accepted code of the reused declarations, has no sorry and uses only propext, Classical.choice and Quot.sound. All child types pass the verifier's lexical validator and elaborate as comparator challenge modules.
