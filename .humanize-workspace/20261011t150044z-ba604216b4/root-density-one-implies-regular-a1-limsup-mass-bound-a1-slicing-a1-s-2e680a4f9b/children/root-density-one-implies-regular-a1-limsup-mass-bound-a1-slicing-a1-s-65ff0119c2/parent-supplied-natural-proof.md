# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.lipschitz_leibniz-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.lipschitz_leibniz-a1.action_dct-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3 of the parent proof (the two outer terms of identity (i) converge by dominated convergence), stated once for an arbitrary integer multiplicity triple and test form so that it applies both to (RB, ω) and to (RT, dω). Notation: μ := Hⁿ⌞M = μHE[n].restrict R.carrier; G(x) := θ(x)·⟨ω(x), ξ(x)⟩ = (R.mult x : ℝ) * R.orient x (ω x), where ω also denotes the underlying form (ω : DifferentialForm (Euclid P) n).

1. (Integrable kernel.) By the sibling action_integrable (Lean `Submission.rsd_cmr_ic_action_integrable P n U R ω`), G is μ-integrable.
2. (Rewriting the integrands.) For every x, θ(x)·h_k(x)·ξ(x)(ω(x)) = h_k(x)·G(x) and θ(x)·h(x)·ξ(x)(ω(x)) = h(x)·G(x), by commutativity and associativity of multiplication in ℝ (`funext` and `ring`). So it suffices to prove ∫ h_k·G dμ → ∫ h·G dμ.
3. (Measurability.) h_k is measurable and real-valued, hence a.e. strongly measurable (`Measurable.aestronglyMeasurable`); G is integrable, hence a.e. strongly measurable. So F_k := h_k·G is a.e. strongly measurable for μ (`AEStronglyMeasurable.mul`).
4. (Domination.) For every k and x, ‖F_k(x)‖ = |h_k(x)|·‖G(x)‖ ≤ C·‖G(x)‖ (`norm_mul`, the hypothesis |h_k(x)| ≤ C and ‖G(x)‖ ≥ 0, `mul_le_mul_of_nonneg_right`). The bound x ↦ C·‖G(x)‖ is μ-integrable (`Integrable.norm`, `Integrable.const_mul`).
5. (Pointwise convergence.) For every x, h_k(x)·G(x) → h(x)·G(x) as k → ∞ (`Tendsto.mul_const` applied to the hypothesis h_k(x) → h(x)).
6. (Dominated convergence.) By steps 3–5 and `tendsto_integral_of_dominated_convergence`, ∫ h_k·G dμ → ∫ h·G dμ. By step 2 this is the claim ∫_M θ·h_k·⟨ω, ξ⟩ dHⁿ → ∫_M θ·h·⟨ω, ξ⟩ dHⁿ. ∎

Lean reference implementation (kernel-checked during this decomposition against GMT.Ch07.Submission, Lean v4.35.0-rc3, Mathlib 25730c7c, with the accepted sibling `Submission.rsd_cmr_ic_action_integrable` in scope; `#print axioms` gives propext, Classical.choice, Quot.sound). Place it after the contract's `noncomputable section … end`, inside `namespace GMT.Ch07`:

```lean
theorem Submission.dor_lmbsf_ll_action_mul_tendsto : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (ω : TestFormOn U n) (hs : ℕ → Euclid P → ℝ) (h : Euclid P → ℝ) (C : ℝ), (∀ k, Measurable (hs k)) → (∀ k x, |hs k x| ≤ C) → (∀ x, Tendsto (fun k => hs k x) atTop (𝓝 (h x))) → Tendsto (fun k => ∫ x in R.carrier, (R.mult x : ℝ) * hs k x * R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]) atTop (𝓝 (∫ x in R.carrier, (R.mult x : ℝ) * h x * R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n])) := by
  intro P n U R ω hs h C hmeas hbdd hlim
  have hG := Submission.rsd_cmr_ic_action_integrable P n U R ω
  set G : Euclid P → ℝ := fun x => (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x)
    with hG_def
  have key : ∀ k, (fun x => (R.mult x : ℝ) * hs k x * R.orient x ((ω : DifferentialForm (Euclid P) n) x))
      = fun x => hs k x * G x := by
    intro k; funext x; simp only [G]; ring
  have keyh : (fun x => (R.mult x : ℝ) * h x * R.orient x ((ω : DifferentialForm (Euclid P) n) x))
      = fun x => h x * G x := by
    funext x; simp only [G]; ring
  rw [keyh]
  simp_rw [key]
  refine tendsto_integral_of_dominated_convergence (fun x => C * ‖G x‖) ?_ ?_ ?_ ?_
  · intro k; exact (hmeas k).aestronglyMeasurable.mul hG.aestronglyMeasurable
  · exact hG.norm.const_mul C
  · intro k
    filter_upwards with x
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using hbdd k x) (norm_nonneg _)
  · filter_upwards with x
    exact (hlim x).mul_const (G x)
```

## Key steps

1. G := θξ(ω) is integrable on M (sibling action_integrable).
2. Rewrite θ·h_k·ξ(ω) = h_k·G and θ·h·ξ(ω) = h·G.
3. h_k·G is a.e. strongly measurable, dominated by C|G| (integrable), and converges pointwise to h·G.
4. Conclude by dominated convergence (tendsto_integral_of_dominated_convergence).

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
