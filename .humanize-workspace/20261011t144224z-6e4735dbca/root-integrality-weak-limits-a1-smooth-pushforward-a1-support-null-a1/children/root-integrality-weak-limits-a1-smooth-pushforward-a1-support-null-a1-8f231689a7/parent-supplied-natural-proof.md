# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.smooth_pushforward-a1.support_null-a1`
- Child DAG node: `root.integrality_weak_limits-a1.smooth_pushforward-a1.support_null-a1.signed_simple_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1(a) and 1(b) of the parent proof, the pointwise algebra at a good point x with τ orthonormal and ξ(x) = ±τ₁ ∧ ⋯ ∧ τ_n. Here w plays the role of ξ(x). Siblings used: none.

Conventions.
- For b ∈ Covector (Eucl P) n, ‖b‖ is the operator norm of the continuous alternating map. Hence |b(v_1, …, v_n)| ≤ ‖b‖·Π_i ‖v_i‖ for every tuple v (Mathlib ContinuousAlternatingMap.le_opNorm).
- simpleNVector τ is the continuous linear functional b ↦ b(τ) = b(τ_1, …, τ_n) (SimonGMT simpleNVector_apply, true by definition).
- innerSL ℝ u : ℝ^P →L[ℝ] ℝ is the functional v ↦ ⟨u, v⟩ (Mathlib innerSL_apply_apply).
- wedgeCovectors n α is the exterior product of the 1-covectors α_1, …, α_n. SimonGMT wedgeCovectors_apply_det states wedgeCovectors n α (v) = det(α_i(v_j))_{i,j}.

1. (Evaluation.) Let b be an n-covector. If w = simpleNVector τ then w(b) = b(τ). If w = −simpleNVector τ then w(b) = −b(τ). In both cases |w(b)| = |b(τ)|.

2. (Bound, part (i).) Orthonormality gives ‖τ_i‖ = 1 for every i, so Π_i ‖τ_i‖ = 1 (for n = 0 the empty product is 1). Hence |b(τ)| ≤ ‖b‖·Π_i ‖τ_i‖ = ‖b‖. By step 1, |w(b)| ≤ ‖b‖ for every n-covector b.

3. (A test covector.) Put b_τ := wedgeCovectors n (i ↦ innerSL ℝ τ_i). By wedgeCovectors_apply_det, b_τ(τ) = det A, where A_{ij} = innerSL ℝ τ_i (τ_j) = ⟨τ_i, τ_j⟩. By orthonormality, ⟨τ_i, τ_j⟩ = 1 if i = j and 0 otherwise (Mathlib orthonormal_iff_ite). So A is the n × n identity matrix and b_τ(τ) = det 1 = 1 (Mathlib Matrix.det_one; for n = 0 the empty determinant is 1).

4. (Nonvanishing, part (ii).) Suppose w = 0. Steps 1 and 3 then give 0 = |0(b_τ)| = |w(b_τ)| = |b_τ(τ)| = |1| = 1, a contradiction. Hence w ≠ 0. ∎

Formalization aid (not part of the mathematical argument). The following Lean proof of exactly this frozen statement compiled with Lean v4.35.0-rc3, Mathlib 25730c7c, frozen project d8d46c9 and the shared pinned packages. It was placed inside `namespace Submission`, immediately before `theorem main_theorem`, in a scratch copy of GMT/Ch06/Submission.lean. `#print axioms` gives [propext, Classical.choice, Quot.sound]. The comparator's generated NodeSolution module (`exact Submission.iwl_sp_sn_signed_simpleNVector_bound_ne_zero`) typechecks.

```lean
theorem iwl_sp_sn_signed_simpleNVector_bound_ne_zero : ∀ (P n : ℕ) (τ : Fin n → Eucl P) (w : NVector (Eucl P) n), Orthonormal ℝ τ → (w = simpleNVector τ ∨ w = -simpleNVector τ) → (∀ b : Covector (Eucl P) n, |w b| ≤ ‖b‖) ∧ w ≠ 0 := by
  intro P n τ w hτ hw
  have habs : ∀ b : Covector (Eucl P) n, |w b| = |b τ| := by
    intro b
    rcases hw with rfl | rfl
    · simp
    · simp
  have hbound : ∀ b : Covector (Eucl P) n, |b τ| ≤ ‖b‖ := by
    intro b
    have h1 := b.le_opNorm τ
    have hprod : ∏ i, ‖τ i‖ = 1 := Finset.prod_eq_one (fun i _ => hτ.1 i)
    rw [hprod, mul_one, Real.norm_eq_abs] at h1
    exact h1
  refine ⟨fun b => (habs b).trans_le (hbound b), ?_⟩
  intro h0
  have hdet : wedgeCovectors n (fun i => innerSL ℝ (τ i)) τ = 1 := by
    rw [wedgeCovectors_apply_det]
    have hm : (Matrix.of fun i j => (innerSL ℝ (τ i)) (τ j)) = (1 : Matrix (Fin n) (Fin n) ℝ) := by
      ext i j
      rw [Matrix.of_apply, innerSL_apply_apply, orthonormal_iff_ite.mp hτ i j, Matrix.one_apply]
    rw [hm, Matrix.det_one]
  have h1 := habs (wedgeCovectors n (fun i => innerSL ℝ (τ i)))
  rw [h0, hdet] at h1
  simp at h1
```

## Key steps

1. |w(b)| = |b(τ_1, …, τ_n)| for every covector b, whatever the sign.
2. |b(τ)| ≤ ‖b‖·Π_i‖τ_i‖ = ‖b‖, because ‖τ_i‖ = 1 (ContinuousAlternatingMap.le_opNorm).
3. b_τ := wedgeCovectors n (i ↦ innerSL ℝ τ_i) satisfies b_τ(τ) = det(⟨τ_i, τ_j⟩) = det 1 = 1 (wedgeCovectors_apply_det, orthonormal_iff_ite).
4. If w = 0, then 0 = |w(b_τ)| = |b_τ(τ)| = 1, a contradiction. So w ≠ 0.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp GMT/Ch06/Submission.lean GMT/Ch06/Contract.lean (identical); cmp GMT/Ch06/Submission.lean local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean (identical); rg -n 'Submission\.' project/GMT/Ch06/Submission.lean (no match)`
- `rg -n 'structure IsRectifiableTriple|def tauAction|orients :|integrableOn :|aestronglyMeasurable :|pos :|nullMeasurableSet :|subset :' project/GMT/Ch06/Contract.lean`
- `rg -n 'theorem IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero' mathlib/Mathlib`
- `rg -n 'theorem isOpen_sUnion_countable' mathlib/Mathlib/Topology/Bases.lean`
- `rg -n 'theorem Module.Basis.ext_multilinear' mathlib/Mathlib; rg -n '^theorem of_injective' mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Defs.lean; rg -n 'def finBasis' mathlib/Mathlib; grep -n 'theorem ext \|^namespace' mathlib/Mathlib/LinearAlgebra/Basis/Defs.lean`
- `rg -n 'theorem orthonormal_iff_ite' mathlib/Mathlib; rg -n 'theorem innerSL_apply_apply' mathlib/Mathlib; rg -n '^theorem le_opNorm ' mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean; rg -n 'theorem det_one' mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `rg -n 'theorem Integrable.mul_bdd |theorem measure_biUnion_null_iff|theorem ae_restrict_mem₀|theorem ae_restrict_of_ae_restrict_of_subset|theorem restrict_restrict |theorem IntegrableOn.locallyIntegrableOn|theorem tsupport_smul_subset_left|theorem HasCompactSupport.smul_right' mathlib/Mathlib`
- `rg -n 'scoped\[MeasureTheory\] notation "μHE\["' mathlib/Mathlib`
- `rg -n 'instance.*FiniteDimensional.*ContinuousAlternatingMap|instance.*Module.Finite.*ContinuousAlternatingMap' mathlib/Mathlib (no match)`
- `rg -n 'iwl_sp_sn|lpf_rsn' project/ (no match); grep -rl 'iwl_sp_sn' runs/20261011T144224Z-6e4735dbca (no match); python3 -I scan of dag.json lean_name/lean_statement duplicates`
- `grep -n 'simpleNVector|wedgeCovectors|VanishesOn|zeroRegion|def support|IsTestForm|IsSmoothForm|TestFormOn' simongmt/Poincare/SimonGMT/Chapter06/{Forms,FormsDuality,Currents,CurrentLocalEquality}.lean`
- `python3 -I read of nodes/root-lipschitz-pushforward-im-a1-rectifiable-support-null-a1/decomposition-v1.json (accepted identical-type precedent)`
- `verifier gmt-compare.py contract_scope + child_modules (contract mode) and lean_contract.validate_lean_statement -> /tmp/iwl-sp-sn-decomp/work2/gen/NodeChallenge_*.lean, NodeSolution_*.lean`
- `pinned lean 4.35.0-rc3 (LEAN_PATH = workspace .lake/build/lib/lean + lake-packages-25730c7c/*/.lake/build/lib/lean) on NodeChallenge_*.lean; scratch Submission.lean -o build/GMT/Ch06/Submission.olean; NodeSolution_*.lean; Axioms.lean (#print axioms); Sufficiency.lean; InstCheck2.lean (#synth Norm (Covector (Eucl 3) 2); IsSmoothForm ω ↔ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω := Iff.rfl)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Multilinear/Basis.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Dimension/Free.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Basis/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/LinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-smooth-pushforward-a1-support-null-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-rectifiable-support-null-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/iwl-sp-sn-decomp/work2/Submission.lean`
- `/tmp/iwl-sp-sn-decomp/work2/gen/Sufficiency.lean`
- `/tmp/iwl-sp-sn-decomp/work2/gen/Axioms.lean`
- `/tmp/iwl-sp-sn-decomp/work/gen/InstCheck2.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) contains the frozen Ch06 Contract. Its byte-identical Submission has no Submission.* declarations, so all five iwl_sp_sn_* names are free; rg found no match in the snapshot, the run directory or dag.json.

Every cited Mathlib lemma exists at the pin with the stated hypotheses:
- IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (AEEqOfIntegralContDiff.lean:205) accepts an arbitrary measure, uses ContDiff ℝ ∞ and needs only LocallyIntegrableOn;
- TopologicalSpace.isOpen_sUnion_countable (Bases.lean:948), Module.Basis.ext_multilinear (Multilinear/Basis.lean:30), FiniteDimensional.of_injective (FiniteDimensional/Defs.lean:84), Module.finBasis and Module.Basis.ext (Basis/Defs.lean:315);
- orthonormal_iff_ite, innerSL_apply_apply, ContinuousAlternatingMap.le_opNorm and Matrix.det_one;
- Integrable.mul_bdd, measure_biUnion_null_iff, ae_restrict_mem₀, ae_restrict_of_ae_restrict_of_subset, Measure.restrict_restrict, IntegrableOn.locallyIntegrableOn, tsupport_smul_subset_left and HasCompactSupport.smul_right.

There is no FiniteDimensional/Module.Finite instance for ContinuousAlternatingMap (no match), so covector_basis proves finite-dimensionality by an injective coordinate map.

The pinned SimonGMT package supplies:
- simpleNVector_apply (by rfl) and wedgeCovectors_apply_det, which together yield the evaluation bound and nonvanishing of ±simpleNVector τ;
- VanishesOn, zeroRegion and support = U \ zeroRegion, matching support_cover.

The accepted identical-type node lpf_rectifiable_support_null was split the same way, with all children accepted.

Scratch Lean runs, with the workspace unmodified:
- all five child types elaborate in the comparator scope;
- the Lean aids compile and every NodeSolution typechecks;
- the parent type follows from the child propositions alone;
- only propext, Classical.choice and Quot.sound are used.
