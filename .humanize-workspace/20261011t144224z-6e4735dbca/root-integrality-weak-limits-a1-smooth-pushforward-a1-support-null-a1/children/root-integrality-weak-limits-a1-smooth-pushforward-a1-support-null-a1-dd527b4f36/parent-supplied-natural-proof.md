# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.smooth_pushforward-a1.support_null-a1`
- Child DAG node: `root.integrality_weak_limits-a1.smooth_pushforward-a1.support_null-a1.support_cover-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 8 of the parent proof (the countable union). Here it is stated for an arbitrary measure μ, with the local nullity of step 7 taken as a hypothesis. Siblings used: none.

The Lean statement is identical to that of the accepted DAG node root.lipschitz_pushforward_im-a1.rectifiable_support_null-a1.support_null_reduction-a1 (lpf_rsn_null_diff_support_of_local_null). This child keeps a fresh name, as this run does for other identical types, so the branch has no cross-branch dependency. The proof below is self-contained.

Conventions.
- ℝ^P = Eucl P = EuclideanSpace ℝ (Fin P) carries its usual metric topology, which is second countable.
- μ is applied to arbitrary subsets as an outer measure. Only monotonicity and countable subadditivity are used.
- "T vanishes on W" (T.VanishesOn W) means T(ω) = 0 for every ω ∈ Dⁿ(U) (TestFormOn U n) with tsupport ω ⊆ W.
- 𝒲 is the family of all W ⊆ ℝ^P such that W is open, closure W is compact, closure W ⊆ U and T vanishes on W.
- By the SimonGMT definitions GeometricCurrentOn.zeroRegion and GeometricCurrentOn.support (Simon Ch. 6, 2.11): T.zeroRegion = ⋃₀ 𝒲 and spt T = T.support = U ∖ T.zeroRegion.

1. (M ∖ spt T ⊆ T.zeroRegion.) Let x ∈ M with x ∉ T.support. Since M ⊆ U, x ∈ U. If x ∉ T.zeroRegion, then x ∈ U ∖ T.zeroRegion = T.support, a contradiction. Hence x ∈ T.zeroRegion.

2. (A countable subfamily with the same union.) Every member of 𝒲 is open and ℝ^P is second countable. By the Lindelöf property of second-countable spaces (Mathlib TopologicalSpace.isOpen_sUnion_countable) there is a countable subfamily 𝒲₀ ⊆ 𝒲 with ⋃₀ 𝒲₀ = ⋃₀ 𝒲 = T.zeroRegion.

3. (Covering.) Let x ∈ M ∖ T.support. By steps 1 and 2, x ∈ ⋃₀ 𝒲₀, so x ∈ W for some W ∈ 𝒲₀. Since also x ∈ M, x ∈ W ∩ M. Hence M ∖ T.support ⊆ ⋃_{W ∈ 𝒲₀} (W ∩ M).

4. (Each piece is null.) Let W ∈ 𝒲₀. Then W ∈ 𝒲, so W is open, closure W is compact, closure W ⊆ U and T vanishes on W. The hypothesis gives μ(M ∩ W) = 0, i.e. μ(W ∩ M) = 0.

5. (Conclusion.) 𝒲₀ is countable, so countable subadditivity and step 4 give μ(⋃_{W ∈ 𝒲₀} (W ∩ M)) = 0 (Mathlib measure_biUnion_null_iff). By step 3 and monotonicity (measure_mono_null), μ(M ∖ T.support) = 0. ∎

Formalization aid (not part of the mathematical argument). The following Lean proof of exactly this frozen statement compiled with Lean v4.35.0-rc3, Mathlib 25730c7c, frozen project d8d46c9 and the shared pinned packages. It was placed inside `namespace Submission`, immediately before `theorem main_theorem`, in a scratch copy of GMT/Ch06/Submission.lean. `#print axioms` gives [propext, Classical.choice, Quot.sound]. The comparator's generated NodeSolution module (`exact Submission.iwl_sp_sn_null_diff_support_of_local_null`) typechecks.

```lean
theorem iwl_sp_sn_null_diff_support_of_local_null : ∀ (P n : ℕ) (U : Set (Eucl P)) (T : GeometricCurrentOn U n) (M : Set (Eucl P)) (μ : Measure (Eucl P)), M ⊆ U → (∀ W : Set (Eucl P), IsOpen W → IsCompact (closure W) → closure W ⊆ U → T.VanishesOn W → μ (M ∩ W) = 0) → μ (M \ T.support) = 0 := by
  intro P n U T M μ hMU hloc
  obtain ⟨S', hS'c, hS'S, hS'eq⟩ := TopologicalSpace.isOpen_sUnion_countable
    {W : Set (Eucl P) | IsOpen W ∧ IsCompact (closure W) ∧ closure W ⊆ U ∧ T.VanishesOn W}
    (fun W hW => hW.1)
  have hsub : M \ T.support ⊆ ⋃ W ∈ S', W ∩ M := by
    intro x ⟨hxM, hxs⟩
    have hxZ : x ∈ T.zeroRegion := by
      by_contra hx
      exact hxs ⟨hMU hxM, hx⟩
    have hxZ' : x ∈ ⋃₀ S' := by
      rw [hS'eq]; exact hxZ
    obtain ⟨W, hW, hxW⟩ := hxZ'
    exact Set.mem_biUnion hW ⟨hxW, hxM⟩
  refine measure_mono_null hsub ?_
  rw [measure_biUnion_null_iff hS'c]
  intro W hW
  obtain ⟨hWo, hWc, hWU, hWv⟩ := hS'S hW
  rw [Set.inter_comm]
  exact hloc W hWo hWc hWU hWv
```

## Key steps

1. Since M ⊆ U, every x ∈ M ∖ spt T lies in T.zeroRegion = ⋃₀𝒲. Here 𝒲 is the family of open W with compact closure inside U on which T vanishes.
2. By second countability (Lindelöf, TopologicalSpace.isOpen_sUnion_countable), a countable subfamily 𝒲₀ ⊆ 𝒲 has the same union.
3. Hence M ∖ spt T ⊆ ⋃_{W∈𝒲₀} (W ∩ M), and each μ(M ∩ W) = 0 by hypothesis.
4. Countable subadditivity (measure_biUnion_null_iff) and monotonicity (measure_mono_null) give μ(M ∖ spt T) = 0.

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
