# Parent-supplied natural-language proof

- Parent DAG node: `root.lipschitz_pushforward_im-a1.rectifiable_support_null-a1`
- Child DAG node: `root.lipschitz_pushforward_im-a1.rectifiable_support_null-a1.support_null_reduction-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. ℝ^P = Eucl P = EuclideanSpace ℝ (Fin P). μ is an arbitrary measure on ℝ^P; it is applied to arbitrary sets as an outer measure, and only monotonicity and countable subadditivity are used. For the current T ∈ D_n(U) (T : GeometricCurrentOn U n), "T vanishes on W" (`T.VanishesOn W`) means T(ω) = 0 for every ω ∈ Dⁿ(U) (`TestFormOn U n`) with tsupport ω ⊆ W. Let 𝒮 be the family of all W ⊆ ℝ^P such that W is open, closure W is compact, closure W ⊆ U and T vanishes on W. By definition (SimonGMT `GeometricCurrentOn.zeroRegion`, `GeometricCurrentOn.support`; Simon Ch. 6, 2.11) the zero region is Z_T := T.zeroRegion = ⋃₀ 𝒮 and spt T := T.support = U ∖ Z_T. This is steps 1, 2 and 9 of the parent proof, stated for an arbitrary measure.

1. (M ∖ spt T ⊆ Z_T.) Let x ∈ M with x ∉ spt T. Since M ⊆ U, x ∈ U. If x ∉ Z_T, then x ∈ U ∖ Z_T = spt T, contradicting x ∉ spt T. Hence x ∈ Z_T.

2. (A countable subfamily has the same union.) Every member of 𝒮 is open and ℝ^P is second countable. Hence there is a countable subfamily 𝒮′ ⊆ 𝒮 with ⋃₀ 𝒮′ = ⋃₀ 𝒮 = Z_T (Lindelöf property of second-countable spaces; Mathlib `TopologicalSpace.isOpen_sUnion_countable`).

3. (Covering.) Let x ∈ M ∖ spt T. By steps 1 and 2, x ∈ Z_T = ⋃₀ 𝒮′, so x ∈ W for some W ∈ 𝒮′; since also x ∈ M, x ∈ W ∩ M. Hence M ∖ spt T ⊆ ⋃_{W ∈ 𝒮′} (W ∩ M).

4. (Every piece is null.) Let W ∈ 𝒮′. Then W ∈ 𝒮, so W is open, closure W is compact, closure W ⊆ U and T vanishes on W. The hypothesis gives μ(M ∩ W) = 0, i.e. μ(W ∩ M) = 0.

5. (Conclusion.) Since 𝒮′ is countable, countable subadditivity and step 4 give μ(⋃_{W ∈ 𝒮′} (W ∩ M)) ≤ Σ_{W ∈ 𝒮′} μ(W ∩ M) = 0 (Mathlib `measure_biUnion_null_iff`). By step 3 and monotonicity (`measure_mono_null`), μ(M ∖ spt T) = 0. ∎

Formalization aid (not part of the mathematical argument). The following Lean proof of exactly this frozen statement compiled (Lean v4.35.0-rc3, Mathlib 25730c7c, frozen project d8d46c9, shared pinned packages) when placed inside `namespace Submission` immediately before `theorem main_theorem` in a scratch copy of GMT/Ch06/Submission.lean; `#print axioms` gives [propext, Classical.choice, Quot.sound], and the comparator's generated NodeSolution module (`exact Submission.lpf_rsn_null_diff_support_of_local_null`) typechecks:

```lean
theorem lpf_rsn_null_diff_support_of_local_null : ∀ (P n : ℕ) (U : Set (Eucl P)) (T : GeometricCurrentOn U n) (M : Set (Eucl P)) (μ : Measure (Eucl P)), M ⊆ U → (∀ W : Set (Eucl P), IsOpen W → IsCompact (closure W) → closure W ⊆ U → T.VanishesOn W → μ (M ∩ W) = 0) → μ (M \ T.support) = 0 := by
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

1. Since M ⊆ U, M ∖ spt T ⊆ Z_T = ⋃₀ 𝒮, where 𝒮 is the family of open W with compact closure inside U on which T vanishes.
2. Lindelöf (second countability of ℝ^P): a countable subfamily 𝒮′ ⊆ 𝒮 has the same union (TopologicalSpace.isOpen_sUnion_countable).
3. Hence M ∖ spt T ⊆ ⋃_{W ∈ 𝒮′} (W ∩ M), and μ(M ∩ W) = 0 for each W ∈ 𝒮′ by hypothesis.
4. Countable subadditivity and monotonicity give μ(M ∖ spt T) = 0.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean GMT/Ch06/Contract.lean (identical); cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean (identical)`
- `rg -n 'theorem IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero' mathlib/Mathlib`
- `rg -n 'theorem isOpen_sUnion_countable' mathlib/Mathlib/Topology/Bases.lean`
- `rg -n 'theorem .*ext_multilinear' mathlib/Mathlib/LinearAlgebra/Multilinear/ mathlib/Mathlib/LinearAlgebra/Basis/`
- `rg -n 'theorem of_injective' mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Defs.lean`
- `rg -n 'theorem ae_restrict_mem₀' mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `rg -n 'theorem measure_biUnion_null_iff' mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`
- `rg -n 'theorem Integrable.mul_bdd|theorem Integrable.bdd_mul' mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `rg -n 'theorem opNorm_zero|theorem opNorm_neg|theorem opNorm_nonneg' mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean mathlib/Mathlib/Analysis/Normed/Operator/NormedSpace.lean`
- `rg -n 'Module.Finite.multilinearMap' mathlib/Mathlib/LinearAlgebra/Multilinear/FiniteDimensional.lean`
- `rg -n 'theorem restrict_restrict ' mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean; rg -n 'theorem IntegrableOn.locallyIntegrableOn' mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `grep -n -E '^(theorem|lemma|def|abbrev|structure|class|instance|noncomputable def)' simongmt/Poincare/SimonGMT/Chapter06/{Currents,Forms,FormsDuality}.lean; sed -n 1,200p simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `grep -rn -E 'FiniteDimensional ℝ \(Covector|FiniteDimensional .*Covector|zeroRegion|VanishesOn' simongmt/Poincare/SimonGMT/Chapter06/*.lean`
- `lake env lean Scratch/Probe1.lean (#check IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero, TopologicalSpace.isOpen_sUnion_countable, wedgeCovectors_apply_det; 'example : FiniteDimensional ℝ (Covector (Eucl P) n) := by infer_instance' fails)`
- `lake env lean Scratch/Probe2.lean (Module.Finite.multilinearMap unknown after import GMT.Ch06.Submission; #synth Module.Finite ℝ (MultilinearMap ℝ (fun _ : Fin n => Eucl P) ℝ) fails)`
- `lake env lean Scratch/Probe3.lean (Module.Basis.ext_multilinear, MultilinearMap.map_sum, EuclideanSpace.basisFun, Module.finBasis, FiniteDimensional.of_injective available)`
- `python3 listing of lean_name fields in dag.json; grep -rl 'lpf_rsn' .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca (no match)`
- `verifier/gmt-compare.py contract_scope + child_modules (contract mode) for the four children and the parent; lean_contract.validate_lean_statement on all statements`
- `lake env lean Scratch/RSNStmts.lean; lake env lean -o (scratch Submission with child proofs); lake env lean Scratch/Node/NodeChallenge_*.lean and Scratch/Node/Ax_NodeSolution_*.lean; lake env lean Scratch/RSNSufficiency.lean`
- `grep -n -i -E 'spt T|support' book/chapter-06.txt; sed -n 292,310p book/chapter-06.txt (Simon 2.11–2.12)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Multilinear/Basis.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Multilinear/FiniteDimensional.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Operator/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-rectifiable-support-null-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/rsn_scratch_lpf/Scratch/RSNStmts.lean`
- `/tmp/rsn_scratch_lpf/Scratch/RSNProofs.lean`
- `/tmp/rsn_scratch_lpf/GMT/Ch06/Submission.lean`
- `/tmp/rsn_scratch_lpf/Scratch/RSNSufficiency.lean`
- `/tmp/rsn_scratch_lpf/Scratch/Node/NodeSolution_lpf_rsn_local_null.lean`

Snapshot and environment.
- The snapshot (project d8d46c95, Mathlib 25730c7c) contains the frozen Ch06 Contract. It is byte-identical to the workspace Contract and Submission.
- In the child scope (`import GMT.Ch06.Submission` plus the replayed namespace and opens), the support is SimonGMT's `GeometricCurrentOn.support = U \\ zeroRegion`. The zero region is the union over W open with compact closure inside U and `T.VanishesOn W`, matching Simon 2.11.
- No SimonGMT lemma packages a support-null statement or finite-dimensionality of covectors.

Available Mathlib lemmas (all at the pinned snapshot):
- `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` (AEEqOfIntegralContDiff.lean:205), needing only `LocallyIntegrableOn`, no local finiteness;
- `TopologicalSpace.isOpen_sUnion_countable` (Bases.lean:948) and `measure_biUnion_null_iff` (OuterMeasure/Basic.lean:107);
- `ae_restrict_mem₀` (Restrict.lean:637) and `Measure.restrict_restrict` (Restrict.lean:205);
- `Integrable.mul_bdd` (Integrable.lean:1072) and `IntegrableOn.locallyIntegrableOn` (LocallyIntegrable.lean:113);
- `Module.Basis.ext_multilinear` (Multilinear/Basis.lean:30) and `FiniteDimensional.of_injective` (FiniteDimensional/Defs.lean:84);
- `ContinuousLinearMap.opNorm_zero`, `opNorm_neg`, `opNorm_nonneg` (Operator/Basic.lean:214–220).

What is not available.
- `FiniteDimensional ℝ (Covector (Eucl P) n)` is not inferred.
- `Module.Finite.multilinearMap` (Multilinear/FiniteDimensional.lean:66) is outside the import closure.
- Hence the separate covector child, proved with an `ext_multilinear` injection.
- Generic `norm_zero`/`norm_neg`/`norm_nonneg` do not rewrite against the `ContinuousLinearMap.hasOpNorm` norm on NVector; the `opNorm_*` lemmas do.

Checks run.
- All four child statements pass the validator and elaborate in the comparator child scope.
- Their scratch Lean proofs compile, and the NodeSolution modules typecheck with standard axioms only.
- The parent assembly and the hypothesis-only sufficiency theorems are kernel-checked with standard axioms; the parent check uses a sorry stub only for the existing sibling dependency `lpf_simple_nvector_algebra`.
- No `lpf_rsn_*` name is reserved anywhere in the run.
