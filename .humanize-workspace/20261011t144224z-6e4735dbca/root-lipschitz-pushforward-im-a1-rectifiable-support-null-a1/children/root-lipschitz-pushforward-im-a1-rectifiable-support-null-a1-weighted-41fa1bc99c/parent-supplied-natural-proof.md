# Parent-supplied natural-language proof

- Parent DAG node: `root.lipschitz_pushforward_im-a1.rectifiable_support_null-a1`
- Child DAG node: `root.lipschitz_pushforward_im-a1.rectifiable_support_null-a1.weighted_fundamental_lemma-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. ℝ^P = Eucl P carries its Borel σ-algebra; μ⌞M := μ.restrict M, and ∫_M h dμ is by definition ∫ h d(μ⌞M). "C^∞" means `ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)`. This is steps 4–7 of the parent proof with the positive weight moved from the measure ν = θ·μ⌞(M ∩ W) into the integrand: we apply the fundamental lemma of the calculus of variations to f := θ·g and the measure μ⌞M, and divide by θ at the end. (In the parent's notation, θ·g = 0 μ⌞M-a.e. on W is the same as g = 0 ν-a.e., and ν-null and μ-null subsets of M ∩ W coincide because θ > 0 on M.)

1. (f := θ·g is integrable on W for μ⌞M.) W is open, hence Borel, so (μ⌞M)⌞W = μ⌞(W ∩ M) = μ⌞(M ∩ W) (Mathlib `Measure.restrict_restrict`). By (ii), θ is integrable for μ⌞(M ∩ W). Since μ⌞(M ∩ W) ≤ μ⌞M (`Measure.restrict_mono`), (iii) gives that g is a.e.-strongly measurable for μ⌞(M ∩ W), and (iv) gives |g(x)| ≤ C for μ⌞(M ∩ W)-a.e. x (an a.e. property for μ⌞M holds a.e. for the restriction to the subset M ∩ W, `ae_restrict_of_ae_restrict_of_subset`). The product of an integrable function with an a.e.-bounded, a.e.-strongly measurable function is integrable (Mathlib `Integrable.mul_bdd`), so θ·g is integrable for μ⌞(M ∩ W), i.e. θ·g is integrable on W for μ⌞M. In particular θ·g is locally integrable on W for μ⌞M (`IntegrableOn.locallyIntegrableOn`).

2. (The tests vanish.) Let φ : ℝ^P → ℝ be C^∞ with compact support and tsupport φ ⊆ W. Pointwise φ(x)·(θ(x)·g(x)) = θ(x)·(φ(x)·g(x)) (commutativity and associativity of the real product). Hence ∫ φ(x)·f(x) d(μ⌞M)(x) = ∫_M θ(x)·(φ(x)·g(x)) dμ(x) = 0 by (v).

3. (Fundamental lemma.) ℝ^P is a finite-dimensional real normed space with its Borel σ-algebra, ℝ is complete, W is open, f is locally integrable on W for μ⌞M (step 1), and ∫ φ·f d(μ⌞M) = 0 for every C^∞ compactly supported φ with tsupport φ ⊆ W (step 2). By the fundamental lemma of the calculus of variations on an open set (Mathlib `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`, whose only analytic hypothesis is local integrability of f on W; no finiteness property of the measure is required), for μ⌞M-a.e. x: x ∈ W ⇒ θ(x)·g(x) = 0.

4. (Remove the weight.) Since M is μ-null-measurable, μ⌞M-a.e. x lies in M (Mathlib `ae_restrict_mem₀`). Take x in the intersection of this full-measure set with the one from step 3, and suppose x ∈ W. Then θ(x)·g(x) = 0, and θ(x) > 0 by (i) because x ∈ M; so θ(x) ≠ 0 and g(x) = 0. Hence for μ⌞M-a.e. x: x ∈ W ⇒ g(x) = 0. ∎

Formalization aid (not part of the mathematical argument). The following Lean proof of exactly this frozen statement compiled (Lean v4.35.0-rc3, Mathlib 25730c7c, frozen project d8d46c9, shared pinned packages) when placed inside `namespace Submission` immediately before `theorem main_theorem` in a scratch copy of GMT/Ch06/Submission.lean; `#print axioms` gives [propext, Classical.choice, Quot.sound], and the comparator's generated NodeSolution module (`exact Submission.lpf_rsn_weighted_fundamental_lemma`) typechecks:

```lean
theorem lpf_rsn_weighted_fundamental_lemma : ∀ (P : ℕ) (μ : Measure (Eucl P)) (M W : Set (Eucl P)) (θ g : Eucl P → ℝ) (C : ℝ), IsOpen W → NullMeasurableSet M μ → (∀ x ∈ M, 0 < θ x) → IntegrableOn θ (M ∩ W) μ → AEStronglyMeasurable g (μ.restrict M) → (∀ᵐ x ∂(μ.restrict M), |g x| ≤ C) → (∀ φ : Eucl P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ W → ∫ x in M, θ x * (φ x * g x) ∂μ = 0) → ∀ᵐ x ∂(μ.restrict M), x ∈ W → g x = 0 := by
  intro P μ M W θ g C hW hM hpos hθ hg hgC hint
  have hfint : IntegrableOn (fun x => θ x * g x) W (μ.restrict M) := by
    rw [IntegrableOn, Measure.restrict_restrict hW.measurableSet, Set.inter_comm]
    have hθ' : Integrable θ (μ.restrict (M ∩ W)) := hθ
    have hg' : AEStronglyMeasurable g (μ.restrict (M ∩ W)) :=
      hg.mono_measure (Measure.restrict_mono Set.inter_subset_left le_rfl)
    have hgC' : ∀ᵐ x ∂(μ.restrict (M ∩ W)), ‖g x‖ ≤ C := by
      have := ae_restrict_of_ae_restrict_of_subset (Set.inter_subset_left : M ∩ W ⊆ M) hgC
      filter_upwards [this] with x hx
      simpa [Real.norm_eq_abs] using hx
    exact hθ'.mul_bdd hg' hgC'
  have hzero := hW.ae_eq_zero_of_integral_contDiff_smul_eq_zero hfint.locallyIntegrableOn
    (fun φ hφ hφc hφW => by
      rw [← hint φ hφ hφc hφW]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [smul_eq_mul]
      ring)
  filter_upwards [hzero, ae_restrict_mem₀ hM] with x hx hxM hxW
  rcases mul_eq_zero.mp (hx hxW) with h | h
  · exact absurd h (hpos x hxM).ne'
  · exact h
```

## Key steps

1. θ·g is integrable on W for μ⌞M: (μ⌞M)⌞W = μ⌞(M ∩ W), θ is integrable there and g is a.e.-bounded and a.e.-strongly measurable (Integrable.mul_bdd).
2. For every C^∞ compactly supported φ with tsupport φ ⊆ W, ∫ φ·(θg) d(μ⌞M) = ∫_M θ·(φg) dμ = 0.
3. Mathlib's fundamental lemma IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero gives θg = 0 μ⌞M-a.e. on W.
4. μ⌞M-a.e. point lies in M (ae_restrict_mem₀), where θ > 0, so g = 0 μ⌞M-a.e. on W.

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
