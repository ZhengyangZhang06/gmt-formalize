# Parent-supplied natural-language proof

- Parent DAG node: `root.half_space_cone_lies_in_boundary-a1.imrep_support_eq_measure_support-a1`
- Child DAG node: `root.half_space_cone_lies_in_boundary-a1.imrep_support_eq_measure_support-a1.current_vanishes_where_weight_null-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 2, the inclusion spt T ⊆ spt μ_T of Simon Ch. 6, 2.11–2.12 (chapter-06.txt lines 296–305).
Notation: ν := H^n⌞M = μHE[n].restrict M and μ := R.measure = ν.withDensity(x ↦ θ(x)). Recall θ(x) ≥ 1 for x ∈ M (R.mult_pos), θ is measurable (R.measurable_mult), and M is Borel (R.measurableSet_carrier). No openness of U or W is needed.

1. Let ω ∈ TestFormOn U n with K := tsupport ω ⊆ W. K is closed, hence Borel. By monotonicity of the measure, μ(K) ≤ μ(W) = 0, so μ(K) = 0.

2. Since K is measurable, μ(K) = ∫⁻_K θ dν (withDensity_apply). So the lintegral of x ↦ (θ(x) : [0,∞]) against ν⌞K is 0. This function is measurable, so θ(x) = 0 for ν⌞K-a.e. x (lintegral_eq_zero_iff).

3. Next, ν(K) = 0.
 - Since M is measurable, ν-a.e. x lies in M (ae_restrict_mem), and hence ν⌞K-a.e. x lies in M (ae_restrict_of_ae).
 - For x ∈ M, θ(x) ≥ 1, so θ(x) ≠ 0.
 - Combined with step 2, ν⌞K-almost every x satisfies a contradiction. Thus (ν⌞K)(ℝ^P) = 0, i.e. ν(K) = 0 (Measure.restrict_apply_univ, measure_eq_zero_iff_ae_notMem).

4. Hence ν-a.e. x satisfies x ∉ K (measure_eq_zero_iff_ae_notMem). For such x, x ∉ tsupport ω gives ω(x) = 0 (image_eq_zero_of_notMem_tsupport). By linearity of ξ(x), θ(x)·ξ(x)(ω(x)) = θ(x)·ξ(x)(0) = 0.

5. So the integrand of R.action(ω) = ∫ θ(x)·ξ(x)(ω(x)) dν(x) vanishes ν-a.e., and the integral is 0 (integral_eq_zero_of_ae). By the representation, T(ω) = R.action(ω) = 0. Since ω was an arbitrary test form in TestFormOn U n with tsupport ω ⊆ W, T vanishes on W.

## Key steps

1. For a test form ω with tsupport ω ⊆ W: μ(tsupport ω) ≤ μ(W) = 0.
2. μ(K) = ∫⁻_K θ d(H^n⌞M) = 0 for the closed set K = tsupport ω, so θ = 0 a.e. on K for H^n⌞M.
3. θ ≥ 1 on M forces (H^n⌞M)(K) = 0.
4. The integrand θ·ξ(ω) vanishes (H^n⌞M)-a.e. because ω = 0 off K, so T(ω) = R.action(ω) = 0.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `cat GMT/Ch07/Submission.lean (IMRep, IMRep.action, IMRep.Represents, IMRep.measure, IsUnitOrientationOf, MultiVector)`
- `cat simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean Currents.lean Forms.lean Mass.lean; sed -n 1,229p Chapter06/FormsDuality.lean; head -20 Chapter06/AffineCurrentPushforward.lean; grep -n import Chapter04/Basic.lean Chapter03/Rectifiable.lean`
- `grep -rn 'det\b|\.det|Matrix.det|mkContinuous|Orthonormal' Chapter06/*.lean`
- `sed -n 1,80p and 140,260p mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `grep -rn 'def alternatization|theorem alternatization_apply|def mkPiAlgebra|theorem mkPiAlgebra_apply' Mathlib/Topology/Algebra/Module/Alternating/Basic.lean Mathlib/Topology/Algebra/Module/Multilinear/Basic.lean; sed -n 630,660p Alternating/Basic.lean`
- `grep -rn 'ext_multilinear|ext_alternating' Mathlib; sed -n 900,915p Mathlib/LinearAlgebra/Alternating/Basic.lean; grep -rn 'continuous_of_finiteDimensional|Module.Finite.multilinearMap'`
- `grep -rn 'measure_eq_zero_iff_ae_notMem|ae_restrict_mem|withDensity_apply|lintegral_eq_zero_iff|withDensity_absolutelyContinuous|locallyIntegrableOn_iff|IntegrableOn.of_bound|integrable_of_forall_notMem_eq_zero|Integrable.bdd_smul|image_eq_zero_of_notMem_tsupport' mathlib/Mathlib`
- `#synth/#check probes: NormedAddCommGroup (MultiVector P n) ok; ContinuousENorm (MultiVector P n) fails (trace: WithLp.instAddCommGroup path); FiniteDimensional/SeparableSpace (Covector (Euclid P) n) not instances; continuous_eval_const and le_opNorm ok`
- `grep -rhoE '"lean_name": *"[^"]+"' dag.json nodes | sort -u; grep -rIl 'imsupp_' workspaces cluster-state .swarm-worktrees (no match)`
- `sed -n 290,310p and 755,775p book/chapter-06.txt (Simon 6.2.11-2.12, 6.3.2(3))`
- `lake env lean /tmp/imsupp-decomp/{Stmts,Assembly,Child1,Child2s,Child2basis,Child3,FinDim2,Final}.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-imrep-support-eq-measure-support-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-imrep-measure-unique-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Multilinear/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Multilinear/FiniteDimensional.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/imsupp-decomp/Stmts.lean`
- `/tmp/imsupp-decomp/Assembly.lean`
- `/tmp/imsupp-decomp/Child1.lean`
- `/tmp/imsupp-decomp/Child2s.lean`
- `/tmp/imsupp-decomp/Child2basis.lean`
- `/tmp/imsupp-decomp/Child3.lean`
- `/tmp/imsupp-decomp/FinDim2.lean`
- `/tmp/imsupp-decomp/Final.lean`

The snapshot contract (project b4d606d, mathlib 25730c7c) is byte-identical to the workspace Contract.lean and Submission.lean.

Relevant definitions:
- SimonGMT CurrentLocalEquality.lean defines GeometricCurrentOn.VanishesOn W as T ω = 0 whenever tsupport ω ⊆ W.
- zeroRegion is ⋃₀ {W | IsOpen W ∧ IsCompact (closure W) ∧ closure W ⊆ U ∧ T.VanishesOn W}, and support is U \ zeroRegion.
- Mathlib Measure.support has mem_support_iff_forall.

Library support for the children:
- The fundamental lemma IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (real- or Banach-valued, LocallyIntegrableOn on an open set, no local finiteness) is in AEEqOfIntegralContDiff.lean.
- integral_withDensity_eq_integral_smul, withDensity_apply, lintegral_eq_zero_iff, measure_eq_zero_iff_ae_notMem, locallyIntegrableOn_iff and IntegrableOn.of_bound are present.
- The determinant covector can be built from ContinuousMultilinearMap.mkPiAlgebra, compContinuousLinearMap and ContinuousMultilinearMap.alternatization. SimonGMT FormsDuality.wedgeCovectors is equivalent but not imported by GMT.Ch07.Submission.

Instance findings:
- ContinuousENorm (MultiVector P n) is not synthesized (instance path through WithLp.instAddCommGroup). NormedAddCommGroup, continuous_eval_const and le_opNorm work.
- FiniteDimensional ℝ (Covector (Euclid P) n) is not an instance, but follows in about 12 lines from Module.Basis.ext_alternating and Module.Finite.of_injective. SeparableSpace then follows by infer_instance.
- Hence child 2's scalar, basis-testing route.

Lean verification: kernel-checked scratch proofs exist for all three children (child 2 given child 1), and the parent's exact frozen type was proved from children 2 and 3. All use only propext, Classical.choice and Quot.sound. The names imsupp_unit_orientation_ne_zero_norm_le_one, imsupp_measure_eq_zero_of_vanishesOn and imsupp_vanishesOn_of_measure_eq_zero are not reserved anywhere in the DAG.
