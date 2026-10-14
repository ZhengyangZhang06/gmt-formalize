# Parent-supplied natural-language proof

- Parent DAG node: `root.half_space_cone_lies_in_boundary-a1.imrep_support_eq_measure_support-a1`
- Child DAG node: `root.half_space_cone_lies_in_boundary-a1.imrep_support_eq_measure_support-a1.unit_orientation_nonzero_bounded-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof steps 1(b)–(c) (Simon Ch. 6, 1.1 and 1.7: a unit orientation is ξ = ±τ_1∧⋯∧τ_n for an orthonormal basis τ of the plane).
Notation: Λ^n = Covector (Euclid P) n carries the operator norm ‖α‖ = inf{C ≥ 0 : |α(w)| ≤ C∏_i‖w_i‖ for all w}, and Λ_n = MultiVector P n = (Λ^n →L[ℝ] ℝ) carries its operator norm. The hypothesis that τ spans Q is not used.

1. Unpacking. By IsUnitOrientationOf ξ Q there are a family τ = (τ_1,…,τ_n) and a sign ε ∈ {1, −1} such that ξ(α) = ε·α(τ) for every α ∈ Λ^n, where α(τ) := α(τ_1,…,τ_n). The family is orthonormal: ‖τ_i‖ = 1 for every i and ⟨τ_i, τ_j⟩ = 0 for i ≠ j. The two branches of the disjunction are ε = 1 and ε = −1.

2. Norm bound. Let α ∈ Λ^n. By the operator-norm inequality for continuous multilinear maps (ContinuousAlternatingMap.le_opNorm) and ‖τ_i‖ = 1,
 |ξ(α)| = |α(τ)| ≤ ‖α‖·∏_{i=1}^n ‖τ_i‖ = ‖α‖.
 So |ξ(α)| ≤ 1·‖α‖ for all α, and therefore ‖ξ‖ ≤ 1 (ContinuousLinearMap.opNorm_le_bound with the constant 1 ≥ 0).

3. A test covector. Put m(w_1,…,w_n) := ∏_{i=1}^n ⟨τ_i, w_i⟩. This is a continuous n-linear form: the product form ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ, composed in slot i with the continuous linear functional innerSL ℝ τ_i via compContinuousLinearMap. Let δ := Alt(m) be its alternatization (ContinuousMultilinearMap.alternatization). Then δ is a continuous alternating n-linear form, i.e. δ ∈ Λ^n, and by alternatization_apply_apply
 δ(w) = Σ_{σ ∈ S_n} sign(σ)·∏_{i} ⟨τ_i, w_{σ(i)}⟩.
 Equivalently, δ(w) = det(⟨τ_i, w_j⟩)_{i,j}.

4. δ(τ) = 1. We have δ(τ) = Σ_σ sign(σ) ∏_i ⟨τ_i, τ_{σ(i)}⟩.
 - If σ ≠ id, choose i with σ(i) ≠ i. Orthonormality gives ⟨τ_i, τ_{σ(i)}⟩ = 0, so that product is 0 (Finset.prod_eq_zero).
 - The term σ = id is sign(id)·∏_i ⟨τ_i, τ_i⟩ = ∏_i ‖τ_i‖² = 1.
 Hence δ(τ) = 1 (Finset.sum_eq_single). This includes n = 0, where S_0 = {id} and the empty product is 1.

5. Nonvanishing. ξ(δ) = ε·δ(τ) = ε ∈ {1, −1}, so ξ(δ) ≠ 0. If ξ were 0 we would have ξ(δ) = 0. Hence ξ ≠ 0.

6. Steps 2 and 5 give ξ ≠ 0 ∧ ‖ξ‖ ≤ 1.

## Key steps

1. Unpack IsUnitOrientationOf: ξ(α) = ε·α(τ) for all covectors α, with τ orthonormal and ε = ±1.
2. |ξ(α)| = |α(τ)| ≤ ‖α‖·∏‖τ_i‖ = ‖α‖ (ContinuousAlternatingMap.le_opNorm), so ‖ξ‖ ≤ 1 (opNorm_le_bound).
3. δ := alternatization of w ↦ ∏_i⟨τ_i, w_i⟩ (mkPiAlgebra ∘ innerSL) is an n-covector with δ(w) = Σ_σ sign σ ∏_i⟨τ_i, w_{σ i}⟩.
4. Orthonormality kills every σ ≠ id, so δ(τ) = 1.
5. ξ(δ) = ±1 ≠ 0, hence ξ ≠ 0.

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
