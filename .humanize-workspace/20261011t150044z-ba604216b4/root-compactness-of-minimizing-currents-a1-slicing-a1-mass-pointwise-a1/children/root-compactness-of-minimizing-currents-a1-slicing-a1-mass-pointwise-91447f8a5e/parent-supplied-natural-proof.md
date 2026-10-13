# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.slicing-a1.mass_pointwise-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.slicing-a1.mass_pointwise-a1.strip_lintegral_le-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 (Estimate for fixed h) of the parent proof of cmcs_slice_mass_pointwise. There it is applied with g = g_h, c = L/(h(1 − h/2)) and S = S_h = {t − h < f < t} (the gradient bound and gradient-support properties come from cmcs_level_cutoff), and with η̂ admissible (tsupport η̂ ⊆ W, |η̂| ≤ 1). Here the bound is proved directly with W in place of the intermediate set K₀ = tsupport η̂ ⊆ W.
1. (Pointwise bound.) Claim: for every x, ofReal(‖Dg(x)‖·|η(x)|) ≤ (W ∩ S).indicator(const ofReal(c))(x).
   a. If x ∈ W ∩ S: ‖Dg(x)‖ ≥ 0 and |η(x)| ≤ 1, so ‖Dg(x)‖·|η(x)| ≤ ‖Dg(x)‖·1 ≤ c. By monotonicity of ofReal, the left side is ≤ ofReal(c), which is the indicator's value at x.
   b. If x ∉ W ∩ S but x ∈ W: then x ∉ S, so Dg(x) = 0, since otherwise x ∈ S by hypothesis. Hence ‖Dg(x)‖ = 0, the product is 0, and the left side is ofReal(0) = 0, the indicator's value at x.
   c. If x ∉ W: then x ∉ tsupport η (as tsupport η ⊆ W), so η(x) = 0 (image_eq_zero_of_notMem_tsupport) and |η(x)| = covectorEuclideanNorm 0 = 0. Again the left side is 0, the indicator's value at x.
2. (Integrate.) By monotonicity of the lower Lebesgue integral (lintegral_mono, pointwise) and step 1, ∫⁻ ofReal(‖Dg(x)‖·|η(x)|) dμ ≤ ∫⁻ (W ∩ S).indicator(const ofReal(c)) dμ.
3. (Indicator integral.) For every set s and every a ∈ [0,∞], ∫⁻ s.indicator(const a) dμ ≤ a·μ(s) (lintegral_indicator_const_le; no measurability of s is needed). With s = W ∩ S and a = ofReal(c), step 2 gives ∫⁻ ofReal(‖Dg(x)‖·|η(x)|) dμ ≤ ofReal(c)·μ(W ∩ S). ∎ (In Lean, after `refine lintegral_mono fun x => ?_`, the goal may show a beta-redex. State the integrand explicitly with `show` before rewriting.)

## Key steps

1. Pointwise: ofReal(‖Dg(x)‖·|η(x)|) ≤ 1_{W∩S}(x)·ofReal(c). On W ∩ S use ‖Dg‖ ≤ c and |η| ≤ 1; on W \ S, Dg(x) = 0; off W, η(x) = 0 because tsupport η ⊆ W.
2. Apply lintegral_mono and then lintegral_indicator_const_le, which needs no measurability of W ∩ S.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean  (IDENTICAL)`
- `rg -n "cmcs_smp|Integrable \(fun x => ξ x|pairing_integrable|cutoff_integral|strip_lintegral" project -g '*.lean'  (no match, exit 1)`
- `rg -n "Integrable" project/GMT -g '*.lean'  (contract-only hits; Ch06 IsMeasureRepresentation assumes integrability of x ↦ v(x)(ω(x)), no proof)`
- `rg -n "theorem lintegral_indicator_const_le|theorem tendsto_integral_filter_of_dominated_convergence|theorem liminf_const_mul_of_ne_top|theorem integral_indicator\b|theorem Integrable.mono'|theorem integrable_indicator_iff|theorem integrableOn_const|theorem isBoundedBilinearMap_apply|theorem continuous_finsetSum|def apply \(m : ι → E\)|theorem ofReal_coe_nnreal|theorem ofReal_mul\b|theorem measurableSet_lt\b|protected theorem Tendsto.mul_const|theorem tendsto_ofReal" mathlib/Mathlib -g '*.lean'`
- `rg -n "HasCompactSupport.intro|bounded_above_of_compact_support|Continuous.comp_aestronglyMeasurable₂|Continuous.sqrt|Tendsto.liminf_eq|image_eq_one_of_notMem_mulTSupport|Ioo_mem_nhdsGT" mathlib/Mathlib -g '*.lean'`
- `grep -n 'def covectorEuclideanNorm|def massAdmissibleOn|def GeometricCurrentOn.massOn|abbrev TestFormOn|def testFormOnSubmodule|def exteriorDerivativeTestOn|theorem GeometricCurrentOn.boundary_apply|theorem tsupport_exteriorDerivative_subset' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/{Mass,Currents,Forms}.lean`
- `python3 -I scan of dag.json: lean_statements containing Integrable together with covectorEuclideanNorm/MultiVector/TestFormOn; statements containing liminf and 𝓝[>]; lean_name and substring collisions for cmcs_smp_pairing_integrable, cmcs_smp_cutoff_integral_tendsto, cmcs_smp_liminf_bound, cmcs_smp_strip_lintegral_le`
- `git for-each-ref --format='%(objectname)' | sort -u | xargs -n 200 git grep -l 'cmcs_smp_' -- '*.lean'  (1259 ref tips, no match)`
- `lean GMT/Scratch/cmcs_mass_pointwise_decomposition/{Assembly,ChildA,ChildB,ChildC,ChildD,Combined}.lean with #print axioms`
- `independent reviewer: review/check_bytes.py (byte identity of all 7 statements), review/CombinedAxioms.lean (uncles as named axioms), review/Elab.lean (autoImplicit false, Iff.rfl against fully explicit forms), review/NegControl.lean ((ENNReal.ofReal h)⁻¹ variant rejected)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Real/Sqrt.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-slicing-a1-mass-pointwise-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcs_mass_pointwise_decomposition/Assembly.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcs_mass_pointwise_decomposition/Combined.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcs_mass_pointwise_decomposition/ChildA.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcs_mass_pointwise_decomposition/ChildB.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcs_mass_pointwise_decomposition/ChildC.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcs_mass_pointwise_decomposition/ChildD.lean`

Snapshot facts:
- The manifest pins project b4d606db and Mathlib 25730c7c.
- The snapshot Ch07 contract is byte-identical to GMT/Ch07/Submission.lean.
- The project snapshot has no cmcs_smp_ name and no proof of pairing integrability, cut-off dominated convergence, the liminf bound or the strip estimate. Its Integrable hits are contract definitions only; Ch06 IsMeasureRepresentation assumes integrability rather than proving it.
- Every Mathlib lemma the child proofs cite exists at the pinned revision, for example:
  - lintegral_indicator_const_le (Lebesgue/Basic.lean:533);
  - tendsto_integral_filter_of_dominated_convergence (DominatedConvergence.lean:67);
  - ENNReal.liminf_const_mul_of_ne_top (Order/Filter/ENNReal.lean:190);
  - integral_indicator (Bochner/Set.lean:185);
  - Integrable.mono' (L1Space/Integrable.lean:104);
  - integrable_indicator_iff and integrableOn_const (IntegrableOn.lean:340, 119);
  - ContinuousAlternatingMap.apply (Alternating/Topology.lean:294);
  - isBoundedBilinearMap_apply (BoundedLinearMaps.lean:391);
  - Continuous.bounded_above_of_compact_support (Normed/Group/Bounded.lean:153);
  - Continuous.comp_aestronglyMeasurable₂ (AEStronglyMeasurable.lean:263);
  - Continuous.sqrt (Real/Sqrt.lean:475);
  - ENNReal.tendsto_ofReal and ENNReal.Tendsto.mul_const (Instances/ENNReal/Lemmas.lean:72, 359);
  - ENNReal.ofReal_mul (Basic/ENNReal/Real.lean:297);
  - Filter.Tendsto.liminf_eq (Topology/Order/LiminfLimsup.lean:195).
- SimonGMT Mass.lean defines massOn as an sSup over massAdmissibleOn, and Currents.lean makes (A.boundary − B) η = A(exteriorDerivativeTestOn U k η) − B η hold by rfl (checked in Lean).

DAG and git:
- The accepted integrability nodes are IMRep-specific (dor_ims_action_eq_integral, regcomp_rim_action_integrable, rsd_cmr_ic_action_integrable) or need finite measures (rsd_mw_wlm_integrable_clm_comp). None has an identical type, so nothing is reused.
- No accepted liminf or limit lemma matches.
- The four new names are absent from dag.json (669 nodes) and from all 1259 git ref tips.

Lean:
- All four child types elaborate in the contract namespace and opens.
- They are proved in scratch with standard axioms only.
- The exact frozen parent type is proved from them plus the frozen cmcs_level_cutoff and cmcs_cutoff_defect_bound; sorryAx enters only through those two uncle stubs.
