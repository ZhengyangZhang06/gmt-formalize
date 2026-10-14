# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.slicing-a1.mass_pointwise-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.slicing-a1.mass_pointwise-a1.liminf_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 6 (Passing to the liminf) of the parent proof of cmcs_slice_mass_pointwise. The parent applies it with z = (∂A − B)(η), Φ(h) = ∫ g_h ξ(dη̂) dμ − ∫ g_h ξ'(η̂) dμ' and v(h) = μ(W ∩ {t − h < f < t}).
1. (Setup.) Put X := L·liminf_{h→0+} ofReal(h⁻¹)v(h) ∈ [0,∞]. The filter 𝓝[>]0 on ℝ is nontrivial, and (0,1) ∈ 𝓝[>]0 (Ioo_mem_nhdsGT).
2. (Limit of the left side.) Since Φ(h) → z, also |Φ(h)| → |z|, and ofReal|Φ(h)| → ofReal|z| by continuity of ofReal (ENNReal.tendsto_ofReal). The filter is nontrivial, so liminf_{h→0+} ofReal|Φ(h)| = ofReal|z| (Tendsto.liminf_eq).
3. (Claim: ofReal(z) ≤ ofReal(r)·X for every real r > 1.) Fix r > 1.
   a. The map h ↦ (1 − h/2)⁻¹ is continuous at h = 0 with value (1 − 0/2)⁻¹ = 1 (Tendsto.inv₀, as 1 ≠ 0). So it tends to 1 along 𝓝[>]0, and since 1 < r, eventually (1 − h/2)⁻¹ < r.
   b. Let h ∈ (0,1) with (1 − h/2)⁻¹ < r. Then 1 − h/2 > 0, and L/(h(1 − h/2)) = (1 − h/2)⁻¹·(L·h⁻¹), with (1 − h/2)⁻¹ ≥ 0 and L ≥ 0. ENNReal.ofReal_mul (twice) and ofReal(L) = L (ENNReal.ofReal_coe_nnreal) give ofReal(L/(h(1 − h/2))) = ofReal((1 − h/2)⁻¹)·L·ofReal(h⁻¹). By hypothesis and monotonicity of ofReal and of multiplication in [0,∞]: ofReal|Φ(h)| ≤ ofReal((1 − h/2)⁻¹)·(L·(ofReal(h⁻¹)v(h))) ≤ ofReal(r)·(L·(ofReal(h⁻¹)v(h))).
   c. By 1 and 3a, the inequality in 3b holds eventually along 𝓝[>]0. Monotonicity of liminf (liminf_le_liminf; its boundedness side conditions are automatic in the complete lattice [0,∞]), together with step 2 and z ≤ |z|, gives:
      ofReal(z) ≤ ofReal|z| = liminf ofReal|Φ(h)| ≤ liminf ofReal(r)·(L·(ofReal(h⁻¹)v(h))) = ofReal(r)·(L·liminf ofReal(h⁻¹)v(h)) = ofReal(r)·X.
      The finite constants ofReal(r) and L are pulled out of the liminf by ENNReal.liminf_const_mul_of_ne_top, applied twice; this uses that the filter is nontrivial.
4. (Letting r ↓ 1.) If X = ∞, then ofReal(z) ≤ X trivially. Otherwise X ≠ ∞. Then r ↦ ofReal(r)·X tends to ofReal(1)·X = X as r → 1 within (1,∞): ofReal is continuous, and ENNReal.Tendsto.mul_const applies with the alternative X ≠ ∞. By step 3, ofReal(z) ≤ ofReal(r)·X for every r in (1,∞), a set in 𝓝[>]1. Passing to the limit (ge_of_tendsto) gives ofReal(z) ≤ X = L·liminf_{h→0+} ofReal(h⁻¹)v(h). ∎

## Key steps

1. ofReal(z) ≤ ofReal|z| = liminf_{h→0+} ofReal|Φ(h)|, by continuity and nontriviality of 𝓝[>]0.
2. For r > 1, eventually (1 − h/2)⁻¹ < r, and ofReal(L/(h(1 − h/2))) = ofReal((1 − h/2)⁻¹)·L·ofReal(h⁻¹) for h ∈ (0,1); so the hypothesis gives ofReal|Φ(h)| ≤ ofReal(r)·L·ofReal(h⁻¹)v(h) eventually.
3. Use liminf_le_liminf and ENNReal.liminf_const_mul_of_ne_top to get ofReal(z) ≤ ofReal(r)·X with X = L·liminf ofReal(h⁻¹)v(h).
4. If X = ∞ the claim is trivial; otherwise let r → 1+ (ENNReal.Tendsto.mul_const, ge_of_tendsto) to get ofReal(z) ≤ X.

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
