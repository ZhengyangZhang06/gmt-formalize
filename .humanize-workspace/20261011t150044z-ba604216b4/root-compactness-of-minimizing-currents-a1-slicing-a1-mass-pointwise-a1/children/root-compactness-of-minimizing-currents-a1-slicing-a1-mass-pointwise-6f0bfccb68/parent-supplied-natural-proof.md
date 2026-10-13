# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.slicing-a1.mass_pointwise-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.slicing-a1.mass_pointwise-a1.pairing_integrable-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 (Integrability) of the parent proof of cmcs_slice_mass_pointwise, stated for an arbitrary degree n and an arbitrary test form ω so that the parent can apply it twice: to ω = dη (degree k+1, the test form exteriorDerivativeTestOn U k η, whose underlying form is exteriorDerivative η̂) with (μ, ξ), and to ω = η (degree k) with (μ', ξ'). Notation: |·| = covectorEuclideanNorm, e = EuclideanSpace.basisFun.
1. (Test-form data.) Write w := ω̂. By definition of TestFormOn U n, w is C^∞ (hence continuous) and has compact support, and K₀ := tsupport w satisfies K₀ ⊆ U. Thus K₀ is compact and μ(K₀) < ∞ by hypothesis. K₀ is closed (isClosed_tsupport), hence measurable. For x ∉ K₀ we have w(x) = 0 (image_eq_zero_of_notMem_tsupport). (In Lean: destructure ω as ⟨w, ⟨⟨hsmooth, hcpt⟩, hsub⟩⟩ and `change` the goal to Integrable (fun x => ξ x (w x)) μ.)
2. (The coefficient norm along w is continuous.) By definition N(x) := |w(x)| = √(Σ_{I : Fin n → Fin P} (if I is strictly increasing then (w(x)(e∘I))² else 0)). For a fixed tuple v, α ↦ α(v) is a continuous linear map on n-covectors (ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ v), so x ↦ w(x)(v) is continuous. Squares, the finite sum (continuous_finsetSum; the other summands are the constant 0) and √ (Continuous.sqrt) preserve continuity, so N is continuous. (Tested: (ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ v).continuous.comp hwc gives this directly.)
3. (Boundedness.) For x ∉ K₀, N(x) = |0| = 0 (covectorEuclideanNorm_zero). So N vanishes outside the compact K₀ and has compact support (HasCompactSupport.intro; in a test, HasCompactSupport.comp_left with covectorEuclideanNorm_zero hit the heartbeat limit). A continuous, compactly supported real function is bounded (Continuous.bounded_above_of_compact_support), so there is M ∈ ℝ with N(x) ≤ M for all x.
4. (Measurability.) The evaluation map (Λ, α) ↦ Λ(α) from MultiVector P n × Covector (Euclid P) n to ℝ is continuous, being bounded bilinear (isBoundedBilinearMap_apply). ξ is μ-a.e. strongly measurable and w is continuous, hence a.e. strongly measurable. So x ↦ ξ(x)(w(x)) is μ-a.e. strongly measurable (Continuous.comp_aestronglyMeasurable₂).
5. (Domination.) Let x lie in the μ-full set where |ξ(x)(α)| ≤ |α| for all α.
   - If x ∈ K₀, then |ξ(x)(w(x))| ≤ |w(x)| = N(x) ≤ M = K₀.indicator(const M)(x).
   - If x ∉ K₀, then w(x) = 0, so ξ(x)(w(x)) = ξ(x)(0) = 0 (linearity) and |ξ(x)(w(x))| = 0 = K₀.indicator(const M)(x).
   Hence ‖ξ(x)(w(x))‖ ≤ K₀.indicator(const M)(x) for μ-a.e. x.
6. (Integrability.) K₀ is measurable and the constant M is integrable on K₀ since μ(K₀) < ∞ (integrableOn_const). So K₀.indicator(const M) is μ-integrable (integrable_indicator_iff). By steps 4 and 5 and Integrable.mono' (an a.e. strongly measurable function dominated a.e. by an integrable real function is integrable), x ↦ ξ(x)(w(x)) = ξ(x)(ω̂(x)) is μ-integrable. ∎

## Key steps

1. ω̂ is continuous, and K₀ = tsupport ω̂ is compact, contained in U and measurable, so μ(K₀) < ∞; ω̂ = 0 off K₀.
2. x ↦ |ω̂(x)| is continuous (evaluation is continuous linear; finite sum; √) and compactly supported, hence bounded by some M.
3. x ↦ ξ(x)(ω̂(x)) is a.e. strongly measurable, because evaluation is a continuous bilinear map (Continuous.comp_aestronglyMeasurable₂).
4. Almost everywhere |ξ(x)(ω̂(x))| ≤ M·1_{K₀}(x), which is integrable; conclude by Integrable.mono'.

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
