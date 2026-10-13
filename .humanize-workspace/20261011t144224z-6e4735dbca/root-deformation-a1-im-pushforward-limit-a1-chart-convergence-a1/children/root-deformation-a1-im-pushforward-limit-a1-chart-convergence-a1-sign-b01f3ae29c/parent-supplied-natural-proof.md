# Parent-supplied natural-language proof

- Parent DAG node: `root.deformation-a1.im_pushforward_limit-a1.chart_convergence-a1`
- Child DAG node: `root.deformation-a1.im_pushforward_limit-a1.chart_convergence-a1.signed_change_of_variables-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step (6b)(β) of the parent proof ("applying the formula to the positive and negative parts … gives … w ↦ φ(Φ(w))·JΦ(w) is L^k⌞D-integrable with ∫_{G_K} φ dH = ∫_D φ(Φ(w))·JΦ(w) dw"). It is stated here for an arbitrary integrable real h and an arbitrary null-measurable A ⊆ Φ(Ω). The parent's implementation remark is followed literally: the signed formula comes from the lintegral identity of chart_change_of_variables applied to ENNReal.ofReal of the positive and negative parts.

Conventions. H := μHE[k] on ℝ^P; L := volume on ℝ^k; J := JΦ; ofReal := ENNReal.ofReal; ‖t‖ₑ = ofReal|t| for t ∈ ℝ; ∫⁻ is the [0,∞]-valued integral.

1. (J is nonnegative and Borel.) J ≥ 0, being a square root. J is Borel measurable:
 - w ↦ DΦ(w) is Borel measurable for every Φ (Mathlib measurable_fderiv);
 - hence so are the columns w ↦ DΦ(w)e_i (evaluation at e_i is continuous linear);
 - the entries ⟨DΦ(w)e_i, DΦ(w)e_j⟩ are measurable (the inner product is continuous);
 - the determinant is a polynomial, hence continuous, function of the entries, and √ is continuous.
2. (The sibling chart_change_of_variables.) Its hypotheses hold for (Φ, Ω, A): Ω is open, Φ is Lipschitz and c-antilipschitz on Ω, A ⊆ Φ(Ω), and A is H-null-measurable. Since h is integrable, hence a.e.-measurable, for H⌞A, the following are a.e.-measurable for H⌞A: g₊ := ofReal∘h, g₋ := ofReal∘(−h) and g₀ := ‖h‖ₑ. The sibling gives:
 - D is L-null-measurable;
 - g₊∘Φ and g₋∘Φ are a.e.-measurable for L⌞D;
 - for g ∈ {g₊, g₋, g₀}: ∫⁻_A g dH = ∫⁻_D g(Φ(w))·ofReal(J(w)) dw.
3. (Measurability on D.) For every real t, t = toReal(ofReal t) − toReal(ofReal(−t)), since one of the two terms is 0. Hence h∘Φ = toReal∘(g₊∘Φ) − toReal∘(g₋∘Φ) is a.e.-measurable for L⌞D. So F(w) := h(Φ(w))·J(w) is a.e.-strongly measurable for L⌞D, as a product with the measurable J.
4. (Integrability on D.) Since J ≥ 0, ‖F(w)‖ₑ = ‖h(Φ(w))‖ₑ·ofReal(J(w)). By step 2 with g₀, ∫⁻_D ‖F‖ₑ dL = ∫⁻_A ‖h‖ₑ dH < ∞, because h is integrable on A. With step 3, F is L-integrable on D. This is the first conclusion.
5. (The identity.) For a real function f integrable for a measure ν,
 ∫ f dν = toReal(∫⁻ ofReal(f) dν) − toReal(∫⁻ ofReal(−f) dν)
 (Mathlib integral_eq_lintegral_pos_part_sub_lintegral_neg_part). Apply this to h on (A, H) and to F on (D, L) (step 4):
 ∫_A h dH = toReal(∫⁻_A ofReal(h) dH) − toReal(∫⁻_A ofReal(−h) dH)
  = toReal(∫⁻_D ofReal(h(Φ w))·ofReal(J w) dw) − toReal(∫⁻_D ofReal(−h(Φ w))·ofReal(J w) dw)   (step 2)
  = toReal(∫⁻_D ofReal(F(w)) dw) − toReal(∫⁻_D ofReal(−F(w)) dw) = ∫_D F dL.
 The third equality uses ofReal(a)·ofReal(b) = ofReal(a·b) for b = J(w) ≥ 0 (ENNReal.ofReal_mul') and −h(Φ w)·J(w) = −F(w). This is the second conclusion. ∎

Lean remark. The script below was verified with Lean v4.35.0-rc3, Mathlib 25730c7c and SimonGMT 2b36630 as `theorem Submission.deformation_ipl_cc_signed_change_of_variables : (<frozen type>) := by` inside `namespace GMT.Ch06` of GMT/Ch06/Submission.lean. It uses the sibling declarations `Submission.lpf_raf_chart_change_of_variables`, which were present as declarations of exactly their frozen types. With those sibling statements taken as hypotheses, #print axioms gives only propext, Classical.choice and Quot.sound. Its only dependency is `Submission.lpf_raf_chart_change_of_variables`; no extra import is needed.
Tactic script:
  intro P k Φ Ω A h hΩ hΦLip hΦanti hAΦ hAm hh
  set J : Eucl k → ℝ := fun w => Real.sqrt (Matrix.of fun i j => inner ℝ
    (fderiv ℝ Φ w (EuclideanSpace.single i 1)) (fderiv ℝ Φ w (EuclideanSpace.single j 1))).det
    with hJdef
  set D : Set (Eucl k) := Ω ∩ Φ ⁻¹' A with hDdef
  have hJ0 : ∀ w, 0 ≤ J w := fun w => Real.sqrt_nonneg _
  have hJm : Measurable J := by
    have hfd : Measurable (fderiv ℝ Φ) := measurable_fderiv ℝ Φ
    have hcol : ∀ i : Fin k, Measurable (fun w => fderiv ℝ Φ w (EuclideanSpace.single i 1)) :=
      fun i => (ContinuousLinearMap.apply ℝ (Eucl P) (EuclideanSpace.single i 1)).continuous.measurable.comp hfd
    have hmat : Measurable (fun w => (fun i j => inner ℝ
        (fderiv ℝ Φ w (EuclideanSpace.single i 1)) (fderiv ℝ Φ w (EuclideanSpace.single j 1)) :
          Fin k → Fin k → ℝ)) := by
      refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
      exact continuous_inner.measurable.comp ((hcol i).prodMk (hcol j))
    have hdet : Continuous (fun f : Fin k → Fin k → ℝ => (Matrix.of f).det) :=
      (show Continuous (fun f : Fin k → Fin k → ℝ => Matrix.of f) from continuous_id).matrix_det
    exact Real.continuous_sqrt.measurable.comp (hdet.measurable.comp hmat)
  -- change of variables for the positive and negative parts and for |h|
  have hpos := Submission.lpf_raf_chart_change_of_variables P k Φ Ω A (fun x => ENNReal.ofReal (h x)) hΩ hΦLip hΦanti hAΦ hAm
    hh.aemeasurable.ennreal_ofReal
  have hneg := Submission.lpf_raf_chart_change_of_variables P k Φ Ω A (fun x => ENNReal.ofReal (-h x)) hΩ hΦLip hΦanti hAΦ hAm
    hh.neg.aemeasurable.ennreal_ofReal
  have habs := Submission.lpf_raf_chart_change_of_variables P k Φ Ω A (fun x => ‖h x‖ₑ) hΩ hΦLip hΦanti hAΦ hAm
    hh.aemeasurable.enorm
  obtain ⟨hDm, hposm, hposeq⟩ := hpos
  obtain ⟨-, hnegm, hnegeq⟩ := hneg
  obtain ⟨-, -, habseq⟩ := habs
  -- measurability of h ∘ Φ on D
  have hhΦ : AEMeasurable (fun w => h (Φ w)) ((volume : Measure (Eucl k)).restrict D) := by
    have h1 := hposm.ennreal_toReal
    have h2 := hnegm.ennreal_toReal
    refine (h1.sub h2).congr (Filter.Eventually.of_forall fun w => ?_)
    simp only [Pi.sub_apply]
    rcases le_total 0 (h (Φ w)) with hw | hw
    · rw [ENNReal.toReal_ofReal hw, ENNReal.ofReal_of_nonpos (by linarith), ENNReal.toReal_zero, sub_zero]
    · rw [ENNReal.ofReal_of_nonpos hw, ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_zero]; ring
  have hFm : AEStronglyMeasurable (fun w => h (Φ w) * J w) ((volume : Measure (Eucl k)).restrict D) :=
    (hhΦ.mul hJm.aemeasurable).aestronglyMeasurable
  have hFint : IntegrableOn (fun w => h (Φ w) * J w) D (volume : Measure (Eucl k)) := by
    refine ⟨hFm, ?_⟩
    rw [HasFiniteIntegral]
    have : ∫⁻ w in D, ‖h (Φ w) * J w‖ₑ = ∫⁻ x in A, ‖h x‖ₑ ∂(μHE[k] : Measure (Eucl P)) := by
      rw [habseq]
      refine lintegral_congr fun w => ?_
      rw [enorm_mul, Real.enorm_eq_ofReal_abs (J w), abs_of_nonneg (hJ0 w)]
    rw [this]
    exact hh.2
  refine ⟨hFint, ?_⟩
  -- the signed identity, from the positive and negative parts
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hh,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hFint, hposeq, hnegeq]
  congr 2
  · refine lintegral_congr fun w => ?_
    rw [← ENNReal.ofReal_mul' (hJ0 w)]
  · refine lintegral_congr fun w => ?_
    rw [← ENNReal.ofReal_mul' (hJ0 w), neg_mul]

## Key steps

1. J ≥ 0 is Borel (measurable_fderiv); chart_change_of_variables gives null-measurability of D, a.e.-measurability of (ofReal∘±h)∘Φ on D, and the lintegral identity for ofReal∘h, ofReal∘(−h) and ‖h‖ₑ.
2. h∘Φ = toReal(ofReal∘h∘Φ) − toReal(ofReal∘(−h)∘Φ) is a.e.-measurable on D, and ∫⁻_D ‖h∘Φ·J‖ₑ = ∫⁻_A ‖h‖ₑ < ∞ gives integrability.
3. integral_eq_lintegral_pos_part_sub_lintegral_neg_part on both sides, with ofReal(a)·ofReal(J) = ofReal(a·J), gives ∫_A h dH^k = ∫_D h(Φ)·JΦ.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); cmp of workspace GMT/Ch06/Submission.lean, GMT/Ch06/Contract.lean and the snapshot project/GMT/Ch06/Contract.lean (byte-identical)`
- `python3 -I over dag.json: status, candidate_commit and lean_statement of the node's dependencies lpf_simple_nvector_algebra, lpf_countably_rectifiable_c1_cover, lpf_chart_chain_rule, lpf_raf_chart_change_of_variables (accepted), deformation_ipl_minor_weak_continuity and deformation_ipl_tangential_pushforward_aestronglyMeasurable (decomposing)`
- `python3 -I over dag.json: regex search jacob|change_of_var|antilip|gram|det|tannery|dominat|chart|area|orient|simple|pushforward over lean names, then lean_statement of lpf_wtc_cat_fderiv_lower_bound, lpf_wtc_cat_gram_jacobian_continuous, lpf_wtc_caf_signed_of_lintegral, lpf_pi_jacobian_local_bound, lpf_pi_measurability, lpf_pic_density_dominated, lpf_raf_chart_preimage_null, lpf_ccr_ae_pullback, lpf_weighted_tangent_on_c1_chart, lpf_wtc_chart_image_measurable_locally_finite, iwl_sp_sn_signed_simpleNVector_bound_ne_zero, fiw_ims_frame_sign, slicing_im_ll_twl_chart_integral_eq (decomposing, not reusable)`
- `python3 -I over nodes/*/parent-child-handoff.json: map the six reused node ids to their directories and check title/statement/lean_statement/lean_name byte-identity with dag.json (all True)`
- `python3 -I over dag.json: lean-name collision check for deformation_ipl_cc_gram_det_lower_bound, deformation_ipl_cc_signed_change_of_variables, deformation_ipl_cc_chart_orientation_sign, deformation_ipl_cc_chart_integral_representation, deformation_ipl_cc_pushforward_integrand_bound, deformation_ipl_cc_tendsto_setIntegral_of_partition (none); rg -l deformation_ipl_cc over GMT, snapshot project, snapshot Mathlib and SimonGMT (no match); git grep over all local branches (no match)`
- `rg -n 'abbrev (Covector|NVector)|def (simpleNVector|nVectorPushforward|covectorPullback|wedgeCovectors)|theorem wedgeCovectors_apply_det|theorem nVectorPushforward_simple' simongmt/Poincare/SimonGMT/Chapter06; rg -n 'HasWeightedApproximateTangentSpaceAt' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `rg -n over snapshot Mathlib: IsOpen.isSigmaCompact (no match), NullMeasurableSet.disjointed, disjointed_subset|iUnion_disjointed|disjoint_disjointed, integral_iUnion_ae, hasSum_integral_iUnion_ae, tendsto_tsum_of_dominated_convergence, setIntegral_congr_set, setIntegral_indicator, aestronglyMeasurable_indicator_iff₀, aestronglyMeasurable_iUnion_iff, Matrix.IsHermitian det_eq_prod_eigenvalues|eigenvalues_eq|mulVec_eigenvectorBasis, prod_le_prod₀, adjoint_inner_right, continuous_compContinuousLinearMapCLM, integral_eq_lintegral_pos_part_sub_lintegral_neg_part, Orthonormal.inner_right_fintype, mem_span_range_iff_exists_fun, HasDerivAt.le_of_lipschitz, norm_fderiv_le_of_lipschitz, IsCompact.cthickening, mem_cthickening_of_dist_le, image_eq_zero_of_notMem_tsupport, HasCompactSupport.exists_bound_of_continuous, opNorm_smul_le, NormedSpace.toNormSMulClass`
- `git show 9fc44225b304fca8af9dead3256575ef03818d1e:GMT/Ch06/Submission.lean (accepted declaration format) and the import lines of all accepted candidate Submissions (extra imports already accepted)`
- `python3 -I verifier/lean_contract.py validate_lean_statement and verifier/gmt-compare.py child_modules (mode contract) for the twelve types`
- `lake env lean /tmp/ccv-decomp/ExactScope.lean (twelve types, exit 0); /tmp/ccv-decomp/Assembly.lean (parent from child and dependency types); /tmp/ccv-decomp/Dproof.lean, Cproof.lean, Bproof.lean, Aproof.lean (+Mathlib.Analysis.Matrix.Spectrum), Eproof.lean, Fproof.lean (+Mathlib.Analysis.Normed.Group.Tannery); /tmp/ccv-decomp/Final_*.lean (final Submission.* forms against stubs); /tmp/ccv-decomp/Inst.lean (NormSMulClass ℝ (NVector …) not synthesized)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-chart-convergence-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-chart-convergence-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1/decomposition-audit-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-simple-nvector-algebra-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-chart-chain-rule-a1-ae-pullback-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1-chart-ch-1ba1e0b708/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-837491fcd9/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-1f4173ea67/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Matrix/Spectrum.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Group/Tannery.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Disjointed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Algebra/Order/BigOperators/GroupWithZero/Finset.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/ccv-decomp/ExactScope.lean`
- `/tmp/ccv-decomp/Assembly.lean`
- `/tmp/ccv-decomp/Dproof.lean`
- `/tmp/ccv-decomp/Cproof.lean`
- `/tmp/ccv-decomp/Final_parent.lean`

Pinned revisions are confirmed, and the frozen contract is byte-identical to the snapshot (Submission = Contract).
Reuse:
- Six accepted declarations are reused by name: lpf_simple_nvector_algebra, lpf_weighted_tangent_on_c1_chart, lpf_ccr_ae_pullback, lpf_raf_chart_change_of_variables, lpf_wtc_cat_fderiv_lower_bound and lpf_wtc_chart_image_measurable_locally_finite.
- Each has status accepted with a candidate commit, and its title, statement and Lean type are copied byte-for-byte from dag.json (identical to its handoff).
- The node's other dependencies (c1_cover, chart_chain_rule, minor_weak_continuity, pushforward_measurable) are used only by the parent assembly.
- No accepted DAG node or library lemma states the signed chart change of variables, the measurable chart orientation sign, the chart integral representation or the partition Tannery lemma. slicing_im_ll_twl_chart_integral_eq is still decomposing, so it cannot be reused.
New names: the six deformation_ipl_cc_ names collide with nothing in dag.json, the project, SimonGMT or the pinned Mathlib.
Library support (all present in the snapshot):
- Matrix.IsHermitian spectral theorem (det_eq_prod_eigenvalues, eigenvalues_eq) and tendsto_tsum_of_dominated_convergence; both modules need an extra import.
- NullMeasurableSet.disjointed, integral_iUnion_ae, hasSum_integral_iUnion_ae, integral_eq_lintegral_pos_part_sub_lintegral_neg_part, ContinuousLinearMap.adjoint_inner_right and ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.
- SimonGMT: wedgeCovectors_apply_det, nVectorPushforward_simple and HasWeightedApproximateTangentSpaceAt.unique.
- IsOpen.isSigmaCompact does not exist; the open-set exhaustion is written out explicitly.
- NormSMulClass ℝ (NVector …) is not synthesized; opNorm_smul_le is used instead.
Lean checks:
- All twelve types validate and elaborate in the exact comparator scope.
- The parent assembly compiles from the frozen child and dependency types.
- Every new child compiles from exactly its declared sibling types.
- All of these give only propext, Classical.choice and Quot.sound.
