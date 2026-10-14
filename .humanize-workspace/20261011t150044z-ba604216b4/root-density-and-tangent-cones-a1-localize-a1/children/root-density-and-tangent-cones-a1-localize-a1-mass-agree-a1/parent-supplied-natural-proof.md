# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.localize-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.localize-a1.mass_agree-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 2 and 6.9 of the parent proof. There, the admissible families defining M_W for a current in U and for a current in U' correspond with equal values. This is Simon 6.2.5 (chapter-06.txt lines 228–233) read with the terminology 6.2.16 (lines 335–337: T₁ = T₂ in W).
Notation. For D ⊆ ℝ^P, 𝒟ⁿ(D) = TestFormOn D n is the space of smooth compactly supported n-forms ω on ℝ^P with tsupport ω ⊆ D. For T ∈ 𝒟_n(D), M_W(T) = T.massOn W = sup{ofReal(T(ω)) : ω ∈ A_D(W)} ∈ [0, ∞], where A_D(W) = massAdmissibleOn D n W = {ω ∈ 𝒟ⁿ(D) : tsupport ω ⊆ W and |ω(y)| ≤ 1 for all y} and |·| = covectorEuclideanNorm. The map ι = testFormOnInclusion hVU n keeps the underlying form (testFormOnInclusion_coe).
1. Put I := {ofReal(S(ω)) : ω ∈ A_U(W)} and I' := {ofReal(S'(ω')) : ω' ∈ A_V(W)}. Since M_W(S) = sup I and M_W(S') = sup I', it suffices to prove I = I'.
2. I ⊆ I'. Let ω ∈ A_U(W). Its underlying form is a test form (IsTestForm), and tsupport ω ⊆ W ⊆ V, so the same form defines an element ω' ∈ 𝒟ⁿ(V). Both conditions defining A_V(W) concern only the underlying form, so ω' ∈ A_V(W). Also ιω' = ω, since both have the same underlying form (Subtype.ext). The hypothesis applied to ω' (tsupport ω' = tsupport ω ⊆ W) gives S(ω) = S(ιω') = S'(ω'). Hence ofReal(S(ω)) = ofReal(S'(ω')) ∈ I'.
3. I' ⊆ I. Let ω' ∈ A_V(W) and ω := ιω' ∈ 𝒟ⁿ(U). It has the same underlying form as ω', so ω ∈ A_U(W), and the hypothesis gives S(ω) = S'(ω'). Hence ofReal(S'(ω')) = ofReal(S(ω)) ∈ I.
4. By steps 2 and 3, I = I', so M_W(S) = sup I = sup I' = M_W(S'). ∎
(In Lean: unfold GeometricCurrentOn.massOn, apply congr 1 and ext r, then prove the two inclusions above.)

## Key steps

1. Each mass M_W is the supremum of ofReal of the current's values on the admissible forms supported in W.
2. Because W ⊆ V ⊆ U, the admissible forms for U and for V are the same underlying forms, related by testFormOnInclusion.
3. The hypothesis gives equal values on corresponding forms, so the two value sets coincide and the suprema are equal.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Submission.lean local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean (both identical; manifest project b4d606d, mathlib 25730c7c)`
- `rg -n 'theorem norm_iteratedFDeriv_smul_le|theorem norm_iteratedFDeriv_mul_le' mathlib/Mathlib/Analysis/Calculus/ContDiff/ (found only in Bounds.lean:250/274)`
- `rg -n 'zero_one_of_isClosed|one_nhds_of|exists_smooth_tsupport_subset|exists_contDiff_tsupport_subset' mathlib/Mathlib/Geometry mathlib/Mathlib/Analysis/Calculus/BumpFunction`
- `grep -n 'μHE|def euclideanHausdorffMeasure|smul₀|homothety|image' mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean; grep -n 'hausdorffMeasure_image_le|hausdorffMeasure_homothety_image' mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `grep -n 'theorem|lemma|def' mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean (Filter.EventuallyEq.extDeriv_eq); rg -n 'notation "ℕ∞ω"|notation3 "∞"' mathlib/Mathlib/Analysis/Calculus/ContDiff`
- `read simongmt Chapter06/{Currents,Mass,CurrentLocalEquality,Forms}.lean and Chapter03/Rectifiable.lean (restrictDomain, testFormOnInclusion, VanishesOn/zeroRegion/support, massAdmissibleOn/massOn, exteriorDerivativeTestOn, exteriorDerivative = extDeriv, blowUpMap, HasApproximateTangentSpaceAt, CountablyRectifiable.mono)`
- `rg -n 'theorem .*(restrict|cutoff|extend|extension|zeroExtend|smulCurrent|mulCurrent|localize)' simongmt/Poincare/SimonGMT (only Chapter04 varifold cutoff lemmas)`
- `rg -n 'HasApproximateTangentSpaceAt' simongmt/Poincare/SimonGMT outside Chapter03/Rectifiable.lean (no locality or null-modification lemma)`
- `#check under import GMT.Ch07.Submission: norm_iteratedFDeriv_smul_le, ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear (unknown); exists_contMDiffMap_one_nhds_of_subset_interior, IsCompact.exists_cthickening_subset_open, Filter.EventuallyEq.extDeriv_eq, LipschitzWith.hausdorffMeasure_image_le, Measure.restrict_congr_set, setIntegral_eq_integral_of_forall_compl_eq_zero, Continuous.comp_aestronglyMeasurable₂, isBoundedBilinearMap_apply, ContinuousAlternatingMap.le_opNorm, norm_integral_le_of_norm_le (available)`
- `grep each proposed lean_name in runs/20261011T150044Z-ba604216b4/dag.json, nodes/ and GMT/Ch07/Submission.lean (no match); lean_name inventory of dag.json (135 nodes)`
- `contract_scope(Contract.lean, 'GMT.Ch07.main_theorem') from verifier/gmt-compare.py; lean_contract.validate_lean_statement on all six child types`
- `lake build GMT.Ch07.Submission (scratch /tmp/loc-decomp-jznkee/proj); lake env lean Check/Exact.lean, Check/Assembly.lean, Check/C1.lean, Check/C2.lean, Check/C3.lean, Check/C4.lean, Check/C6.lean, Check/C7.lean, Check/All.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Bounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-localize-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-localize-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-vanish-off-support-a1/rlcr-plan-v1.md`
- `/tmp/loc-decomp-jznkee/proj/Check/Exact.lean`
- `/tmp/loc-decomp-jznkee/proj/Check/Assembly.lean`
- `/tmp/loc-decomp-jznkee/proj/Check/C1.lean`
- `/tmp/loc-decomp-jznkee/proj/Check/C2.lean`
- `/tmp/loc-decomp-jznkee/proj/Check/C3.lean`
- `/tmp/loc-decomp-jznkee/proj/Check/C4.lean`
- `/tmp/loc-decomp-jznkee/proj/Check/C6.lean`
- `/tmp/loc-decomp-jznkee/proj/Check/C7.lean`
- `/tmp/loc-decomp-jznkee/proj/Check/All.lean`

The snapshot Contract.lean and Submission.lean (project b4d606d, mathlib 25730c7c) are byte-identical to the workspace files. SimonGMT supplies the frozen objects used: restrictDomain, testFormOnInclusion and testFormOnInclusion_coe, VanishesOn, zeroRegion and isOpen_zeroRegion, support and support_subset_domain, massAdmissibleOn and massOn, exteriorDerivativeTestOn, exteriorDerivative = Mathlib extDeriv, blowUpMap, HasApproximateTangentSpaceAt, and CountablyRectifiable.mono. It has no locality or null-modification lemma for approximate tangent spaces, no IMRep-to-current constructor, no restriction lemma for integer multiplicity currents, and no extension-by-zero lemma; these become the children. Under the frozen imports Mathlib provides the smooth Urysohn lemma exists_contMDiffMap_one_nhds_of_subset_interior, IsCompact.exists_cthickening_subset_open, Filter.EventuallyEq.extDeriv_eq, LipschitzWith.hausdorffMeasure_image_le, μHE[d] = c·μH[d] with c ≠ 0, Measure.restrict_congr_set, Continuous.comp_aestronglyMeasurable₂, isBoundedBilinearMap_apply and ContinuousAlternatingMap.le_opNorm. It does not provide the Leibniz bound norm_iteratedFDeriv_smul_le (Bounds.lean is not imported). So the extension child defines X̃ by the integral formula of step 6.6 rather than by X(χω). All six child types elaborate in the comparator scope and have complete Lean proofs using only propext, Classical.choice and Quot.sound. The parent type follows from them plus vanish_off_support, mass_eq_measure and im_sub. No proposed name collides with a DAG name.
