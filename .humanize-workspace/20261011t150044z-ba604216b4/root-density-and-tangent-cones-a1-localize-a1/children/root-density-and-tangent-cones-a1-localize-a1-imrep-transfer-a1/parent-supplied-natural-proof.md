# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.localize-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.localize-a1.imrep_transfer-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 6.6 of the parent proof (R̃ := (M_X ∩ K, θ_X, ξ_X) is an IMRep in U), with Simon 6.3.1 (chapter-06.txt lines 733–753). Uses the sibling dtc_approxTangent_of_null_diff, called (A) below. Let R' have carrier M ∩ K, multiplicity θ and orientation ξ.
1. M ∩ K and M are Hⁿ-a.e. equal: (M ∩ K) ∖ M = ∅, and M ∖ (M ∩ K) = M ∖ K is Hⁿ-null by hypothesis (ae_eq_set). Hence Hⁿ⌞(M ∩ K) = Hⁿ⌞M (Measure.restrict_congr_set).
2. Measurability: K is compact, hence closed and Borel, and M is Borel, so M ∩ K is Borel.
3. M ∩ K ⊆ K ⊆ U; this also gives R'.carrier ⊆ K.
4. Rectifiability: M ∩ K ⊆ M (CountablyRectifiable.mono).
5. θ is measurable, and θ(x) > 0 for x ∈ M ∩ K ⊆ M.
6. Local integrability in U. Let C be compact with C ⊆ U. Then (M ∩ K) ∩ C ⊆ M ∩ K, so ∫_{(M∩K)∩C} θ dHⁿ ≤ ∫_{M∩K} θ dHⁿ (lintegral_mono_set). The right side is finite by the local integrability of R in V, applied to the compact set K ⊆ V.
7. ξ is a.e. strongly measurable for Hⁿ⌞(M ∩ K), because Hⁿ⌞(M ∩ K) ≤ Hⁿ⌞M (AEStronglyMeasurable.mono_measure).
8. Orientation. For Hⁿ⌞M-a.e. x, hence Hⁿ⌞(M ∩ K)-a.e. x (ae_restrict_of_ae_restrict_of_subset), there is Q with HasApproximateTangentSpaceAt n M x Q and IsUnitOrientationOf (ξ x) Q. Apply (A) with M' := M ∩ K ⊆ M and the open set ℝ^P (univ), which contains x: (M ∖ (M ∩ K)) ∩ ℝ^P = M ∖ K is Hⁿ-null. So HasApproximateTangentSpaceAt n (M ∩ K) x Q holds, with the same unit orientation ξ(x). Thus R' is an IMRep of U with carrier ⊆ K.
9. Action. For every n-form ω, R'.action ω = ∫ θ⟨ω, ξ⟩ d(Hⁿ⌞(M ∩ K)) = ∫ θ⟨ω, ξ⟩ d(Hⁿ⌞M) = R.action ω by step 1. The two measures are equal, so no integrability is needed. ∎

## Key steps

1. Take R' = (M ∩ K, θ, ξ). M ∩ K and M differ by the Hⁿ-null set M ∖ K, so Hⁿ⌞(M ∩ K) = Hⁿ⌞M and the actions coincide.
2. Local integrability in U follows from finiteness of the θ-integral over the compact set K ⊆ V.
3. The approximate tangent planes of M and M ∩ K agree because the sets differ by a null set (sibling A with the open set ℝ^P).

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
