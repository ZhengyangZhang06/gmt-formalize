# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.localize-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.localize-a1.approx_tangent_local-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 3, Definition 1.4 (chapter-03.txt lines 77–85). This is the locality fact behind step 5 of the parent proof (orientation of M ∩ U') and step 6.6 (M_X and M_X ∩ K differ by an Hⁿ-null set).
Notation: μ := Hⁿ = μHE[n]; η_r := η_{x,r} = Chapter03.blowUpMap x r; for an arbitrary set A, ∫_A f dμ := ∫ f d(μ⌞A) (Mathlib's set integal). No measurability of A is needed below.
1. Reduction. The condition dim Q = n is part of the hypothesis and does not involve M. Fix f ∈ C_c(ℝ^P). By hypothesis ∫_{η_r(M)} f dμ → ∫_Q f dμ as r ↓ 0. So it suffices to find r₀ > 0 with ∫_{η_r(M')} f dμ = ∫_{η_r(M)} f dμ for all r ∈ (0, r₀). The two functions of r then agree on (0, r₀), a set in the filter 𝓝[>] 0 (Ioo_mem_nhdsGT), so they have the same limit (Tendsto.congr').
2. Choice of r₀. V is open and x ∈ V, so choose s > 0 with B_s(x) ⊆ V. tsupport f is compact, hence bounded, so choose L > 0 with tsupport f ⊆ B := B_L(0) (open ball). Then f(y) = 0 for y ∉ B. Put r₀ := s/L > 0 and fix r ∈ (0, r₀).
3. Cutting to B. For every set A ⊆ ℝ^P, ∫_A f dμ = ∫_{B∩A} f dμ. Indeed f vanishes off B, so ∫ f d(μ⌞A) = ∫_B f d(μ⌞A) (setIntegral_eq_integral_of_forall_compl_eq_zero). And (μ⌞A)⌞B = μ⌞(B ∩ A) because B is Borel (Measure.restrict_restrict).
4. η_r maps μ-null sets to μ-null sets. |η_r(a) − η_r(b)| = r⁻¹|a − b|, so η_r is Lipschitz with constant r⁻¹, and μH[n](η_r(N)) ≤ (r⁻¹)ⁿ μH[n](N) for every N ⊆ ℝ^P (LipschitzWith.hausdorffMeasure_image_le). μHE[n] = c·μH[n] with a constant c ∈ (0, ∞) (Measure.euclideanHausdorffMeasure_def; addHaarScalarFactor_volume_hausdorffMeasure_ne_zero), so μ and μH[n] have the same null sets. Hence μ(N) = 0 implies μ(η_r(N)) = 0. Apply this to N := (M ∖ M') ∩ V, which is μ-null by hypothesis: μ(η_r(N)) = 0.
5. (B ∩ η_r(M)) ∖ (B ∩ η_r(M')) ⊆ η_r(N). Let y ∈ B with y = η_r(z) for some z ∈ M, and y ∉ η_r(M'). Then z ∉ M', since otherwise y ∈ η_r(M'). Inverting η_r gives z = x + r·y, so |z − x| = r|y| < rL < r₀L = s and z ∈ B_s(x) ⊆ V. Thus z ∈ (M ∖ M') ∩ V = N and y = η_r(z) ∈ η_r(N).
6. M' ⊆ M gives B ∩ η_r(M') ⊆ B ∩ η_r(M), so (B ∩ η_r(M')) ∖ (B ∩ η_r(M)) = ∅. With steps 4–5, μ((B ∩ η_r(M)) ∖ (B ∩ η_r(M'))) = 0. Hence B ∩ η_r(M') and B ∩ η_r(M) are μ-a.e. equal (ae_eq_set), and μ⌞(B ∩ η_r(M')) = μ⌞(B ∩ η_r(M)) (Measure.restrict_congr_set).
7. By steps 3 and 6, for every r ∈ (0, r₀): ∫_{η_r(M')} f dμ = ∫_{B∩η_r(M')} f dμ = ∫_{B∩η_r(M)} f dμ = ∫_{η_r(M)} f dμ. By step 1, HasApproximateTangentSpaceAt n M' x Q. ∎

## Key steps

1. Only the blow-up integrals need checking. For f ∈ C_c pick L with spt f ⊆ B_L(0) and s with B_s(x) ⊆ V, and take 0 < r < s/L.
2. Each blow-up integral equals its integral over B_L(0). For such r, the parts of η_r(M) and η_r(M') inside B_L(0) differ by a subset of η_r((M ∖ M') ∩ V).
3. η_r is Lipschitz, so this set is Hⁿ-null. The restricted measures coincide, so the integrals agree for all small r and the limits are equal.

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
