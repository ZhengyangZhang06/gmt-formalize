# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.localize-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.localize-a1.imrep_current-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon 6.3.1 (chapter-06.txt lines 733–753), where formula (‡) is asserted to define a current. The parent proof uses this in step 6.6 for X̃ = τ(M_X ∩ K, θ_X, ξ_X) in U.
Notation: μ := Hⁿ⌞M = μHE[n].restrict M; for a covector α, ‖α‖ is its operator norm as a continuous alternating map.
1. Unit orientations have norm at most one. By the field orients, for μ-a.e. x there are a subspace Q and an orthonormal family τ = (τ₁, …, τₙ) such that ξ(x)(α) = α(τ) for all α, or ξ(x)(α) = −α(τ) for all α (IsUnitOrientationOf). Then for every covector α, |ξ(x)(α)| = |α(τ₁, …, τₙ)| ≤ ‖α‖·∏ᵢ|τᵢ| = ‖α‖ (ContinuousAlternatingMap.le_opNorm; the product is empty when n = 0).
2. Measurability. For every continuous n-form ω, the function x ↦ θ(x)ξ(x)(ω(x)) is μ-a.e. strongly measurable. Indeed θ is measurable (ℕ-valued), ξ is μ-a.e. strongly measurable (field aestronglyMeasurable_orient), ω is continuous, and evaluation (L, α) ↦ L(α) is continuous because it is bounded bilinear (isBoundedBilinearMap_apply; Continuous.comp_aestronglyMeasurable₂).
3. θ is integrable over compact sets. Let K be compact with K ⊆ U. Then 1_K θ is μ-integrable: it is measurable, and ∫ 1_K θ dμ = ∫_{M∩K} θ dHⁿ < ∞ by the field locallyIntegrable_mult, since (Hⁿ⌞M)⌞K = Hⁿ⌞(K ∩ M) (Measure.restrict_restrict; integrable_indicator_iff). Write C_K := ∫ 1_K θ dμ ∈ [0, ∞).
4. Integrability of the integrand. Let ω ∈ 𝒟ⁿ(U), K := tsupport ω (compact, ⊆ U), and B := sup_y ‖ω(y)‖ < ∞ (ω is continuous with compact support). By step 1, for μ-a.e. x, |θ(x)ξ(x)(ω(x))| ≤ θ(x)‖ω(x)‖ ≤ B·1_K(x)θ(x); if x ∉ K then ω(x) = 0. By steps 2–3 and domination (Integrable.mono'), x ↦ θ(x)ξ(x)(ω(x)) is μ-integrable.
5. Linearity. Define T(ω) := R.action ω for ω ∈ 𝒟ⁿ(U). Each ξ(x) is linear, so the integrand for ω + η is the sum of the integrands for ω and η. Both are integrable by step 4, so T(ω + η) = T(ω) + T(η) (integral_add). The integrand for cω is c times the integrand for ω, so T(cω) = cT(ω) (integral_const_mul). Thus T is a linear functional on 𝒟ⁿ(U), and R.Represents T holds by definition.
6. Sequential continuity. Let ω_j → 0 in 𝒟ⁿ(U) (TestFormOnConverges ω_j 0). Then there is a compact K ⊆ U with tsupport ω_j ⊆ K for all j, and every derivative converges uniformly on K. For the 0-th derivative (‖D⁰g(x)‖ = ‖g(x)‖ and D⁰0 = 0) this says ε_j := sup_{x∈K} ‖ω_j(x)‖ → 0. By step 1, for μ-a.e. x, |θ(x)ξ(x)(ω_j(x))| ≤ ε_j·1_K(x)θ(x), since ω_j(x) = 0 off K. Hence |T(ω_j)| ≤ ε_j·C_K (norm_integral_le_of_norm_le with step 3). Given ε > 0, choose N such that ‖ω_j(x)‖ < ε/(C_K + 1) for all j ≥ N and x ∈ K. Then |T(ω_j)| ≤ εC_K/(C_K + 1) < ε for j ≥ N, so T(ω_j) → 0.
7. By steps 5 and 6, T is a GeometricCurrentOn U n with T(ω) = R.action ω for every ω ∈ 𝒟ⁿ(U). ∎

## Key steps

1. Unit orientations satisfy |ξ(x)(α)| ≤ ‖α‖ for a.e. x in M.
2. For a test form ω the integrand is a.e. strongly measurable and dominated by sup|ω|·1_{spt ω}·θ, which is integrable by local integrability of θ. Hence ω ↦ ∫_M θ⟨ω, ξ⟩ dHⁿ is linear.
3. If ω_j → 0 in 𝒟ⁿ(U) with supports in a compact K, then |T(ω_j)| ≤ sup_K|ω_j|·∫_{M∩K} θ → 0, so T is a current.

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
