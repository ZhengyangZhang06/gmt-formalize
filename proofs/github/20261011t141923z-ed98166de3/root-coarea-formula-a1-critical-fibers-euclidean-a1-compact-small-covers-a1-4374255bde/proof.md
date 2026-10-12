# Parent-supplied natural-language proof

- Parent DAG node: `root.coarea_formula-a1.critical_fibers_euclidean-a1`
- Child DAG node: `root.coarea_formula-a1.critical_fibers_euclidean-a1.compact_small_covers-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1, 3, 4–6 of the parent-supplied proof for one compact piece Q (constants ρ₀, L_G, the modulus of continuity of DG, and the integral estimate ε(r) → 0 using n = m + k), with steps 4 and 5 supplied by the sibling theorems.
Notation: n := m + k, DG(z) := fderiv ℝ G z, K := {x ∈ Q : DG(x) is not surjective}, B̄ closed balls, Lᵐ = volume on ℝᵐ. Fix ε > 0 and δ > 0.
1. The case m = 0. Every map into ℝ⁰ = {0} is surjective, so K = ∅. Take s := ∅ and r := δ/4. Then r > 0, 2r ≤ δ, K ⊆ ∅ = ⋃_{x∈∅} B̄(x, r), and the sum is 0 ≤ ofReal(ε). From now on assume m = m′ + 1 with m′ ∈ ℕ, so m − 1 = m′ and n = m′ + 1 + k.
2. Room around Q. Q is compact, V is open and Q ⊆ V. So there is ρ₀ > 0 with K₁ := cthickening(ρ₀, Q) ⊆ V (IsCompact.exists_cthickening_subset_open). K₁ is compact (IsCompact.cthickening, ℝⁿ is proper), and Q ⊆ K₁ (self_subset_cthickening).
3. Regularity of G. G is C¹ on the open set V. Hence G is differentiable at every point of V (ContDiffOn.differentiableOn with 1 ≠ 0, then DifferentiableOn.differentiableAt using IsOpen.mem_nhds). Also z ↦ DG(z) is continuous on V (ContDiffOn.continuousOn_fderiv_of_isOpen). So DG is continuous on the compact set K₁, which gives two facts. (a) Bound: there is L with ‖DG(z)‖ ≤ L for all z ∈ K₁ (IsCompact.exists_bound_of_continuousOn); put L′ := max(L, 0) ≥ 0. (b) Uniform continuity (Heine–Cantor, IsCompact.uniformContinuousOn_of_continuous with Metric.uniformContinuousOn_iff): for every η > 0 there is ρ > 0 such that ‖DG(z) − DG(z′)‖ < η whenever z, z′ ∈ K₁ and dist(z, z′) < ρ.
4. Covering constant. K ⊆ Q is bounded (Q is compact). The sibling theorem bounded_set_closedBall_cover_card_mul_pow_le, applied to K in ℝⁿ, gives a constant C ∈ ℝ with the following property. For every r with 0 < r ≤ 1 there is a finite s ⊆ K with K ⊆ ⋃_{x∈s} B̄(x, r) and card(s)·rⁿ ≤ C. Put C′ := max(C, 0) ≥ 0.
5. Choice of η, ρ and r. Let D := 2^{k+m}·(L′ + 1)^{m′}·C′ ≥ 0 and η := min(1, ε/(D + 1)). Then 0 < η ≤ 1. Also D·η ≤ D·ε/(D + 1) ≤ ε, since D/(D + 1) ≤ 1 and ε > 0. Let ρ > 0 be given by step 3(b) for this η. Put r := min(min(ρ₀, δ/2), min(ρ/2, 1)). Then r > 0, r ≤ ρ₀, 2r ≤ δ, r < ρ (as r ≤ ρ/2 < ρ) and r ≤ 1.
6. The cover. Step 4 with this r gives a finite s ⊆ K with K ⊆ ⋃_{x∈s} B̄(x, r) and card(s)·rⁿ ≤ C ≤ C′. We return s and r. The conditions 0 < r, 2r ≤ δ and K ⊆ ⋃_{x∈s} B̄(x, r) already hold, so it remains to bound the sum.
7. One ball. Let x ∈ s. Then x ∈ K, so x ∈ Q and DG(x) is not surjective. Every z ∈ B̄(x, r) has dist(z, x) ≤ r ≤ ρ₀ with x ∈ Q, so z ∈ K₁ (Metric.mem_cthickening_of_dist_le). Hence B̄(x, r) ⊆ K₁ ⊆ V, and G is differentiable at each z ∈ B̄(x, r) by step 3. Since x, z ∈ K₁ and dist(z, x) ≤ r < ρ, step 3(b) gives ‖DG(z) − DG(x)‖ < η, so ‖DG(z) − DG(x)‖ ≤ η. Also ‖DG(x)‖ ≤ L ≤ L′, as x ∈ K₁. Apply the sibling theorem volume_image_closedBall_le_of_fderiv_not_surjective to G, x, r ≥ 0, η and L′. It gives Lᵐ(G(B̄(x, r))) ≤ ofReal(2(ηr)·(2((L′ + η)r))^{m′}).
8. Summation. By step 7, Σ_{x∈s} ofReal((2r)^k)·Lᵐ(G(B̄(x, r))) ≤ Σ_{x∈s} ofReal((2r)^k)·ofReal(2(ηr)·(2((L′ + η)r))^{m′}). This equals ofReal(card(s)·((2r)^k·(2(ηr)·(2((L′ + η)r))^{m′}))), by Finset.sum_const, ENNReal.ofReal_mul, ENNReal.ofReal_natCast and nonnegativity. Expanding powers of products (mul_pow) and using n = m′ + 1 + k:
   card(s)·(2r)^k·2ηr·(2(L′ + η)r)^{m′} = 2^{k+m}·η·(L′ + η)^{m′}·(card(s)·rⁿ).
   Since 0 ≤ L′ + η ≤ L′ + 1, we have (L′ + η)^{m′} ≤ (L′ + 1)^{m′}. Also 0 ≤ card(s)·rⁿ ≤ C′, and all factors are nonnegative. So the right side is at most 2^{k+m}·η·(L′ + 1)^{m′}·C′ = D·η ≤ ε. By ENNReal.ofReal_le_ofReal, the sum is at most ofReal(ε), which completes the proof.

## Key steps

1. If m = 0 then K = ∅; take s = ∅.
2. K₁ := cthickening(ρ₀, Q) ⊆ V is compact; DG is bounded by L′ ≥ 0 and uniformly continuous on K₁.
3. bounded_set_closedBall_cover_card_mul_pow_le gives C′ ≥ 0 with card(s)·rⁿ ≤ C′ for covers of K at every r ∈ (0,1].
4. Take η := min(1, ε/(D+1)) with D := 2^{k+m}(L′+1)^{m−1}C′, ρ from uniform continuity, and r := min(ρ₀, δ/2, ρ/2, 1).
5. For each centre x ∈ s, volume_image_closedBall_le_of_fderiv_not_surjective gives Lᵐ(G(B̄(x,r))) ≤ 2ηr(2(L′+η)r)^{m−1}.
6. Sum ≤ 2^{k+m}·η·(L′+1)^{m−1}·card(s)·rⁿ ≤ D·η ≤ ε, using n = m + k.

## Reference use

### local-project

Queries:
- `rg -n 'theorem .*[Ss]ard' mathlib/Mathlib (no match)`
- `rg -il 'coarea' mathlib/Mathlib (no match)`
- `rg -n 'theorem hausdorffMeasure_le_liminf_sum|theorem hausdorffMeasure_apply' mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n 'theorem MeasureTheory.Measure.euclideanHausdorffMeasure_def|notation "μHE' mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n 'def maximalSeparatedSet|lemma isCover_maximalSeparatedSet|def packingNumber' mathlib/Mathlib/Topology/MetricSpace/CoveringNumbers.lean`
- `rg -n 'def IsCover|def IsSeparated' mathlib/Mathlib/Topology/MetricSpace`
- `rg -n 'exists_orthonormalBasis_extension' mathlib/Mathlib`
- `rg -n 'theorem OrthonormalBasis.measurePreserving_repr|theorem PiLp.volume_preserving_ofLp' mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `rg -n 'theorem volume_Icc_pi|theorem addHaar_ball_of_pos|theorem addHaar_ball_center' mathlib/Mathlib/MeasureTheory/Measure/Lebesgue`
- `rg -n "theorem norm_image_sub_le_of_norm_fderiv_le'?" mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `rg -n 'theorem orthogonal_eq_bot_iff|theorem mem_orthogonal' mathlib/Mathlib/Analysis/InnerProductSpace`
- `rg -n 'exists_cthickening_subset_open|IsCompact.cthickening|mem_cthickening_of_dist_le|self_subset_cthickening' mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `rg -n 'theorem ContDiffOn.continuousOn_fderiv_of_isOpen|theorem ContDiffOn.differentiableOn' mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `rg -n 'IsCompact.uniformContinuousOn_of_continuous|theorem uniformContinuousOn_iff |exists_bound_of_continuousOn' mathlib/Mathlib/Topology mathlib/Mathlib/Analysis/Normed`
- `rg -n 'theorem lintegral_liminf_le|theorem lintegral_finsetSum|theorem Measurable.liminf|theorem measure_toMeasurable|theorem subset_toMeasurable|theorem lintegral_indicator_one' mathlib/Mathlib/MeasureTheory`
- `rg -n 'theorem isOpen_iUnion_countable|theorem ae_ball_iff|theorem measure_biUnion_null_iff' mathlib/Mathlib`
- `rg -n 'theorem ediam_le_of_forall_dist_le|def ediam' mathlib/Mathlib/Topology`
- `rg -n 'abbrev Rn|def coareaJacobian|def CoareaFormula|def C1Sard' project/GMT/Ch02/Contract.lean`
- `grep -n '^theorem' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `sed -n 1405,1530p book/chapter-02.txt (Simon §6: no printed proof of the critical-fibre statement)`
- `python3 -I gen_checks.py (gmt-compare.py child_modules contract scope + lean_contract.validate_lean_statement) on the five statements; lean NodeChallenge_00..04.lean against a scratch olean of GMT.Ch02.Submission`
- `lean Assembly1.lean / Assembly2.lean / LeafC1.lean / LeafC3.lean / LeafC4.lean / FullFinal.lean (five children proved verbatim; check_parent : frozen type; #print axioms)`
- `python3 -I: list lean_name of all 52 nodes in dag.json and test the five proposed names`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/CoveringNumbers.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/Cover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/MetricSeparated.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Submodule.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/Orthogonal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/UniformSpace/HeineCantor.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/EMetricSpace/Diam.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Group/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-coarea-formula-a1-critical-fibers-euclidean-a1/parent-child-handoff.json`
- `/tmp/critfib-decomp/checks_final/NodeChallenge_00.lean`
- `/tmp/critfib-decomp/checks_final/NodeChallenge_04.lean`
- `/tmp/critfib-decomp/assembly/FullFinal.lean`

The snapshot contains no Sard or co-area theorem: both rg searches return no match. The project defines Rn (Contract.lean l.48), coareaJacobian, CoareaFormula and C1Sard, but no Submission lemmas. SimonGMT's AreaCritical.area_image_eq_zero_of_critical covers only the equal-dimension critical-image case (the k = 0 analogue), so it is not reused.

The snapshot's Mathlib supplies every tool the children need:
- Measure.hausdorffMeasure_le_liminf_sum (Hausdorff.lean l.563) and euclideanHausdorffMeasure_def (Measure.lean l.74);
- maximalSeparatedSet, isCover_maximalSeparatedSet and packingNumber (CoveringNumbers.lean), an alternative route for child 3;
- Orthonormal.exists_orthonormalBasis_extension_of_card_eq (PiL2.lean l.1044);
- OrthonormalBasis.measurePreserving_repr (l.111) and PiLp.volume_preserving_ofLp (l.134) in Haar/InnerProductSpace.lean;
- Real.volume_Icc_pi (Lebesgue/Basic.lean l.235) and Measure.addHaar_ball_of_pos (EqHaar.lean l.445);
- Convex.norm_image_sub_le_of_norm_fderiv_le' (MeanValue.lean l.549) and Submodule.orthogonal_eq_bot_iff (Projection/Submodule.lean l.122);
- IsCompact.exists_cthickening_subset_open (l.426) and IsCompact.cthickening (l.283) in Thickening.lean;
- ContDiffOn.continuousOn_fderiv_of_isOpen and ContDiffOn.differentiableOn (ContDiff/Defs.lean), and IsCompact.uniformContinuousOn_of_continuous (HeineCantor.lean);
- lintegral_liminf_le, lintegral_finsetSum, Measurable.liminf, measure_toMeasurable and ediam_le_of_forall_dist_le;
- isOpen_iUnion_countable, ae_ball_iff and measure_biUnion_null_iff.

All five statements pass validate_lean_statement, and their NodeChallenge modules compile in the replayed contract scope. The scratch FullFinal.lean proves all five children verbatim and the selected frozen type, with only propext, Classical.choice and Quot.sound. None of the five lean_names is reserved in dag.json (52 nodes checked).
