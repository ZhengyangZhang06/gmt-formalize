# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.zero_dim_vanishing-a1`
- Child DAG node: `root.dimension_reduction_results-a1.zero_dim_vanishing-a1.tangent_erase-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation: Hⁿ := μHE[n], η_r := η_{x,r} = blowUpMap x r, so η_r(y) = r⁻¹(y − x).
1. (Reduction.) The first component of HasApproximateTangentSpaceAt, finrank Q = n, does not involve the set, so it carries over unchanged. Fix f ∈ C_c(ℝ^P, ℝ) and put F(r) := ∫_{η_r(M)} f dHⁿ and G(r) := ∫_{η_r(M∖{p})} f dHⁿ. By hypothesis F(r) → ∫_Q f dHⁿ as r → 0⁺. It suffices to find r₀ > 0 with F(r) = G(r) for all r ∈ (0, r₀). Then F and G agree eventually in the filter 𝓝[>] 0, so G(r) → ∫_Q f dHⁿ as well (Tendsto.congr'). This is the second component of HasApproximateTangentSpaceAt n (M ∖ {p}) x Q.
2. (Choice of r₀.) f has compact support, so tsupport f is bounded: there is R₀ ∈ ℝ with tsupport f ⊆ closedBall(0, R₀). Put R₁ := max(R₀, 1) > 0 and d := ‖p − x‖ > 0 (because x ≠ p). Let r₀ := d/(R₁ + 1) > 0, and fix r with 0 < r < r₀.
3. (Image of the punctured set.) Since r ≠ 0, η_r is injective: r⁻¹(a − x) = r⁻¹(b − x) implies a = b. Hence η_r(M ∖ {p}) = η_r(M) ∖ η_r({p}) = η_r(M) ∖ {q}, where q := η_r(p) = r⁻¹(p − x).
4. (Measurability.) η_r(M) = {y : x + r·y ∈ M}. Indeed, if y = r⁻¹(z − x) with z ∈ M, then x + r·y = z ∈ M; conversely, if x + r·y ∈ M, then y = η_r(x + r·y). The map y ↦ x + r·y is continuous, so η_r(M) is the preimage of the Borel set M under a measurable map and is Borel.
5. (f vanishes at q.) ‖q‖ = r⁻¹·d. From r < d/(R₁ + 1) we get r(R₁ + 1) < d, so ‖q‖ = d/r > R₁ + 1 > R₀, using R₁ ≥ R₀. Thus q ∉ closedBall(0, R₀) ⊇ tsupport f, so f(q) = 0, since a function vanishes outside its topological support.
6. (Equality of the integrals.) Let t := η_r(M), which is Borel by step 4, and s := t ∖ {q} ⊆ t. Every point of t ∖ s equals q, where f vanishes by step 5. Hence ∫_t f dHⁿ = ∫_s f dHⁿ, by Mathlib's setIntegral_eq_of_subset_of_forall_sdiff_eq_zero: if t is measurable, s ⊆ t and f = 0 on t ∖ s, the two Bochner set integrals coincide. This includes the case where f is not integrable on t, when both sides are 0. By step 3, s = η_r(M ∖ {p}), so F(r) = G(r).
7. Step 6 holds for every r ∈ (0, r₀). By step 1, HasApproximateTangentSpaceAt n (M ∖ {p}) x Q.

## Key steps

1. The dimension part is unchanged; it suffices that the blow-up integrals over M and over M ∖ {p} agree for all small r > 0.
2. For r > 0, η_{x,r} is injective, so η_{x,r}(M ∖ {p}) = η_{x,r}(M) ∖ {q} with q = r⁻¹(p − x); and η_{x,r}(M) = {y : x + r y ∈ M} is Borel.
3. ‖q‖ = ‖p − x‖/r exceeds the support radius of f once r < ‖p − x‖/(max(R₀,1)+1), so f(q) = 0.
4. Deleting a point where the integrand vanishes does not change the set integral (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero), so the limits coincide (Tendsto.congr').

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD`
- `grep -n 'euclideanHausdorffMeasure_zero' local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean; sed -n 620,665p local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n 'theorem setIntegral_eq_of_subset_of_forall_sdiff_eq_zero|theorem setIntegral_union |theorem integral_singleton |theorem lintegral_finset|theorem integrableOn_finite_biUnion|theorem IntegrableOn.of_forall_sdiff_eq_zero|theorem integrableOn_singleton |theorem Infinite.exists_subset_card_eq|theorem hausdorffMeasure_zero_singleton' (snapshot mathlib)`
- `grep -rn -i 'dirac\|pointCurrent\|pointGeometricCurrentOn\|TestFormOnConverges\.' .lake/packages/simongmt/Poincare/SimonGMT; sed -n 1,70p Chapter06/GeometricPointProduct.lean`
- `grep -n 'def HasApproximateTangentSpaceAt\|def CountablyRectifiable\|def blowUpMap\|CountablyRectifiable.mono' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `sed -n 1,200p simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean (VanishesOn, zeroRegion, support); sed -n 1,320p Chapter06/Currents.lean (TestFormOnConverges, GeometricCurrentOn, ext, Zero); sed -n 1,140p Chapter06/Mass.lean (massOn)`
- `lake env lean /tmp/zdv-check/Probe.lean: env.contains of Poincare.SimonGMT.Chapter06.pointGeometricCurrentOn, Poincare.SimonGMT.Chapter06.TestFormOnConverges.tendsto_eval and GMT.Ch07.Submission.dimred_im_mass_measure after import GMT.Ch07.Submission`
- `python3 inspection of dag.json: dtc_dim_zero_eq_zero, dtc_dim_zero_carrier_finite, dtc_dim_zero_erase_point, dtc_point_current, dtc_approxTangent_sdiff_singleton, dor_zero_dim_minimizing_support_disjoint, regcomp_rim_sub_imrep, rsd_cmr_imrep_restrict (statements and statuses)`
- `grep -c dimred_zdv dag.json; for d in .swarm-worktrees/*/gmt-ch07/GMT; do grep -rl dimred_zdv $d; done`
- `lake env lean /tmp/zdv-check/Assembly.lean; lake env lean /tmp/zdv-check/Children.lean; lake env lean /tmp/zdv-check/Full.lean with #print axioms; string comparison of the tested parent and sibling types with the handoff lean_statement fields`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Countable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Finite/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/GeometricPointProduct.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-zero-dim-vanishing-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-im-mass-measure-a1/parent-child-handoff.json`
- `/tmp/zdv-check/Probe.lean`
- `/tmp/zdv-check/Assembly.lean`
- `/tmp/zdv-check/Children.lean`
- `/tmp/zdv-check/Full.lean`

Pins match. The snapshot is project b4d606d, equal to workspace HEAD, with mathlib 25730c7c and simongmt 2b36630. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

Mathlib facts used:
- μHE[0] = μH[0] (Measure.lean:82) and μH[0]{x} = 1 (Hausdorff.lean:628), so H⁰{x} = 1.
- Set-integral and integrability lemmas: setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (Bochner/Set.lean:466), setIntegral_union (:87), integral_singleton (Bochner/Basic.lean:1254), lintegral_finset (Lebesgue/Countable.lean:149), integrableOn_singleton / integrableOn_finite_biUnion / IntegrableOn.of_forall_sdiff_eq_zero (IntegrableOn.lean:221/226/435), Set.Infinite.exists_subset_card_eq (Data/Set/Finite/Basic.lean:862).

SimonGMT facts used:
- HasApproximateTangentSpaceAt integrates f over blowUpMap x r '' M against μHE[n] as r → 0⁺ (Rectifiable.lean:96–111). CountablyRectifiable.mono exists.
- support = U \ zeroRegion, where zeroRegion is the union of open W with compact closure ⊆ U on which the current vanishes (CurrentLocalEquality.lean).
- GeometricCurrentOn continuity is defined via TestFormOnConverges to 0; GeometricCurrentOn.ext and Zero are in Currents.lean.
- pointGeometricCurrentOn and TestFormOnConverges.tendsto_eval exist only in Chapter06/GeometricPointProduct.lean, which the contract does not import. The probe confirmed both are absent after import GMT.Ch07.Submission, so point_current must be proved as a child.

Related nodes. dtc_dim_zero_* and dtc_point_current, dor_zero_dim_minimizing_support_disjoint, regcomp_rim_sub_imrep and rsd_cmr_imrep_restrict are all status decomposing, none accepted. So no exact accepted declaration can be reused, and the names chosen here use the unused prefix dimred_zdv_; grep found no match in dag.json, the workspace GMT tree or any of the 544 swarm worktrees.

Lean check (scratch files only, workspace untouched):
- All four child types elaborate in GMT.Ch07 with the contract opens.
- All four children were fully proved (axioms propext, Classical.choice, Quot.sound).
- The frozen parent type was proved from them plus a stub of the frozen sibling dimred_im_mass_measure; the parent depends on sorryAx only through that stub.
