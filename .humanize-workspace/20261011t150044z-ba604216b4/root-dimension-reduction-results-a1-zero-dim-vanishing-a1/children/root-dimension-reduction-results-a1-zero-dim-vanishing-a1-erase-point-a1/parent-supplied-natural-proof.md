# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.zero_dim_vanishing-a1`
- Child DAG node: `root.dimension_reduction_results-a1.zero_dim_vanishing-a1.erase_point-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation: H⁰ := μHE[0], M := R.carrier, θ := R.mult, ξ := R.orient, M' := M ∖ {p}.

Sibling results used:
- carrier_finite: for every R ∈ IMRep U 0 and compact K ⊆ U, R.carrier ∩ K is finite.
- tangent_erase: for Borel M, x ≠ p and any n, HasApproximateTangentSpaceAt n M x Q implies HasApproximateTangentSpaceAt n (M ∖ {p}) x Q.

1. H⁰{x} = 1 for every x, because μHE[0] = μH[0] (Measure.euclideanHausdorffMeasure_zero) and μH[0]{x} = 1 (Measure.hausdorffMeasure_zero_singleton).
2. (Construction of R'.) Define R' with carrier M', multiplicity θ and orientation ξ, and verify the fields of IMRep U 0:
 (a) measurableSet_carrier: M' = M ∖ {p} is Borel, since M is Borel and {p} is closed.
 (b) carrier_subset: M' ⊆ M ⊆ U.
 (c) rectifiable: M' ⊆ M and M is countably 0-rectifiable, so M' is countably 0-rectifiable (CountablyRectifiable.mono).
 (d) measurable_mult: θ is unchanged, hence measurable.
 (e) mult_pos: if x ∈ M' then x ∈ M, so θ(x) > 0.
 (f) locallyIntegrable_mult: for compact K ⊆ U, M' ∩ K ⊆ M ∩ K, so ∫⁻_{M'∩K} θ dH⁰ ≤ ∫⁻_{M∩K} θ dH⁰ < ∞ (lintegral_mono_set and the corresponding field of R).
 (g) aestronglyMeasurable_orient: H⁰⌞M' ≤ H⁰⌞M (Measure.restrict_mono), and a.e.-strong measurability passes to a smaller measure (AEStronglyMeasurable.mono_measure).
 (h) orients: By R.orients, for H⁰⌞M-a.e. x there is a subspace Q with HasApproximateTangentSpaceAt 0 M x Q and IsUnitOrientationOf (ξ x) Q. Since M' ⊆ M, this also holds for H⁰⌞M'-a.e. x (ae_restrict_of_ae_restrict_of_subset). Also, H⁰⌞M'-a.e. x lies in M' (ae_restrict_mem; M' is measurable). For such x we have x ≠ p. Applying tangent_erase with n = 0, the Borel set M, base point x and deleted point p gives HasApproximateTangentSpaceAt 0 M' x Q; the condition IsUnitOrientationOf (ξ x) Q is unchanged. So for H⁰⌞M'-a.e. x there is Q with HasApproximateTangentSpaceAt 0 M' x Q ∧ IsUnitOrientationOf (ξ x) Q.
 By construction R'.carrier = M ∖ {p}, R'.mult = θ and R'.orient = ξ.
3. (The integrand.) Fix ω ∈ TestFormOn U 0 and let g(x) := θ(x)·ξ(x)(ω(x)) ∈ ℝ, so R.action ω = ∫_M g dH⁰ and R'.action ω = ∫_{M'} g dH⁰. Let K := tsupport ω. Then K is compact, since ω has compact support, and K ⊆ U by the test-form condition. If x ∉ K then ω(x) = 0, so g(x) = θ(x)·ξ(x)(0) = 0 by linearity of ξ(x).
4. (Integrability.) By carrier_finite applied to R and K, M ∩ K is finite. For each y, g is integrable on {y} because H⁰{y} = 1 < ∞ (integrableOn_singleton). Hence g is integrable on the finite union M ∩ K = ⋃_{y∈M∩K}{y} (integrableOn_finite_biUnion). M is measurable and g = 0 on M ∖ (M ∩ K) ⊆ ℝ^P ∖ K, so g is integrable on M (IntegrableOn.of_forall_sdiff_eq_zero). It is therefore integrable on the subsets M' and {p}.
5. (Splitting.) Since p ∈ M, M = M' ∪ {p}, a disjoint union with {p} measurable. By additivity of the Bochner integral over disjoint sets on which g is integrable (setIntegral_union), ∫_M g dH⁰ = ∫_{M'} g dH⁰ + ∫_{{p}} g dH⁰.
6. (The point term.) ∫_{{p}} g dH⁰ = H⁰{p}·g(p) = g(p) = θ(p)·ξ(p)(ω(p)), by integral_singleton and step 1.
7. Steps 5 and 6 give R.action ω = R'.action ω + θ(p)·ξ(p)(ω(p)) for every ω ∈ TestFormOn U 0. Together with step 2 this proves the claim.

## Key steps

1. R' = (M ∖ {p}, θ, ξ) satisfies every IMRep field: Borel, ⊆ U, rectifiable by monotonicity, θ positive and locally integrable on the smaller set, ξ a.e.-strongly measurable for the smaller restricted measure.
2. The a.e. orientation condition transfers: H⁰⌞(M∖{p})-a.e. x lies in M∖{p}, so x ≠ p and tangent_erase keeps the approximate tangent space.
3. For a test form ω, the integrand vanishes off the compact tsupport ω, and M ∩ tsupport ω is finite (carrier_finite), so the integrand is integrable on M.
4. Splitting M = (M ∖ {p}) ∪ {p} and using H⁰{p} = 1 gives R.action ω = R'.action ω + θ(p)ξ(p)(ω(p)).

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
