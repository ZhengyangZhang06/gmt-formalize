# Parent-supplied natural-language proof

- Parent DAG node: `root.deformation-a1.im_combination-a1`
- Child DAG node: `root.deformation-a1.im_combination-a1.weight_change-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the weight lemma of the parent proof (its Lemma 2, Simon Ch. 3, Remark 1.8(1)): on a set with locally finite Hᵏ measure the approximate tangent space does not depend on the positive multiplicity. Weight 1 is the unweighted Definition 1.4, so θ′ ≡ 1 or θ ≡ 1 gives the two directions of that Lemma 2. The parent proof uses Lusin's theorem and continuity on compact pieces. Here the same comparison uses normalized Lebesgue points, which are the reused sibling lebesgue_points (Submission.iwl_imc_normalized_lebesgue_points, statement (LP)), together with the reused sibling tangent_locality ((TL), as stated in subset_locality). Notation as in subset_locality: ‖t‖ₑ = |t|, B̄_ρ(x) := closedBall x ρ, r^{−k} := ENNReal.ofReal((r^k)⁻¹).

(LP) [sibling lebesgue_points, used with U := ℝ^N]: if E ⊆ ℝ^N is H-null-measurable, H(E ∩ K) < ∞ and f : ℝ^N → ℝ is H-integrable on E ∩ K for every compact K, then for H⌞E-a.e. x and every R > 0, r^{−k}·∫⁻_{E∩B̄_{Rr}(x)} ‖f(y) − f(x)‖ₑ dH(y) → 0 as r ↓ 0.
(TL) [sibling tangent_locality]: for H-null-measurable M, M′, functions θ, θ′ and a point x with θ(x) = θ′(x), suppose that for some ρ > 0 θ is integrable on M ∩ B̄_ρ(x) and θ′ on M′ ∩ B̄_ρ(x), and that r^{−k}·∫⁻_{B̄_{Rr}(x)} ‖1_Mθ − 1_{M′}θ′‖ₑ dH → 0 as r ↓ 0 for every R > 0. Then HasWeightedApproximateTangentSpaceAt k M θ x Q ↔ HasWeightedApproximateTangentSpaceAt k M′ θ′ x Q for every Q.

1. (Good points.)
   - Apply (LP) to f := θ and to f := θ′. The hypotheses are E null-measurable, H(E ∩ K) < ∞, and integrability of θ, θ′ on E ∩ K; the conditions K ⊆ ℝ^N and E ⊆ ℝ^N are automatic.
   - Intersect the two H⌞E-a.e. statements with x ∈ E (ae_restrict_mem₀). Then H⌞E-a.e. x satisfies x ∈ E and, for every R > 0, as r ↓ 0:
     A(r) := r^{−k}·∫⁻_{E∩B̄_{Rr}(x)} ‖θ(y) − θ(x)‖ₑ dH(y) → 0,
     A′(r) := r^{−k}·∫⁻_{E∩B̄_{Rr}(x)} ‖θ′(y) − θ′(x)‖ₑ dH(y) → 0.
   Fix such an x and a linear subspace Q with HasWeightedApproximateTangentSpaceAt k E θ x Q.

2. (Normalizing constant.) θ(x) > 0 because x ∈ E. Put c := θ′(x)/θ(x) and θ̃(y) := c·θ(y). Then θ̃(x) = c·θ(x) = θ′(x).

3. (Homogeneity of Definition 1.7.) HasWeightedApproximateTangentSpaceAt k E θ̃ x Q holds.
   - finrank Q = k is unchanged.
   - For f ∈ C_c(ℝ^N) and every r, ∫_{η_{x,r}(E)} f(y)·θ̃(x + ry) dH(y) = c·∫_{η_{x,r}(E)} f(y)·θ(x + ry) dH(y). This is integral_const_mul, valid for every integrand (both sides vanish together if the integrand is not integrable).
   - By hypothesis the right side tends to c·θ(x)·∫_Q f dH = θ̃(x)·∫_Q f dH as r ↓ 0.

4. (Density estimate.) Fix R > 0 and r ∈ ℝ, and write B := B̄_{Rr}(x).
   - For z ∈ E, c·θ(x) = θ′(x) gives θ̃(z) − θ′(z) = c(θ(z) − θ(x)) − (θ′(z) − θ′(x)). Hence ‖θ̃(z) − θ′(z)‖ₑ ≤ ‖c‖ₑ·‖θ(z) − θ(x)‖ₑ + ‖θ′(z) − θ′(x)‖ₑ.
   - ‖1_Eθ̃(z) − 1_Eθ′(z)‖ₑ = 1_E(z)·‖θ̃(z) − θ′(z)‖ₑ, and E is null-measurable for H⌞B. As in step 4 of subset_locality, ∫⁻_B ‖1_Eθ̃ − 1_Eθ′‖ₑ dH = ∫⁻_{E∩B} ‖θ̃ − θ′‖ₑ dH.
   - Integrate the pointwise bound over E ∩ B. Then ∫⁻_{E∩B} ‖θ̃ − θ′‖ₑ dH ≤ ‖c‖ₑ·∫⁻_{E∩B} ‖θ − θ(x)‖ₑ dH + ∫⁻_{E∩B} ‖θ′ − θ′(x)‖ₑ dH.
     · The integral of the sum splits (lintegral_add_left′), because y ↦ ‖c‖ₑ·‖θ(y) − θ(x)‖ₑ is a.e.-measurable for H⌞(E ∩ B): θ is integrable on E ∩ B (the integrability hypothesis with the compact set K := B).
     · The constant ‖c‖ₑ < ∞ is pulled out by lintegral_const_mul′.
   - Multiply by r^{−k}: 0 ≤ r^{−k}·∫⁻_B ‖1_Eθ̃ − 1_Eθ′‖ₑ dH ≤ ‖c‖ₑ·A(r) + A′(r).
   - By step 1 the right side tends to ‖c‖ₑ·0 + 0 = 0 as r ↓ 0 (ENNReal.Tendsto.const_mul, Tendsto.add). By squeezing, so does the middle term, for every R > 0.

5. (Apply (TL).) Use (TL) with (M, θ) := (E, θ̃), (M′, θ′) := (E, θ′) and the point x:
   - E is H-null-measurable, and θ̃(x) = θ′(x) by step 2;
   - with ρ := 1, θ̃ = cθ and θ′ are integrable on E ∩ B̄_1(x) (the integrability hypotheses with the compact set K := B̄_1(x), and Integrable.const_mul);
   - the density hypothesis is step 4.
   Hence HasWeightedApproximateTangentSpaceAt k E θ̃ x Q ↔ HasWeightedApproximateTangentSpaceAt k E θ′ x Q, and step 3 gives the left side. So Q is a weighted approximate tangent space of (E, θ′) at x. This holds for H⌞E-a.e. x and every Q. ∎

## Key steps

1. lebesgue_points for θ and θ′ on E: r^{−k}·∫⁻_{E∩B̄_{Rr}(x)} |θ − θ(x)| dH → 0 and likewise for θ′, H⌞E-a.e.
2. c := θ′(x)/θ(x); homogeneity of Definition 1.7: HasWATS(E, θ, x, Q) implies HasWATS(E, cθ, x, Q)
3. |cθ − θ′| ≤ |c|·|θ − θ(x)| + |θ′ − θ′(x)| on E, hence r^{−k}·∫⁻_{B̄_{Rr}(x)} |1_E cθ − 1_E θ′| dH → 0
4. tangent_locality with (E, cθ) and (E, θ′), using cθ(x) = θ′(x)

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp snapshot project/GMT/Ch06/Contract.lean vs workspace GMT/Ch06/Contract.lean; cmp snapshot Submission.lean vs Contract.lean; cmp workspace Submission.lean vs Contract.lean (all byte-identical)`
- `python3 -I scans of dag.json: lean_name/status/candidate_commit/lean_statement of nodes matching tangent|density|weight|locality|orient|combin|triple|tau|lincomb; duplicate lean_name scan (none); reuse-closure scan of all parents with reused children`
- `python3 -I: parent-child-handoff.json of the 9 reused nodes (key, depends_on, title/statement/lean_statement equality with dag.json) and their isolated-comparator-result.json (passed = true)`
- `sed -n 6557,6597p and 2365,2369p /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_existing_lean_name_problem, _accepted_checkpoint: identical-type reuse of accepted nodes allowed, unaccepted names reserved)`
- `rg -n 'deformation_imcomb' project lake-packages-25730c7c/simongmt dag.json (no match)`
- `rg -n 'def HasWeightedApproximateTangentSpaceAt|def HasApproximateTangentSpaceAt|def blowUpMap' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (lines 330, 102, 96)`
- `rg -n 'theorem hasProd_prod_of_ne_finset_one|theorem lintegral_indicator₀|theorem restrict_restrict₀ |theorem ae_restrict_mem₀|theorem ae_restrict_iUnion_iff|theorem ae_restrict_iff'₀|theorem ofReal_inv_of_pos|aestronglyMeasurable_iUnion_iff|theorem iUnion_closedBall_nat|exists_nat_one_div_lt|theorem integral_const_mul|theorem lintegral_add_left'|theorem lintegral_const_mul' ' in the snapshot mathlib/Mathlib`
- `sed -n 750,770p book/chapter-06.txt (3.2 Remarks); sed -n 284,330p book/chapter-03.txt (1.7, 1.8(1), 1.9); sed -n 698,735p and 920,940p book/chapter-01.txt (3.6, 3.7(2), 3.17)`
- `python3 -I scripts/challenges.py: verifier/lean_contract.validate_lean_statement and gmt-compare.child_modules (contract mode) for the 12 child types and the parent type`
- `lake env lean (toolchain v4.35.0-rc3, frozen workspace build) on nc/NC_*.lean (13 files, exit 0, only the sorry warning), src/Assembly.lean, src/ChildA.lean, src/ChildB.lean, src/ChildC.lean and src/Integrated.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-combination-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-series-a1-im-combine-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-series-a1-im-combine-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-tangent-locality-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-im-closure-a1-lebesgue-points-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-zero-3299c8304e/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-im-closure-a1/decomposition-v2.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/InfiniteSum/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/imcomb-decomp-k7q2/src/Integrated.lean`
- `/tmp/imcomb-decomp-k7q2/logs/integrated.log`
- `/tmp/imcomb-decomp-k7q2/src/Assembly.lean`

Pinned revisions confirmed; the frozen contract is byte-identical to the snapshot and Submission = Contract. Nine needed results are already comparator-accepted with identical-type reuse allowed: fiw_ims_combine (Steps 4–8 for an integer series, hence for a·X + b·Y) with its DAG dependencies orientation_sign, frame_sign, overlap_finite, tsum_tau; iwl_weighted_tangent_locality (TL); lpf_wtc_ae_zero_density_off_set (Upper Density Theorem); and iwl_imc_normalized_lebesgue_points with its dependency rectifiability_density_comparison. All passed their isolated comparators. No accepted node gives the tangent comparison on overlaps for positive multiplicities; fiw_tangent_locality and iwl_imc_tangent_overlap are unaccepted and stay untouched. So it is supplied by three new, unreserved lemmas. The 12 child types and the parent type validate and elaborate in the exact comparator scope. Complete Lean proofs of the three new lemmas plus the parent assembly compile against stubs of the reused types, with axioms [propext, Classical.choice, Quot.sound] plus exactly the intended stubs. The Mathlib facts used (finite HasSum, null-measurable indicator integrals, countable a.e. unions, ofReal_inv_of_pos, aestronglyMeasurable_iUnion_iff) are located in the snapshot.
