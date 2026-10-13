# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1.approx_tangent_in_tangent_space-a1`
- Child DAG node: `root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1.approx_tangent_in_tangent_space-a1.blowup_points-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof steps 3, 5 and 6 (Simon Ch. 3, Definition 1.4). Uses the sibling children plane_integral_pos (Submission.dsmc_att_setIntegral_submodule_pos) and blowup_null_image (Submission.dsmc_att_blowUpMap_image_null).
Notation. Hⁿ := μHE[n]. η_λ := blowUpMap x λ, so η_λ(y) = λ⁻¹(y − x). For S ⊆ ℝ^P, ∫_S f dHⁿ := ∫ f d(Hⁿ⌞S), where (Hⁿ⌞S)(B) = Hⁿ(B ∩ S) for every Borel set B (Measure.restrict_apply); S need not be measurable.
Fix w ∈ Q and s > 0.
1. Test function. Let g(y) := max(0, s − |y − w|).
 (a) g is continuous, g ≥ 0, and g(w) = s > 0.
 (b) If |y − w| > s then s − |y − w| < 0, so g(y) = 0. Hence g vanishes outside the compact set closedBall(w, s) and has compact support.
 (c) g(y) ≠ 0 forces |y − w| < s, i.e. {g ≠ 0} ⊆ ball(w, s).
 (d) Let f ∈ C_c(ℝ^P, ℝ) be g regarded as a compactly supported continuous map, so f(y) = g(y) for all y.
2. The limit is positive. HasApproximateTangentSpaceAt n M x Q contains dim Q = n. Apply plane_integral_pos to Q, g and w (g is continuous, compactly supported and ≥ 0, w ∈ Q, g(w) > 0). This gives I := ∫_Q f dHⁿ = ∫_Q g dHⁿ > 0.
3. Choice of λ₀.
 (a) By the convergence part of HasApproximateTangentSpaceAt applied to f, F(λ) := ∫_{η_λ(M)} f dHⁿ tends to I as λ → 0 within (0, ∞).
 (b) Since I > 0, the open set (0, ∞) is a neighbourhood of I. So {λ : F(λ) > 0} belongs to the filter of neighbourhoods of 0 within (0, ∞).
 (c) Hence there is λ₀ > 0 with F(λ) > 0 for every λ ∈ (0, λ₀). Fix this λ₀ and let λ ∈ (0, λ₀).
4. The blow-up charges the ball. Put S := η_λ(M). Suppose Hⁿ(S ∩ ball(w, s)) = 0.
 (a) The ball is open, hence Borel, so (Hⁿ⌞S)(ball(w, s)) = Hⁿ(ball(w, s) ∩ S) = 0.
 (b) Since {f ≠ 0} ⊆ ball(w, s), the set {f ≠ 0} is Hⁿ⌞S-null. So f = 0 holds Hⁿ⌞S-almost everywhere, and F(λ) = ∫ f d(Hⁿ⌞S) = 0.
 (c) This contradicts F(λ) > 0. Hence Hⁿ(S ∩ ball(w, s)) ≠ 0.
5. The exceptional part is null. λ ≠ 0 (as λ > 0) and Hⁿ(M ∖ N) = 0, so blowup_null_image gives Hⁿ(η_λ(M ∖ N)) = 0.
6. Covering. Let z ∈ S ∩ ball(w, s); then z = η_λ(y) for some y ∈ M. If y ∈ N, then z ∈ η_λ(M ∩ N) ∩ ball(w, s). Otherwise y ∈ M ∖ N and z ∈ η_λ(M ∖ N). Hence S ∩ ball(w, s) ⊆ (η_λ(M ∩ N) ∩ ball(w, s)) ∪ η_λ(M ∖ N).
7. Suppose Hⁿ(η_λ(M ∩ N) ∩ ball(w, s)) were 0. Then step 6, monotonicity and subadditivity of the outer measure Hⁿ, and step 5 give Hⁿ(S ∩ ball(w, s)) ≤ 0 + 0 = 0, contradicting step 4. So Hⁿ(η_λ(M ∩ N) ∩ ball(w, s)) ≠ 0, and in particular this set is nonempty (the empty set has measure 0).
8. Take z in it. Then z = η_λ(y) = λ⁻¹(y − x) for some y ∈ M ∩ N, and z ∈ ball(w, s), i.e. |λ⁻¹(y − x) − w| = dist(z, w) < s. Since λ ∈ (0, λ₀) was arbitrary, λ₀ has the required property.

## Key steps

1. The tent function f(y) = max(0, s − |y − w|) lies in C_c, vanishes off ball(w, s), and f(w) = s > 0.
2. plane_integral_pos gives ∫_Q f dHⁿ > 0, so by approximate-tangent convergence ∫_{η_λ(M)} f dHⁿ > 0 for all λ ∈ (0, λ₀).
3. A positive integral of f over η_λ(M) forces Hⁿ(η_λ(M) ∩ ball(w, s)) ≠ 0.
4. blowup_null_image makes η_λ(M ∖ N) null, so η_λ(M ∩ N) ∩ ball(w, s) is nonempty. This gives y ∈ M ∩ N with |λ⁻¹(y − x) − w| < s.

## Reference use

### local-project

Queries:
- `cat nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1-ap-97f6c0d738/{parent-child-handoff.json,parent-supplied-plan.md,parent-supplied-natural-proof.md}`
- `python3 -I over dag.json (lean_name, lean_statement, status of all 214 nodes; sibling chart_tangent_space frozen type; related nodes approx_tangent_in_submanifold, hausdorff_scaling, blowup_measure_scaling, tangent_invariance, tangent_null_invariance, approx_tangent_local, blowup_integral_continuous, plane_quadratic_moment)`
- `cat nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1-ch-f0862c44ef/parent-supplied-natural-proof.md (sibling chart_tangent_space proof)`
- `diff GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; cmp GMT/Ch07/Contract.lean local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean (both identical)`
- `sed -n 1,280p .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (blowUpMap, HasApproximateTangentSpaceAt, support_euclideanHausdorffMeasure_restrict_submodule, regular_euclideanHausdorffMeasure_restrict_submodule)`
- `cat local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (euclideanHausdorffMeasure_smul₀, Isometry.euclideanHausdorffMeasure_image, Isometry.map_euclideanHausdorffMeasure, isAddHaarMeasure_euclideanHausdorffMeasure, homothety lemmas)`
- `sed -n 60,175p book/chapter-03.txt (Simon 1.4, 1.5, proof of 1.6)`
- `rg -l 'dsmc_att_|setIntegral_submodule_pos|blowUpMap_image_null|blowUp_points_of_approxTangent|mem_range_of_secant_blowUp' on dag.json, DAG.md, issue-workers.json, problem.json, problem.md, nodes/, GMT, SimonGMT and the Mathlib snapshot (no match)`
- `lake env lean /tmp/atts-decomp/Stmts.lean (the four child types elaborate in namespace GMT.Ch07 with the contract opens)`
- `lake env lean /tmp/atts-decomp/Assembly.lean (parent from child and sibling stubs)`
- `lake env lean /tmp/atts-decomp/ChildAB.lean, ChildB.lean, ChildCD.lean, Final2.lean (full child proofs, parent assembly, #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1-ap-97f6c0d738/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1-ap-97f6c0d738/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1-ap-97f6c0d738/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1-ch-f0862c44ef/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/atts-decomp/Stmts.lean`
- `/tmp/atts-decomp/Assembly.lean`
- `/tmp/atts-decomp/ChildAB.lean`
- `/tmp/atts-decomp/ChildB.lean`
- `/tmp/atts-decomp/ChildCD.lean`
- `/tmp/atts-decomp/Final2.lean`
- `/tmp/atts-decomp/sibling_stmt.txt`
- `/tmp/atts-decomp/proposal.md`
- `/tmp/atts-review/Check.lean`
- `/tmp/atts-review/NoSorry.lean`

Snapshot: project b4d606db, mathlib 25730c7c. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

Reusable facts found:
- SimonGMT Chapter03/Rectifiable.lean. blowUpMap x r y = r⁻¹ • (y − x). HasApproximateTangentSpaceAt n M x Q = finrank Q = n together with convergence of ∫ over blowUpMap x r '' M of every C_c test along 𝓝[>] 0. support_euclideanHausdorffMeasure_restrict_submodule (the support of μHE[n]⌞Q is Q) and regular_euclideanHausdorffMeasure_restrict_submodule are used in child A.
- Mathlib Geometry/Euclidean/Volume/Measure.lean. Isometry.euclideanHausdorffMeasure_image and Measure.euclideanHausdorffMeasure_smul₀ are used in child B; isAddHaarMeasure_euclideanHausdorffMeasure and Isometry.map_euclideanHausdorffMeasure are used in child A.
- Mathlib measure/integral API used in children A and C: integral_pos_iff_support_of_nonneg, Continuous.integrable_of_hasCompactSupport, Measure.mem_support_iff_forall, Measure.restrict_apply (no measurability needed on the restricting set), integral_eq_zero_of_ae, nonempty_of_measure_ne_zero, mem_nhdsGT_iff_exists_Ioo_subset.
- Submodule.closed_of_finiteDimensional is used in child D.
- The sibling chart_tangent_space (dsmc_chart_tangentSpace_eq_range; DAG status decomposing, declared dependency) gives tangentSpace N (ψ v) = Set.range (fderiv ℝ ψ v) and the secant estimate, verbatim in the form of child D's hypothesis.

Related nodes in other branches, not reused (different types):
- approxTangent_le_submanifold_tangentSpace (the r = 1 variant, decomposing); no child solves it.
- dtc_hausdorff_dilation and regcomp_atl_blowUp_measure_scaling (both accepted).

Name check: no match for any proposed identifier or the dsmc_att_ prefix anywhere.

Lean checks:
- All four child types elaborate after import GMT.Ch07.Submission.
- All four children are fully proved, using only propext, Classical.choice and Quot.sound.
- The frozen parent type is proved from the children plus the sibling's frozen-type stub; that stub is the only sorryAx.
- An independent reviewer reproduced these checks and accepted the split.
