# Parent-supplied natural-language proof

- Parent DAG node: `root.half_space_cone_lies_in_boundary-a1.tangent_projection_aemeasurable-a1`
- Child DAG node: `root.half_space_cone_lies_in_boundary-a1.tangent_projection_aemeasurable-a1.blowup_integral_continuous-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5 of the parent-supplied proof of imrep_univ_tangent_starProjection_aemeasurable. The integral is the one in Simon's Definition 1.4 of Ch. 3 (chapter-03.txt lines 77–86; SimonGMT HasApproximateTangentSpaceAt), where M is likewise assumed to have Hⁿ(M ∩ K) < ∞ for compact K. Simon prints no proof, so the parent's argument is given with all details. It uses neither measurability of M nor any property of M beyond the local-finiteness hypothesis.

Notation. Hⁿ := μHE[n] on ℝ^P. For a set A, ∫_A g dHⁿ := ∫ g d(Hⁿ⌞A). η_{x,r}(y) := r⁻¹(y − x) (blowUpMap x r), and ν := Hⁿ⌞M.

1. Scaling of Hⁿ under η_{x,r}. Fix x ∈ ℝ^P. Claim: Hⁿ(η_{x,r}(S)) = r⁻ⁿHⁿ(S) for every set S ⊆ ℝ^P, measurable or not. Indeed η_{x,r}(S) = h(τ(S)), where τ(y) := y − x and h(z) := r⁻¹z.
- τ is an isometry of ℝ^P, and isometries preserve Hⁿ of every set (Isometry.euclideanHausdorffMeasure_image).
- h is the homothety with centre 0 and ratio r⁻¹ ≠ 0, so Hⁿ(h(S')) = |r⁻¹|ⁿHⁿ(S') for every S' (euclideanHausdorffMeasure_homothety_image).
As r > 0, |r⁻¹|ⁿ = r⁻ⁿ.

2. Push-forward identity. b := η_{x,r} is a homeomorphism of ℝ^P with inverse b⁻¹(z) = x + rz. Let ν_x := Hⁿ⌞b(M). Claim: (b⁻¹)_#ν_x = r⁻ⁿν. Let A be a Borel set. Then (b⁻¹)⁻¹(A) = b(A), which is Borel, and
(b⁻¹)_#ν_x(A) = ν_x(b(A)) = Hⁿ(b(A) ∩ b(M)) = Hⁿ(b(A ∩ M)) = r⁻ⁿHⁿ(A ∩ M) = r⁻ⁿν(A).
The third equality uses that b is injective, and the fourth uses step 1. Two measures that agree on all Borel sets are equal.

3. Change of variables. b⁻¹ is a homeomorphism, hence a measurable embedding. Applying MeasurableEmbedding.integral_map to the function f∘b:
∫ f dν_x = ∫ (f∘b)(b⁻¹z) dν_x(z) = ∫ f∘b d((b⁻¹)_#ν_x) = ∫ f∘b d(r⁻ⁿν) = r⁻ⁿ∫ f(r⁻¹(y − x)) dν(y).
Hence, for every x, Φ(x) := ∫_{η_{x,r}(M)} f dHⁿ = r⁻ⁿΨ(x), where Ψ(x) := ∫_M f(r⁻¹(y − x)) dHⁿ(y).

4. Bounds for f. Since f is continuous with compact support, there is C ≥ 0 with |f(z)| ≤ C for all z, and there is R ≥ 0 with tsupport f ⊆ closedBall(0, R).

5. Local domination. Fix x₀ ∈ ℝ^P and let B := closedBall(x₀, 1 + rR), a compact set. Let x ∈ ball(x₀, 1) and let y ∈ ℝ^P with y ∉ B. Suppose f(r⁻¹(y − x)) ≠ 0. Then r⁻¹(y − x) ∈ tsupport f ⊆ closedBall(0, R), so |y − x| ≤ rR and |y − x₀| ≤ |y − x| + |x − x₀| < rR + 1. That means y ∈ B, a contradiction. Hence |f(r⁻¹(y − x))| ≤ C·1_B(y) for all y ∈ ℝ^P and all x ∈ ball(x₀, 1).

6. The dominating function is integrable. B is Borel, so ν(B) = Hⁿ(B ∩ M) = Hⁿ(M ∩ B). This is finite by the hypothesis applied to the compact set B. Therefore C·1_B is ν-integrable.

7. Measurability and pointwise continuity. For each x, the map y ↦ f(r⁻¹(y − x)) is continuous, hence (strongly) measurable. For each y, the map x ↦ f(r⁻¹(y − x)) is continuous.

8. Dominated convergence. Apply the dominated convergence theorem for parameter-dependent integrals (continuousAt_of_dominated) with the bound of step 5, which is valid on the neighbourhood ball(x₀, 1) of x₀, the integrable bound of step 6 and the continuity of step 7. It shows that Ψ is continuous at x₀. Since x₀ is arbitrary, Ψ is continuous on ℝ^P. By step 3, so is Φ = r⁻ⁿΨ; that is, x ↦ ∫_{η_{x,r}(M)} f dHⁿ is continuous. ∎

## Key steps

1. Hⁿ(η_{x,r}(S)) = r⁻ⁿHⁿ(S) for every set S (the translation is an isometry, followed by a homothety of ratio r⁻¹).
2. (η_{x,r}⁻¹)_#(Hⁿ⌞η_{x,r}(M)) = r⁻ⁿHⁿ⌞M, hence ∫_{η_{x,r}(M)} f dHⁿ = r⁻ⁿ∫_M f(r⁻¹(y−x)) dHⁿ(y).
3. For x ∈ ball(x₀,1) the integrand is bounded by sup|f|·1_{closedBall(x₀,1+rR)}, which is integrable because Hⁿ(M ∩ K) < ∞ for compact K.
4. Dominated convergence gives continuity at every x₀; multiplying by r⁻ⁿ preserves continuity.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; git show cd85cf76069b4253c566d71bc95ea30382f99c75:GMT/Ch07/Submission.lean | cmp - GMT/Ch07/Submission.lean`
- `cat local-references/123e8435b4a2469b/manifest.json`
- `cat nodes/root-half-space-cone-lies-in-boundary-a1-tangent-projection-aemeasurable-a1/{parent-child-handoff.json,parent-supplied-plan.md,parent-supplied-natural-proof.md,decomposition-v1.json,decomposition-audit-v1.json,decomposition-review-receipt-v1.json}`
- `sed -n 85,280p .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (blowUpMap, HasApproximateTangentSpaceAt, HasApproximateTangentSpaceAt.unique, aemeasurable_starProjection_of_approximateTangentField)`
- `sed -n 70,100p book/chapter-03.txt (Definition 1.4, Remarks 1.5)`
- `rg -n 'theorem Isometry.map_euclideanHausdorffMeasure|euclideanHausdorffMeasure_eq_volume|euclideanHausdorffMeasure_homothety_image|theorem Isometry.euclideanHausdorffMeasure_image' mathlib/Mathlib`
- `rg -n "theorem aemeasurable_of_tendsto_metrizable_ae'|theorem continuousAt_of_dominated|integral_pos_of_hasCompactSupport_nonneg_nonzero|piLpCongrRight|piLpCongrLeft|theorem measurePreserving|theorem MeasurePreserving.integral_comp" mathlib/Mathlib`
- `rg -n 'starProjection_eq_sum_rankOne|theorem inner_starProjection_left_eq_right|theorem AEMeasurable.of_eval|theorem withDensity_absolutelyContinuous|instance instMeasurableSpace|instance instBorelSpace' mathlib/Mathlib`
- `grep -rhoE '"lean_name": *"[^"]+"' nodes dag.json problem.json | sort | uniq -c (161 distinct names); rg -n -w 'exists_plane_cutoff_quadratic_moment_eq|continuous_blowUp_image_setIntegral|aemeasurable_starProjection_of_aemeasurable_norm_sq' simongmt/Poincare project/GMT mathlib/Mathlib nodes dag.json problem.json DAG.md`
- `python3 scan of nodes/*/*.json for lean_name dtc_cone_tangentProjection_aemeasurable and imrep_approxTangent_starProjection_aesm (their lean_statements)`
- `lake env lean /tmp/tpa-v2/Stmts.lean (child/parent types, #synth MeasurableSpace/BorelSpace on Euclid P →L[ℝ] Euclid P, rfl to borel, pp.explicit #check); lake env lean /tmp/tpa-v2/Assembly.lean; lake env lean /tmp/tpa-v2/Full.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/PROBLEM.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-tangent-projection-aemeasurable-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-tangent-projection-aemeasurable-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-tangent-projection-aemeasurable-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-tangent-projection-aemeasurable-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-tangent-projection-aemeasurable-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-tangent-projection-aemeasurable-a1/decomposition-review-receipt-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Metrizable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/tmp/tpa-v2/Stmts.lean`
- `/tmp/tpa-v2/Assembly.lean`
- `/tmp/tpa-v2/Full.lean`

Contract and Submission:
- The snapshot contract (project b4d606d, mathlib 25730c7c) is byte-identical to the workspace Contract.lean and Submission.lean.
- The parent's dispatch commit cd85cf76 leaves Submission.lean unchanged, so no Submission declaration can collide with the child names.

SimonGMT:
- Chapter03/Rectifiable.lean defines blowUpMap x r y = r⁻¹(y−x).
- It defines HasApproximateTangentSpaceAt as finrank = n plus convergence for every C_c test function as r → 0⁺. This is Simon Ch. 3, Def. 1.4 (chapter-03.txt lines 77–86).
- It proves uniqueness of the tangent plane but not measurability of the tangent-plane field, so the three children are new obligations.

Mathlib snapshot:
- It supplies every lemma the child proofs cite: Isometry.map_euclideanHausdorffMeasure, Isometry.euclideanHausdorffMeasure_image, euclideanHausdorffMeasure_homothety_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, LinearIsometryEquiv.piLpCongrLeft / piLpCongrRight, LinearIsometryEquiv.measurePreserving, MeasurePreserving.integral_comp, Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero, continuousAt_of_dominated, aemeasurable_of_tendsto_metrizable_ae', OrthonormalBasis.starProjection_eq_sum_rankOne, Submodule.inner_starProjection_left_eq_right, AEMeasurable.of_eval and withDensity_absolutelyContinuous.
- ContinuousLinearMap.instMeasurableSpace is borel _. It is the instance used in both the parent type and child C.

Lean checks:
- All three child types elaborate after `import GMT.Ch07.Submission`.
- The conditional assembly compiles; its sorryAx comes only from the sorry'd children.
- Full.lean (sha256 5f31f5e9…) proves the three children at their exact frozen types and the parent from them. All four use only propext, Classical.choice and Quot.sound.

Names:
- exists_plane_cutoff_quadratic_moment_eq is new everywhere.
- continuous_blowUp_image_setIntegral and aemeasurable_starProjection_of_aemeasurable_norm_sq occur only in this node's rejected v1 files, with identical types.
- The nearest DAG statements are different propositions: imrep_approxTangent_starProjection_aesm (AEStronglyMeasurable, general U, Hⁿ⌞M) and dtc_cone_tangentProjection_aemeasurable (general U, Hⁿ⌞M).
