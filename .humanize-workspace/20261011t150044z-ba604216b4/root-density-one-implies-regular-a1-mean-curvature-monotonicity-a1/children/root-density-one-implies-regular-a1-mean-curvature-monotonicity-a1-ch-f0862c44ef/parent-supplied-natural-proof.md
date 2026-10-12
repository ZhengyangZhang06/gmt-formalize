# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1`
- Child DAG node: `root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1.chart_tangent_space-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 2, §4 (chapter-02.txt). Definition (4.1) describes an embedded C^r submanifold by proper, injective charts of maximal rank, and T_yM is the set of velocities of C¹ curves in M. The parent proof uses two consequences: step 1 ("T_qN = Dψ(v)(ℝ^{n+ℓ}) for q = ψ(v): C¹ curves in N ∩ W₀ lift through a local inverse of ψ") and step 3 ("since N ∩ W₀ is a C¹ submanifold, the unit vectors (x_i − x)/|x_i − x| accumulate only in T_xN"). Both are proved here from the chart axioms.
Notation. Fix v ∈ V and put q := ψ(v) and A := Dψ(v) = fderiv ℝ ψ v. V is open and ψ is C^r on V with r ≥ 1, so ψ is continuous on V and differentiable at every z ∈ V with derivative fderiv ℝ ψ z. Also q ∈ ψ(V) = W ∩ N, so q ∈ W and q ∈ N.
1. Lower bound for A. A : ℝ^d → ℝ^P is linear and injective. If d = 0, put m := 1. Otherwise a ↦ |Aa| is continuous and positive on the compact unit sphere of ℝ^d, so m := min_{|a|=1} |Aa| > 0. In both cases |Aa| ≥ m|a| for all a ∈ ℝ^d.
2. Proof of (ii). Suppose (ii) fails.
 (a) Then there are ε > 0 and points v_j ∈ V (j ∈ ℕ) with |ψ(v_j) − q| < 1/(j+1) and |v_j − v| ≥ ε.
 (b) The set K := {ψ(v_j) : j ∈ ℕ} ∪ {q} is compact, being a convergent sequence together with its limit. Also K ⊆ W, because ψ(V) = W ∩ N ⊆ W.
 (c) By properness, V ∩ ψ⁻¹(K) is compact. It contains every v_j, so a subsequence v_{j_i} converges to some v* ∈ V ∩ ψ⁻¹(K) ⊆ V.
 (d) ψ is continuous on V, and all v_{j_i} and v* lie in V, so ψ(v*) = lim ψ(v_{j_i}) = q = ψ(v). Injectivity of ψ on V gives v* = v, which contradicts |v_{j_i} − v| ≥ ε.
3. Differentiability estimate. ψ is differentiable at v with derivative A. So for every η > 0 there is ρ(η) > 0 such that |ψ(v') − q − A(v' − v)| ≤ η|v' − v| whenever |v' − v| < ρ(η). Take η = m/2 and |v' − v| < ρ(m/2). By step 1, |ψ(v') − q| ≥ |A(v' − v)| − (m/2)|v' − v| ≥ (m/2)|v' − v|, that is, |v' − v| ≤ (2/m)|ψ(v') − q|.
4. Proof of (iii). Let ε > 0, η := min(m/2, εm/2) and ρ := min(ρ(η), ρ(m/2)).
 (a) By (ii), choose δ₁ > 0 such that v' ∈ V and |ψ(v') − q| < δ₁ imply |v' − v| < ρ.
 (b) W is open and q ∈ W, so choose δ₂ > 0 with ball(q, δ₂) ⊆ W. Put δ := min(δ₁, δ₂).
 (c) Let y ∈ N with |y − q| < δ. Then y ∈ W ∩ N = ψ(V), so y = ψ(v') with v' ∈ V, and |v' − v| < ρ by (a).
 (d) With a := v' − v, step 3 gives |y − q − Aa| ≤ η|v' − v| ≤ (2η/m)|y − q| ≤ ε|y − q|.
5. tangentSpace N q ⊆ A(ℝ^d).
 (a) L := A(ℝ^d) is a linear subspace of the finite-dimensional space ℝ^P, hence closed. Write dist(u, L) for the distance from u to L.
 (b) Let w ∈ tangentSpace N q, witnessed by γ : ℝ → ℝ^P. Here γ is C¹ on (−1, 1), γ((−1, 1)) ⊆ N, γ(0) = q and γ'(0) = w (HasDerivAt).
 (c) Let ε > 0 and let δ be as in (iii). γ is continuous at 0, so there is t₀ ∈ (0, 1) with |γ(t) − q| < δ for |t| < t₀.
 (d) For 0 < |t| < t₀ we have γ(t) ∈ N, so (iii) gives a_t with |γ(t) − q − Aa_t| ≤ ε|γ(t) − q|. Since L is a linear subspace, dist((γ(t) − q)/t, L) ≤ |(γ(t) − q)/t − A(a_t/t)| ≤ ε|γ(t) − q|/|t|.
 (e) As t → 0, (γ(t) − q)/t → w and |γ(t) − q|/|t| → |w|. The function u ↦ dist(u, L) is continuous, so dist(w, L) ≤ ε|w|.
 (f) Since ε > 0 is arbitrary, dist(w, L) = 0. Hence w ∈ L, because L is closed.
6. A(ℝ^d) ⊆ tangentSpace N q. Let a ∈ ℝ^d.
 (a) Case a = 0. The constant curve γ(t) := q is C^∞, maps into N, and has γ(0) = q and γ'(0) = 0 = A0.
 (b) Case a ≠ 0. Choose ρ₀ > 0 with closedBall(v, ρ₀) ⊆ V. Put c := ρ₀/|a| and h(t) := t/(1 + t²/c²). Then h is C^∞, h(0) = 0 and h'(0) = 1 (h'(t) = (1 − t²/c²)/(1 + t²/c²)²). Also |h(t)| ≤ c/2 for all t, because c² + t² ≥ 2c|t|.
 (c) Let γ(t) := ψ(v + h(t)a). For all t, |h(t)a| ≤ ρ₀/2, so v + h(t)a ∈ V. Hence γ maps (−1, 1) into ψ(V) ⊆ N, and γ(0) = ψ(v) = q.
 (d) γ is C¹ on (−1, 1). It is the composition of the C^∞ map t ↦ v + h(t)a, which takes values in the open set V, with ψ, which is C^r with r ≥ 1 on V.
 (e) By the chain rule, γ'(0) = Dψ(v)(h'(0)a) = Aa. So Aa ∈ tangentSpace N q.
7. Steps 5 and 6 give (i): tangentSpace N (ψ v) = Set.range (fderiv ℝ ψ v). Steps 2 and 4 give (ii) and (iii). (Remark: (ii) is also SimonGMT Chapter02/SubmanifoldTopology.lean, IsSimonLocalRepresentation.isEmbedding_chartMap. That module is not imported by the contract, and the argument above is self-contained.)

## Key steps

1. Injectivity of A = Dψ(v) gives m > 0 with |Aa| ≥ m|a|.
2. Properness and injectivity of ψ on V give continuity of ψ⁻¹ at q (sequential compactness).
3. Differentiability at v plus continuity of ψ⁻¹ give the secant estimate |y − q − Aa| ≤ ε|y − q| for y ∈ N near q.
4. Along a C¹ curve in N, the secant estimate puts γ'(0) in the closed subspace A(ℝ^d); conversely the curves t ↦ ψ(v + h(t)a) realize every Aa.

## Reference use

### local-project

Queries:
- `cat nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1/{parent-child-handoff.json,parent-supplied-plan.md,parent-supplied-natural-proof.md}`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical)`
- `python3 -I (list dag.json nodes: ids, lean_name, lean_statement, status)`
- `grep -rn dsmc dag.json problem.json GMT lake-packages-25730c7c/simongmt/Poincare (name-collision check: no match)`
- `grep -n '^theorem\|^def' simongmt Chapter04/MeanCurvature.lean Chapter04/FirstVariation.lean; sed -n 1,120p,300,520p MeanCurvature.lean; sed -n 40,430p,1190,1200p FirstVariation.lean; cat Chapter04/Basic.lean`
- `sed -n 1,280p simongmt Chapter03/Rectifiable.lean (HasApproximateTangentSpaceAt, unique, support_euclideanHausdorffMeasure_restrict_submodule)`
- `grep -rn 'abbrev Covector' simongmt Chapter06/*.lean (Covector = E [⋀^Fin n]→L[ℝ] ℝ)`
- `sed -n 20,146p simongmt Chapter02/Submanifold.lean, SubmanifoldTopology.lean (IsSimonLocalRepresentation.isEmbedding_chartMap)`
- `cat nodes/root-half-space-cone-lies-in-boundary-a1-tangent-projection-aemeasurable-a1/parent-supplied-natural-proof.md`
- `sed -n 150,215p and 215,450p book/chapter-04.txt; sed -n 1270,1360p book/chapter-02.txt`
- `grep -rln Binet mathlib/Mathlib (no Cauchy–Binet in LinearAlgebra); grep for measure_compl_support, ae_withDensity_iff, toOpenPartialHomeomorph, contDiffAt_ringInverse, ContinuousLinearMap.adjoint, measurable_fderiv, Measurable.lintegral_prod_right', aemeasurable_of_tendsto_metrizable_ae', integral_withDensity_eq_integral_smul, euclideanHausdorffMeasure_smul₀, Isometry.map_euclideanHausdorffMeasure, hasDerivAt_integral_of_dominated_loc_of_deriv_le, monotoneOn_of_deriv_nonneg, fderiv_clm_apply`
- `lake env lean /tmp/dsmc-decomp/Final.lean (seven exact child types + conditional assembly of dor_stationary_mean_curvature_monotonicity; #print axioms)`
- `lake env lean /tmp/dsmc-decomp/Use.lean (chart lemma applied to IsEmbeddedSubmanifold r and 2 chart data)`
- `lake env lean /tmp/dsmc-decomp/Assembly.lean (#synth MeasurableSpace/BorelSpace (Euclid 3 →L[ℝ] Euclid 3); inner ℝ on Euclid P is the PiLp inner product)`
- `lake env lean /tmp/dsmc-decomp/Imports.lean, Imports2.lean (#check of cited library lemmas under import GMT.Ch07.Submission)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-tangent-projection-aemeasurable-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/MeanCurvature.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/FirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Submanifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldTopology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/tmp/dsmc-decomp/Final.lean`
- `/tmp/dsmc-decomp/Use.lean`
- `/tmp/dsmc-decomp/Assembly.lean`
- `/tmp/dsmc-decomp/spec/statements.json`

Snapshot: project b4d606d, mathlib 25730c7c. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

Reusable facts found:
- SimonGMT Chapter03/Rectifiable.lean: HasApproximateTangentSpaceAt (finrank = n plus blow-up convergence of Bochner integrals), HasApproximateTangentSpaceAt.unique, and support_euclideanHausdorffMeasure_restrict_submodule. These are used by approx_tangent_in_tangent_space and tangent_projection_measurable.
- Mathlib: Measure.measure_compl_support and ae_withDensity_iff (parent assembly); HasStrictFDerivAt.toOpenPartialHomeomorph, OpenPartialHomeomorph.contDiffAt_symm, contDiffAt_ringInverse and ContinuousLinearMap.adjoint (tangent_projection_field); measurable_fderiv and fderiv_clm_apply (mean_curvature_formula); Measurable.lintegral_prod_right', aemeasurable_of_tendsto_metrizable_ae', euclideanHausdorffMeasure_smul₀ and Isometry.map_euclideanHausdorffMeasure (tangent_projection_measurable); integral_withDensity_eq_integral_smul (first_variation_integral); hasDerivAt_integral_of_dominated_loc_of_deriv_le and monotoneOn_of_deriv_nonneg (exp_monotonicity).
- The half-space branch's accepted measurability proof for U = ℝ^P was adapted to open U.

Not available here:
- No tubular-neighbourhood or nearest-point theorem exists in Mathlib or SimonGMT. A retraction is therefore built with the inverse function theorem.
- Mathlib has no Cauchy–Binet. The ξ-based measurability sketch is therefore replaced.
- SimonGMT's monotonicity (Chapter04/MeanCurvature.lean, exp_normalizedBallMass_monotoneOn) concerns its RectifiableVarifold, which needs a globally locally finite weight and closed balls, and it is not imported by the contract. It is therefore used only as a reference.
- SimonGMT Chapter02 IsSimonLocalRepresentation.isEmbedding_chartMap is not imported. It is mentioned as optional.

Lean checks:
- All seven child types elaborate after import GMT.Ch07.Submission in namespace GMT.Ch07 with the contract's opens.
- The instances are as intended: Borel MeasurableSpace and BorelSpace on Euclid P →L[ℝ] Euclid P, and inner ℝ is the Euclidean (PiLp) inner product.
- The chart lemma applies to chart data from both IsEmbeddedSubmanifold r and IsEmbeddedSubmanifold 2.
- The conditional assembly of dor_stationary_mean_curvature_monotonicity elaborates from the seven stubs plus the frozen type of dor_imrep_massOn_eq_measure_and_support, with axioms propext, Classical.choice, Quot.sound and the stub sorryAx.
