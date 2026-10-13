# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1`
- Child DAG node: `root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1.exp_monotonicity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 6; Simon Ch. 4, 3.1–3.6 (chapter-04.txt lines 215–312) and 3.14–3.17 (lines 370–430). The first range gives radial vector fields γ(r)(x − ξ), the formula div_M = nγ + rγ'(1 − |∇^⊥r|²) and the I, J identity; the second treats bounded generalized mean curvature. We use Simon's sign convention δV(X) = −∫X·H and prove the stated form directly, with open balls and e^{κs}s^{−n}μ(B_s(z)) nondecreasing. Open balls arise because the cutoffs increase to the indicator of (−∞, 1). Uses the sibling first_variation_integral.
Notation. μ := R.measure, M := R.carrier, θ := R.mult, T_x := approxTangentPlane n M x with orthogonal projection p_x, and ϱ(x) := |x − z|.
0. Preliminaries.
 (a) κ ≥ 0, since 0 ≤ ‖H(z)‖ ≤ κ.
 (b) μ(closedBall(z, r)) < ∞. The set closedBall(z, r) is compact, closed and contained in U, so μ(closedBall(z, r)) = ∫⁻_{M∩closedBall(z, r)} θ dHⁿ < ∞ (R.locallyIntegrable_mult).
 (c) For μ-a.e. x, finrank T_x = n, and hence trace(p_x) = n. By R.orients, Hⁿ⌞M-a.e. x admits Q with HasApproximateTangentSpaceAt n M x Q; then T_x is such a Q (definition of approxTangentPlane), so finrank T_x = n. Moreover μ = (Hⁿ⌞M).withDensity θ ≪ Hⁿ⌞M.
 (d) If r ≤ 0, there are no σ, ρ with 0 < σ ≤ ρ ≤ r. So assume r > 0.
1. Cutoffs. Let g(t) := 0 for t ≤ 0, g(t) := 3t² − 2t³ for 0 ≤ t ≤ 1, and g(t) := 1 for t ≥ 1. Then g is C¹ (g' = 6t − 6t² on [0, 1] vanishes at 0 and 1), nondecreasing, and [0, 1]-valued. For ε ∈ (0, 1) let γ(t) := g((1 − t)/ε). Then γ is C¹, γ' ≤ 0, |γ'| ≤ 3/(2ε), 0 ≤ γ ≤ 1, γ(t) = 1 for t ≤ 1 − ε, and γ(t) = 0 for t ≥ 1. Any other C¹ nondecreasing g with g = 0 on (−∞, 0] and g = 1 on [1, ∞) works equally well, for example Mathlib's Real.smoothTransition; then the bound on |γ'| becomes sup|g'|/ε.
2. Radial fields. For s > 0 put φ_s(x) := γ(ϱ(x)/s) and X_s(x) := φ_s(x)(x − z).
 (a) φ_s and X_s are C¹: on ℝ^P ∖ {z}, ϱ is C^∞; on ball(z, (1 − ε)s), φ_s ≡ 1 and X_s(x) = x − z.
 (b) φ_s(x) ≠ 0 implies ϱ(x) < s. So tsupport X_s ⊆ closedBall(z, s), which is compact. For 0 < s < r, tsupport X_s ⊆ ball(z, r) ⊆ U.
 (c) Divergence. For x with finrank T_x = n, div_M X_s(x) = nφ_s(x) + ψ_s(x)q(x). Here ψ_s(x) := (ϱ(x)/s)γ'(ϱ(x)/s), q(x) := |p_x(x − z)|²/ϱ(x)² for x ≠ z, and q(z) := 0.
  - For x ≠ z: DX_s(x)v = φ_s(x)v + (γ'(ϱ/s)/(sϱ))⟨x − z, v⟩(x − z). Since trace(p_x) = n and the trace of p_x ∘ (v ↦ ⟨a, v⟩a) is ⟨a, p_x a⟩ = |p_x a|², we get div_M X_s(x) = nφ_s(x) + (γ'(ϱ/s)/(sϱ))|p_x(x − z)|² = nφ_s(x) + ψ_s(x)q(x).
  - At x = z: DX_s(z) = I, so div_M X_s(z) = n = nφ_s(z) + ψ_s(z)q(z), because φ_s(z) = 1 and ψ_s(z) = 0.
 (d) ψ_s is continuous, ψ_s ≤ 0, and ψ_s(x) = 0 unless (1 − ε)s < ϱ(x) < s. Also 0 ≤ q ≤ 1, since |p_x a| ≤ |a|, and q is μ-AEMeasurable by the AEMeasurable hypothesis on p_x.
3. First variation inequality. Let 0 < s < r and I(s) := ∫ φ_s dμ.
 (a) By first_variation_integral, R.firstVariation X_s = ∫ div_M X_s dμ. By 2(c) and 0(c), the integrand equals nφ_s + ψ_s q μ-a.e.
 (b) φ_s, ψ_s q and φ_s⟨x − z, H⟩ are bounded and AEStronglyMeasurable, and they vanish off closedBall(z, s), which has finite measure. So they are integrable.
 (c) The hypothesis applied to X_s gives nI(s) + ∫ψ_s q dμ = −∫ φ_s⟨x − z, H⟩ dμ.
 (d) ψ_s ≤ 0 and q ≤ 1 give ψ_s q ≥ ψ_s. On {φ_s ≠ 0}, |⟨x − z, H(x)⟩| ≤ ϱ(x)κ ≤ sκ. Hence
  (★) nI(s) + ∫ψ_s dμ ≤ κ s I(s).
4. Differentiability of I.
 (a) For each x, s ↦ φ_s(x) is differentiable on (0, ∞) with derivative −(ϱ(x)/s²)γ'(ϱ(x)/s) = −ψ_s(x)/s.
 (b) For s in a compact interval [a, b] ⊆ (0, r), this derivative is 0 unless ϱ(x) < s ≤ b, and it is bounded by (b/a²)·sup|γ'|. The dominating function (b/a²)·sup|γ'|·1_{closedBall(z, b)} is μ-integrable by 0(b).
 (c) By differentiation under the integral sign (hasDerivAt_integral_of_dominated_loc_of_deriv_le), I is differentiable on (0, r) with sI'(s) = −∫ψ_s dμ.
 (d) I is continuous on (0, r] by dominated convergence: s ↦ φ_s(x) is continuous, and |φ_s| ≤ 1_{closedBall(z, r)} for s ≤ r.
5. Monotonicity.
 (a) Let F(s) := e^{κs}s^{−n}I(s) for s ∈ (0, r]. By (★) and step 4, nI(s) − sI'(s) ≤ κsI(s) on (0, r). So F'(s) = e^{κs}s^{−n−1}(κsI(s) + sI'(s) − nI(s)) ≥ 0 there.
 (b) F is continuous on (0, r]. By the mean value theorem (monotoneOn_of_deriv_nonneg on the convex set (0, r], whose interior is (0, r)), F is nondecreasing on (0, r]. So for 0 < σ ≤ ρ ≤ r:
  (★★) e^{κσ}σ^{−n}∫γ(ϱ/σ) dμ ≤ e^{κρ}ρ^{−n}∫γ(ϱ/ρ) dμ.
6. Removing the cutoff.
 (a) Apply (★★) with ε = ε_j := 1/(j + 2), writing γ_j for the corresponding cutoff.
 (b) For every t: if t ≥ 1 then γ_j(t) = 0; if t < 1 then (1 − t)/ε_j ≥ 1 for large j, so γ_j(t) = 1. Hence γ_j(ϱ(x)/s) → 1_{ball(z, s)}(x) for every x and every s > 0. Also |γ_j(ϱ/s)| ≤ 1_{closedBall(z, r)} for s ≤ r.
 (c) By dominated convergence, ∫γ_j(ϱ/s) dμ → μ(ball(z, s)) for s ∈ {σ, ρ}.
 (d) Passing to the limit in (★★) gives e^{κσ}σ^{−n}μ(ball(z, σ)) ≤ e^{κρ}ρ^{−n}μ(ball(z, ρ)) as real numbers; both measures are finite by 0(b).
7. Extended reals. For s ∈ {σ, ρ}, μ(ball(z, s)) < ∞ and e^{κs}/s^n ≥ 0, so ENNReal.ofReal(e^{κs}/s^n)·μ(ball(z, s)) = ENNReal.ofReal(e^{κs}s^{−n}·μ(ball(z, s)).toReal). ENNReal.ofReal is monotone, so step 6 gives the claim.

## Key steps

1. C¹ radial fields X_s = γ(|x − z|/s)(x − z), with cutoffs γ = 1 on (−∞, 1 − ε] and γ = 0 on [1, ∞), satisfy div_M X_s = nφ_s + ψ_s q μ_R-a.e.
2. The first variation hypothesis, together with q ≤ 1, ψ_s ≤ 0 and |⟨x − z, H⟩| ≤ κs, gives nI − sI' ≤ κsI.
3. (e^{κs}s^{−n}I(s))' ≥ 0 on (0, r), and continuity on (0, r] makes it nondecreasing on (0, r].
4. As ε ↓ 0, I(s) → μ_R(B_s(z)) by dominated convergence; then transfer the inequality to [0, ∞].

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
