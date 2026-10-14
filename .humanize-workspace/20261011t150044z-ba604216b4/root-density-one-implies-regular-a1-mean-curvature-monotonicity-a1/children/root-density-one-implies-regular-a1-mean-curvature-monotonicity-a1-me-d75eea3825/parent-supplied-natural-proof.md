# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1`
- Child DAG node: `root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1.mean_curvature_formula-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof steps 4–5; Simon Ch. 4, 2.5–2.7 (chapter-04.txt lines 157–210) and Ch. 2, 5.9–5.10 (chapter-02.txt lines 1318–1360). There, div_M X = div_M X^T − X·H̄_N with H̄_N = Σ_i B_x(τ_i, τ_i), and stationarity in U ∩ N kills ∫ div_M X^T. Here X^T := Pt·X, and H is written directly with the derivative of Pt. On N, (DPt(x)τ)τ is the second fundamental form B_x(τ, τ), but that identification is not needed. Uses the sibling first_variation_integral.
Notation. E := ℝ^P, μ := R.measure, M := R.carrier, T_x := approxTangentPlane n M x and p_x its orthogonal projection. B_x := DPt(x) = fderiv ℝ Pt x ∈ L(E, L(E, E)); e_1, …, e_P is the standard orthonormal basis; div_M Z(x) := tangentialDivergence n M Z x = trace(p_x ∘ DZ(x)). If r ≤ 0 then ball(y₀, 2r) = ∅; in all cases ball(y₀, 2r) ⊆ ball(y₀, 3r).
1. Linear algebra.
 (a) finrank T_x ≤ n for every x. Indeed T_x is either a subspace Q with HasApproximateTangentSpaceAt n M x Q, which has finrank n, or ⊥.
 (b) For linear D : E → E and an orthonormal basis τ_1, …, τ_m of T_x, trace(p_x ∘ D) = Σ_{i≤m} ⟨τ_i, Dτ_i⟩. To see this, extend τ to an orthonormal basis τ_1, …, τ_P of E. Then trace(p_x∘D) = Σ_b ⟨τ_b, p_x Dτ_b⟩ = Σ_b ⟨p_xτ_b, Dτ_b⟩, and p_xτ_b = τ_b for b ≤ m and 0 for b > m.
 (c) For B ∈ L(E, L(E, E)) and τ as in (b), Σ_a (B(p_x e_a))e_a = Σ_i (Bτ_i)τ_i. To see this, insert p_x e_a = Σ_i ⟨τ_i, e_a⟩τ_i, use Σ_a ⟨τ_i, e_a⟩e_a = τ_i, and use linearity.
 (d) For x ∈ ball(y₀, 3r) and u ∈ E, the operator B_x u is self-adjoint. For fixed a, b, the function y ↦ ⟨Pt(y)a, b⟩ − ⟨a, Pt(y)b⟩ vanishes on the open set ball(y₀, 3r) by hypothesis. Pt is differentiable at x, being C¹ on an open set. By the chain rule, the derivative of this function at x in direction u is ⟨(B_x u)a, b⟩ − ⟨a, (B_x u)b⟩, and it is 0.
2. Definition of H. Put H(x) := Σ_{a=1}^P (B_x(p_x e_a))e_a for x ∈ ball(y₀, 2r), and H(x) := 0 otherwise.
 (a) Bound. For x ∈ ball(y₀, 2r), take an orthonormal basis τ_1, …, τ_m of T_x, with m ≤ n by 1(a). By 1(c), H(x) = Σ_i (B_xτ_i)τ_i, so ‖H(x)‖ ≤ Σ_i ‖B_x‖|τ_i|² = m‖B_x‖ ≤ nβ, using ‖B_x‖ ≤ β and β ≥ 0. For other x, ‖H(x)‖ = 0 ≤ nβ.
 (b) Measurability. x ↦ B_x is Borel measurable (measurable_fderiv), x ↦ p_x is μ-AEMeasurable (hypothesis), and (B, p) ↦ Σ_a (B(pe_a))e_a is continuous. Multiplying by the indicator of the open ball preserves measurability. So H is μ-AEMeasurable, hence μ-AEStronglyMeasurable.
3. Splitting. Let X be C¹ with compact support, and K := tsupport X ⊆ ball(y₀, 2r) ⊆ ball(y₀, 3r) ⊆ U. Put X^T(x) := Pt(x)(X(x)) for all x, and Y := X − X^T.
 (a) X^T is C¹. At x ∈ ball(y₀, 3r), Pt and X are C¹ near x, hence so is x ↦ Pt(x)(X(x)). At x ∉ ball(y₀, 3r) we have x ∉ K, so X vanishes on the open neighbourhood E ∖ K of x, and so does X^T, since Pt(y)0 = 0.
 (b) X^T vanishes off K, so tsupport X^T ⊆ K. Thus X^T has compact support contained in U, and the same holds for Y.
 (c) X^T(x) ∈ tangentSpace N x for every x ∈ N ∩ U. If x ∈ ball(y₀, 3r), this follows from the hypothesis that Pt(q)u ∈ tangentSpace N q. Otherwise X(x) = 0, so X^T(x) = 0, and 0 ∈ tangentSpace N x (constant curve at x ∈ N).
 (d) Hence R.IsStationaryAlong N gives R.firstVariation X^T = 0.
4. Integral form.
 (a) X, X^T and Y are C¹ with compact support in U, and p_x is AEMeasurable. So by first_variation_integral, div_M X, div_M X^T and div_M Y are μ-integrable, and R.firstVariation Z = ∫ div_M Z dμ for Z ∈ {X, X^T, Y}.
 (b) X = X^T + Y with both summands differentiable, so DX = DX^T + DY and div_M X = div_M X^T + div_M Y pointwise.
 (c) Hence R.firstVariation X = ∫ div_M X^T dμ + ∫ div_M Y dμ = R.firstVariation X^T + ∫ div_M Y dμ = ∫ div_M Y dμ.
5. Pointwise identity. By hypothesis, μ-a.e. x satisfies x ∈ N and (x ∈ ball(y₀, 3r) ⇒ T_x ⊆ tangentSpace N x). Fix such an x.
 (a) Case x ∉ K. X, X^T and Y vanish near x, so DY(x) = 0 and div_M Y(x) = 0 = −⟨X(x), H(x)⟩.
 (b) Case x ∈ K. Then x ∈ ball(y₀, 2r), x ∈ N ∩ ball(y₀, 3r), and T_x ⊆ tangentSpace N x. By the product rule (fderiv_clm_apply), DX^T(x)u = (B_x u)(X(x)) + Pt(x)(DX(x)u), so DY(x)u = DX(x)u − Pt(x)DX(x)u − (B_x u)X(x).
 (c) Let τ_1, …, τ_m be an orthonormal basis of T_x. Each τ_i ∈ tangentSpace N x, so the hypothesis gives Pt(x)τ_i = τ_i. By self-adjointness, ⟨τ_i, Pt(x)DX(x)τ_i⟩ = ⟨Pt(x)τ_i, DX(x)τ_i⟩ = ⟨τ_i, DX(x)τ_i⟩. By 1(d), ⟨τ_i, (B_xτ_i)X(x)⟩ = ⟨(B_xτ_i)τ_i, X(x)⟩.
 (d) By 1(b) and 1(c), div_M Y(x) = Σ_i ⟨τ_i, DY(x)τ_i⟩ = −Σ_i ⟨(B_xτ_i)τ_i, X(x)⟩ = −⟨H(x), X(x)⟩.
 (e) So div_M Y = −⟨X, H⟩ μ-a.e.
6. Conclusion. By steps 4–5 and integral_congr_ae, R.firstVariation X = ∫ div_M Y dμ = −∫ ⟨X(x), H(x)⟩ dμ, using that the inner product is symmetric. The H of step 2 does not depend on X, so together with step 2 this proves the claim.

## Key steps

1. H(x) := Σ_a (DPt(x)(p_x e_a))e_a = Σ_i (DPt(x)τ_i)τ_i on B_{2r}(y₀), and 0 elsewhere; |H| ≤ nβ and H is AEMeasurable.
2. X^T := Pt·X is C¹, tangent to N on N ∩ U, and compactly supported in U, so stationarity gives δV(X^T) = 0.
3. By first_variation_integral, δV(X) = ∫ div_M X^T dμ_R + ∫ div_M Y dμ_R = ∫ div_M Y dμ_R with Y = X − X^T.
4. div_M Y = −⟨X, H⟩ a.e., using Pt(x)τ_i = τ_i, self-adjointness of Pt(x), and self-adjointness of DPt(x)u.

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
