# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1`
- Child DAG node: `root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1.tangent_projection_measurable-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 4 (measurability of x ↦ P_{T_xM}); Simon Ch. 3, Definition 1.4 (chapter-03.txt lines 75–90); Ch. 6, 3.1 (chapter-06.txt lines 733–753: ξ orients T_xM "in an Hⁿ-measurable way").
The parent sketches this through the orientation: P_{T_xM} is a continuous function of the unit simple n-vector ξ(x). Writing that function explicitly needs Cauchy–Binet identities, for which the pinned Mathlib has no support. So we prove the statement directly from the blow-up definition of T_xM, using only the fields of R. The argument is the one accepted for U = ℝ^P in the half-space branch (node tangent_projection_aemeasurable). There, continuity of the blow-up integrals is used; here it is replaced by Tonelli measurability, so that U may be any open set.
Notation. M := R.carrier, θ := R.mult, Hⁿ := μHE[n], ν := Hⁿ⌞M (μHE[n].restrict M), μ := R.measure = ν.withDensity θ. T_x := approxTangentPlane n M x, p_x := its starProjection, η_{x,λ}(y) := λ⁻¹(y − x) (blowUpMap x λ), and e_1, …, e_P is the standard orthonormal basis.
0. Reduction to ν. μ = ν.withDensity θ ≪ ν (withDensity_absolutelyContinuous), so every ν-AEMeasurable function is μ-AEMeasurable (AEMeasurable.mono_ac). We show that x ↦ p_x is ν-AEMeasurable.
1. Case n = 0. If some Q satisfies HasApproximateTangentSpaceAt 0 M x Q, then T_x is such a Q (the chosen witness in the definition of approxTangentPlane). Its finrank is 0, so T_x = ⊥. Otherwise T_x = ⊥ by definition. So x ↦ p_x is constant, hence measurable. From now on assume n ≥ 1.
2. ν is σ-finite.
 (a) U is open, so U = ⋃_j K_j with K_j := {y : |y| ≤ j, dist(y, ℝ^P ∖ U) ≥ 1/(j+1)} compact and K_j ⊆ U. (If U = ℝ^P, take K_j := closedBall(0, j).)
 (b) θ ≥ 1 on M (R.mult_pos), so ν(K_j) = Hⁿ(M ∩ K_j) ≤ ∫_{M∩K_j} θ dHⁿ < ∞ (R.locallyIntegrable_mult).
 (c) ν(ℝ^P ∖ U) = Hⁿ(M ∖ U) = 0, because M ⊆ U (R.carrier_subset).
 (d) So ℝ^P is a countable union of sets of finite ν-measure. Hence ν is σ-finite, in particular s-finite. In Lean this instance must be supplied by hand from (a)–(c); it is needed for step 6.
3. Tangent planes a.e. By R.orients, for ν-a.e. x there is Q with HasApproximateTangentSpaceAt n M x Q. At such x, T_x is the chosen witness, so HasApproximateTangentSpaceAt n M x T_x holds and finrank T_x = n. Let G be the set of these x; then ν(ℝ^P ∖ G) = 0.
4. Test functions. Let χ(t) := max(1 − t, 0), and for u ∈ ℝ^P let f_u(y) := χ(|y|²)⟨u, y⟩². f_u is continuous and ≥ 0 and vanishes outside closedBall(0, 1), so f_u ∈ C_c(ℝ^P, ℝ).
5. Integrals over n-planes. Claim: for every subspace Q with finrank Q = n, ∫_Q f_u dHⁿ = c_n|p_Q u|², where c_n := ∫_{ℝ^n} χ(|z|²) z₁² dz ∈ (0, ∞) (Lebesgue measure).
 (a) Take an orthonormal basis τ₁, …, τ_n of Q, and the linear isometry ι : ℝ^n → ℝ^P, ι(z) = Σ_i z_i τ_i, whose range is Q. Then Hⁿ⌞Q is the push-forward of Hⁿ on ℝ^n under ι (Isometry.map_euclideanHausdorffMeasure), and Hⁿ on ℝ^n is Lebesgue measure (EuclideanSpace.euclideanHausdorffMeasure_eq_volume).
 (b) With a_i := ⟨u, τ_i⟩, f_u(ι(z)) = χ(|z|²)(Σ_i a_i z_i)². So ∫_Q f_u dHⁿ = Σ_{i,j} a_i a_j ∫ χ(|z|²) z_i z_j dz.
 (c) For i ≠ j, the reflection z_i ↦ −z_i preserves Lebesgue measure and |z| and changes the sign of z_i z_j, so that integral is 0. For i = j, the coordinate swap z_i ↔ z₁ shows that the integral equals c_n.
 (d) Hence ∫_Q f_u dHⁿ = c_n Σ_i a_i² = c_n|p_Q u|². Finally c_n < ∞, since the integrand is continuous with compact support, and c_n > 0, since it is continuous, ≥ 0, and positive at (1/2, 0, …, 0).
6. Blow-up integrals are measurable in x. Fix u and λ > 0, and put Φ(x) := ∫_{η_{x,λ}(M)} f_u dHⁿ, the integral appearing in HasApproximateTangentSpaceAt.
 (a) f_u ≥ 0 is continuous, so Φ(x) = (∫⁻_{η_{x,λ}(M)} f_u dHⁿ).toReal (integral_eq_lintegral_of_nonneg_ae). This holds whether or not f_u is integrable there.
 (b) η_{x,λ} is a translation followed by multiplication by λ⁻¹, hence a homeomorphism, so η_{x,λ}(M) is Borel. Also Hⁿ(η_{x,λ}(B)) = λ^{−n}Hⁿ(B) for every B (Isometry.euclideanHausdorffMeasure_image for the translation, Measure.euclideanHausdorffMeasure_smul₀ for the dilation).
 (c) For Borel B, Hⁿ(B ∩ η_{x,λ}(M)) = Hⁿ(η_{x,λ}(η_{x,λ}⁻¹(B) ∩ M)) = λ^{−n}ν(η_{x,λ}⁻¹(B)). That is, Hⁿ⌞η_{x,λ}(M) = λ^{−n}(η_{x,λ})_*ν. Therefore ∫⁻_{η_{x,λ}(M)} f_u dHⁿ = λ^{−n}∫⁻ f_u(λ⁻¹(y − x)) dν(y) (lintegral_map).
 (d) (x, y) ↦ f_u(λ⁻¹(y − x)) is continuous on ℝ^P × ℝ^P, hence measurable for the product σ-algebra (ℝ^P is second countable). Since ν is s-finite (step 2), x ↦ ∫⁻ f_u(λ⁻¹(y − x)) dν(y) is measurable (Measurable.lintegral_prod_right'). Hence Φ is Borel measurable.
7. Limits.
 (a) Let λ_k := 1/(k+1), and let Φ_{u,k} be the function of step 6 with λ = λ_k.
 (b) For x ∈ G, apply HasApproximateTangentSpaceAt n M x T_x to f_u, with λ_k → 0 through positive values. This gives Φ_{u,k}(x) → ∫_{T_x} f_u dHⁿ = c_n|p_x u|², by step 5 and finrank T_x = n.
 (c) ν-a.e. x lies in G, so x ↦ c_n|p_x u|² is a ν-a.e. limit of measurable functions. Hence it is ν-AEMeasurable (aemeasurable_of_tendsto_metrizable_ae'). Dividing by c_n > 0, x ↦ |p_x u|² is ν-AEMeasurable for every u ∈ ℝ^P.
8. Polarization. p_x is self-adjoint and idempotent, so ⟨p_x u, w⟩ = ⟨p_x u, p_x w⟩ = (|p_x(u + w)|² − |p_x(u − w)|²)/4. Hence x ↦ ⟨p_x u, w⟩ is ν-AEMeasurable for all u, w.
9. Assembly.
 (a) For every x, p_x = Σ_{a,b} ⟨p_x e_a, e_b⟩ L_{ab}, with the constant maps L_{ab} ∈ L(ℝ^P, ℝ^P), L_{ab}(v) := ⟨e_a, v⟩e_b. This holds because p_x v = Σ_b ⟨p_x v, e_b⟩e_b and v = Σ_a ⟨e_a, v⟩e_a.
 (b) A finite sum of ν-AEMeasurable real functions times constant vectors of the normed space L(ℝ^P, ℝ^P) (Borel σ-algebra) is ν-AEMeasurable. So x ↦ p_x = (approxTangentPlane n R.carrier x).starProjection is ν-AEMeasurable, hence R.measure-AEMeasurable by step 0.

## Key steps

1. μ_R ≪ ν = Hⁿ⌞M, and ν is σ-finite because U is open and θ ≥ 1 is locally integrable; the case n = 0 is trivial.
2. For f_u(y) = max(1 − |y|², 0)⟨u, y⟩², ∫_Q f_u dHⁿ = c_n|p_Q u|² for every n-plane Q, with c_n > 0.
3. x ↦ ∫_{η_{x,λ}(M)} f_u dHⁿ = λ^{−n}∫ f_u(λ⁻¹(y − x)) dν(y) is measurable (Tonelli); at a.e. x it tends to c_n|p_x u|² as λ = 1/(k+1) → 0.
4. Polarization and a basis expansion give AEMeasurable x ↦ p_x, first for ν and then for μ_R.

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
