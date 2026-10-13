# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1`
- Child DAG node: `root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1.tangent_projection_field-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 1; Simon Ch. 4, 2.5–2.7 (chapter-04.txt lines 157–210) and Ch. 2, 5.9 (chapter-02.txt lines 1318–1345: X = X^T + X^⊥ with X^T tangent to N).
The parent builds Π = P∘π from the C¹ nearest-point projection π (tubular neighbourhood theorem: R. L. Foote, Proc. AMS 92 (1984) 153–155; G. Leobacher, A. Steinicke, Ann. Global Anal. Geom. 60 (2021) 559–587). The later steps (parent steps 4–5, child mean_curvature_formula) use only the properties in the statement. These hold for P∘π̃ with any C¹ retraction π̃ of a neighbourhood of y₀ onto N. We construct such a retraction from a chart by the inverse function theorem, using that N is locally a graph over T_{y₀}N. This avoids the tubular-neighbourhood theorem, which is not in Mathlib or SimonGMT. Uses the sibling chart_tangent_space.
Notation. E := ℝ^P. For a linear map B between Euclidean spaces, B* is its adjoint. Spaces of linear maps carry the operator norm.
1. Chart.
 (a) IsEmbeddedSubmanifold 2 d N at y₀ ∈ N gives: open V ⊆ ℝ^d; open W ⊆ E with y₀ ∈ W; and ψ : ℝ^d → E which is C² on V and injective on V, with ψ(V) = W ∩ N, V ∩ ψ⁻¹(K) compact for every compact K ⊆ W, and Dψ(z) injective for all z ∈ V.
 (b) As y₀ ∈ W ∩ N = ψ(V), y₀ = ψ(v₀) with v₀ ∈ V. For z ∈ V put A_z := Dψ(z) ∈ L(ℝ^d, E). V is open and ψ is C² on V, so z ↦ A_z is C¹ on V (ContDiffOn.fderiv_of_isOpen).
 (c) chart_tangent_space (with r = 2 ≥ 1) applies to this chart. For every z ∈ V, tangentSpace N (ψ(z)) = A_z(ℝ^d). Moreover, for every ε > 0 there is δ > 0 such that z ∈ V and |ψ(z) − y₀| < δ imply |z − v₀| < ε.
2. Projections onto ranges. Let B ∈ L(ℝ^d, E) be injective. Then B*B ∈ L(ℝ^d, ℝ^d) satisfies ⟨B*Ba, a⟩ = |Ba|² > 0 for a ≠ 0. So B*B is injective, hence invertible. Put G(B) := B(B*B)⁻¹B* ∈ L(E, E).
 (a) G(B)* = B((B*B)⁻¹)*B* = G(B), since B*B and hence (B*B)⁻¹ are self-adjoint. So ⟨G(B)u, w⟩ = ⟨u, G(B)w⟩.
 (b) G(B)(Ba) = B(B*B)⁻¹(B*B)a = Ba, so G(B) is the identity on B(ℝ^d).
 (c) G(B)u = B((B*B)⁻¹B*u) ∈ B(ℝ^d) for every u.
 (d) Let 𝒰 := {B : B*B is invertible}. It is open in L(ℝ^d, E): it is the preimage of the open set of units of the complete normed algebra L(ℝ^d, ℝ^d) under the continuous map B ↦ B*B. It contains every injective B.
 (e) On 𝒰, B ↦ G(B) is C^∞. B ↦ B* is a continuous ℝ-linear map: ContinuousLinearMap.adjoint is a star-semilinear isometry, and over ℝ, starRingEnd ℝ = id. Composition of continuous linear maps is a continuous bilinear operation, and inversion is C^∞ on the units (contDiffAt_ringInverse).
 (f) Hence g(z) := G(A_z) defines a C¹ map g : V → L(E, E). For each z ∈ V, g(z) is self-adjoint, maps E into A_z(ℝ^d), and fixes A_z(ℝ^d) pointwise.
3. N as a graph over the tangent plane at y₀.
 (a) Let Λ := A_{v₀}(ℝ^d). It is a linear subspace of E of dimension d, because A_{v₀} is injective. Let p ∈ L(E, Λ) be the orthogonal projection onto Λ, and put f := p∘ψ : ℝ^d → Λ.
 (b) f is C² on V and Df(z) = p∘A_z. Df(v₀) is injective, since p(A_{v₀}a) = A_{v₀}a for A_{v₀}a ∈ Λ. It maps between spaces of equal dimension d, so it is a linear isomorphism ℝ^d → Λ.
 (c) z ↦ Df(z) is continuous on V and the isomorphisms form an open set. So there is an open O₀ ⊆ V with v₀ ∈ O₀ on which every Df(z) is an isomorphism.
 (d) By the inverse function theorem (HasStrictFDerivAt.toOpenPartialHomeomorph, applied at v₀, where f is C² near v₀ and Df(v₀) is an isomorphism), there is a partial homeomorphism e with open source S ∋ v₀ and open target, such that e = f on S. Put O₁ := S ∩ O₀, which is open and contains v₀. Put O₂ := e(O₁) = f(O₁); it is open in Λ, because e is a homeomorphism of S onto its open target, and it contains f(v₀). Then f maps O₁ bijectively onto O₂ with inverse λ := e⁻¹ on O₂. λ is C¹ at every point f(z) ∈ O₂ (OpenPartialHomeomorph.contDiffAt_symm), because f is C² near z ∈ O₁ ⊆ V and Df(z) is an isomorphism since z ∈ O₀. (The source of the partial homeomorphism produced by Mathlib need not lie in O₀; this is why we intersect with O₀.)
4. Retraction parameter.
 (a) O₃ := p⁻¹(O₂) is open in E and contains y₀, since p(y₀) = p(ψ(v₀)) = f(v₀) ∈ O₂.
 (b) Define σ(y) := λ(p(y)) for y ∈ O₃. σ is C¹ on O₃, with values in O₁ ⊆ V.
 (c) For z ∈ O₁, p(ψ(z)) = f(z) ∈ O₂. Hence ψ(z) ∈ O₃ and σ(ψ(z)) = λ(f(z)) = z.
5. Definition of Pt. Pt(y) := g(σ(y)) = G(A_{σ(y)}) for y ∈ O₃, and Pt(y) := 0 for y ∉ O₃. On the open set O₃, Pt is C¹ as a composition of C¹ maps, and Pt(y) is self-adjoint by step 2(a).
6. Choice of r.
 (a) Choose ε₁ > 0 with ball(v₀, ε₁) ⊆ O₁. By step 1(c), choose δ₁ > 0 such that z ∈ V and |ψ(z) − y₀| < δ₁ imply |z − v₀| < ε₁.
 (b) U, W and O₃ are open and contain y₀. Choose r > 0 with 3r ≤ δ₁ and closedBall(y₀, 3r) ⊆ U ∩ W ∩ O₃.
 (c) Then closedBall(y₀, 3r) ⊆ U and ball(y₀, 3r) ⊆ O₃. So Pt is C¹ on ball(y₀, 3r), and ⟨Pt(y)u, w⟩ = ⟨u, Pt(y)w⟩ for y ∈ ball(y₀, 3r) and all u, w.
7. The bound β.
 (a) Pt is C¹ on the open set ball(y₀, 3r), so y ↦ DPt(y) = fderiv ℝ Pt y is continuous there (ContDiffOn.continuousOn_fderiv_of_isOpen).
 (b) The compact set closedBall(y₀, 2r) lies in ball(y₀, 3r). So there is C with ‖DPt(y)‖ ≤ C on it (IsCompact.exists_bound_of_continuousOn).
 (c) Put β := max(C, 0). Then β ≥ 0 and ‖DPt(y)‖ ≤ β for every y ∈ ball(y₀, 2r).
8. Tangency on N. Let q ∈ N ∩ ball(y₀, 3r).
 (a) q ∈ W ∩ N = ψ(V), so q = ψ(z) with z ∈ V. Since |ψ(z) − y₀| < 3r ≤ δ₁, we get |z − v₀| < ε₁, so z ∈ O₁.
 (b) By step 4(c), σ(q) = z and Pt(q) = G(A_z). By step 1(c), tangentSpace N q = A_z(ℝ^d).
 (c) By step 2(c), Pt(q)u ∈ A_z(ℝ^d) = tangentSpace N q for every u ∈ E. By step 2(b), Pt(q)u = u for every u ∈ A_z(ℝ^d) = tangentSpace N q.
9. Steps 6–8 give r > 0, β ≥ 0 and Pt with all the required properties.

## Key steps

1. Take a C² chart ψ at y₀ = ψ(v₀). By chart_tangent_space, T_{ψ(z)}N = Dψ(z)(ℝ^d) and ψ⁻¹ is continuous at y₀.
2. For injective B, G(B) = B(B*B)⁻¹B* is a C^∞ self-adjoint projection onto range B, so z ↦ G(Dψ(z)) is C¹ on V.
3. The inverse function theorem for p_Λ∘ψ (Λ = T_{y₀}N), restricted to the open set where Df is invertible, gives a C¹ map σ = λ∘p_Λ near y₀ with σ(ψ(z)) = z.
4. Pt := G(Dψ(σ(·))) is C¹ and self-adjoint near y₀ and is the projection onto T_qN on N. β bounds ‖DPt‖ on the compact closedBall(y₀, 2r).

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
