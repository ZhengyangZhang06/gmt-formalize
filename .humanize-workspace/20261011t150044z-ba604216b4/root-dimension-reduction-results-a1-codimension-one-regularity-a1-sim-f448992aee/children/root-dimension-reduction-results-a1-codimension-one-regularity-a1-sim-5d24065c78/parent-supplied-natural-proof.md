# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.area_comparison-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.area_comparison-a1.submanifold_approx_tangent-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Simon Ch. 3, proof of 1.6 "⇒" (chapter-03.txt lines 113–126: "since x ∈ N_j and N_j is a C¹ submanifold, lim_{λ↓0} ∫_{η_{x,λ}(N_j)} f dH^n = ∫_{T_xN_j} f dH^n", stated there without proof), Definition 1.4 (lines 77–84); Simon Ch. 2, 3.1–3.3 (area formula, chapter-02.txt lines 743–779) and 4.1–4.3 (local representations). It supplies the approximate tangent planes needed in parent step 4a (integer multiplicity of the pieces carrying the competitor). Uses the sibling chart_tangent_space (Submission.chart_tangentSpace_eq_range_fderiv).
Lean note. The proof may add to Submission.lean the imports Poincare.SimonGMT.Chapter03.SubmanifoldCover (measurableSet_of_isSimonSubmanifold, countablyRectifiable_of_isSimonSubmanifold), Poincare.SimonGMT.Chapter02.AreaFormula and Chapter02.AreaApproximation (injective_area_formula_of_injective_derivative, continuous_normDet) and Poincare.SimonGMT.Chapter02.SubmanifoldTopology (IsSimonLocalRepresentation.isEmbedding_chartMap), as accepted branches already add SimonGMT imports; the frozen statement uses none of them. SimonGMT's IsSimonSubmanifold (E := Euclid m) 1 N follows from IsEmbeddedSubmanifold 1 m N by reordering the chart conditions (the smoothness exponent (1 : ℕ) casts to (1 : ℕ∞), and the properness condition has its arguments permuted); this node's own Lean proof performs exactly this conversion for M.
Notation. |·| Euclidean norm, ‖·‖ operator norm, B_ρ(z) open ball, B̄_ρ(z) closed ball, L^m Lebesgue measure on ℝ^m (= μHE[m] on Euclid m, Mathlib EuclideanSpace.euclideanHausdorffMeasure_eq_volume). For a linear map L : ℝ^m → ℝ^P, J(L) := normDet(L) = (det(LᵀL))^{1/2} (Mathlib LinearMap.normDet; Simon 3.3); L ↦ J(L) is continuous (SimonGMT Chapter02 continuous_normDet). η_{x,r} = SimonGMT blowUpMap x r.
Area formula (Simon 3.2; SimonGMT Chapter02 injective_area_formula_of_injective_derivative): if D ⊆ ℝ^m is open, F : ℝ^m → ℝ^P is C¹ on D, injective on D, with DF(u) injective for u ∈ D, then H^m(F(A)) = ∫_A J(DF(u)) du for every Borel A ⊆ D. Since F(D ∩ F^{-1}(E)) = F(D) ∩ E, this says that the Borel measures E ↦ H^m(F(G) ∩ E) and E ↦ ∫_{G ∩ F^{-1}(E)} J(DF) du agree for every Borel G ⊆ D, i.e. H^m⌞F(G) is the image of J(DF)·L^m⌞G under F (in Lean, Measure.map F (…) with the a.e.-measurability of F on G supplied by ContinuousOn.aemeasurable, since Measure.map of a non-a.e.-measurable map is 0; F(A) is Borel for Borel A ⊆ D by MeasurableSet.image_of_continuousOn_injOn); hence (★) ∫_{F(G)} g dH^m = ∫_G g(F(u)) J(DF(u)) du for every bounded Borel g : ℝ^P → ℝ when the right side has an integrable bound (apply the measure identity to g⁺ and g⁻).

Proof.
1. (Chart; dimension of Q.) By IsEmbeddedSubmanifold 1 m N at x there are open V ⊆ ℝ^m, W₀ ⊆ ℝ^P with x ∈ W₀ and ψ : ℝ^m → ℝ^P, C¹ on V, injective on V, with ψ(V) = W₀ ∩ N, V ∩ ψ^{-1}(K) compact for every compact K ⊆ W₀, and Dψ(v) injective for v ∈ V. Choose v₀ ∈ V with ψ(v₀) = x and put A := Dψ(v₀). By chart_tangent_space, T_xN = range A; hence Q = range A as subspaces (equal underlying sets). A is injective, so dim Q = m: the first conjunct.
2. (Uniform bounds near v₀.) As m ≥ 1 and A is injective, c₀ := min_{|u|=1}|Au| > 0 (the unit sphere of ℝ^m is compact and nonempty), and |Au| ≥ c₀|u| for all u. By continuity of Dψ at v₀ (ψ is C¹ on the open set V) choose ρ₀ > 0 with B̄_{ρ₀}(v₀) ⊆ V and ‖Dψ(v) − A‖ ≤ c₀/2 for v ∈ B̄_{ρ₀}(v₀). The mean value inequality for v ↦ ψ(v) − Av on the convex set B̄_{ρ₀}(v₀) gives |ψ(v) − ψ(v′) − A(v − v′)| ≤ (c₀/2)|v − v′|, hence
 (2.1) |ψ(v) − ψ(v′)| ≥ (c₀/2)|v − v′| for v, v′ ∈ B̄_{ρ₀}(v₀).
 Moreover v ↦ J(Dψ(v)) is continuous on the compact set B̄_{ρ₀}(v₀), so C_J := max_{B̄_{ρ₀}(v₀)} J(Dψ) < ∞.
3. (Localization.) Choose ε > 0 with B̄_ε(x) ⊆ W ∩ W₀. The set C₁ := (V ∩ ψ^{-1}(B̄_ε(x))) ∖ B_{ρ₀}(v₀) is compact (a closed subset of the compact set V ∩ ψ^{-1}(B̄_ε(x)), properness), so ψ(C₁) is compact (ψ is continuous on V ⊇ C₁). x ∉ ψ(C₁), since ψ(v) = x = ψ(v₀) with v ∈ V forces v = v₀ ∈ B_{ρ₀}(v₀). Let δ := min(ε, dist(x, ψ(C₁))) > 0 (δ := ε if C₁ = ∅). Then
 (3.1) N ∩ B_δ(x) ⊆ ψ(B_{ρ₀}(v₀)) and N ∩ B_δ(x) ⊆ N ∩ W.
 Indeed let y ∈ N with |y − x| < δ ≤ ε; then y ∈ W ∩ W₀ ∩ N, so y = ψ(v) with v ∈ V and ψ(v) ∈ B̄_ε(x); if v ∉ B_{ρ₀}(v₀) then v ∈ C₁ and |y − x| ≥ dist(x, ψ(C₁)) ≥ δ, a contradiction.
4. (Reduction to the chart.) Fix f ∈ C_c(ℝ^P) and R > 0 with f = 0 outside B_R(0). Let 0 < r < δ/R. Put G_r := B_{ρ₀/r}(0) ⊆ ℝ^m (so v₀ + ru ∈ B_{ρ₀}(v₀) for u ∈ G_r), ψ_r(u) := r^{-1}(ψ(v₀ + ru) − x), and G′_r := {u ∈ G_r : |ψ_r(u)| < R}, an open set (ψ_r is continuous on the open set G_r). Then
 (4.1) η_{x,r}(N ∩ W) ∩ B_R(0) = ψ_r(G′_r).
 ⊇: for u ∈ G′_r, y := ψ(v₀ + ru) ∈ ψ(V) ⊆ N, and |y − x| = r|ψ_r(u)| < rR < δ ≤ ε, so y ∈ W; thus ψ_r(u) = η_{x,r}(y) ∈ η_{x,r}(N ∩ W) ∩ B_R(0). ⊆: if y ∈ N ∩ W and |η_{x,r}(y)| < R, then |y − x| < rR < δ, so by (3.1) y = ψ(v) with v ∈ B_{ρ₀}(v₀); u := (v − v₀)/r ∈ G_r and ψ_r(u) = η_{x,r}(y), so u ∈ G′_r.
 N is Borel (SimonGMT measurableSet_of_isSimonSubmanifold, after unfolding the contract's chart conditions into IsSimonSubmanifold), W is open and η_{x,r} is a homeomorphism, so η_{x,r}(N ∩ W) is Borel. Since f vanishes outside B_R(0), Mathlib setIntegral_eq_of_subset_of_forall_sdiff_eq_zero and (4.1) give
 (4.2) ∫_{η_{x,r}(N∩W)} f dH^m = ∫_{ψ_r(G′_r)} f dH^m.
5. (Area formula in the chart.) ψ_r is C¹ on the open set G_r, injective there (ψ is injective on V), and Dψ_r(u) = Dψ(v₀ + ru) (chain rule) is injective. By (2.1), for u ∈ G′_r: R > |ψ_r(u)| = r^{-1}|ψ(v₀ + ru) − ψ(v₀)| ≥ (c₀/2)|u|, so G′_r ⊆ B_{2R/c₀}(0), and J(Dψ_r(u)) ≤ C_J. Hence (★) applies to F = ψ_r, G = G′_r and g = f, and since f(ψ_r(u)) = 0 for u ∈ G_r ∖ G′_r:
 (5.1) ∫_{ψ_r(G′_r)} f dH^m = ∫_{G′_r} f(ψ_r(u)) J(Dψ(v₀ + ru)) du = ∫_{ℝ^m} h_r(u) du, h_r(u) := 1_{G_r}(u) f(ψ_r(u)) J(Dψ(v₀ + ru)).
6. (Domination.) If h_r(u) ≠ 0 then u ∈ G′_r, so |u| < 2R/c₀ (step 5). Hence |h_r(u)| ≤ H(u) := sup|f|·C_J·1_{B_{2R/c₀}(0)}(u) for all u and all r ∈ (0, δ/R); H is integrable and independent of r. Each h_r is measurable (indicator of the open set G_r times a function continuous on G_r).
7. (Pointwise limit.) Fix u ∈ ℝ^m. For r < ρ₀/(|u| + 1) we have u ∈ G_r. As r ↓ 0: ψ_r(u) = r^{-1}(ψ(v₀ + ru) − ψ(v₀)) → Au (differentiability of ψ at v₀), so f(ψ_r(u)) → f(Au) by continuity of f; and Dψ(v₀ + ru) → A (continuity of Dψ at v₀), so J(Dψ(v₀ + ru)) → J(A) by continuity of J. Hence h_r(u) → J(A) f(Au).
8. (Dominated convergence.) The filter r ↓ 0 (𝓝[>] 0) is countably generated; by steps 6–7 and the dominated convergence theorem (Mathlib tendsto_integral_filter_of_dominated_convergence), ∫ h_r du → J(A)∫_{ℝ^m} f(Au) du. By (4.2) and (5.1), lim_{r↓0} ∫_{η_{x,r}(N∩W)} f dH^m = J(A)∫_{ℝ^m} f(Au) du.
9. (The plane.) For the injective linear map A, H^m(A(S)) = J(A)·L^m(S) for every S ⊆ ℝ^m (Simon 3.1; Mathlib LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume). As A is injective, A(A^{-1}(E)) = range A ∩ E, so H^m⌞range A is the image of J(A)·L^m under A, and ∫_{range A} f dH^m = J(A)∫_{ℝ^m} f(Au) du (f is continuous with compact support, so all integrals are finite). Since range A = Q (step 1), step 8 gives ∫_{η_{x,r}(N∩W)} f dH^m → ∫_Q f dH^m as r ↓ 0.
10. (Conclusion.) Steps 1 and 9 (f ∈ C_c(ℝ^P) arbitrary) are the two conjuncts of HasApproximateTangentSpaceAt m (N ∩ W) x Q. ∎

## Key steps

1. Chart (V, W₀, ψ) at x = ψ(v₀); chart_tangent_space gives Q = range Dψ(v₀) = range A, so dim Q = m.
2. Near v₀: |ψ(v) − ψ(v′)| ≥ (c₀/2)|v − v′| with c₀ = min_{|u|=1}|Au| > 0, and J(Dψ) ≤ C_J.
3. Properness and injectivity give δ > 0 with N ∩ B_δ(x) ⊆ ψ(B_{ρ₀}(v₀)) ∩ W.
4. For f supported in B_R(0) and r < δ/R, ∫_{η_{x,r}(N∩W)} f = ∫ 1_{G_r}(u) f(ψ_r(u)) J(Dψ(v₀ + ru)) du with ψ_r(u) = r^{-1}(ψ(v₀ + ru) − x) (area formula).
5. Dominated by sup|f|·C_J·1_{B_{2R/c₀}(0)}; pointwise limit J(A) f(Au); dominated convergence.
6. Linear area formula: J(A)∫ f(Au) du = ∫_{range A} f dH^m = ∫_Q f dH^m.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; sha256sum local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `sed -n 1,457p GMT/Ch07/Contract.lean (IMRep, IsIntegerMultiplicity, Sub instance, SameBoundary, BoundaryVanishes, CompactlyContained, IsMinimizingIn, IsEmbeddedSubmanifold, tangentSpace, IsOrientation, IsUnitOrientationOf)`
- `grep -n '^def \|^theorem \|^structure \|^abbrev ' SimonGMT/Chapter06/{Currents,Forms,Mass,CurrentLocalEquality,AffineCurrentPushforward}.lean`
- `grep -n '^def \|^theorem ' SimonGMT/Chapter03/{Rectifiable,SubmanifoldCover}.lean SimonGMT/Chapter02/{Submanifold,AreaFormula,SubmanifoldTopology,AreaSubmanifoldExample}.lean; grep -n normDet SimonGMT/Chapter02/{Area,AreaApproximation}.lean`
- `grep -rn 'HasApproximateTangentSpaceAt' SimonGMT (existence for C¹ submanifolds: no match)`
- `grep -n 'theorem exists_open_between_and_isCompact_closure|setIntegral_eq_of_subset_of_forall_sdiff_eq_zero|theorem measure_union|le_of_add_le_add_right|theorem fderiv_id|continuous_compContinuousLinearMapCLM|normDet_comp|normDet_sq_eq_det_gram|euclideanHausdorffMeasure_image_eq_normDet_mul_volume|Continuous.measurableEmbedding|MeasurableSet.image_of_continuousOn_injOn' in Mathlib`
- `python3 scans of dag.json (902 nodes): lean names/titles matching push|diffeo|pullback|area|approxTangent|IMRep|IsIntegerMultiplicity; statuses and frozen types of the 7 reused names and of imrep_c1_diffeo_pushforward_im (speculative-ready), dpf_area_formula_bilipschitz_rectifiable, dpf_imrep_bilipschitz_image_rep (speculative-ready)`
- `git show <candidate>:GMT/Ch07/Submission.lean for 3de784c0d8f0, 74a1c6be7019, a95facf7331f, b711b515f5a8, 863f6d9cf603, 9c8432cb0101, d626082a69a0 (declaration present, type byte-identical, imports)`
- `git grep -l codim1_ac_ over all 4046 refs -- GMT/Ch07/Submission.lean; grep -c codim1_ac_ dag.json GMT SimonGMT (no match)`
- `runtime.py of flow gmt-claude-b888e19cffb1: _existing_lean_name_problem, _accepted_checkpoint, _overlay_accepted_children, _wait_for_accepted_dependencies`
- `lean -DautoImplicit=false /tmp/area-split/check/Types.lean; lean -DautoImplicit=false /tmp/area-split/check/Assembly.lean; lean -DautoImplicit=false /tmp/area-split/check/AssemblyAx.lean`
- `book: chapter-02.txt 743-1000 (3.1-3.5 area formula, 4.1-4.14 submanifolds and 4.11-4.13 area formula on M); chapter-03.txt 60-145 (1.3-1.6 approximate tangent spaces)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Separation/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Submanifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaFormula.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-f448992aee/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-7577af74dd/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-pushforwa-db3aef81cd/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-pushforwa-b3d596d026/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-pushforwa-72cd9bd2a7/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-integer-multiplicity-sub-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-orientati-f9454fcfd5/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1-unit-or-24edf309fb/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-chart-tangent-space-a1/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/area-split/check/Types.lean`
- `/tmp/area-split/check/Assembly.lean`
- `/tmp/area-split/check/AssemblyAx.lean`

Pins match.
- The manifest records project b4d606db and Mathlib 25730c7c, equal to workspace HEAD and .lake/packages/mathlib.
- The snapshot Contract.lean, the workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).
- The six Mathlib files cited are byte-identical between the snapshot and the workspace.
Library.
- SimonGMT Chapter06 has GeometricCurrentOn, massOn (sSup over massAdmissibleOn), support = U ∖ zeroRegion and boundary, but only an affine push-forward; a nonlinear push-forward must come from accepted DAG nodes.
- SimonGMT Chapter03 defines CountablyRectifiable and HasApproximateTangentSpaceAt (blowUpMap, C_c test functions, 𝓝[>] 0). It has no existence theorem for approximate tangent spaces of C¹ submanifolds: grep finds only flat planes and uniqueness. Hence the new child submanifold_approx_tangent.
- SimonGMT SubmanifoldCover gives measurableSet_of_isSimonSubmanifold and countablyRectifiable_of_isSimonSubmanifold. AreaFormula gives the parametric injective_area_formula_of_injective_derivative and AreaApproximation gives continuous_normDet. There is no area formula on submanifolds: hence submanifold_area.
- Mathlib supplies:
  - normDet_comp, normDet_sq_eq_det_gram and euclideanHausdorffMeasure_image_eq_normDet_mul_volume (NormDet.lean);
  - continuous_compContinuousLinearMapCLM (Alternating/Basic.lean);
  - exists_open_between_and_isCompact_closure (Regular.lean);
  - setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (Bochner/Set.lean);
  - Continuous.measurableEmbedding and MeasurableSet.image_of_continuousOn_injOn (Polish/Basic.lean).
DAG.
- The general push-forward of IM currents, imrep_c1_diffeo_pushforward_im, and its children dpf_imrep_bilipschitz_image_rep and dpf_area_formula_bilipschitz_rectifiable are speculative-ready, i.e. unaccepted. By runtime._existing_lean_name_problem they cannot be reused, so step 4a is routed through C¹ pieces.
- Seven accepted declarations are reused with byte-identical types: dpf_pushforward_formula_current_exists, dpf_pushforward_formula_boundaryVanishes, dpf_pb_smooth_pullback_isTestForm, regcomp_integer_multiplicity_sub, dpf_unitOrientation_map_gramNormalized, dor_ims_unitOrientation_dual, chart_tangentSpace_eq_range_fderiv. Each candidate commit contains its declaration and adds no imports.
- The 5 new codim1_ac_ names are free in dag.json, GMT/, SimonGMT and all 4046 refs.
Lean.
- Types.lean elaborates all 12 child types (exit 0).
- Assembly.lean proves the selected frozen type from them (exit 0).
- AssemblyAx.lean's axioms are propext, Classical.choice, Quot.sound and 6 children.
