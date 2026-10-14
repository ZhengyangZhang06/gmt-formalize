# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.area_comparison-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.area_comparison-a1.submanifold_area-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Simon Ch. 2, 4.11–4.13 (chapter-02.txt lines 956–994: with τ an orthonormal basis of T_yM, J(f∘ψ)(x) = Jψ(x)·J^Mf(y), J^Mf(y) = (det(D_{τ_k}f·D_{τ_l}f))^{1/2}, and for 1:1 f: H^n(f(A)) = ∫_A J^Mf dH^n, ∫_{f(M)} h∘f^{-1} dH^n = ∫_M h J^Mf dH^n), resting on the parametric area formula Simon 3.2 (lines 756–779). This is the area formula invoked in parent step 6 ("Area formula for the injective C¹ map Φ on the C¹ submanifold M"). Uses the sibling chart_tangent_space (Submission.chart_tangentSpace_eq_range_fderiv).
Lean note. The proof may add to Submission.lean the imports Poincare.SimonGMT.Chapter03.SubmanifoldCover (measurableSet_of_isSimonSubmanifold, countablyRectifiable_of_isSimonSubmanifold), Poincare.SimonGMT.Chapter02.AreaFormula and Chapter02.AreaApproximation (injective_area_formula_of_injective_derivative, continuous_normDet) and Poincare.SimonGMT.Chapter02.SubmanifoldTopology (IsSimonLocalRepresentation.isEmbedding_chartMap), as accepted branches already add SimonGMT imports; the frozen statement uses none of them. SimonGMT's IsSimonSubmanifold (E := Euclid m) 1 N follows from IsEmbeddedSubmanifold 1 m N by reordering the chart conditions (the smoothness exponent (1 : ℕ) casts to (1 : ℕ∞), and the properness condition has its arguments permuted); this node's own Lean proof performs exactly this conversion for M.
Notation. For a linear map L : U → ℝ^P on a finite-dimensional inner product space U, normDet(L) ≥ 0 is the Mathlib LinearMap.normDet: normDet(L)² = det(⟨Lb_i, Lb_j⟩) for every orthonormal basis b of U (LinearMap.normDet_sq_eq_det_gram); normDet(L) > 0 iff L is injective; normDet(g∘f) = normDet(g|_{range f})·normDet(f) (LinearMap.normDet_comp); L ↦ normDet(L) is continuous on maps ℝ^m → ℝ^P (SimonGMT Chapter02 continuous_normDet). L^m is Lebesgue measure on ℝ^m (= μHE[m] there).

Proof.
1. (J is a norm determinant.) For x ∈ ℝ^P let L_x : Q(x) → ℝ^P be the restriction of DΦ(x). Applying normDet_sq_eq_det_gram with the orthonormal basis e(x) of Q(x): J(x)² = det(⟨DΦ(x)e_i(x), DΦ(x)e_j(x)⟩) = normDet(L_x)², and both J(x) and normDet(L_x) are ≥ 0, so J(x) = normDet(L_x). In particular J(x) depends only on DΦ(x) and the subspace Q(x), and J(x) > 0 because L_x is injective.
2. (Chart formula.) Let (V, W₀, ψ) be a local representation of N (V ⊆ ℝ^m open, W₀ ⊆ ℝ^P open, ψ C¹ on V and injective on V, ψ(V) = W₀ ∩ N, proper, Dψ injective on V) and v ∈ V. By chart_tangent_space, Q(ψ(v)) = T_{ψ(v)}N = range Dψ(v). By the chain rule D(Φ∘ψ)(v) = DΦ(ψ(v))∘Dψ(v), and by normDet_comp and step 1 (the restriction of DΦ(ψ(v)) to range Dψ(v) = Q(ψ(v)) is L_{ψ(v)}):
 (2.1) normDet(D(Φ∘ψ)(v)) = J(ψ(v))·normDet(Dψ(v)), with normDet(Dψ(v)) > 0.
3. (ψ is a homeomorphism onto W₀ ∩ N; Simon 4.2.) ψ maps V continuously and bijectively onto W₀ ∩ N. It is relatively closed: let F ⊆ V be closed in V and y_j = ψ(v_j) → y ∈ W₀ ∩ N with v_j ∈ F. The set K := {y} ∪ {y_j : j ≥ j₀} is compact and, for j₀ large, contained in W₀ (W₀ is an open neighbourhood of y), so the v_j (j ≥ j₀) lie in the compact set V ∩ ψ^{-1}(K); a subsequence converges to some v ∈ V ∩ ψ^{-1}(K), v ∈ F as F is closed in V, and ψ(v) = y. Hence ψ(F) is closed in W₀ ∩ N, and ψ^{-1} : W₀ ∩ N → V is continuous. (SimonGMT IsSimonLocalRepresentation.isEmbedding_chartMap.)
4. (Continuity of J on N.) On V the maps v ↦ Dψ(v) and v ↦ DΦ(ψ(v)) are continuous (ψ is C¹ on the open set V, Φ is C¹), hence so is v ↦ D(Φ∘ψ)(v), and normDet is continuous. By (2.1), J∘ψ = normDet(D(Φ∘ψ))/normDet(Dψ) is continuous on V. By step 3, J = (J∘ψ)∘ψ^{-1} is continuous on W₀ ∩ N. W₀ ∩ N is a neighbourhood of each of its points relative to N (W₀ is open), so J is continuous within N at each point of W₀ ∩ N. The charts cover N, so J is continuous on N: the first conclusion.
5. (Φ is a measurable embedding.) Φ is continuous and injective on the Polish space ℝ^P, so by the Lusin–Souslin theorem it is a measurable embedding (Mathlib Continuous.measurableEmbedding): Φ(E) is Borel for Borel E, and ∫ g d(Φ_*μ) = ∫ g∘Φ dμ for every g : ℝ^P → [0, ∞] and every measure μ (MeasurableEmbedding.lintegral_map). (Alternatively: DΦ(x) is invertible for every x, so Φ is an open map by the inverse function theorem and a homeomorphism onto its open image.)
6. (N is Borel.) N is covered by countably many chart sets W₀ ∩ N = ψ(V) (Lindelöf, ℝ^P second countable), each σ-compact (V is σ-compact and ψ continuous on V), so N is Borel (SimonGMT measurableSet_of_isSimonSubmanifold, after unfolding the contract's chart conditions into IsSimonSubmanifold). By step 4, J·1_N is Borel; in particular J is a.e.-measurable for H^m⌞B whenever B ⊆ N is Borel.
7. (Set formula in a chart.) Let (V, W₀, ψ) be a chart and A ⊆ V Borel. ψ and Φ∘ψ are injective on A, differentiable within A, with injective derivatives. By the parametric area formula (Simon 3.2; SimonGMT Chapter02 injective_area_formula_of_injective_derivative) and (2.1):
 (7.1) H^m(ψ(A)) = ∫_A normDet(Dψ(v)) dv,
 (7.2) H^m(Φ(ψ(A))) = ∫_A normDet(D(Φ∘ψ)(v)) dv = ∫_A J(ψ(v)) normDet(Dψ(v)) dv.
 Formula (7.1) for all Borel A ⊆ V says (as ψ(V ∩ ψ^{-1}(E)) = ψ(V) ∩ E, and V ∩ ψ^{-1}(E) is Borel for Borel E) that H^m⌞ψ(V) is the image of normDet(Dψ)·L^m⌞V under ψ (in Lean, Measure.map ψ (…) with the a.e.-measurability of ψ on V supplied by ContinuousOn.aemeasurable — Measure.map of a non-a.e.-measurable map is 0 — and ψ(A) Borel by MeasurableSet.image_of_continuousOn_injOn). Integrating the H^m⌞ψ(V)-measurable function 1_{ψ(A)}·J (step 6) against this measure gives ∫_{ψ(A)} J dH^m = ∫_A J(ψ(v)) normDet(Dψ(v)) dv. Comparing with (7.2): H^m(Φ(B)) = ∫_B J dH^m for every Borel B ⊆ W₀ ∩ N (take A := V ∩ ψ^{-1}(B), so ψ(A) = B).
8. (Set formula on N.) Choose charts (V_k, W_k, ψ_k), k ∈ ℕ, whose sets W_k cover N (step 6). For a Borel B ⊆ N let B_k := (B ∩ W_k) ∖ ⋃_{i<k} W_i: Borel, pairwise disjoint, with union B, and B_k ⊆ W_k ∩ N. Since Φ is injective, the Borel sets Φ(B_k) are pairwise disjoint with union Φ(B). By step 7 and countable additivity:
 (8.1) H^m(Φ(B)) = Σ_k H^m(Φ(B_k)) = Σ_k ∫_{B_k} J dH^m = ∫_B J dH^m for every Borel B ⊆ N.
9. (Function formula.) Fix a Borel B ⊆ N. Let ν₁ := H^m⌞Φ(B) and ν₂ := Φ_*(J·(H^m⌞B)), where J·μ denotes the measure with density ofReal∘J. For Borel E, Φ(B) ∩ E = Φ(B ∩ Φ^{-1}(E)) (Φ injective) and B ∩ Φ^{-1}(E) is a Borel subset of N, so by (8.1) ν₁(E) = ∫_{B∩Φ^{-1}(E)} J dH^m = ν₂(E). Hence ν₁ = ν₂, and for every g : ℝ^P → [0, ∞]:
 ∫_{Φ(B)} g dH^m = ∫ g dν₁ = ∫ g dν₂ = ∫_B J·(g∘Φ) dH^m,
 using step 5 (integration against an image measure by a measurable embedding, valid for every g) and ∫ h d(J·μ) = ∫ J·h dμ for every h ≥ 0 when J is a.e.-measurable and finite (Mathlib lintegral_withDensity_eq_lintegral_mul_non_measurable₀; step 6). With ofReal(J(x)) in place of J(x) this is the asserted identity ∫⁻_{Φ(B)} g dH^m = ∫⁻_B ofReal(J(x))·g(Φ(x)) dH^m(x). ∎

## Key steps

1. J(x) = normDet(DΦ(x)|_{Q(x)}) > 0 (Gram determinant in an orthonormal basis).
2. In a chart: Q(ψ(v)) = range Dψ(v) (chart_tangent_space) and normDet(D(Φ∘ψ)(v)) = J(ψ(v))·normDet(Dψ(v)) (normDet_comp).
3. Charts are homeomorphisms onto W₀ ∩ N (properness), so J = normDet(D(Φ∘ψ))/normDet(Dψ)∘ψ^{-1} is continuous on N.
4. Parametric area formula for ψ and Φ∘ψ gives H^m(Φ(B)) = ∫_B J dH^m for Borel B in a chart; countable chart cover and injectivity extend it to Borel B ⊆ N.
5. Hence H^m⌞Φ(B) = Φ_*(J·H^m⌞B); integrating g (Φ a measurable embedding, J a.e.-measurable) gives ∫_{Φ(B)} g = ∫_B J g∘Φ.

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
