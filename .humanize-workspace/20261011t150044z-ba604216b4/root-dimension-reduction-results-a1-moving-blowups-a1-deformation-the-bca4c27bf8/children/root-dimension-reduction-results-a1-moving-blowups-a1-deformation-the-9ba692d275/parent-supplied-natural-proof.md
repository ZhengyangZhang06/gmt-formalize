# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.face_replacement-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.face_replacement-a1.boundary_variation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5 of the parent proof (parent E7(b); Simon (27)–(28), (32)). There the variation of the density on a face is bounded by Var_F := M_{N_F}(∂Q₀) for explicit pairwise disjoint open neighbourhoods N_F, and Σ_F Var_F ≤ M(∂Q₀). The support part is the argument of step 9: Var_F > 0 implies that F meets spt ∂Q₀. Uses the hypothesis (VO) and the siblings face_geometry, face_divergence, face_integral_current and current_calculus (Lean names Submission.dimred_mbl_dtfr_face_geometry, …_face_divergence, …_face_integral_current, …_current_calculus).

Notation.
 - n := m + 1; e_i := EuclideanSpace.single i (1 : ℝ); Q₁ := {y ∈ Euclid n : ∀ i, 0 < y_i < 1}; Cⁿ := {y : ∀ i, 0 ≤ y_i ≤ 1}.
 - Φ_p(y) := WithLp.toLp 2 (fun i => (b i : ℝ)) + Σ_j y_j • e_{ι(j)}, E_p := (j ↦ e_{ι(j)}), F̆_p := Φ_p(Q₁), F_p := Φ_p(Cⁿ).
 - For p = (ι, b) let p̃_p : Euclid P → Euclid n be p̃_p(x)_j := x_{ι(j)} − b_{ι(j)}. It is continuous and affine (C^∞), and p̃_p(Φ_p y) = y.
 - δ(t) := min(1, min_j min(t_j, 1 − t_j)) for t ∈ Euclid n. δ is continuous, and δ(t) > 0 for t ∈ Q₁.
 - |α| := covectorEuclideanNorm α.
 - For an m-current S on univ and a set W, M_W(S) = sSup{ofReal(S γ) : γ ∈ massAdmissibleOn univ m W}; the admissible γ are the test forms with tsupport γ ⊆ W and |γ(x)| ≤ 1 for all x. M(S) = M_univ(S).

1. Neighbourhoods. For p ∈ s let N_p := {x : p̃_p(x) ∈ Q₁ and dist(x, Φ_p(p̃_p x)) < δ(p̃_p x)/2}. N_p is open, because Q₁ is open, all maps involved are continuous, and the inequality is strict. F̆_p ⊆ N_p: for x = Φ_p(y) with y ∈ Q₁, p̃_p(x) = y and the distance is 0.
 (i) N_p ∩ F_q = ∅ for q ∈ s with q ≠ p. Suppose x ∈ N_p and x = Φ_q(y') with y' ∈ Cⁿ, and put t := p̃_p(x) ∈ Q₁. Clause (c) of face_geometry (for the pairs p ≠ q, t ∈ Q₁ and y' ∈ Cⁿ) gives dist(Φ_p t, x) ≥ 1, or dist(Φ_p t, x) ≥ min(t_j, 1 − t_j) for some j. In both cases dist(Φ_p t, x) ≥ δ(t), contradicting dist(x, Φ_p t) < δ(t)/2.
 (ii) N_p ∩ N_q = ∅ for distinct p, q ∈ s. Suppose x lies in both. Put t := p̃_p x and t' := p̃_q x (both in Q₁), y := Φ_p t and y' := Φ_q t'. Clause (c) for (p, q, t, t') gives dist(y, y') ≥ δ(t), and clause (c) for (q, p, t', t) gives dist(y', y) ≥ δ(t'). But dist(y, y') ≤ dist(y, x) + dist(x, y') < δ(t)/2 + δ(t')/2 ≤ max(δ(t), δ(t')), a contradiction.
2. Supports. Apply face_integral_current to s and w := u (its hypotheses are among ours), and use part (III)(c) with D := Q₀ (its formula is our hypothesis). It gives: every x ∈ spt Q₀ equals Φ_q(y) for some q ∈ s and y ∈ Cⁿ. By current_calculus, spt ∂Q₀ ⊆ spt Q₀. Hence every point of spt ∂Q₀ lies in F_q for some q ∈ s.
3. Definition of V. M_{N_p}(∂Q₀) ≤ M(∂Q₀) < ∞ (GeometricCurrentOn.massOn_mono). Put V_p := (M_{N_p}(∂Q₀)).toReal ≥ 0 for p ∈ s, and V_p := 0 otherwise. For every γ admissible for N_p, ofReal(∂Q₀ γ) ≤ M_{N_p}(∂Q₀) (GeometricCurrentOn.le_massOn). Since this mass is finite, ∂Q₀(γ) ≤ V_p.
4. Coordinate covectors. For J : Fin m → Fin P let dx^J be the m-covector (v_0, …, v_{m−1}) ↦ det[(v_a)_{J(c)}]_{a,c}. It is the alternating map Matrix.detRowAlternating composed with the linear map v ↦ (v_{J(c)})_c, made continuous by finite dimensionality (e.g. AlternatingMap.mkContinuous with a bound from finite dimensionality).
 - For strictly increasing I, J : Fin m → Fin P, dx^J(e_{I(0)}, …, e_{I(m−1)}) = 1 if I = J and 0 otherwise. The matrix [(e_{I(a)})_{J(c)}] = [I(a) = J(c)] is the identity if I = J. If I ≠ J, then range I ≠ range J (strictly increasing maps with equal ranges coincide), so some I(a) ∉ range J and row a vanishes.
 - For j ∈ Fin n let ε_j := (−1)^j dx^{ι∘succAbove j}. The maps ι ∘ succAbove j are strictly increasing and pairwise distinct, because ι is injective and Fin.succAbove is injective in its first argument.
 Hence, for reals c_j, (Σ_j c_j ε_j)(e_I) = (−1)^j c_j if I = ι ∘ succAbove j, and 0 for every other strictly increasing I. Consequently |Σ_j c_j ε_j|² = Σ_j c_j², and (Σ_{j'} c_{j'} ε_{j'})(E_p ∘ succAbove i) = (−1)^i c_i. (For m = 0, ι ∘ succAbove 0 is the empty map and ε_0 is the constant 0-covector 1.)
5. The test form for g. Fix p ∈ s and g as in (i). If tsupport g = ∅ then g = 0, the integral is 0, and 0 ≤ V_p; so assume tsupport g ≠ ∅.
 - Kg := Φ_p(tsupport g) is compact (g has compact support), and Kg ⊆ F̆_p ⊆ N_p.
 - Choose r > 0 with cthickening(3r, Kg) ⊆ N_p (IsCompact.exists_cthickening_subset_open).
 - Apply exists_contDiff_support_eq_eq_one_iff (order ⊤ : ℕ∞, i.e. C^∞) to the open set thickening(2r, Kg) and the closed set cthickening(r, Kg) ⊆ thickening(2r, Kg). It gives a C^∞ map χ : Euclid P → [0, 1] with support χ = thickening(2r, Kg). So tsupport χ ⊆ cthickening(2r, Kg) ⊆ N_p is compact (IsCompact.cthickening). Also χ = 1 on cthickening(r, Kg), hence on the open neighbourhood thickening(r, Kg) of Kg.
 Put γ(x) := χ(x) · Σ_j g_j(p̃_p x) ε_j. γ is C^∞ and tsupport γ ⊆ tsupport χ ⊆ N_p is compact, so γ is a test m-form on univ. By step 4, |γ(x)| = χ(x) ‖g(p̃_p x)‖ ≤ 1. So γ is admissible for N_p, and ∂Q₀(γ) ≤ V_p by step 3.
6. dγ on the face p. Let G := (y ↦ χ(Φ_p y) • g(y)) : Euclid n → Euclid n. By step 4 and p̃_p(Φ_p y) = y, (−1)^i γ(Φ_p y)(E_p ∘ succAbove i) = (−1)^i χ(Φ_p y) Σ_j g_j(y) ε_j(E_p ∘ succAbove i) = χ(Φ_p y) g_i(y) = G(y)_i for all y and i. So face_divergence (ι := p.1, b := p.2, γ, G) gives dγ(Φ_p y)(E_p) = trace DG(y) for all y. Moreover trace DG(y) = trace Dg(y) for every y:
 - The open set O := Φ_p⁻¹(thickening(r, Kg)) contains tsupport g, and χ∘Φ_p = 1 on O. So G = g on O, and DG(y) = Dg(y) for y ∈ O (Filter.EventuallyEq.fderiv_eq).
 - If y ∉ O then y ∉ tsupport g, so g and G = (χ∘Φ_p)·g both vanish on a neighbourhood of y, and DG(y) = 0 = Dg(y).
 Hence dγ(Φ_p y)(E_p) = trace Dg(y) for all y.
7. Other faces. For q ∈ s with q ≠ p and y ∈ Q₁, Φ_q(y) ∈ F_q. F_q is disjoint from N_p by step 1(i), and N_p ⊇ tsupport γ ⊇ tsupport dγ (tsupport_exteriorDerivative_subset). So dγ(Φ_q y) = 0.
8. Bound (i). Apply the formula for Q₀ to the test form dγ and use steps 6–7: ∂Q₀(γ) = Q₀(dγ) = Σ_{q∈s} ∫_{Q₁} u_q(y) dγ(Φ_q y)(E_q) dy = ∫_{Q₁} u_p(y) trace Dg(y) dy. With step 5 this proves ∫_{Q₁} u_p · trace Dg ≤ V_p.
9. Sum bound. Let η > 0. For each p ∈ s choose γ_p admissible for N_p with ∂Q₀(γ_p) ≥ V_p − η. If V_p ≤ η take γ_p := 0. Otherwise ofReal(V_p − η) < ofReal(V_p) = M_{N_p}(∂Q₀), so lt_sSup_iff supplies an admissible γ_p with ofReal(∂Q₀ γ_p) > ofReal(V_p − η), hence ∂Q₀(γ_p) > V_p − η. Put γ := Σ_{p∈s} γ_p, a test m-form. At each x at most one γ_p(x) is nonzero: γ_p(x) ≠ 0 forces x ∈ tsupport γ_p ⊆ N_p, and the N_p are pairwise disjoint (step 1(ii)). So |γ(x)| ≤ 1, and γ is admissible for univ. Hence Σ_{p∈s}(V_p − η) ≤ Σ_p ∂Q₀(γ_p) = ∂Q₀(γ) ≤ M(∂Q₀).toReal (step 3 with W = univ). Letting η → 0 gives Σ_{p∈s} V_p ≤ M(∂Q₀).toReal. Since M(∂Q₀) < ∞, ofReal(Σ_{p∈s} V_p) ≤ M(∂Q₀).
10. Support (ii). Let p ∈ s with V_p ≠ 0. Then M_{N_p}(∂Q₀) ≠ 0, so by lt_sSup_iff some γ admissible for N_p has ofReal(∂Q₀ γ) > 0, i.e. ∂Q₀(γ) ≠ 0. By (VO) applied to S := ∂Q₀ (degree m, U = univ), tsupport γ is not disjoint from spt ∂Q₀. Take x ∈ tsupport γ ∩ spt ∂Q₀ ⊆ N_p ∩ spt ∂Q₀. By step 2, x ∈ F_q for some q ∈ s, and q = p by step 1(i). So x = Φ_p(y) with y ∈ Cⁿ and x ∈ spt ∂Q₀.
11. Steps 3 and 8–10 give all conclusions: V_p ≥ 0 for p ∈ s, ofReal(Σ_{p∈s} V_p) ≤ M(∂Q₀), the bound (i), and the support statement (ii). ∎

## Key steps

1. Open neighbourhoods N_p ⊇ F̆_p with N_p ∩ F_q = ∅ (q ≠ p), pairwise disjoint, from face_geometry separation; spt ∂Q₀ ⊆ spt Q₀ ⊆ ⋃_q F_q by current_calculus and face_integral_current (III)(c).
2. V_p := M_{N_p}(∂Q₀).toReal (finite) bounds ∂Q₀(γ) for every admissible γ supported in N_p.
3. For g, γ := χ Σ_j g_j(p̃_p ·) (−1)^j dx^{ι∘succAbove j} is admissible in N_p; face_divergence and χ = 1 near Φ_p(tsupport g) give dγ(Φ_p y)(E_p) = div g(y), and dγ vanishes on the other faces, so ∫ u_p div g = ∂Q₀(γ) ≤ V_p.
4. Summing near-optimal forms over the disjoint N_p gives Σ V_p ≤ M(∂Q₀); if V_p ≠ 0, (VO) gives a point of spt ∂Q₀ in N_p, which must lie on F_p.

## Reference use

### local-project

Queries:
- `cat RUN/local-references/123e8435b4a2469b/manifest.json (project_commit b4d606db, mathlib_commit 25730c7c); git -C SNAPSHOT/mathlib rev-parse HEAD (25730c7c759d108ef87ab70af2342a196760f79d); cmp GMT/Ch07/Submission.lean GMT/Ch07/Contract.lean (identical)`
- `rg -n 'dimred_mbl_dtfr|dtfr_' SNAPSHOT/project GMT lake-packages-25730c7c/simongmt -g '*.lean' (no match); python3 -I scan of RUN/dag.json lean_name fields (1611 nodes): the only 'dtfr' names are the twin's nine cmcdtfr_* (decomposing, not accepted); no duplicate lean_names`
- `python3 -I scan of the 1023 accepted RUN/dag.json nodes for reusable identical types (IsUnitOrientationOf, approxTangent, support/mass of differences, insertNth/succAbove/removeNth): related lemmas such as cbrld_ns_support_sub_subset, cbrld_ns_massOn_sub_le, dgcr_unitOrientation_eq_or_neg, atsm_approxTangent_le_of_flat and dimred_mbl_fnd_coordinate_divergence_form have different types; none reused`
- `python3/cat of the twin node root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1: decomposition-v1.json, decomposition-audit-v1.json, decomposition-review-receipt-v1.json (identical frozen type, accepted 9-child split), and its children's decomposition files (face_geometry 4-child split proved in scratch; skeleton_null atomic with an in-closure route; plane_orientation 2-child split proved in scratch)`
- `sed/grep of SimonGMT Chapter06 Currents.lean (GeometricCurrentOn, ext, Zero, boundary, exteriorDerivativeTestOn, tsupport_exteriorDerivative_subset), Mass.lean (covectorEuclideanNorm, massAdmissibleOn, massOn, mass, massOn_mono, le_massOn), CurrentLocalEquality.lean (VanishesOn, zeroRegion, support), Forms.lean (Covector, DifferentialForm, IsSmoothForm = ContDiff ℝ ∞, exteriorDerivative_apply) and Chapter03 Rectifiable.lean (CountablyRectifiable, countablyRectifiable_range/_iUnion/_of_measure_zero/mono, blowUpMap, HasApproximateTangentSpaceAt, hasApproximateTangentSpaceAt_submodule, support_/regular_euclideanHausdorffMeasure_restrict_submodule)`
- `rg -n -l on SNAPSHOT/mathlib/Mathlib for Isometry.euclideanHausdorffMeasure_image and euclideanHausdorffMeasure_zero_or_top (Geometry/Euclidean/Volume/Measure.lean), volume_preserving_piFinSuccAbove (MeasureTheory/Constructions/Pi.lean), exists_contDiff_support_eq_eq_one_iff (Geometry/Manifold/PartitionOfUnity.lean), intervalIntegral.integral_eq_sub_of_hasDerivAt (MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean), integral_divergence_of_hasFDerivAt_off_countable' (MeasureTheory/Integral/DivergenceTheorem.lean, not imported) and hausdorffMeasure_of_dimH_lt (Topology/MetricSpace/HausdorffDimension.lean, not imported)`
- `lake env lean /tmp/dmfr/lean/Closure.lean, Closure2.lean, Closure3.lean, Closure4.lean: #check of every Mathlib/SimonGMT name cited in the child proofs under import GMT.Ch07.Submission (all resolve; integral_divergence_of_hasFDerivAt_off_countable', hausdorffMeasure_of_dimH_lt, dimH_univ_eq_finrank, LipschitzWith.dimH_image_le, exists_smooth_tsupport_subset, Integrable.bdd_mul' and AlternatingMap.toContinuousAlternatingMap are unknown and are not cited)`
- `lake env lean /tmp/dmfr/lean/Types.lean (11 child types + CB + selected type, comparator challenge form, only sorry warnings); InstCheck.lean (clean); Assembly.lean (#print axioms DMFRAsm.check: propext, Classical.choice, Quot.sound); E2E.lean (comparator-style target compiles from Submission stand-ins); FD.lean (face_divergence and current_calculus proved, standard axioms)`
- `grep/sed of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_decompose, _existing_lean_name_problem, _solve_children, _accepted_checkpoint) and decomposition_scope.py; verifier/gmt-compare.py (child_modules, contract_scope, CHILD_TARGET)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/HausdorffDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-bca4c27bf8/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-fac-297ffaa421/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-fac-297ffaa421/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-fac-14c5ade45a/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-fac-1dd1ac6935/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-fac-342d8827bb/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/tmp/dmfr/lean/Types.lean`
- `/tmp/dmfr/lean/InstCheck.lean`
- `/tmp/dmfr/lean/Assembly.lean`
- `/tmp/dmfr/lean/E2E.lean`
- `/tmp/dmfr/lean/FD.lean`
- `/tmp/dmfr/lean/Closure.lean`
- `/tmp/dmfr/lean/Closure2.lean`
- `/tmp/dmfr/lean/Closure3.lean`
- `/tmp/dmfr/lean/Closure4.lean`

Pins match: project b4d606db, Mathlib 25730c7c and SimonGMT 2b36630. Submission.lean is byte-identical to the frozen contract.
Neither the snapshot project nor Mathlib contains lattice-face currents, cubical Stokes, polyhedral chains or a deformation theorem, so these obligations are new. The twin node cmcdt_face_replacement has the identical frozen type and an audited 9-child split, but its cmcdtfr_* declarations are reserved by an active branch and not accepted. Accepted DAG lemmas with related content have different types. So all eleven children get fresh dimred_mbl_dtfr_* names, which collide with nothing in the DAG, the snapshot, Mathlib or SimonGMT.
Every cited Mathlib or SimonGMT name resolves under the frozen imports. Two lemmas cited by the twin's proofs do not resolve there: integral_divergence_of_hasFDerivAt_off_countable' (DivergenceTheorem.lean) and hausdorffMeasure_of_dimH_lt (HausdorffDimension.lean). They are not cited here; the chain_boundary and skeleton_null proofs use in-closure replacements.
The 11 child types elaborate in the comparator's scope. A Lean assembly proves the exact selected type from CB's frozen type and the 11 child types, using only propext, Classical.choice and Quot.sound. The new children face_divergence and current_calculus were proved in full in scratch.
