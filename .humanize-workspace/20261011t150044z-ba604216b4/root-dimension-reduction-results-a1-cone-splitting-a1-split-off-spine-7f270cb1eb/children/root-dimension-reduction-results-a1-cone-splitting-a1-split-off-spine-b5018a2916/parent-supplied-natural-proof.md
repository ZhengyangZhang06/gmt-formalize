# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1`
- Child DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.cube_cycle-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 4–6 of the selected proof: Z_r := (−1)^d ∂([[Q_r]] × Y₀) = [[Q_r]] × X₀ + (−1)^d E'_r is integer multiplicity, ∂Z_r = 0 (∂∂ = 0), spt Z_r ⊆ Q_r + spt Y₀, and M(E'_r) ≤ 2d(2r)^{d−1}M(Y₀). Here the sign (−1)^k is absorbed into E'.
Siblings used: product_current (Submission.idtp_fons_cs_sos_product_current), interior_product (Submission.dimred_cs_sos_mt_interior_product), cube_stokes (Submission.dimred_cs_sos_mt_cube_stokes), face_currents (Submission.dimred_cs_sos_mt_face_currents), mass_triangle (Submission.lcmp_massOn_le_add_of_eval_eq). Accepted results cited by name (dependencies of the selected node or of its ancestors): imrep_represents_massOn_eq_measure (F1), imrep_carrier_sdiff_support_null (F6), rsd_isIntegerMultiplicity_int_combination (F4), dimred_im_mass_measure (part (b): x ∈ spt T iff R.measure(ball(x, ε)) ≠ 0 for every ε > 0).
Notation: write k = j + 1 (k ≥ 1); g^(a) := g ∘ a.succAbove; R_X, R_Y are IMReps of X, Y; σ_Y := R_Y.measure; ω̂ := (ω : DifferentialForm (Euclid P) n'). Since n' = (j + 1) + m, also h₁ : n' + 1 = (j + 1) + (m + 1) and h₂ : n' = j + (m + 1).

Step 1 (concentration on G^⊥). (a) spt X ⊆ spt Y: if O is open with compact closure and Y vanishes on O, then so does X = Y.boundary, because for a test m-form φ with tsupport φ ⊆ O we have tsupport dφ ⊆ tsupport φ ⊆ O (tsupport_exteriorDerivative_subset), so X(φ) = Y(dφ) = 0; hence the zero region of Y is contained in that of X. (b) If an IM current T is represented by R_T = (M_T, θ_T, ξ_T), then R_T.measure(ℝ^P ∖ spt T) = ∫_{M_T ∖ spt T} θ_T dH = 0, as M_T ∖ spt T is null by imrep_carrier_sdiff_support_null (spt T is closed, so the set is Borel). Since spt X ⊆ spt Y ⊆ G^⊥: σ_Y(ℝ^P ∖ G^⊥) ≤ σ_Y(ℝ^P ∖ spt Y) = 0 and R_X.measure(ℝ^P ∖ G^⊥) ≤ R_X.measure(ℝ^P ∖ spt X) = 0.

Step 2 (interior products). By interior_product (a) choose continuous linear maps flatD : Λ^{n'+1} → Λ^{m+1} for (g, h₁), flat₀ : Λ^{n'} → Λ^m for (g, h), and flatF a : Λ^{n'} → Λ^{m+1} for (g^(a), h₂), a ∈ Fin (j + 1), each with its defining identity.

Step 3 (the products and the faces). Q_r is closed (hence Borel) and Q_r ⊆ G. By product_current:
 - with (k, m' := m + 1, n' + 1, h₁, E := Q_r, A := Y, R_Y) — R_Y is carried by G^⊥ by Step 1 — there are B ∈ 𝒟_{n'+1}(ℝ^P) and an IMRep R_B of B with R_B.measure(C) = ∫_{Q_r} σ_Y((y ↦ t + y)⁻¹'C) dH^k(t) for Borel C and B(η) = ∫_{Q_r} currentEval Y (y ↦ flatD(η̂(t + y))) dH^k(t) for every test (n'+1)-form η;
 - with (k, m' := m > 0, n', h, E := Q_r, A := X, R_X) there are B_X ∈ 𝒟_{n'}(ℝ^P) and an IMRep R_{BX} of B_X with B_X(ω) = ∫_{Q_r} currentEval X (y ↦ fl(ω̂(t + y))) dH^k(t) for every map fl with the identity for (g, h) and every test n'-form ω.
By face_currents (R_Y carried by G^⊥, r > 0) there is an integer multiplicity E'' ∈ 𝒟_{n'}(ℝ^P) with M(E'') ≤ ENNReal.ofReal(2(j + 1)(2r)^j)·σ_Y(ℝ^P) and, using the maps flatF a, E''(ω) = Σ_a (−1)^a·[∫_{Q'_a} currentEval Y (y ↦ flatF a(ω̂(s + r·g_a + y))) dH^j(s) − ∫_{Q'_a} currentEval Y (y ↦ flatF a(ω̂(s − r·g_a + y))) dH^j(s)].

Step 4 (boundary formula). Let ω be a test n'-form. The test form exteriorDerivativeTestOn ω has underlying form dω̂, so ∂B(ω) = B(dω) = ∫_{Q_r} currentEval Y (y ↦ flatD(dω̂(t + y))) dH^k(t). By cube_stokes (with X, Y, R_Y, Y.boundary = X, the maps flatD, flat₀, flatF and r > 0) this equals Σ_a (−1)^a·[…] + (−1)^{j+1}·∫_{Q_r} currentEval X (y ↦ flat₀(ω̂(t + y))) dH^k(t) = E''(ω) + (−1)^{j+1}·B_X(ω) (Step 3 with fl := flat₀).

Step 5 (Z and E'). Let c := (−1)^{j+1}, so c² = 1. Define currents Z(ω) := B_X(ω) + c·E''(ω) and E'(ω) := c·E''(ω) (linear, and sequentially continuous as combinations of currents).
 - Z = c·∂B: c·∂B(ω) = c·E''(ω) + c²·B_X(ω) = Z(ω) by Step 4.
 - Z is integer multiplicity: rsd_isIntegerMultiplicity_int_combination with T₁ := B_X (represented by R_{BX}), T₂ := E'', p₁ := 1, p₂ := (−1)^{j+1} ∈ ℤ.
 - ∂Z = 0: n' ≥ 2 is a successor, and for every test form φ of degree n' − 1, ∂Z(φ) = Z(dφ) = c·∂B(dφ) = c·B(d(dφ)) = c·B(0) = 0 (exteriorDerivative_sq).
 - M(E') ≤ M(E''): mass_triangle with X := 0, Y := E'', Z := E', the constant c (|c| = 1) and G := ℝ^P, together with M(0) = 0.
 - M(E'') ≤ ENNReal.ofReal(2k(2r)^{k−1})·M(Y), because σ_Y(ℝ^P) = M(Y) by imrep_represents_massOn_eq_measure (W = ℝ^P) and 2(j + 1)(2r)^j = 2k(2r)^{k−1}.
 - Action: for every map fl with the identity for (g, h) and every ω, Z(ω) = B_X(ω) + E'(ω) = ∫_{Q_r} currentEval X (y ↦ fl(ω̂(t + y))) dH^k(t) + E'(ω) by Step 3.

Step 6 (support of B). Let F := {t + y : t ∈ Q_r, y ∈ spt Y}, the image of the compact set Q_r × spt Y under addition (Q_r is closed and bounded, spt Y is compact by hypothesis), hence compact and closed. For t ∈ Q_r, (y ↦ t + y)⁻¹'(ℝ^P ∖ F) ⊆ ℝ^P ∖ spt Y, so R_B.measure(ℝ^P ∖ F) = ∫_{Q_r} σ_Y((y ↦ t + y)⁻¹'(ℝ^P ∖ F)) dH^k(t) ≤ ∫_{Q_r} σ_Y(ℝ^P ∖ spt Y) dH^k(t) = 0 by Step 1 (b). If x ∉ F, choose ε > 0 with ball(x, ε) ⊆ ℝ^P ∖ F; then R_B.measure(ball(x, ε)) = 0, so x ∉ spt B by dimred_im_mass_measure (b) (R_B represents B in the open set ℝ^P). Hence spt B ⊆ F.

Step 7 (support of Z). If B vanishes on an open O with compact closure, so does ∂B (as in Step 1 (a)) and hence Z = c·∂B. So spt Z ⊆ spt B ⊆ F, and spt Z, being closed, is compact. Finally F ⊆ {x : |⟨g_i, x⟩| ≤ r for all i} ∩ q⁻¹(spt Y): for x = t + y with t ∈ Q_r ⊆ G and y ∈ spt Y ⊆ G^⊥, ⟨g_i, x⟩ = ⟨g_i, t⟩ (as g_i ∈ G and y ⊥ G), so |⟨g_i, x⟩| ≤ r; and q(x) = q(t) + q(y) = 0 + y ∈ spt Y.

Steps 5–7 give all the conclusions for Z and E'. ∎

## Key steps

1. spt X ⊆ spt Y ⊆ G^⊥ makes R_X, R_Y carried by G^⊥ (F6); product_current gives B = [[Q_r]] × Y and B_X = [[Q_r]] × X, and face_currents gives the face current E''.
2. cube_stokes turns ∂B(ω) = B(dω) into E''(ω) + (−1)^k B_X(ω).
3. Z := B_X + (−1)^k E'' = (−1)^k ∂B is integer multiplicity (F4) with ∂Z = 0 (d² = 0); E' := (−1)^k E'' has M(E') ≤ M(E'') ≤ 2k(2r)^{k−1}M(Y) (mass_triangle, F1).
4. R_B vanishes off the compact set Q_r + spt Y, so spt Z ⊆ spt B ⊆ Q_r + spt Y ⊆ {|⟨g_i, x⟩| ≤ r} ∩ q⁻¹(spt Y) (dimred_im_mass_measure (b)).

## Reference use

### local-project

Queries:
- `cat manifest.json (project b4d606db1, mathlib 25730c7c); diff GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical)`
- `python3 over dag.json: split_off_spine nodes and statuses; ancestors and their depends_on; all 2101 accepted nodes dumped to /tmp/mt-decomp/accepted.txt and grepped for translate|massOn_le_add|measure_restrict|support|blowUp|hasDerivAt`
- `git show <candidate>:GMT/Ch07/Submission.lean for idtp_fons_cs_sos_product_current (4aa9ba8d), lcmp_massOn_le_add_of_eval_eq (c7dea4b8), dimred_cs_ti_translate_action_hasDerivAt (f899c748): declarations present, types byte-identical; product_current adds import Poincare.SimonGMT.Chapter02.AreaLipschitz`
- `read nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-60772a06fe/parent-supplied-natural-proof.md (parallel minimality_transfer with the identical frozen type, product construction moved to product_current) and the accepted proofs of the three reused nodes`
- `grep -n over runtime.py (_dependency_problem, _existing_lean_name_problem, _overlay_accepted_children) and inherited.py (cited_inherited: ancestor dependencies cited by exact Lean name)`
- `grep -n over SimonGMT Chapter06/{Currents,Mass,Forms,CurrentLocalEquality}.lean and Chapter03/Rectifiable.lean: GeometricCurrentOn.boundary(_apply), exteriorDerivativeTestOn, CurrentOn.boundary_boundary, massOn/mass/massOn_mono, zeroRegion/support, exteriorDerivative_apply, CountablyRectifiable, blowUpMap, HasApproximateTangentSpaceAt`
- `grep -n over snapshot mathlib Geometry/Euclidean/Volume/Measure.lean: EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Isometry.map_euclideanHausdorffMeasure, Isometry.euclideanHausdorffMeasure_image, IsometryEquiv.measurePreserving_euclideanHausdorffMeasure`
- `rg -n over snapshot mathlib: PiLp.volume_preserving_toLp, Real.volume_pi_closedBall, Real.volume_pi_ball, measurePreserving_piFinSuccAbove, intervalIntegral.integral_eq_sub_of_hasDerivAt, continuousAt_of_dominated, setIntegral_sdiff (integral_diff deprecated alias), measure_add_measure_compl, withDensity_apply, Measure.restrict_restrict, Measure.integrableOn_of_bounded, Fin.append_left, fderiv_comp_add_left, finrank_span_eq_card, Submodule.eq_of_le_of_finrank_eq, ENNReal.le_of_add_le_add_left, lintegral_indicator_const, Fin.removeNth`
- `rg -n "Cartesian product of currents|slice of a current|cartesianProduct" snapshot mathlib (no match)`
- `lake env lean /tmp/mt-decomp/check/{Types,Assembly,CubeCycle,CompMass}.lean (Lean v4.35.0-rc3)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-7f270cb1eb/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-7f270cb1eb/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-60772a06fe/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-da13543666/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-local-comparison-a1-mass-triangle-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-translation-inv-37aaf335d9/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/runtime/flows/gmt-claude-cf346c63e6ef/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-cf346c63e6ef/_recursive_lean/inherited.py`
- `/runtime/flows/gmt-claude-cf346c63e6ef/_recursive_lean/models.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/mt-decomp/check/Types.lean`
- `/tmp/mt-decomp/check/Assembly.lean`
- `/tmp/mt-decomp/check/CubeCycle.lean`
- `/tmp/mt-decomp/check/CompMass.lean`

Pins match. The snapshot manifest records project b4d606db1 (= workspace HEAD) and mathlib 25730c7c; the snapshot Contract.lean equals the workspace Contract.lean and Submission.lean.

Library gaps. Simon leaves Lemma 7.3.5 to the reader (book/chapter-07.txt), so the supplied proof is the project's own argument. SimonGMT has:
- no general Cartesian products of currents;
- no slicing;
- no translation lemma for currents.
Snapshot mathlib has no currents at all ("Cartesian product of currents|slice of a current": no match).

Accepted reuse. dag.json has 2101 accepted declarations. Three fit this proof with byte-identical frozen types, present in their candidate commits:
- idtp_fons_cs_sos_product_current (4aa9ba8d): exactly the I.3 product construction; it also carries the AreaLipschitz import;
- lcmp_massOn_le_add_of_eval_eq (c7dea4b8): the mass triangle inequality;
- dimred_cs_ti_translate_action_hasDerivAt (f899c748): the derivative of s ↦ R.action(ω(sv + ·)).
These are reused as children. Inherited by exact-name citation (inherited.py): dtc_imrep_current, imrep_represents_massOn_eq_measure, imrep_carrier_sdiff_support_null, rsd_isIntegerMultiplicity_int_combination and dimred_im_mass_measure.

Mathlib facts the child proofs need are present in the snapshot, among them:
- μHE[k] = volume on EuclideanSpace and the isometry push-forward Isometry.map_euclideanHausdorffMeasure;
- PiLp.volume_preserving_toLp, Real.volume_pi_closedBall / volume_pi_ball and measurePreserving_piFinSuccAbove;
- the FTC integral_eq_sub_of_hasDerivAt, continuousAt_of_dominated and setIntegral_sdiff;
- finrank_span_eq_card and Submodule.eq_of_le_of_finrank_eq;
- SimonGMT exteriorDerivative_apply, GeometricCurrentOn.boundary_apply and the CountablyRectifiable / HasApproximateTangentSpaceAt definitions via blowUpMap images.

Lean checks. All 12 child types elaborate. The parent's frozen type compiles from the child stubs and its own dependency stubs (axioms: propext, sorryAx from stubs only, Classical.choice, Quot.sound). Skeletons of cube_cycle and competitor_mass compile against their sibling stubs. The runtime gates (ScopedDecomposition validation, _dependency_problem, _existing_lean_name_problem) pass on dag.json. The parallel node idtp_fons_cs_sos_minimality_transfer has the identical frozen type but is not accepted, so it is not reused.
