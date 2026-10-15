# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.face_replacement-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.face_replacement-a1.face_integral_current-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 7 and 9 of the parent proof, namely the estimates (34a) and (34b) and the support bullets (Simon (29)–(30), (34)). Here they are proved for an arbitrary finite family of unit faces with integrable densities. Part (III)(b) uses the sibling face_divergence (Submission.dimred_mbl_dtfr_face_divergence).

Notation.
 - n := m + 1; e_i := EuclideanSpace.single i (1 : ℝ); Q₁ := {y ∈ Euclid n : ∀ i, 0 < y_i < 1}; Cⁿ := {y : ∀ i, 0 ≤ y_i ≤ 1}.
 - For p = (ι, b): Φ_p(y) := WithLp.toLp 2 (fun i => (b i : ℝ)) + Σ_j y_j • e_{ι(j)}, E_p := (j ↦ e_{ι(j)}), and F_p := Φ_p(Cⁿ).
 - For a test n-form ω, h_{p,ω}(y) := ω(Φ_p y)(E_p).
 - |α| := covectorEuclideanNorm α, and ‖α‖ is the operator norm of the continuous alternating map α.
 (F1) For a k-covector α and strictly increasing I : Fin k → Fin P, α(e_{I(0)}, …, e_{I(k−1)})² is one of the summands defining |α|² (EuclideanSpace.basisFun (Fin P) ℝ i = e_i). So |α(e_I)| ≤ |α|. Also |α(e_I)| ≤ ‖α‖ Π_j ‖e_{I(j)}‖ = ‖α‖.
 (F2) A test form ω is continuous with compact support, so sup_x ‖ω(x)‖ < ∞ and sup_x |ω(x)| < ∞.

1. (I) Integrability. h_{p,ω} is continuous, because Φ_p is affine and evaluation at the fixed tuple E_p is a continuous linear map. By (F1)–(F2), |h_{p,ω}| ≤ sup_x ‖ω(x)‖. Since w_p is integrable on Q₁, so is w_p · h_{p,ω} (Integrable.bdd_mul, after commuting the two factors).
2. (II) Existence. For ω ∈ TestFormOn univ n define L(ω) := Σ_{p∈s} ∫_{Q₁} w_p h_{p,ω}.
 - Linearity: ω ↦ h_{p,ω} is linear and the integrands are integrable by (I), so L is linear (integral_add, integral_smul).
 - Bound: |L(ω)| ≤ (Σ_p ∫_{Q₁}|w_p|) · sup_x ‖ω(x)‖.
 - Continuity: suppose TestFormOnConverges ω_j 0. Then some compact K contains every tsupport ω_j. The iterated derivative of order 0 has norm ‖ω_j(x)‖ at x (norm_iteratedFDeriv_zero), so ω_j → 0 uniformly on K. Since ω_j = 0 off K, sup_x ‖ω_j(x)‖ → 0, and the bound gives L(ω_j) → 0.
 So ⟨L, continuity⟩ is a GeometricCurrentOn univ n, and D := ⟨L, continuity⟩ satisfies the displayed formula.
3. (III)(a) Mass. Let D satisfy the formula, and let ω be admissible for M(D) = M_univ(D), i.e. |ω(x)| ≤ 1 for all x. By (F1) with I = ι, |h_{p,ω}(y)| ≤ |ω(Φ_p y)| ≤ 1, so D(ω) ≤ |D(ω)| ≤ Σ_p ∫_{Q₁}|w_p|. Hence ofReal(D ω) ≤ ofReal(Σ_p ∫_{Q₁}|w_p|) for every admissible ω. Taking the supremum (sSup_le) gives M(D) ≤ ofReal(Σ_p ∫_{Q₁}|w_p|).
4. (III)(b) Boundary mass. Let B satisfy the hypothesis, and let γ be an admissible test m-form (|γ(x)| ≤ 1 for all x). For p = (ι, b) ∈ s define G_p : Euclid n → Euclid n by G_p(y) := WithLp.toLp 2 (fun i => (−1)^i γ(Φ_p y)(E_p ∘ succAbove i)). γ is C^∞, being a test form. So face_divergence (with ι := p.1, b := p.2, γ and G := G_p) gives:
 - G_p is C^∞;
 - ‖G_p(y)‖ ≤ |γ(Φ_p y)| ≤ 1 for all y;
 - dγ(Φ_p y)(E_p) = trace DG_p(y) for all y, where dγ = exteriorDerivative γ is the form underlying exteriorDerivativeTestOn univ m γ.
 Apply the formula for D to the test form dγ:
 ∂D(γ) = D(dγ) = Σ_{p∈s} ∫_{Q₁} w_p(y) · trace DG_p(y) dy ≤ Σ_{p∈s} |∫_{Q₁} w_p · trace DG_p| ≤ Σ_{p∈s} B_p.
 The last step is the hypothesis on B, which applies because G_p is C^∞ with |G_p| ≤ 1. So ofReal(∂D γ) ≤ ofReal(Σ_p B_p). Taking the supremum over admissible γ gives M(∂D) ≤ ofReal(Σ_{p∈s} B_p).
5. (III)(c) Support. Let s* := {p ∈ s : ∫_{Q₁}|w_p| ≠ 0} and Z := ⋃_{p∈s*} F_p. Z is a finite union of continuous images of the compact set Cⁿ, so it is compact and hence closed.
 - For p ∈ s ∖ s*, w_p = 0 a.e. on Q₁ (integral_eq_zero_iff_of_nonneg). So the p-th summand of D(ω) is 0 for every ω.
 - Let x ∉ Z and choose r > 0 with ball(x, r) ∩ Z = ∅. If tsupport ω ⊆ ball(x, r), then ω(Φ_p y) = 0 for p ∈ s* and y ∈ Q₁, because Φ_p y ∈ Z. So D(ω) = 0.
 - The open ball(x, r) has compact closure (contained in closedBall(x, r); Euclid P is proper), and that closure lies in univ. So ball(x, r) ⊆ zeroRegion D, and x ∉ spt D.
 Hence every x ∈ spt D lies in Z, i.e. x = Φ_p(y) for some p ∈ s with ∫_{Q₁}|w_p| ≠ 0 and some y ∈ Cⁿ. ∎

## Key steps

1. Integrability: w_p times the bounded continuous function y ↦ ω(Φ_p y)(E_p).
2. Existence: the formula is linear and bounded by Σ∫|w_p| · sup‖ω‖, hence sequentially continuous already at order 0.
3. Mass: |ω(x)(E_p)| ≤ covectorEuclideanNorm(ω(x)), one coefficient of the norm.
4. Boundary mass: face_divergence gives C^∞ fields G_p with |G_p| ≤ |γ| ≤ 1 and dγ(Φ_p y)(E_p) = div G_p(y), so ∂D(γ) = Σ_p ∫ w_p div G_p ≤ Σ_p B_p.
5. Support: faces with ∫|w_p| = 0 contribute nothing, and D vanishes off the closed union of the remaining faces.

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
