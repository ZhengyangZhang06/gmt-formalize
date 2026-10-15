# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.face_replacement-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.face_replacement-a1.chain_boundary-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 8 (boundary part) of the parent proof: "Fubini and the fundamental theorem of calculus on [0,1]ⁿ give [[F]](dγ) = Σ_j (−1)^{j−1}([[G_j^1]](γ) − [[G_j^0]](γ))", so ∂Pc is a finite integer combination of (n−1)-face currents. Indices here are 0-based, so the sign is (−1)^j. Uses the sibling face_divergence (Submission.dimred_mbl_dtfr_face_divergence). The frozen contract does not import Mathlib.MeasureTheory.Integral.DivergenceTheorem, so the cube identity is proved directly from Fubini and the one-variable fundamental theorem of calculus. All lemmas cited below are available under the frozen imports.

Notation.
 - n := m + 1; e_i := EuclideanSpace.single i (1 : ℝ); Q₁^k := {y ∈ Euclid k : ∀ i, 0 < y_i < 1}.
 - For p = (ι, b) with ι : Fin k → Fin P: Φ_p(y) := WithLp.toLp 2 (fun i => (b i : ℝ)) + Σ_j y_j • e_{ι(j)}, E_p := (j ↦ e_{ι(j)}), and [[p]](γ) := ∫_{Q₁^k} γ(Φ_p y)(E_p) dy.
 - For j ∈ Fin n, t ∈ ℝ and y' ∈ Euclid m, ins_j(t, y') := WithLp.toLp 2 (Fin.insertNth j t (WithLp.ofLp y')) ∈ Euclid n: its j-th coordinate is t and the others are y' in order.
 - ∂T(γ) = T(dγ), where dγ = exteriorDerivativeTestOn univ m γ has underlying form exteriorDerivative γ.

1. Faces of a face. For p = (ι, b) ∈ s, j ∈ Fin n and ε ∈ {0, 1} put q(p, j, ε) := (ι ∘ succAbove j, b + ε·𝟙_{ι(j)}), where (b + ε·𝟙_{ι(j)})_i := b_i + (if i = ι(j) then ε else 0).
 - ι ∘ succAbove j : Fin m → Fin P is strictly increasing.
 - Φ_{q(p,j,ε)}(y') = Φ_p(ins_j(ε, y')). Compare coordinates: at ι(j) both sides equal b_{ι(j)} + ε; at ι(succAbove j l) both equal b_{ι(succAbove j l)} + y'_l; at i ∉ range ι both equal b_i. Equivalently, expand Σ_{l : Fin n} with Fin.sum_univ_succAbove j.
 - E_{q(p,j,ε)} = E_p ∘ succAbove j = Fin.removeNth j E_p.
2. dγ as a divergence. Fix p ∈ s and a test m-form γ, which is C^∞. Define G : Euclid n → Euclid n by G(y) := WithLp.toLp 2 (fun i => (−1)^i γ(Φ_p y)(E_p ∘ succAbove i)). By face_divergence (ι := p.1, b := p.2), G is C^∞ and dγ(Φ_p y)(E_p) = trace DG(y) for all y. Computing the trace in the standard basis, trace DG(y) = Σ_i ∂_i G_i(y), where G_i(y) := G(y)_i is C^∞ and ∂_i h(y) := Dh(y)(e_i).
3. The cube identity. Claim: for every C^1 function h : Euclid n → ℝ and every i ∈ Fin n, ∫_{Q₁^n} ∂_i h(y) dy = ∫_{Q₁^m} (h(ins_i(1, y')) − h(ins_i(0, y'))) dy'. Proof:
 (a) Transport to Fin n → ℝ by the measure-preserving map WithLp.ofLp (PiLp.volume_preserving_ofLp). Q₁^n corresponds to the box B_n := Set.pi univ (fun _ => Ioo 0 1).
 (b) MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i : (Fin n → ℝ) ≃ᵐ ℝ × (Fin m → ℝ), z ↦ (z_i, removeNth i z), has inverse (t, z') ↦ Fin.insertNth i t z'. It is measure preserving (MeasureTheory.volume_preserving_piFinSuccAbove), and it maps B_n onto Ioo 0 1 ×ˢ B_m.
 (c) ∂_i h is continuous, hence bounded on the compact closed cube. So the integrand times the indicator of Ioo 0 1 ×ˢ B_m is integrable for volume = volume.prod volume. Fubini (MeasureTheory.integral_prod_symm, or integral_prod followed by integral_integral_swap) gives ∫_{Q₁^n} ∂_i h = ∫_{z'∈B_m} ∫_{t∈Ioo 0 1} ∂_i h(toLp(insertNth i t z')) dt dz'.
 (d) Fix z'. The curve t ↦ toLp(insertNth i t z') has derivative e_i. By the chain rule, t ↦ h(toLp(insertNth i t z')) has derivative ∂_i h(toLp(insertNth i t z')), which is continuous in t. The fundamental theorem of calculus (intervalIntegral.integral_eq_sub_of_hasDerivAt, with ∫_{Ioo 0 1} = ∫_0^1 by MeasureTheory.integral_Ioc_eq_integral_Ioo and intervalIntegral.integral_of_le) gives the inner integral h(toLp(insertNth i 1 z')) − h(toLp(insertNth i 0 z')).
 (e) Transport z' back to Euclid m by ofLp. For m = 0, B_0 and Q₁^0 = Euclid 0 are single points of measure 1, and the identity is the fundamental theorem of calculus on [0, 1].
4. Cubical Stokes. Apply steps 2–3 with h := G_i. All integrands are bounded continuous functions on bounded sets, so the finite sums may be exchanged with the integrals:
 ∫_{Q₁^n} dγ(Φ_p y)(E_p) dy = Σ_{i∈Fin n} ∫_{Q₁^m} (G_i(ins_i(1, y')) − G_i(ins_i(0, y'))) dy'.
 By step 1, G_i(ins_i(ε, y')) = (−1)^i γ(Φ_{q(p,i,ε)} y')(E_{q(p,i,ε)}). Hence
 ∫_{Q₁^n} dγ(Φ_p y)(E_p) dy = Σ_{i∈Fin n} (−1)^i ([[q(p,i,1)]](γ) − [[q(p,i,0)]](γ)).
5. Boundary of T. Applying the hypothesis on T to the test form dγ gives
 ∂T(γ) = T(dγ) = Σ_{p∈s} β_p ∫_{Q₁^n} dγ(Φ_p y)(E_p) dy = Σ_{p∈s} Σ_{i∈Fin n} Σ_{ε∈{0,1}} β_p (−1)^i (2ε − 1) [[q(p,i,ε)]](γ).
6. Regrouping. Let 𝒜 := s ×ˢ (Finset.univ : Finset (Fin n)) ×ˢ {0, 1}, a finite set, with κ(p, i, ε) := q(p, i, ε) and c(p, i, ε) := β_p (−1)^i (2ε − 1) ∈ ℤ. Put s' := 𝒜.image κ and β'_q := Σ_{a∈𝒜, κ(a) = q} c(a) ∈ ℤ (β'_q := 0 for q ∉ s'). Every q ∈ s' has strictly increasing first component by step 1. Grouping the finite sum of step 5 by the value of κ (Finset.sum_fiberwise_of_maps_to, or Finset.sum_image') gives Σ_{a∈𝒜} c(a)[[κ a]](γ) = Σ_{q∈s'} β'_q [[q]](γ), with the integer coefficients cast to ℝ. Therefore ∂T(γ) = Σ_{q∈s'} (β'_q : ℝ) ∫_{Q₁^m} γ(Φ_q y)(E_q) dy for every test m-form γ, and s', β' do not depend on γ. ∎

## Key steps

1. Faces of a face: q(p, j, ε) = (ι∘succAbove j, b + ε·𝟙_{ι(j)}), with Φ_{q(p,j,ε)} = Φ_p ∘ insertNth j ε and E_{q(p,j,ε)} = E_p∘succAbove j.
2. face_divergence: dγ(Φ_p y)(E_p) = div G(y) with G_i(y) = (−1)^i γ(Φ_p y)(E_p∘succAbove i), G C^∞.
3. Cube identity by Fubini (piFinSuccAbove, measure preserving) and the one-variable fundamental theorem of calculus: [[p]](dγ) = Σ_j (−1)^j([[q(p,j,1)]](γ) − [[q(p,j,0)]](γ)).
4. Regroup the finite family (p, j, ε) by the resulting face to get integer coefficients β'.

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
