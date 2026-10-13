# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.plane_integer-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.plane_integer-a1.plane_measure-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 0 of the supplied proof of cbr_ci_plane_multiplicity_nat ("ι : ℝⁿ → ℝ^P, ι(z) := Σ_j z_j v_j, a linear isometry onto V₀; Hⁿ⌞V₀ = ι_*(Lⁿ) (Isometry.map_euclideanHausdorffMeasure, EuclideanSpace.euclideanHausdorffMeasure_eq_volume)"), stated for an arbitrary affine plane and with the local finiteness and positivity used in steps 2, 4, 5 and 6 of that proof. Write Euclid m := EuclideanSpace ℝ (Fin m) (Euclidean norm) and toLp : (Fin m → ℝ) → Euclid m for the identity on coordinates (WithLp.toLp 2).

1. (Isometric parametrisation.) Define J : Euclid m → ℝ^P, J(u) := a + Σ_i u_i w_i. For c ∈ Euclid m, orthonormality gives ⟨Σ_i c_i w_i, Σ_i c_i w_i⟩ = Σ_i c_i² (Orthonormal.inner_sum), and Σ_i c_i² = ‖c‖² (EuclideanSpace.real_norm_sq_eq); since both norms are ≥ 0, ‖Σ_i c_i w_i‖ = ‖c‖. Hence ‖J(u) − J(u′)‖ = ‖Σ_i (u_i − u′_i) w_i‖ = ‖u − u′‖, i.e. J is an isometry (Isometry.of_dist_eq).

2. (Range.) range(J) = S. Indeed y = J(u) iff y − a = Σ_i u_i w_i; conversely, if y − a ∈ span(w) then y − a = Σ_i c_i w_i for some c : Fin m → ℝ (Submodule.mem_span_range_iff_exists_fun, Fin m being finite), and y = J(toLp c).

3. (Hausdorff measure under the isometry.) For an isometry, the image of μHE[m] is μHE[m] restricted to the range (Isometry.map_euclideanHausdorffMeasure), and μHE[m] on Euclid m is the Lebesgue measure (EuclideanSpace.euclideanHausdorffMeasure_eq_volume). By step 2, J_*(L_Euclid) = Hᵐ⌞S, where L_Euclid is the Lebesgue measure (volume) of Euclid m.

4. (Proof of (i).) j = J ∘ toLp, and toLp is measure preserving from the product Lebesgue measure of Fin m → ℝ to the Lebesgue measure of Euclid m (PiLp.volume_preserving_toLp). Both maps are continuous, hence measurable, so j_*(Lᵐ) = J_*(toLp_*(Lᵐ)) = J_*(L_Euclid) = Hᵐ⌞S (Measure.map_map and step 3).

5. (Proof of (ii).) S is the preimage of the linear subspace span(w) under the continuous map y ↦ y − a; span(w) is finite-dimensional, hence closed (Submodule.closed_of_finiteDimensional). So S is closed (and in particular Borel).

6. (Proof of (iii).) Let K be compact; K is closed, hence Borel, so by step 3 (Hᵐ⌞S)(K) = J_*(L_Euclid)(K) = L_Euclid(J⁻¹(K)) (Measure.map_apply). An isometry defined on a complete space is a closed embedding (Isometry.isClosedEmbedding), so J⁻¹(K) is compact (IsClosedEmbedding.isCompact_preimage), and compact sets have finite Lebesgue measure. Hence (Hᵐ⌞S)(K) < ∞.

7. (Proof of (iv).) Let r > 0. As in step 6, (Hᵐ⌞S)(B_r(a)) = L_Euclid(J⁻¹(B_r(a))). The set J⁻¹(B_r(a)) is open (J is continuous) and contains 0 because J(0) = a. Nonempty open sets have positive Lebesgue measure (IsOpen.measure_pos; L_Euclid is an additive Haar measure, also for m = 0, where Euclid 0 is a single point of measure 1). Hence (Hᵐ⌞S)(B_r(a)) > 0. ∎

## Key steps

1. J(u) = a + Σ_i u_i w_i is an isometry of Euclid m onto S (orthonormality: ‖Σ c_i w_i‖ = ‖c‖; range by mem_span_range_iff_exists_fun).
2. J_*(Lebesgue) = μHE[m]⌞S by Isometry.map_euclideanHausdorffMeasure and euclideanHausdorffMeasure_eq_volume; composing with the measure-preserving toLp gives (i).
3. S is the preimage of a finite-dimensional (closed) subspace, so closed.
4. (Hᵐ⌞S)(K) = Leb(J⁻¹K) < ∞ since J is a closed embedding; (Hᵐ⌞S)(B_r(a)) = Leb(J⁻¹B_r(a)) > 0 since this open set contains 0.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean; cmp /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean (both identical)`
- `rg -l --fixed-strings over /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib for 'theorem Isometry.map_euclideanHausdorffMeasure', 'theorem EuclideanSpace.euclideanHausdorffMeasure_eq_volume', 'theorem MeasureTheory.Measure.euclideanHausdorffMeasure_zero', 'theorem PiLp.volume_preserving_toLp', 'theorem volume_preserving_piFinSuccAbove', 'theorem integral_prod_symm', 'theorem integral_Iic_of_hasDerivAt_of_tendsto', 'theorem integral_of_hasDerivAt_of_tendsto', 'theorem ext_of_generateFrom_of_iUnion', 'theorem ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite', 'theorem extDeriv_apply', 'theorem Orthonormal.inner_sum', 'theorem setIntegral_map', 'theorem LinearMap.isClosedEmbedding_of_injective', 'theorem HasCompactSupport.fderiv_apply', 'theorem ae_neBot', 'theorem integral_divergence_of_hasFDerivWithinAt_off_countable' (all found; the last only in MeasureTheory/Integral/DivergenceTheorem.lean)`
- `lake env lean on a scratch file importing GMT.Ch07.Submission: #check @MeasureTheory.integral_divergence_of_hasFDerivWithinAt_off_countable_of_le -> unknown identifier (divergence theorem outside the contract's import closure); #check of Isometry.map_euclideanHausdorffMeasure, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Measure.euclideanHausdorffMeasure_zero, Measure.hausdorffMeasure_zero_singleton, ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite, Measure.ext_of_generateFrom_of_iUnion, ContinuousAlternatingMap.apply, Fin.removeNth_zero, integral_Iic_of_hasDerivAt_of_tendsto, integral_of_hasDerivAt_of_tendsto, volume_preserving_piFinSuccAbove, PiLp.volume_preserving_toLp, setIntegral_map, LinearMap.isClosedEmbedding_of_injective, HasCompactSupport.comp_isClosedEmbedding, exteriorDerivative_apply, tsupport_exteriorDerivative_subset (all reachable); inferInstance : (ae (volume : Measure ℝ)).NeBot (succeeds)`
- `rg -il 'stokes|divergence theorem|half.?space' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT (only Chapter02/SubmanifoldIntegral.lean, outside the contract's import closure; no plane-current or half-space Stokes lemma); rg -n 'theorem .*boundary.*plane|planeCurrent|orientedPlane' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT (no match)`
- `python3 -I scans of /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json: lean_name prefixes cbr_cipi_, cbr_pi_, cipi_ (no match); accepted nodes with lean_statement containing Covector/μHE/exteriorDerivative/Submodule.span (regcomp_covector_eval_orthonormal_le and regcomp_exists_covector_eval_orthonormal_eq_one accepted with candidates b7846b6/baaca6e; cbr_imRep_measure_basic, idtp_tdc_subspace_ball_measure, dgoj_exists_continuous_covector_eval noted but not needed); no accepted half-space Stokes or plane-boundary lemma; sibling cbr_ci_const_vector_massOn frozen type extracted; 419 existing cross-branch reuses of accepted children`
- `sed of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_solve_children, _existing_lean_name_problem, _install_parent_supplied_child_handoff, _overlay_accepted_children, _accepted_checkpoint), store.py (ensure) and leaf_verification.py (check_source_delta)`
- `lake env lean /tmp/pi-decomp/lean/{Stmts,Check1,SliceCheck,StokesCheck,PlaneCheck,FtcCheck,WeightCheck,E2E_A,E2E_B,E2E_C,E2E_D}.lean (all statements elaborate; assembly and all child proofs compile; #print axioms: propext, Classical.choice, Quot.sound)`
- `python3 -I verifier/lean_contract.py validate_lean_statement on the seven child statements (all pass)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/AEEqOfLIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Filter.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-93e0ab338f/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-93e0ab338f/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-im-calculus-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/store.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/pi-decomp/lean/Check1.lean`
- `/tmp/pi-decomp/lean/StokesCheck.lean`
- `/tmp/pi-decomp/lean/SliceCheck.lean`
- `/tmp/pi-decomp/lean/PlaneCheck.lean`
- `/tmp/pi-decomp/lean/FtcCheck.lean`
- `/tmp/pi-decomp/lean/WeightCheck.lean`

The snapshot contract is byte-identical to the workspace Contract.lean and Submission.lean (project b4d606db, Mathlib 25730c7c). Every library lemma the child proofs rely on exists in the snapshot and is reachable from `import GMT.Ch07.Submission`. Mathlib's divergence theorem is not reachable, and leaves cannot add imports, so the half-space Stokes formula is supplied by halfspace_ftc (Fubini + FTC) and plane_stokes. Neither SimonGMT nor the DAG has a plane or half-space Stokes lemma, an affine-plane Hausdorff-measure parametrisation or an IM-weight integrality lemma, so these are new children. The covector facts (O1) and (O2) are accepted DAG declarations, reused at byte-identical types. No cbr_cipi_ name exists. In scratch Lean, all statements elaborate, the frozen parent type follows from the children plus const_mass, and every new child has a compiled proof. All use only propext, Classical.choice and Quot.sound.
