# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.plane_integer-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.plane_integer-a1.halfspace_ftc-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3 of the supplied proof of cbr_ci_plane_multiplicity_nat ("For j ≥ 2, integrating first in z_j over ℝ gives 0; for j = 1, ∫_{z_1<t}∂_1φ̃_1dz = ∫_{ℝ^{n−1}}φ̃_1(t, z′)dz′"; the coordinates are indexed from 0 here), i.e. Fubini's theorem and the fundamental theorem of calculus, written for one C¹ function with compact support. Norms on ℝ^{d+1} are sup norms (only used for boundedness).

1. (Support bound.) tsupport g is compact, hence bounded: tsupport g ⊆ B̄_R(0) for some R ∈ ℝ. If ‖z‖ > R then z ∉ tsupport g, so g(z) = 0; and since tsupport(Dg) ⊆ tsupport g (tsupport_fderiv_subset), also Dg(z) = 0.

2. (Coordinate lines.) For i ∈ Fin (d+1) and y ∈ ℝ^d let ℓ(s) := insertNth i s y ∈ ℝ^{d+1} (i-th coordinate s, coordinate i.succAbove k equal to y_k). Checking coordinates, ℓ(s) = ℓ(0) + s·e_i, so ℓ is affine with derivative e_i, and |s| = |ℓ(s)_i| ≤ ‖ℓ(s)‖. By the chain rule h(s) := g(ℓ(s)) is differentiable with h′(s) = Dg(ℓ(s))(e_i) = ∂_i g(ℓ(s)) for every s ∈ ℝ.

3. (Behaviour of h.) If |s| > |R| then ‖ℓ(s)‖ > R, so h(s) = 0 and h′(s) = 0 by step 1. Hence h → 0 at −∞ and at +∞ (it is eventually 0), and h′ is continuous (g is C¹) with support in [−|R|, |R|], hence integrable on ℝ.

4. (Fubini.) The map z ↦ (z_i, removeNth i z) is a measure-preserving measurable equivalence ℝ^{d+1} → ℝ × ℝ^d (MeasurableEquiv.piFinSuccAbove, volume_preserving_piFinSuccAbove) whose inverse is (s, y) ↦ insertNth i s y. The function G := 1_H·∂_i g is integrable on ℝ^{d+1}: ∂_i g is continuous with compact support (HasCompactSupport.fderiv_apply) and H is Borel. Hence G ∘ (inverse) is integrable for the product measure (MeasurePreserving.integrable_comp_emb), and by change of variables and Fubini (MeasurePreserving.integral_comp′, integral_prod_symm):
   ∫_H ∂_i g = ∫ G = ∫_{y∈ℝ^d} ( ∫_{s∈ℝ} G(insertNth i s y) ds ) dy.

5. (Proof of (a).) Let i ≠ 0. Then d ≥ 1 (Fin 1 has only the element 0), and 0 = i.succAbove 0 (Fin.succAbove_ne_zero_zero), so (insertNth i s y)_0 = y_0 does not depend on s. For fixed y the inner integral is therefore 0 if y_0 ≥ t, and equals ∫_ℝ h′(s) ds if y_0 < t, where h is the function of step 2 for this i and y. By steps 2–3 and the fundamental theorem of calculus on ℝ (integral_of_hasDerivAt_of_tendsto), ∫_ℝ h′ = 0 − 0 = 0. Thus every inner integral vanishes and ∫_H ∂_i g = 0.

6. (Proof of (b).) Let i = 0. Then insertNth 0 s y = Fin.cons s y (Fin.insertNth_zero′) has 0-th coordinate s, so for fixed y the inner integral is ∫_{s<t} h′(s) ds = ∫_{(−∞, t)} h′ = ∫_{(−∞, t]} h′ (a point is Lebesgue-null; integral_Iic_eq_integral_Iio). By steps 2–3 and the fundamental theorem of calculus on a half-line (integral_Iic_of_hasDerivAt_of_tendsto′), this equals h(t) − lim_{s→−∞} h(s) = g(Fin.cons t y) − 0. Integrating over y ∈ ℝ^d gives ∫_H ∂_0 g = ∫_{ℝ^d} g(t, y) dy. ∎

## Key steps

1. g and Dg vanish outside a ball B̄_R(0); along the line s ↦ insertNth i s y, h(s) = g(…) has h′ = ∂_i g(…), vanishes for |s| > |R|, and h′ is integrable.
2. Fubini through the measure-preserving equivalence z ↦ (z_i, removeNth i z): ∫_H ∂_i g = ∫_y ∫_s 1_H ∂_i g(insertNth i s y) ds dy.
3. i ≠ 0: membership in H does not depend on s, and ∫_ℝ h′ = 0 by the fundamental theorem of calculus.
4. i = 0: the inner integral is ∫_{(−∞,t]} h′ = h(t) = g(Fin.cons t y).

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
