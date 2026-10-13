# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.plane_integer-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.plane_integer-a1.weight_nat-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 5 and 6 of the supplied proof of cbr_ci_plane_multiplicity_nat ("the Borel measures R.measure and θ₀H^d⌞L_t agree on all open sets … so R.measure = θ₀H^d⌞L_t (Measure.ext_of_generateFrom_of_iUnion)"; "θ′ = θ₀ H^d-a.e. on D ∩ M_t (ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite) … θ′ takes values in ℕ, so θ₀ = θ′(x) ∈ ℕ"), for a general Borel set S in place of the plane L_t and a general ball in place of B_1(tv_1). Write ν := Hᵐ⌞S, M := R.carrier (Borel), θ := R.mult (measurable, ℕ-valued).

1. (Finiteness on balls.) For every ball, ν(B_ρ(z)) ≤ ν(B̄_ρ(z)) < ∞, because closed balls of ℝ^P are compact.

2. (R.measure = c·ν.) The open subsets of ℝ^P form a π-system (isPiSystem_isOpen) generating the Borel σ-algebra (BorelSpace.measurable_eq). The open balls B_{j+1}(0), j ∈ ℕ, cover ℝ^P (iUnion_ball_nat_succ) and R.measure(B_{j+1}(0)) = c·ν(B_{j+1}(0)) < ∞ by the hypothesis and step 1. By hypothesis R.measure and c·ν agree on every open set, so by the uniqueness theorem for measures agreeing on a generating π-system with a finite cover (Measure.ext_of_generateFrom_of_iUnion), R.measure = c·ν.

3. (A set of positive finite measure.) Let x, r be as in the hypothesis and D := S ∩ B_r(x), a Borel set. Then Hᵐ(D) = ν(B_r(x)) (Measure.restrict_apply), so 0 < Hᵐ(D) < ∞ by the hypothesis and step 1.

4. (Formula for the weight.) For Borel E, R.measure(E) = ∫_E θ d(Hᵐ⌞M) = ∫_{E∩M} θ dHᵐ (withDensity_apply, Measure.restrict_restrict).

5. (D is essentially inside M.) By step 4, R.measure(D \ M) = ∫_{(D\M)∩M} θ dHᵐ = 0, since (D \ M) ∩ M = ∅. By step 2 and D \ M ⊆ S, R.measure(D \ M) = c·Hᵐ((D \ M) ∩ S) = c·Hᵐ(D \ M). As c > 0 (so ENNReal.ofReal c ≠ 0), Hᵐ(D \ M) = 0, and therefore Hᵐ(D ∩ M) = Hᵐ(D) > 0 (measure_inter_add_diff).

6. (θ = c almost everywhere on D ∩ M.) Let μ′ := Hᵐ⌞(D ∩ M), a finite measure since μ′(ℝ^P) = Hᵐ(D ∩ M) = Hᵐ(D) < ∞. For every Borel E, using steps 4 and 2, D ⊆ S, and Hᵐ((E ∩ D) \ M) ≤ Hᵐ(D \ M) = 0:
   ∫_E θ dμ′ = ∫_{E∩D∩M} θ dHᵐ = R.measure(E ∩ D) = c·Hᵐ(E ∩ D ∩ S) = c·Hᵐ(E ∩ D) = c·Hᵐ(E ∩ D ∩ M) = ∫_E c dμ′.
   The functions x ↦ (θ(x) : [0, ∞]) and the constant c are measurable and μ′ is σ-finite, so θ = c μ′-almost everywhere (ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite).

7. (Conclusion.) μ′ ≠ 0 because μ′(ℝ^P) = Hᵐ(D ∩ M) > 0 (step 5), so the almost-everywhere filter of μ′ is non-trivial (ae_neBot) and there is a point y with (θ(y) : [0, ∞]) = ENNReal.ofReal c. Taking real parts (c ≥ 0, ENNReal.toReal_ofReal) gives c = θ(y) with θ(y) ∈ ℕ. ∎

## Key steps

1. R.measure and c·Hᵐ⌞S agree on the π-system of open sets and are finite on the balls B_{j+1}(0), so they are equal.
2. For D = S ∩ B_r(x): 0 < Hᵐ(D) < ∞ and R.measure(D \ M) = 0 forces Hᵐ(D \ M) = 0, so Hᵐ(D ∩ M) > 0.
3. Set-lintegrals of θ and of the constant c agree on every Borel set for the finite measure Hᵐ⌞(D ∩ M), so θ = c a.e. there.
4. A point of the non-null set where θ = c gives c = θ(y) ∈ ℕ.

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
