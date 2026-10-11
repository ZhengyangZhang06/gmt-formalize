# Parent-supplied natural-language proof

- Parent DAG node: `root.stationary_results-a1`
- Child DAG node: `root.stationary_results-a1.measure_bounds-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the finiteness hypothesis "Hⁿ(K ∩ M) < ∞ for each compact K ⊂ U" of Simon Ch. 2, §5 (pp. 61-63), and the parent proof (II.1 step 3, II.2 steps 4 and 7), where these two facts are used; proved here completely.

Setting. M ⊆ ℝᴺ with IsSimonSubmanifold (E := ℝⁿ) r M: r ≥ 1 and every y ∈ M lies in W for some chart (V, W, ψ) of class r (V ⊆ ℝⁿ, W ⊆ ℝᴺ open, ψ C^r, hence C¹, on V, injective on V, ψ(V) = W ∩ M, relatively proper: V ∩ ψ⁻¹(K) is compact for every compact K ⊆ W, Dψ(x) injective for x ∈ V). Hⁿ := μHE[n].

Preliminaries.
(P1) On every metric space, μHE[n] = c_n · μH[n] with the same constant c_n := addHaarScalarFactor (volume on EuclideanSpace ℝ (Fin n)) μH[n] ∈ (0, ∞), which is defined through the model space ℝⁿ and therefore does not depend on the ambient space (definition Measure.euclideanHausdorffMeasure; addHaarScalarFactor_volume_hausdorffMeasure_ne_zero; it is finite since it is an NNReal). Hence, if f is K-Lipschitz on s, then μHE[n](f(s)) ≤ Kⁿ μHE[n](s) (LipschitzOnWith.hausdorffMeasure_image_le with d = n, multiplied by c_n). On ℝⁿ, μHE[n] is Lebesgue measure (EuclideanSpace.euclideanHausdorffMeasure_eq_volume), so bounded subsets of ℝⁿ have finite μHE[n]-measure.
(P2) If ψ is C¹ on the open set V and x ∈ V, choose δ > 0 with B̄(x, δ) ⊆ V. Dψ is continuous on the compact set B̄(x, δ), so K_x := sup over B̄(x, δ) of ‖Dψ‖ is finite, and by the mean value inequality on the convex ball (Convex.lipschitzOnWith_of_nnnorm_fderiv_le) ψ is K_x-Lipschitz on B(x, δ). (Alternatively ContDiffAt.exists_lipschitzOnWith.)

(a) Compact subsets of M have finite Hⁿ-measure.
1. Let C ⊆ M be compact. For each y ∈ C choose a chart (V_y, W_y, ψ_y) of class r with y ∈ W_y, and ρ_y > 0 with B̄(y, ρ_y) ⊆ W_y (W_y is open). The open balls B(y, ρ_y), y ∈ C, cover C; choose y_1, …, y_p with C ⊆ ⋃_q B(y_q, ρ_q). Then C = ⋃_q C_q with C_q := C ∩ B̄(y_q, ρ_q), each compact and contained in W_q := W_{y_q}.
2. Fix q and write (V, W, ψ) := (V_{y_q}, W_q, ψ_{y_q}). By relative properness, Q := V ∩ ψ⁻¹(C_q) is compact. Since C_q ⊆ M ∩ W = ψ(V), every z ∈ C_q equals ψ(x) for some x ∈ V, and then x ∈ Q; hence C_q = ψ(Q).
3. By (P2) and compactness of Q, there are finitely many balls B(x_j, δ_j) ⊆ V (j = 1, …, m) covering Q such that ψ is K_j-Lipschitz on B(x_j, δ_j). By (P1), μHE[n](ψ(B(x_j, δ_j))) ≤ K_jⁿ · Lⁿ(B(x_j, δ_j)) < ∞. Since C_q = ψ(Q) ⊆ ⋃_j ψ(B(x_j, δ_j)), monotonicity and subadditivity give μHE[n](C_q) < ∞.
4. Hence μHE[n](C) ≤ Σ_q μHE[n](C_q) < ∞.
(Alternative for step 3: by the SimonGMT area formula IsSimonLocalRepresentation.area_formula, μHE[n](ψ(Q)) = ∫_Q Jψ dLⁿ, and the continuous function Jψ = areaJacobianAt ψ is bounded on the compact Q, while Lⁿ(Q) < ∞.)

(b) Relatively open pieces of M have positive Hⁿ-measure.
5. Let y ∈ M and O ⊆ ℝᴺ open with y ∈ O. Choose a chart (V, W, ψ) of class r with y ∈ W; since y ∈ W ∩ M = ψ(V), y = ψ(x₀) for some x₀ ∈ V. Because ψ is continuous on the open set V, V′ := V ∩ ψ⁻¹(O ∩ W) is open (ContinuousOn.isOpen_inter_preimage) and contains x₀. Moreover ψ(V′) ⊆ O ∩ (W ∩ M) ⊆ M ∩ O.
6. By the SimonGMT area formula for charts, IsSimonLocalRepresentation.area_formula (applicable since r ≥ 1 and V′ is a measurable subset of V), μHE[finrank ℝ ℝⁿ](ψ(V′)) = ∫⁻_{V′} ENNReal.ofReal(Jψ(x)) dLⁿ(x), where Jψ(x) = areaJacobianAt ψ x = normDet(Dψ(x)); and finrank ℝ ℝⁿ = n (finrank_euclideanSpace_fin).
7. For x ∈ V′, Dψ(x) is injective, so normDet(Dψ(x)) ≠ 0 (LinearMap.normDet_ne_zero_tfae), hence Jψ(x) > 0 (normDet ≥ 0). The function x ↦ ofReal(Jψ(x)) is measurable (SimonGMT measurable_areaJacobianAt) and strictly positive on V′, and Lⁿ(V′) > 0 because V′ is a nonempty open set (IsOpen.measure_pos). A lintegral over V′ of a measurable function vanishes only if the function vanishes a.e. on V′, which is impossible here; so ∫⁻_{V′} ofReal(Jψ) dLⁿ > 0.
8. By monotonicity of the outer measure μHE[n], μHE[n](M ∩ O) ≥ μHE[n](ψ(V′)) > 0.
(No case distinction on n is needed: for n = 0, ℝ⁰ is a single point of Lebesgue measure 1 and the normDet of a map out of the zero space is 1.)

## Key steps

1. Cover a compact C ⊆ M by finitely many compact pieces C_q = C ∩ B̄(y_q, ρ_q) inside chart targets; C_q = ψ_q(Q_q) with Q_q compact by relative properness.
2. ψ_q is locally Lipschitz (C¹), so μHE[n](ψ_q(Q_q)) ≤ Σ_j K_jⁿ Lⁿ(B_j) < ∞; sum over q.
3. For y = ψ(x₀) ∈ M ∩ O, V′ := V ∩ ψ⁻¹(O ∩ W) is a nonempty open set with ψ(V′) ⊆ M ∩ O.
4. Area formula: μHE[n](ψ(V′)) = ∫_{V′} Jψ dLⁿ > 0 because Jψ > 0 (Dψ injective) and Lⁿ(V′) > 0.

## Reference use

### local-project

Queries:
- `cat -n GMT/Ch02/Contract.lean; diff GMT/Ch02/Contract.lean GMT/Ch02/Submission.lean; cat GMT/Ch02/README.md`
- `grep -rn "μHE\[" mathlib/Mathlib --include=*.lean | grep -E "notation|def "; sed -n 1,140p mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `cat -n simongmt/Poincare/SimonGMT/Chapter02/{Submanifold,SubmanifoldCalculus,SecondFundamentalForm,SecondFundamentalFormCalculus,SubmanifoldIntegral,SubmanifoldTopology,WeightedArea,Area}.lean; grep -n 'injective_area_formula_of_injective_derivative' AreaFormula.lean`
- `grep -rn "theorem ContDiffAt.isSymmSndFDerivAt\|theorem HasFDerivWithinAt.unique_on\|theorem ContDiffAt.to_localInverse\|theorem LipschitzOnWith.hausdorffMeasure_image_le\|theorem HasCompactSupport.fderiv\|theorem finrank_euclideanSpace_fin" mathlib/Mathlib`
- `grep -rn tangentConeAt mathlib/Mathlib --include=*.lean | grep -E "theorem|lemma" | grep -iE "deriv|curve|segment|mem_tangentCone"; grep -rn mapsTo_tangent mathlib/Mathlib`
- `grep -rn "integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable\|integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable" mathlib/Mathlib; grep -n "theorem\|lemma" mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `grep -rn "Submission\.\|stationary_imp_mean_curvature_zero\|second_fundamental_form_chart_formula\|submanifold_divergence_identity_compact\|deformation_velocity_acceleration_regularity" project simongmt/Poincare; python3 -I lean_name collision check against dag.json`
- `python3 -I gen_checks.py (replays verifier gmt-compare.py contract_scope/child_modules and lean_contract.validate_lean_statement for the 10 lean_statements); lake build GMT.Ch02.Submission; lake env lean NodeChallenge_00..09.lean; lake env lean AssemblyCheck.lean`
- `lake env lean LibCheck.lean: #print axioms Poincare.SimonGMT.Chapter02.{integral_area_formula_of_injective_derivative, IsSimonLocalRepresentation.area_formula, IsSimonLocalRepresentation.weighted_area_formula, IsSimonLocalRepresentation.exists_open_image_eq_inter, IsSimonLocalRepresentation.isEmbedding_chartMap, submanifoldDivergenceAt_eq_sum_inner, measurable_areaJacobianAt}; #check of every cited Mathlib lemma`
- `sed -n 1030,1420p book/chapter-02.txt (printed 4.18-5.12); read dag.json and nodes/root-stationary-results-a1/parent-child-handoff.json`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Equiv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/TangentCone/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Submanifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SecondFundamentalForm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SecondFundamentalFormCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldTopology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaFormula.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-stationary-results-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/stat-decomp2/AssemblyCheck.lean`

The frozen contract (Contract.lean lines 83-176 and 297-342) defines the key notions:
- B is fderivWithin of tangentProjection;
- H is the frame trace;
- IsStationaryIn is defined variationally.

Collision checks: the snapshot project has no Submission.* declarations and no declaration with any of the ten proposed names, and dag.json (50 nodes) has no lean_name collision.

SimonGMT supplies kernel-checked tools used by the children:
- WeightedArea.lean: integral_area_formula_of_injective_derivative and IsSimonLocalRepresentation.area_formula;
- SubmanifoldTopology.lean: IsSimonLocalRepresentation.exists_open_image_eq_inter and isEmbedding_chartMap;
- SubmanifoldCalculus.lean: submanifoldDivergenceAt_eq_sum_inner;
- measurable_areaJacobianAt.
#print axioms shows only propext, Classical.choice and Quot.sound for all of them.

SimonGMT has no divergence theorem on submanifolds (integral_submanifoldDivergence_eq_curvature_sub_boundary takes it as a hypothesis), no chart formula for the frame-free B, and nothing on admissible deformations. These are therefore genuine new obligations.

Mathlib 25730c7c supplies ContDiffAt.isSymmSndFDerivAt, HasFDerivWithinAt.unique_on, HasFDerivWithinAt.mapsTo_tangent_cone, tangentConeAt_mono, tangentConeAt_of_mem_nhds, ContDiffAt.toOpenPartialHomeomorph, ContDiffAt.to_localInverse, OpenPartialHomeomorph.contDiffAt_symm, integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable, LinearMap.normDet_ne_zero_tfae, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, LipschitzOnWith.hausdorffMeasure_image_le, ContractingWith.fixedPoint, HasCompactSupport.fderiv and ContDiffBump. exists_smooth_tsupport_subset does not exist, so it is not cited. setIntegral_eq_of_subset_of_forall_diff_eq_zero is deprecated, so the _sdiff_ name is cited.

Compile checks:
- All ten lean_statements pass the workflow validator and elaborate in the comparator-replayed contract scope; NodeChallenge_00..09 compiled with only sorry warnings.
- AssemblyCheck.lean proves the frozen parent type StationaryIffMeanCurvatureZero ∧ SecondVariationStationary from the children and the sibling types. Its axioms are sorryAx from the stubs plus propext, Classical.choice and Quot.sound.
- Glue examples that instantiate the children as their proofs use them also compile.
