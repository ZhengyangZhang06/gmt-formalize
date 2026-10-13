# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.density_rep-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.density_rep-a1.dual_norm-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 1 (dual norm), with the omitted linear algebra filled in.

Notation:
- V := Λⁿ(ℝ^P) = Covector (Euclid P) n, with its operator norm ‖·‖.
- e_1, …, e_P is the standard orthonormal basis of ℝ^P (EuclideanSpace.basisFun).
- For J : Fin n → Fin P, e_J := (e_{J(1)}, …, e_{J(n)}).
- |α| := covectorEuclideanNorm α = √(Σ_{J strictly increasing} α(e_J)²).

An n-vector ζ is a continuous linear functional on V; MultiVector P n carries the operator norm.

1. Coordinate bound. Let I be strictly increasing. Then α(e_I)² is one of the nonnegative summands defining |α|². Hence α(e_I)² ≤ Σ_J [J strictly increasing] α(e_J)² (Finset.single_le_sum), and |α(e_I)| = √(α(e_I)²) ≤ |α| (Real.sqrt_sq_eq_abs, Real.sqrt_le_sqrt).

2. Definiteness: if α(e_I) = 0 for every strictly increasing I, then α = 0.
(a) First, α(e_J) = 0 for every J : Fin n → Fin P.
- If J is not injective, then the tuple e_J is not injective (e is injective), so α(e_J) = 0 because α is alternating (ContinuousAlternatingMap.map_eq_zero_of_not_injective).
- If J is injective, let σ := Tuple.sort J. This is a permutation of Fin n with J∘σ monotone (Tuple.monotone_sort). J∘σ is injective, hence strictly monotone (Monotone.strictMono_of_injective), so α(e_{J∘σ}) = 0 by hypothesis. Since e_{J∘σ} = e_J∘σ, alternation gives 0 = α(e_J∘σ) = sign(σ)·α(e_J) (AlternatingMap.map_perm). As sign(σ) = ±1 is invertible, α(e_J) = 0 (smul_eq_zero_iff_eq).
(b) Now take any v = (v_1, …, v_n) and expand v_i = Σ_j v_i(j)·e_j (OrthonormalBasis.sum_repr, EuclideanSpace.basisFun_repr). Multilinearity gives α(v) = Σ_{r : Fin n → Fin P} α((v_i(r(i))·e_{r(i)})_i) = Σ_r (Π_i v_i(r(i)))·α(e_r) (ContinuousAlternatingMap.map_sum, map_smul_univ). Every α(e_r) = 0 by (a), so α = 0.

3. Properties of |·|.
(i) |·| is continuous on V: α ↦ α(e_I) is evaluation at a fixed tuple (continuous_eval_const), and squares, finite sums and √ are continuous.
(ii) |tα| = |t|·|α|: every summand gains the factor t², and √(t²S) = |t|√S (Finset.mul_sum, Real.sqrt_mul, Real.sqrt_sq_eq_abs).
(iii) |−α| = |α| (covectorEuclideanNorm_neg).
(iv) If |α| = 0 then α = 0: by step 1, |α(e_I)| ≤ 0 for every strictly increasing I, so step 2 applies.

4. Finite dimension and norm comparison. Let L : V → ((Fin n → Fin P) → ℝ) be the linear map with (Lα)(I) := α(e_I) if I is strictly increasing and 0 otherwise.
- L is injective by step 2, so V is finite-dimensional (FiniteDimensional.of_injective) and hence a proper metric space (FiniteDimensional.proper_real).
- L is antilipschitz: there is K > 0 with ‖α‖ ≤ K‖Lα‖ for all α (LinearMap.exists_antilipschitzWith with ker L = ⊥, applied to the points 0 and α).
- The target carries the sup norm, and each coordinate of Lα has absolute value at most |α| (step 1, or it is 0). So ‖Lα‖ ≤ |α| (pi_norm_le_iff_of_nonneg).
Therefore ‖α‖ ≤ K|α| for all α ∈ V.

5. Compact unit ball. B := {β ∈ V : |β| ≤ 1} is closed by step 3(i) and bounded because ‖β‖ ≤ K on B by step 4. As V is proper, B is compact (Metric.isCompact_of_isClosed_isBounded). Also 0 ∈ B (covectorEuclideanNorm_zero).

6. Definition of N. For an n-vector ζ, the set ζ(B) ⊆ ℝ is compact (continuous image) and nonempty. Define N(ζ) := sup ζ(B).
- N(ζ) ∈ ζ(B) (IsCompact.sSup_mem): there is β ∈ B, i.e. |β| ≤ 1, with ζ(β) = N(ζ). This is clause (iv).
- ζ(β′) ≤ N(ζ) for every β′ ∈ B (le_csSup; ζ(B) is bounded above by compactness).

7. Nonnegativity. 0 ∈ B and ζ(0) = 0, so N(ζ) ≥ 0. This is clause (ii).

8. Domination. Suppose |α| = 0. Then α = 0 by step 3(iv), and both sides of |ζ(α)| ≤ N(ζ)|α| are 0. Otherwise let β := |α|⁻¹α. Then |β| = 1 by step 3(ii), so β ∈ B, and −β ∈ B by step 3(iii). Since α = |α|β, we get ζ(α) = |α|ζ(β) ≤ |α|N(ζ) and −ζ(α) = |α|ζ(−β) ≤ |α|N(ζ). Hence |ζ(α)| ≤ N(ζ)|α|. This is clause (iii).

9. Continuity. For n-vectors ζ, ζ′ pick β ∈ B with ζ(β) = N(ζ) (step 6). Then N(ζ) = ζ′(β) + (ζ − ζ′)(β) ≤ N(ζ′) + ‖ζ − ζ′‖·‖β‖ ≤ N(ζ′) + K‖ζ − ζ′‖. This uses the operator-norm bound (ContinuousLinearMap.le_opNorm) and ‖β‖ ≤ K from step 4. By symmetry N is K-Lipschitz (LipschitzWith.of_le_add_mul), hence continuous. This is clause (i).

Steps 6–9 give all four clauses. ∎

## Key steps

1. Coordinate bound |α(e_I)| ≤ |α|. Definiteness: α vanishes if all strictly increasing coordinates vanish (sorting permutation, alternation, multilinear expansion).
2. The coordinate map L is injective, so covectors are finite-dimensional and ‖α‖ ≤ K|α|; the unit ball B = {|β| ≤ 1} is compact.
3. N(ζ) := sup ζ(B) is attained and nonnegative, and |ζ(α)| ≤ N(ζ)|α| by rescaling α to |α|⁻¹α ∈ B.
4. N is K-Lipschitz for the operator norm, hence continuous.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); cmp snapshot project/GMT/Ch07/Contract.lean against workspace GMT/Ch07/Contract.lean and GMT/Ch07/Submission.lean (all identical); lake-manifest.json mathlib rev 25730c7c759d108ef87ab70af2342a196760f79d`
- `grep -rn in the snapshot mathlib/Mathlib for: theorem exists_disjoint_subfamily_covering_enlargement_closedBall; theorem hausdorffMeasure_le_liminf_tsum; def euclideanHausdorffMeasure / euclideanHausdorffMeasure_def; countable_of_nonempty_interior; theorem mul_le_of_le_div; theorem eventually_lt_of_lt_liminf; exists_antilipschitzWith; theorem IsCompact.sSup_mem; theorem monotone_sort; theorem map_perm; map_eq_zero_of_not_injective; theorem map_sum; map_smul_univ; def apply (ContinuousAlternatingMap); le_opNorm; theorem integral_withDensity_eq_integral_toReal_smul; singularPart_eq_zero_of_ac; theorem haveLebesgueDecomposition_add; theorem rnDeriv_lt_top; theorem measurable_rnDeriv; theorem withDensity_apply; theorem integral_eq_zero_iff_of_nonneg_ae; theorem measure_ball_pos; ediam_le_of_forall_dist_le; theorem liminf_le_of_frequently_le'; of_le_add_mul; le_mul_norm_sub; theorem of_injective (FiniteDimensional); theorem sum_repr / basisFun_repr; pi_norm_le_iff_of_nonneg; Integrable.of_bound; toReal_le_of_le_ofReal. All were found.`
- `grep -rn 'Module.Finite\|FiniteDimensional' restricted to multilinear/alternating files in the snapshot Mathlib: no instance for ContinuousAlternatingMap (only Module.Finite.multilinearMap), so finite-dimensionality is derived from an injective coordinate map`
- `python3 -I scan of .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json lean_statement/title fields with regexes 'covectorEuclideanNorm β ≤ 1', '‖α‖ ≤ .*covectorEuclideanNorm', 'covectorEuclideanNorm α = 0 →', '(?i)vitali|upper density|lower density.*Hausdorff|dual norm|comass|attain'. Found accepted regcomp_covectorEuclideanNorm_seminorm_retract, rsd_mw_tfa_norm_props, regcomp_covector_unit_ball_dense_seq, regcomp_covector_field_near_maximizer, cmr_coordinate_covectors_span, dorag_lip_vitali_two_measure_bound, cmr_vr_cd_density_representation and regcomp_atl_upper_density_zero. None has the type of a needed child.`
- `grep -c '"<name>"' dag.json and grep -rn <name> GMT/ plus the snapshot project for the five proposed lean_names: 0 matches. Python count: 1331 DAG lean names, 0 with prefix cbr_ci_dr`
- `sed of lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean (covectorEuclideanNorm, massAdmissibleOn, GeometricCurrentOn.massOn), Forms.lean (Covector, DifferentialForm, IsTestForm) and Currents.lean (TestFormOn, GeometricCurrentOn)`
- `grep of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py check_source_delta (one theorem per leaf; no helper declarations or set_option) and runtime.py _existing_lean_name_problem/_solve_children (cross-branch reuse only for accepted nodes with identical types)`
- `lake env lean /tmp/dr-decomp/lean/{Types,Assembly,C1,C2,C3,C4,C5,Full}.lean from the workspace root. All succeed. Full.lean: #print axioms dr_full_check = [propext, Classical.choice, Quot.sound]`
- `python3 -I /tmp/dr-decomp/py/validate.py: verifier/lean_contract.py validate_lean_statement passes on all five child statements, and each exact string occurs in Types.lean and Full.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-af13c47156/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-af13c47156/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/EMetricSpace/Diam.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Uniform.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Multilinear/FiniteDimensional.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fin/Tuple/Sort.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/dr-decomp/lean/Types.lean`
- `/tmp/dr-decomp/lean/Assembly.lean`
- `/tmp/dr-decomp/lean/C1.lean`
- `/tmp/dr-decomp/lean/C2.lean`
- `/tmp/dr-decomp/lean/C3.lean`
- `/tmp/dr-decomp/lean/C4.lean`
- `/tmp/dr-decomp/lean/C5.lean`
- `/tmp/dr-decomp/lean/Full.lean`

The snapshot contract is byte-identical to the workspace Contract.lean and Submission.lean (project b4d606db, Mathlib 25730c7c).

Every Mathlib lemma the child proofs rely on exists in the snapshot and is reachable from `import GMT.Ch07.Submission`, including:
- Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall and Measure.hausdorffMeasure_le_liminf_tsum
- euclideanHausdorffMeasure_def (finite NNReal scalar)
- haveLebesgueDecomposition_add, singularPart_eq_zero_of_ac and rnDeriv_lt_top
- integral_withDensity_eq_integral_toReal_smul
- LinearMap.exists_antilipschitzWith, Tuple.monotone_sort and AlternatingMap.map_perm

Mathlib has no FiniteDimensional instance for continuous alternating maps; the dual_norm proof derives it from the injective coordinate map.

No accepted DAG declaration matches a needed child type exactly. The covector-norm toolkits lack definiteness and the lower bound, the two-measure Vitali bound is circular for Hⁿ, and the C_c density representation has no carrier. The five fresh names (prefix cbr_ci_dr_) collide with nothing.

All five exact child types elaborate, pass validate_lean_statement and have complete Lean proofs (C1–C5). Assembly and Full prove the exact frozen parent type from them using only propext, Classical.choice and Quot.sound.
