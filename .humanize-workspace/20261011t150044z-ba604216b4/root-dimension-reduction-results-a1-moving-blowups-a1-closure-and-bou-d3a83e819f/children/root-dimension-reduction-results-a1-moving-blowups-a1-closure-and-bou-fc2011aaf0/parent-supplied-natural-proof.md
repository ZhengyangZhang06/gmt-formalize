# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.plane_integer-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.plane_integer-a1.slice_im-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 of the supplied proof of dmcbr_ci_plane_multiplicity_nat (word for word the supplied proof of cbr_ci_plane_multiplicity_nat): "(μ, ξ) := (θ₀Hⁿ⌞V₀, ξ_v), ξ_v(β) := β(v), is an admissible representation of C … (0, 0) represents ∂C = 0. Apply (SL) with U := ℝ^P, k := d, this data, f, L := 1 … ISP of C instantiated with (μ, ξ_v), (0, 0) and f gives an L¹-null set N such that Z_t := ∂A_t − B_t is integer multiplicity for every t ∉ N; Z_t(φ) = ∂A_t(φ)". It also uses step 1 (∂C = 0) and the half-space formula of step 3, "Z_t(φ) = θ₀∫_{L_t}φ(y)(v_2, …, v_n)dH^d(y)".

The siblings used are:
- plane_measure (PM) = Submission.cbr_cipi_affine_plane_measure;
- halfspace_ftc (FTC) = Submission.cbr_cipi_halfspace_partial_integral;
- halfspace_boundary (HB) = Submission.cbr_cipi_plane_halfspace_boundary;
- boundary_zero (BZ) = Submission.cbr_cipi_plane_boundary_zero;
- covector_eval_le (O1) = Submission.regcomp_covector_eval_orthonormal_le.
Nothing else is needed, and the whole argument is one theorem.

Notation:
- n := d + 1 and Hᵐ := μHE[m].
- V₀ := span(range v) and H_t := {y : ⟨y, v_0⟩ < t}.
- L_t := {y : y − t v_0 ∈ span(range(Fin.tail v))}, where Fin.tail v = (v_1, …, v_d).
- dφ := exteriorDerivative φ, and ∂X(η) = X(dη) (GeometricCurrentOn.boundary_apply).
Introduce (SL), P, d, v (orthonormal), θ₀ > 0, C with C(ω) = θ₀∫_{V₀}ω(y)(v)dHⁿ(y) for every test n-form ω, and the ISP hypothesis on C.

0. (Stokes on V₀ and on its half-planes.) The first two hypotheses of (HB), (PM) and (FTC), are exactly the frozen statements of the siblings plane_measure and halfspace_ftc. So (HB) applied to these two siblings and to P, d, v gives, for every test d-form φ and every t ∈ ℝ,
   (b) ∫_{V₀∩H_t} dφ(y)(v) dHⁿ(y) = ∫_{L_t} φ(y)(Fin.tail v) dH^d(y).
   For fixed φ, statement (b) for all t is exactly the hypothesis (HS) of (BZ). So (BZ) applied to P, d, v and φ gives
   (a) ∫_{V₀} dφ(y)(v) dHⁿ(y) = 0.

1. (Representation of C.) Let μ := θ₀·(Hⁿ⌞V₀), with scalar ENNReal.ofReal θ₀. Let ξ_v ∈ Λ_n be evaluation at v, ξ_v(α) := α(v_0, …, v_d) (ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ v), and ξ(x) := ξ_v for all x.
   (a′) μ is finite on compact sets. (PM)(iii) with m := n, w := v, a := 0 gives Hⁿ(V₀ ∩ K) < ∞, because {y : y − 0 ∈ V₀} = V₀. Hence μ(K) = θ₀Hⁿ(V₀ ∩ K) < ∞ (ENNReal.mul_lt_top).
   (b′) ξ is constant, hence a.e. strongly measurable. Since v is orthonormal, (O1) gives |ξ(x)(α)| = |α(v)| ≤ |α| for every α.
   (c′) For every test n-form ω, ∫ξ(x)(ω(x))dμ(x) = (ENNReal.ofReal θ₀).toReal·∫_{V₀}ω(y)(v)dHⁿ(y) = θ₀∫_{V₀}ω(y)(v)dHⁿ(y) = C(ω) (integral_smul_measure, ENNReal.toReal_ofReal with θ₀ ≥ 0).

2. (∂C = 0 and its representation.) For a test d-form η, ∂C(η) = C(dη) = θ₀∫_{V₀}dη(y)(v)dHⁿ(y) = θ₀·0 = 0, by (a) of step 0 applied to η. Take μ′ := 0 and ξ′ := 0.
   - μ′ is finite.
   - ξ′ is constant.
   - The bound holds because μ′-a.e. statements are vacuous for μ′ = 0; it also holds pointwise, since |0| = 0 ≤ |α| (covectorEuclideanNorm_nonneg).
   - ∫ξ′(x)(η(x))dμ′ = 0 = ∂C(η) (integral_zero_measure).

3. (The slicing function.) f(y) := ⟨y, v_0⟩ is 1-Lipschitz (LipschitzWith.of_dist_le_mul). By Cauchy–Schwarz (abs_real_inner_le_norm) and ‖v_0‖ = 1, |f(y) − f(y′)| = |⟨y − y′, v_0⟩| ≤ ‖y − y′‖·‖v_0‖ = ‖y − y′‖.

4. (Slices from (SL).) Apply (SL) with:
   - U := ℝ^P (open), k := d and T := C;
   - the data (μ, ξ) and (μ′, ξ′) of steps 1–2, finite on compact subsets of U by step 1(a′);
   - f of step 3 and L := 1.
   This gives currents A_t ∈ 𝒟_n(ℝ^P) and B_t ∈ 𝒟_d(ℝ^P) (t ∈ ℝ) with A_t(ω) = ∫_{f<t}ξ(x)(ω(x))dμ(x) and B_t(η) = ∫_{f<t}ξ′(x)(η(x))dμ′(x) for all t and all test forms. Only these two formulas are used.

5. (Integer multiplicity from ISP.) Steps 1–3 are exactly the hypotheses of ISP for (μ, ξ), (μ′, ξ′), f and L = 1. So there is an L¹-null set N such that, for t ∉ N, every pair (A, B) with these two integral formulas has ∂A − B of integer multiplicity. For t ∉ N the pair (A_t, B_t) of step 4 qualifies, so Z := ∂A_t − B_t is integer multiplicity. In Lean this is filter_upwards on the ∀ᵐ t given by ISP.

6. (Formula for Z.) Fix t ∉ N and a test d-form φ.
   - By the contract's subtraction of currents and ∂A(φ) = A(dφ), Z(φ) = A_t(dφ) − B_t(φ).
   - B_t(φ) = ∫ … d(μ′⌞{f<t}) = 0, since μ′ = 0 (Measure.restrict_zero, integral_zero_measure).
   - The half-space {f < t} = H_t is open (isOpen_lt), hence Borel. So μ⌞{f<t} = θ₀·Hⁿ⌞({f<t} ∩ V₀) (Measure.restrict_smul, Measure.restrict_restrict).
   - By integral_smul_measure and ENNReal.toReal_ofReal, then (b) of step 0 with Set.inter_comm,
     A_t(dφ) = θ₀∫_{V₀∩H_t} dφ(y)(v)dHⁿ(y) = θ₀∫_{L_t}φ(y)(Fin.tail v)dH^d(y).
   Hence Z(φ) = θ₀∫_{L_t}φ(y)(Fin.tail v)dH^d(y) for every test d-form φ and every t ∉ N, that is, for L¹-almost every t. ∎

## Key steps

1. Step 0: halfspace_boundary, applied to the siblings plane_measure and halfspace_ftc, gives the half-plane Stokes formula ∫_{V₀∩{⟨y,v_0⟩<t}} dφ(v) dHⁿ = ∫_{L_t} φ(Fin.tail v) dH^d for every φ and t; boundary_zero turns this into ∫_{V₀} dφ(v) dHⁿ = 0.
2. (θ₀Hⁿ⌞V₀, constant evaluation at v) is an admissible representation of C: local finiteness by plane_measure (iii), the bound by covector_eval_le, the formula by integral_smul_measure.
3. ∂C = 0 by step 0, so (0, 0) represents ∂C; f = ⟨·, v_0⟩ is 1-Lipschitz.
4. (SL) gives slices A_t, B_t with the two integral formulas; ISP makes Z_t = ∂A_t − B_t integer multiplicity for a.e. t.
5. Z_t(φ) = A_t(dφ) − 0 = θ₀∫_{V₀∩{⟨y,v_0⟩<t}} dφ(v) dHⁿ = θ₀∫_{L_t} φ(Fin.tail v) dH^d by step 0.

## Reference use

### local-project

Queries:
- `cat SNAPSHOT/manifest.json -> mode local-project, project_commit b4d606db1 (= workspace HEAD), mathlib_commit 25730c7c (= .lake/packages/mathlib HEAD); cmp SNAPSHOT/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean -> identical`
- `python3 -I scans of RUN/dag.json: status, candidate_commit, updated_at, depends_on and children of the cbr_cipi_*, regcomp_covector_* and cbr_ci_const_vector_massOn nodes, the twin cbr_ci_plane_multiplicity_nat and its plane_stokes subtree; byte comparison of this node's handoff (lean_statement, natural_proof, proof_key_steps) with the twin's -> identical; dimred_mbl_slice_mass_bounds vs cmc_slice_mass_bounds vs the parent's second hypothesis vs slice_im's first hypothesis -> identical`
- `RUN/issue-workers.json: worker 3e1017a5 for this node (issue 7075) started 2026-10-14T00:50:35Z; RUN/nodes/<a2d19864c9>/accepted-candidate.json dated 01:02:11Z, DAG updated_at 01:06:14Z -> plane_stokes was accepted after attempt 1's store snapshot`
- `grep/sed /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py: _decompose, _existing_lean_name_problem, _accepted_checkpoint, _solve_children existing_by_name, _install_parent_supplied_child_handoff (returns early for accepted checkpoints), _overlay_accepted_children, _reference_use_problem; store.py refresh/update/ensure; shared_dag.merge_nodes`
- `python3 -I replica of _existing_lean_name_problem over dag.json for the 9 proposed names, run on the current DAG and again with every node touched after 00:50:35Z treated as unaccepted -> 8 accepted identical-type reuses + 1 fresh name, in both cases`
- `read decomposition-v1.json and decomposition-audit-v1.json of nodes 93e0ab338f (twin plane_integer; every child acceptable) and a2d19864c9 (twin plane_stokes; every child acceptable), decomposition-v1.json of bf84361bcd (isodiametric_bound precedent, which reuses accepted grandchildren), and this node's rejected attempt-1 decomposition-v1.json`
- `git show <21dd628c|a6ce523c|547023ad|bdf50352|95db7096|b7846b63|baaca6e4|6c348627|bc226ec6>:GMT/Ch07/Submission.lean -> 'theorem Submission.<name> : <frozen type> := by' present, 0 sorry before main_theorem; bdf50352 also contains extderiv_coords, plane_measure and halfspace_ftc; git show 558a0fd4 (the one-line plane_stokes composition); isolated-comparator-result.json of all 8 reused nodes -> passed=true at those commits`
- `rg -l dmcbr_cipi SNAPSHOT GMT .lake/packages/simongmt -> no match (exit 1); rg -c 'cbr_cipi|regcomp_covector' SNAPSHOT -> no match (exit 1); git log --all -S dmcbr_cipi_slice_integer_multiplicity -- GMT/Ch07/Submission.lean -> empty; grep -c dmcbr_cipi dag.json -> 0`
- `rg over SNAPSHOT/mathlib/Mathlib for the library facts in the new child's proof: integral_smul_measure, integral_zero_measure, integral_const_mul (MeasureTheory/Integral/Bochner/Basic.lean:1052, :1020, :290), restrict_smul and restrict_restrict (MeasureTheory/Measure/Restrict.lean:193, :205), setIntegral_map (MeasureTheory/Integral/Bochner/Set.lean:554), isOpen_lt (Topology/Order/OrderClosed.lean:588), abs_real_inner_le_norm (Analysis/InnerProductSpace/Basic.lean:471), LipschitzWith.of_dist_le_mul (Topology/MetricSpace/Lipschitz.lean:49), Filter.Eventually.exists (Order/Filter/Basic.lean:814), Orthonormal.comp (Analysis/InnerProductSpace/Orthonormal.lean:193), ENNReal.toReal_ofReal (Basic/ENNReal/Basic.lean:252) -> all found`
- `rg in .lake/packages/simongmt and GMT/Ch07/Submission.lean: GeometricCurrentOn.boundary_apply (Chapter06/Currents.lean:333), covectorEuclideanNorm and covectorEuclideanNorm_nonneg (Chapter06/Mass.lean:30, :42), IMRep (Submission.lean:61), IMRep.measure (:88), IsIntegerMultiplicity (:92)`
- `python3 -I verifier/gmt-compare.py contract_scope(Submission.lean, GMT.Ch07.main_theorem) -> the contract's opens + namespace GMT.Ch07 (used as the header of all scratch Lean files)`
- `lake env lean /tmp/dmcbr_cipi_v2/lean/E2E.lean -> exit 0, no warnings; #print axioms: slice theorem = propext, Classical.choice, Quot.sound + exactly its 5 declared siblings; parent = those + covector_norming, weight_nat, const_mass`
- `python3 -I _recursive_lean.lean_contract.validate_lean_statement on the 9 child types -> valid and unchanged`
- `independent reviewer subagent: re-ran the runtime's own _existing_lean_name_problem and _dependency_problem (both pass), recompiled E2E.lean (exit 0, all types byte-identical to the DAG and handoff), and checked all 9 accepted commits -> ACCEPT; its prose remarks are incorporated`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/OrderClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/issue-workers.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-d3a83e819f/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-d3a83e819f/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-93e0ab338f/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-93e0ab338f/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-93e0ab338f/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-a2d19864c9/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-a2d19864c9/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-a2d19864c9/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-bf84361bcd/decomposition-v1.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/store.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/shared_dag.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/dmcbr_cipi_v2/lean/E2E.lean`

The snapshot is compatible: the pins match and the snapshot contract is byte-identical to Submission.lean. The snapshot contains no cbr_cipi, regcomp_covector or dmcbr_cipi declaration; the reused declarations live only in their accepted candidate commits, each at exactly its frozen type and without sorry. Every library fact used by the new child's proof exists at the pinned revisions. The eight reused nodes are comparator-accepted with byte-identical types and were all accepted before this node's worker started at 00:50:35Z, so they pass the runtime name check even on attempt 1's stale snapshot. cbr_cipi_plane_halfspace_stokes, the rejected name, is not proposed: its three accepted children are reused and its one-line composition moves into the new child. The fresh name dmcbr_cipi_slice_integer_multiplicity is unused everywhere. The scratch E2E file proves the new child from exactly its five declared siblings, and proves the exact frozen parent type from the nine children plus const_mass, using only standard axioms besides the child stubs.
