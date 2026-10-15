# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.boundary_variation-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.boundary_variation-a1.face_neighbourhoods-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1 of the supplied proof of cmcdtfr_boundary_variation (Simon Ch. 6, proof of 5.1: the open faces F̆_p get pairwise disjoint neighbourhoods N_p), for an arbitrary dimension k. The threshold δ_p(t) = min(1, min_j min(t_j, 1 − t_j)) of the parent proof is written as finitely many strict inequalities. The separation property (S) is the hypothesis; in the parent it is part (c) of cmcdtfr_face_geometry.

Notation. e_l := EuclideanSpace.single l 1 ∈ ℝ^P; its l'-th coordinate is 1 if l' = l and 0 otherwise. x_l denotes the l-th coordinate of x ∈ ℝ^P, so (Φ_p y)_l = b_l + Σ_j y_j·[ι(j) = l]. For an index pair p = (ι, b) define π_p : ℝ^P → Euclid k by π_p(x) := (x_{ι(j)} − b_{ι(j)})_j (Lean: WithLp.toLp 2 (fun j => x (ι j) − b (ι j))) and d_p(x) := dist(x, Φ_p(π_p(x))) ≥ 0.

1. Continuity. Φ_p is continuous: it is a constant plus the finite sum of the continuous maps y ↦ y_j·e_{ι(j)}. π_p is continuous, because each coordinate x ↦ x_{ι(j)} − b_{ι(j)} is continuous and a map into Euclid k is continuous when all its coordinates are. Hence x ↦ π_p(x)_j and x ↦ d_p(x) are continuous.
2. Left inverse. If ι is strictly increasing, hence injective, then π_p(Φ_p y) = y for every y ∈ Euclid k. Indeed (Φ_p y)_{ι(i)} = b_{ι(i)} + Σ_j y_j·[ι(j) = ι(i)] = b_{ι(i)} + y_i, since ι(j) = ι(i) only for j = i.
3. Definition. Let N_p be the set of x ∈ ℝ^P satisfying all of: 0 < π_p(x)_j and π_p(x)_j < 1 for every j; 2·d_p(x) < 1; and 2·d_p(x) < min(π_p(x)_j, 1 − π_p(x)_j) for every j. The same formula is used for every index pair. If x ∈ N_p, then π_p(x) ∈ Q₁.
4. N_p is open. N_p is the intersection of the finitely many sets {x : 0 < π_p(x)_j}, {x : π_p(x)_j < 1}, {x : 2d_p(x) < 1} and {x : 2d_p(x) < min(π_p(x)_j, 1 − π_p(x)_j)}, for j ∈ Fin k. Each has the form {x : f(x) < h(x)} with f, h continuous by step 1 (a min of continuous functions is continuous), so each is open (isOpen_lt). A finite intersection of open sets is open (isOpen_iInter_of_finite over the finite type Fin k, and IsOpen.inter).
5. The open face lies in N_p. Let ι be strictly increasing, y ∈ Q₁ and x := Φ_p(y). By step 2, π_p(x) = y ∈ Q₁ and d_p(x) = dist(x, Φ_p(y)) = dist(x, x) = 0. So 2d_p(x) = 0 < 1, and 2d_p(x) = 0 < min(y_j, 1 − y_j) for every j because 0 < y_j < 1. Hence x ∈ N_p.
6. Key inequality. Let p and q have strictly increasing first components, p ≠ q, let x ∈ N_p, t := π_p(x), and y' ∈ Cᵏ. Then 2d_p(x) < dist(Φ_p(t), Φ_q(y')). Indeed t ∈ Q₁ by step 3, so (S) applies to p, q, t, y'. If 1 ≤ dist(Φ_p t, Φ_q y'), use 2d_p(x) < 1. If min(t_j, 1 − t_j) ≤ dist(Φ_p t, Φ_q y') for some j, use 2d_p(x) < min(t_j, 1 − t_j).
7. Other closed faces avoid N_p. Let p, q be as in step 6, y ∈ Cᵏ, and suppose x := Φ_q(y) ∈ N_p. With t := π_p(x), step 6 (y' := y) gives 2d_p(x) < dist(Φ_p(t), x) = dist(x, Φ_p(π_p x)) = d_p(x). This is impossible since d_p(x) ≥ 0. Hence Φ_q(y) ∉ N_p.
8. Disjointness. Let p, q be as in step 6 and suppose x ∈ N_p ∩ N_q. Put t := π_p(x) ∈ Q₁, t' := π_q(x) ∈ Q₁, y₁ := Φ_p(t), y₂ := Φ_q(t'), d₁ := d_p(x) = dist(x, y₁), d₂ := d_q(x) = dist(x, y₂) and D := dist(y₁, y₂). Since t' ∈ Q₁ ⊆ Cᵏ, step 6 for (p, q, x, y' := t') gives 2d₁ < D. Since t ∈ Q₁ ⊆ Cᵏ and q ≠ p, step 6 with p and q exchanged (x ∈ N_q, y' := t) gives 2d₂ < dist(y₂, y₁) = D. By the triangle inequality, D ≤ dist(y₁, x) + dist(x, y₂) = d₁ + d₂ < D/2 + D/2 = D, a contradiction. So N_p ∩ N_q = ∅, i.e. Disjoint (N p) (N q).
9. Steps 4, 5, 7 and 8 give all required properties, for every p with strictly increasing first component and every such q ≠ p. For k = 0 the conditions indexed by j are vacuous and Q₁ = Cᵏ is the one-point space; the proof is unchanged, since only the alternative 1 ≤ dist of (S) can occur. ∎

## Key steps

1. π_p(x) := (x_{ι(j)} − b_{ι(j)})_j is continuous and, for strictly increasing ι, a left inverse of Φ_p.
2. N_p := {x : π_p(x) ∈ Q₁, 2·dist(x, Φ_p(π_p x)) < 1 and < min(π_p(x)_j, 1 − π_p(x)_j) for all j} is a finite intersection of strict inequalities between continuous functions, hence open, and contains Φ_p(Q₁).
3. (S) gives 2·dist(x, Φ_p(π_p x)) < dist(Φ_p(π_p x), Φ_q y') for x ∈ N_p, q ≠ p and y' ∈ [0,1]^k.
4. Taking Φ_q y' = x shows Φ_q([0,1]^k) ∩ N_p = ∅. Applying the inequality for (p, q) and (q, p) together with the triangle inequality shows N_p ∩ N_q = ∅.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); git -C local-references/123e8435b4a2469b/mathlib rev-parse HEAD (25730c7c759d108ef87ab70af2342a196760f79d, matches manifest)`
- `rg -n 'cmcdtfrbv' project mathlib/Mathlib -g '*.lean' (no match)`
- `python3 scan of runs/20261011T150044Z-ba604216b4/dag.json lean_name/lean_statement over 1598 nodes: no cmcdtfrbv_* names; patterns LinearMap.trace|removeNth|PairwiseDisjoint|massOn A + massOn B|boundary.support ⊆|0 < T.massOn over accepted nodes (found cmr_cc_det_covector_exists, cmr_cc_det_covector_basis_kronecker, cmr_coordinate_divergence_form, dgcr_bwd_coordinate_covector, dgcr_bwd_extDeriv_smul_const, codim1_zsl_fl_divergence_lift, subadditive lcmp_massOn_le_add_of_eval_eq/cmc_fcl_massOn_le_add, codim1_rdo_massOn_pos_of_mem_support)`
- `rg -n 'theorem exists_contDiff_support_eq_eq_one_iff' mathlib/Mathlib (Geometry/Manifold/PartitionOfUnity.lean:789)`
- `rg -n 'exists_cthickening_subset_open|theorem cthickening_subset_thickening|theorem closure_thickening_subset_cthickening|theorem self_subset_thickening' mathlib/Mathlib/Topology/MetricSpace/Thickening.lean (:426, :261, :293, :309)`
- `rg -n 'theorem trace_eq_matrix_trace' mathlib/Mathlib/LinearAlgebra (Trace.lean:87); rg -n 'theorem basisFun_apply|theorem basisFun_repr' mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean (:806, :810); rg -n 'def removeNth' mathlib/Mathlib/Data/Fin/Tuple/Basic.lean (:845); rg -n 'theorem fderiv_const_mul' mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean (:379)`
- `rg -n 'support_sum|mulSupport_prod' mathlib/Mathlib/Algebra/BigOperators (Group/Finset/Lemmas.lean:56 mulSupport_prod, additive Finset.support_sum); rg -n 'theorem setIntegral_eq_zero_of_forall_eq_zero|theorem setIntegral_congr_fun ' mathlib/Mathlib/MeasureTheory (Integral/Bochner/Set.lean:73)`
- `grep -n in lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06: Forms.lean:119 exteriorDerivative_apply; Currents.lean:182 tsupport_exteriorDerivative_subset, :193 exteriorDerivativeTestOn, :325/:333 GeometricCurrentOn.boundary(_apply); Mass.lean:30 covectorEuclideanNorm, :57 massAdmissibleOn, :68 massOn, :74 mass, :81 massOn_mono, :90 le_massOn; CurrentLocalEquality.lean:101/:108/:115 VanishesOn, zeroRegion, support`
- `grep -n 'def _existing_lean_name_problem' -A 40; sed -n 1820,1860p and 4370,4395p /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py (accepted declarations are reused by identical lean_name and stripped lean_statement)`
- `lake env lean /tmp/bvdecomp/lean/Types.lean (8 child types plus the selected type, each wrapped as verifier/gmt-compare.py child_modules does after the replayed contract scope; only sorry warnings)`
- `python3 -I /tmp/bvdecomp/scripts/validate.py (verifier/lean_contract.py validate_lean_statement: all 8 valid; new names unused; reused names accepted with identical statements)`
- `lake env lean /tmp/bvdecomp/lean/Assembly.lean (BVAsm.check, BVAsm.c4_of, BVAsm.c3_of; #print axioms: propext, Classical.choice, Quot.sound)`
- `lake env lean /tmp/bvdecomp/lean/Probe.lean, Probe2.lean, Probe3.lean (#check of every lemma cited by the child proofs after import GMT.Ch07.Submission; Function.support_finset_sum is unknown, so Finset.support_sum is cited instead)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-fac-6211ac03c6/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-fac-6211ac03c6/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-coo-498906c61d/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-coo-498906c61d/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-coo-40c536ad5f/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-coo-40c536ad5f/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1/decomposition-v1.json`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/bvdecomp/lean/Types.lean`
- `/tmp/bvdecomp/lean/Assembly.lean`
- `/tmp/bvdecomp/lean/Probe.lean`
- `/tmp/bvdecomp/lean/Probe2.lean`
- `/tmp/bvdecomp/lean/Probe3.lean`

The snapshot (project b4d606db, Mathlib 25730c7c) has the same Ch07 contract as the workspace, and Submission.lean equals the contract. Neither the snapshot nor the DAG contains a cmcdtfrbv_ declaration, so all six new names are free. The DAG holds the accepted declarations cmr_cc_det_covector_exists and cmr_cc_det_covector_basis_kronecker. They give the determinant covectors dx^J and their Kronecker property with exactly the needed frozen types, so they are reused, which the controller's reuse rule permits. No accepted node matches the other children. Only subadditive mass lemmas exist, not superadditivity over disjoint regions. Nothing localizes spt ∂Q₀. cmr_coordinate_divergence_form has a norm bound K instead of 1, dgcr_bwd_coordinate_covector is limited to P = m + 1, and codim1_zsl_fl_divergence_lift carries a factor K⁻¹. These therefore become new children. The import closure of GMT.Ch07.Submission supplies every tool cited by the child proofs. From Mathlib: the smooth Urysohn lemma, the cthickening/thickening lemmas, trace_eq_matrix_trace with basisFun, Fin.removeNth/succAbove lemmas, fderiv_const_mul, Finset.support_sum and the set-integral lemmas. From SimonGMT: exteriorDerivative_apply, tsupport_exteriorDerivative_subset, massAdmissibleOn/massOn/le_massOn/massOn_mono and support/zeroRegion. In Lean, all eight types elaborate in the comparator scope and pass validation. Three implications compile with only propext, Classical.choice and Quot.sound: (1) the frozen face_geometry type plus face_neighbourhoods, boundary_support_faces, divergence_test_form and mass_disjoint_sum imply the selected frozen type; (2) face_covectors and cutoff_field imply divergence_test_form; (3) the two reused types imply face_covectors.
