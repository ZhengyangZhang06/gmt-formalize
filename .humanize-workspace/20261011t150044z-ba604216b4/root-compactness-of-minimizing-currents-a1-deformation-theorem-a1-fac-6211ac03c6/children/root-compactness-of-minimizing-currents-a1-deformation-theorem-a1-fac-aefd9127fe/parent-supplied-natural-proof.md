# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.boundary_variation-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.boundary_variation-a1.divergence_test_form-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 5–6 of the supplied proof of cmcdtfr_boundary_variation, which build γ(x) := χ(x) Σ_j g_j(π x) ε_j and compute its exterior derivative. Here γ is assembled from the siblings face_covectors (the covectors ε_j) and cutoff_field (the field G = χ·(g∘π)).

Notation. e_l := EuclideanSpace.single l 1, E := (fun j => e_{ι(j)}) = (e_{ι(0)}, …, e_{ι(m)}), and x₀ := Φ_p(y). By definition Fin.removeNth i E = (fun k => E(i.succAbove k)) = (fun k => e_{ι(i.succAbove k)}).

1. Apply face_covectors to ι. It gives covectors ε_0, …, ε_m such that, for all c : Fin (m+1) → ℝ and all j: (a) covectorEuclideanNorm(Σ_j c_j ε_j) = √(Σ_j c_j²); (b) (Σ_{j'} c_{j'} ε_{j'})(fun k => e_{ι(j.succAbove k)}) = (−1)^j c_j.
2. Apply cutoff_field to (P, m, p, N, g). It gives a C^∞ map G : ℝ^P → Euclid n with compact support, tsupport G ⊆ N and ‖G(x)‖ ≤ 1, such that Σ_a D(G_a)(Φ_p y)(e_{ι(a)}) = trace(Dg(y)) for y ∈ Q₁, where G_a(x) := G(x)_a.
3. Definition. ω(x) := Σ_j G_j(x)·ε_j ∈ Covector(ℝ^P, m).
4. Smoothness. Each G_j = (v ↦ v_j)∘G is C^∞, as the composition with the continuous linear coordinate functional EuclideanSpace.proj j. Hence x ↦ G_j(x)·ε_j is C^∞ (ContDiff.smul with the constant ε_j), and so is the finite sum ω (ContDiff.sum).
5. Support. If G(x) = 0 then every G_j(x) = 0 and ω(x) = 0. So support ω ⊆ support G and tsupport ω ⊆ tsupport G ⊆ N. ω has compact support (HasCompactSupport.mono'), since tsupport ω is a closed subset of the compact tsupport G. Hence ω is a test form with tsupport ω ⊆ univ: γ := ω ∈ TestFormOn univ m, and tsupport γ ⊆ N.
6. Norm. Fix x. By (a) with c_j := G_j(x), covectorEuclideanNorm(γ(x)) = √(Σ_j G_j(x)²) = ‖G(x)‖ (EuclideanSpace.norm_eq and |t|² = t²) ≤ 1.
7. Exterior derivative. Let y ∈ Q₁.
- γ is C^∞, hence differentiable at x₀. The coordinate formula (SimonGMT exteriorDerivative_apply) gives dγ(x₀)(E) = Σ_i (−1)^i·D[x ↦ γ(x)(Fin.removeNth i E)](x₀)(e_{ι(i)}).
- By (b) with c_j := G_j(x) and j := i, γ(x)(Fin.removeNth i E) = (−1)^i G_i(x) for every x. So the i-th function differentiated is (−1)^i·G_i. Its derivative at x₀ is (−1)^i·D(G_i)(x₀) (fderiv_const_mul; G_i is differentiable).
- So the i-th term is (−1)^i·(−1)^i·D(G_i)(x₀)(e_{ι(i)}) = D(G_i)(x₀)(e_{ι(i)}), since ((−1)^i)² = 1.
- Summing over i and using step 2: dγ(Φ_p y)(E) = Σ_i D(G_i)(Φ_p y)(e_{ι(i)}) = trace(Dg(y)).
8. Steps 5–7 give the three required properties. ∎

## Key steps

1. Take ε_j from face_covectors (for ι) and G from cutoff_field, and set γ(x) := Σ_j G_j(x)·ε_j.
2. γ is C^∞ with tsupport γ ⊆ tsupport G ⊆ N compact. By the norm identity, covectorEuclideanNorm(γ(x)) = ‖G(x)‖ ≤ 1.
3. The face evaluation gives γ(x)(removeNth i E) = (−1)^i G_i(x). Then exteriorDerivative_apply gives dγ(Φ_p y)(E) = Σ_i D(G_i)(Φ_p y)(e_{ι(i)}) = trace Dg(y).

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
