# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.face_replacement-a1.boundary_variation-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.face_replacement-a1.boundary_variation-a1.face_test_form-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 5 and 6 of the supplied proof of the selected theorem. Those steps build the cut-off χ around Kg = Φ_p(tsupport g) and the test form γ := χ·Σ_j g_j(p̃_p ·) ε_j, prove that γ is admissible, and compute its values on the face p, which feed face_divergence. These are the forms that realise the BV estimate of Simon Ch. 6, 2.35 and (28) (chapter-06.txt lines 606ff. and 1851–1857). Because χ = 1 on Kg, the field G(y) := χ(Φ_p y)·g(y) of parent step 6 equals g identically. So the face identity proved here is exactly the hypothesis of face_divergence with G := g. The ε_j come from the sibling face_covectors (Submission.cmcdtfrbv_face_covectors).

Notation. p = (ι, b), n := m + 1, e_l := EuclideanSpace.single l 1, Φ := Φ_p, Q₁ := (0,1)ⁿ, and |·| := covectorEuclideanNorm. Let π : Euclid P → Euclid n be π(x) := (x_{ι(j)} − b_{ι(j)})_j (Lean: WithLp.toLp 2 (fun j => x (ι j) - (b (ι j) : ℝ))). This is the parent's p̃_p. Throughout, C^∞ means ContDiff ℝ (⊤ : ℕ∞), the order of the hypothesis on g. In Lean write this order explicitly as (⊤ : ℕ∞); the scoped notation ∞ for it requires open scoped ContDiff.

1. The face map and its left inverse.
 - Φ is continuous: it is a constant plus a finite sum of the continuous maps y ↦ y_j • e_{ι(j)} (continuous_finsetSum, PiLp.continuous_apply).
 - π is C^∞. By contDiff_piLp it suffices that each coordinate x ↦ x_{ι(j)} − b_{ι(j)} is C^∞, and it is: a coordinate (contDiff_piLp_apply) minus a constant.
 - π(Φ(y)) = y for every y. The ι(j)-th coordinate of Φ(y) is b_{ι(j)} + Σ_{j'} y_{j'}·[ι(j) = ι(j')] = b_{ι(j)} + y_j, because ι is injective. (Lemmas: PiLp.add_apply, PiLp.toLp_apply, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, PiLp.single_apply, StrictMono.injective, Finset.sum_ite_eq.)
2. The compact set. K := Φ(tsupport g) is compact, as the continuous image of the compact set tsupport g (HasCompactSupport g). Also K ⊆ N, because tsupport g ⊆ Q₁ and Φ(Q₁) ⊆ N.
3. The cut-off.
 - N is open and K is compact, so there is r > 0 with cthickening(r, K) ⊆ N (IsCompact.exists_cthickening_subset_open).
 - Apply exists_contDiff_support_eq_eq_one_iff with order n := ⊤ : ℕ∞, i.e. C^∞, to the open set thickening(r, K) (isOpen_thickening) and the closed set K ⊆ thickening(r, K) (IsCompact.isClosed, self_subset_thickening). It gives a C^∞ map χ : Euclid P → ℝ with range in [0, 1], support χ = thickening(r, K), and χ(x) = 1 ⟺ x ∈ K.
 - tsupport χ = closure(thickening(r, K)) ⊆ cthickening(r, K) ⊆ N (closure_thickening_subset_cthickening).
 - χ has compact support: tsupport χ is closed and lies in the compact set cthickening(r, K) (IsCompact.cthickening, IsCompact.of_isClosed_subset).
 The parent used the radii r, 2r and 3r so that χ = 1 near K. Here χ = 1 on K suffices.
4. The covectors. Apply face_covectors to P, m and ι and choose ε : Fin n → Covector (Euclid P) m such that, for all c : Fin n → ℝ and i ∈ Fin n:
 (a) |Σ_j c_j ε_j| = √(Σ_j c_j²);
 (b) (Σ_{j'} c_{j'} ε_{j'})(fun l => e_{ι(i.succAbove l)}) = (−1)^i c_i.
5. The form. Define γ(x) := Σ_j (χ(x)·g(π x)_j) • ε_j (Lean: fun x => ∑ j, (χ x * g (π x) j) • ε j).
 - γ is C^∞. Each coefficient x ↦ χ(x)·g(π x)_j is the product (ContDiff.mul) of χ and the j-th coordinate (contDiff_piLp_apply) of g ∘ π (ContDiff.comp), so it is C^∞. Multiplying by the constant covector ε_j (ContDiff.smul_const) and taking the finite sum (ContDiff.sum) keep it C^∞.
 - support γ ⊆ support χ: if χ(x) = 0, every coefficient vanishes and γ(x) = 0. Hence γ has compact support (HasCompactSupport.mono), and tsupport γ ⊆ tsupport χ ⊆ N (closure_mono and step 3).
 - So γ is smooth with compact support and tsupport γ ⊆ univ. Together with these proofs it is an element of TestFormOn univ m whose underlying form is γ.
6. The norm bound. Fix x and put c_j := χ(x)·g(π x)_j. By (a), |γ(x)| = √(Σ_j c_j²). Now Σ_j c_j² = χ(x)²·Σ_j g(π x)_j² = χ(x)²·‖g(π x)‖² (EuclideanSpace.real_norm_sq_eq). Since 0 ≤ χ(x) ≤ 1 and 0 ≤ ‖g(π x)‖ ≤ 1, this is at most 1. Hence |γ(x)| ≤ 1 (Real.sqrt_le_one).
7. The face values. Fix y ∈ Euclid n and i ∈ Fin n. Apply (b) with c_j := χ(Φ y)·g(π(Φ y))_j, and use π(Φ y) = y (step 1):
 γ(Φ y)(fun l => e_{ι(i.succAbove l)}) = (−1)^i·χ(Φ y)·g(y)_i.
 Multiply by (−1)^i and use ((−1)^i)² = 1: (−1)^i·γ(Φ y)(fun l => e_{ι(i.succAbove l)}) = χ(Φ y)·g(y)_i.
 - If y ∈ tsupport g, then Φ y ∈ K, so χ(Φ y) = 1 and the right side is g(y)_i.
 - If y ∉ tsupport g, then g(y) = 0 (image_eq_zero_of_notMem_tsupport), and both sides are 0.
 Hence g(y)_i = (−1)^i·γ(Φ y)(fun l => e_{ι(i.succAbove l)}) for all y and i.
8. By steps 5–7, γ ∈ TestFormOn univ m satisfies tsupport γ ⊆ N, |γ(x)| ≤ 1 for every x, and the face identity. No case split is needed for tsupport g = ∅ (then K = ∅ and χ = 0) or for m = 0. ∎

## Key steps

1. π(x) := (x_{ι(j)} − b_{ι(j)})_j is C^∞ with π ∘ Φ_p = id, and K := Φ_p(tsupport g) is a compact subset of N.
2. Choose r > 0 with cthickening(r, K) ⊆ N. A C^∞ cut-off χ with values in [0,1], support χ = thickening(r, K) and χ = 1 exactly on K has compact tsupport contained in N.
3. γ(x) := Σ_j χ(x)·g(π x)_j·ε_j, with ε from face_covectors, is a test m-form with tsupport γ ⊆ N and |γ(x)| = |χ(x)|·‖g(π x)‖ ≤ 1.
4. By face_covectors (b) and χ = 1 on K, (−1)^i·γ(Φ_p y)(E_p ∘ succAbove i) = χ(Φ_p y)·g(y)_i = g(y)_i for all y and i.

## Reference use

### local-project

Queries:
- `cat SNAPSHOT/manifest.json (project_commit b4d606db, mathlib_commit 25730c7c); git -C SNAPSHOT/mathlib rev-parse HEAD (25730c7c759d108ef87ab70af2342a196760f79d); md5sum GMT/Ch07/Submission.lean GMT/Ch07/Contract.lean (identical)`
- `rg -n -l 'dimred_mbl_dtfrbv|cmcdtfrbv_face_covectors|cmr_cc_det_covector' SNAPSHOT/mathlib/Mathlib SNAPSHOT/project -g '*.lean' (no match); rg -n -l dimred_mbl_dtfrbv_face_neighbourhoods / _massOn_disjoint_sum_le / _face_test_form over SNAPSHOT/project, lake-packages-25730c7c/simongmt and workspace GMT (no match); grep -c of each new name in RUN/dag.json (0)`
- `python3 -I scans of RUN/dag.json: status, candidate_commit, updated_at, depends_on and lean_statement of cmcdtfrbv_face_covectors (accepted, d7f25773, 2026-10-14T01:14:25Z), cmr_cc_det_covector_exists (accepted, fee01ff8) and cmr_cc_det_covector_basis_kronecker (accepted, 00788882); this node (decomposing, attempt 2, 01:29:31Z); the twin cmcdtfr_boundary_variation children (cmcdtfrbv_face_neighbourhoods and cmcdtfrbv_massOn_disjoint_sum_le: comparing at 01:30Z, accepted only after this attempt began; same types as two new children); byte equality of the reused frozen types and of the selected type with the twin type`
- `cat of the face_covectors node files accepted-candidate.json, isolated-comparator-result.json (passed) and lean-audit-v1.json (machine-leaf, comparator_passed, Submission.cmcdtfrbv_face_covectors); python3 -I check that the three reused natural proofs and key steps are verbatim from their parent-child-handoff.json`
- `grep/sed of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_decompose depth guard, _existing_lean_name_problem, _accepted_checkpoint, _solve_children, _install_parent_supplied_child_handoff early return for accepted children, _solve resume of accepted candidates), store.py (refresh, accepted-status immutability), decomposition_recovery.py, prompts.py DECOMPOSITION_AUDIT, lean_contract.validate_lean_statement; swarm-project.json (max_depth 6, max_children 12, decomposition_attempts 5)`
- `python3 -I contract_scope(GMT/Ch07/Contract.lean, GMT.Ch07.main_theorem) from verifier/gmt-compare.py: open Filter Function Set MeasureTheory Metric; open scoped ENNReal Topology; namespace GMT.Ch07; open Poincare.SimonGMT.Chapter06; open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt); noncomputable section; end`
- `sed/grep of SimonGMT Chapter06 Mass.lean (covectorEuclideanNorm, covectorEuclideanNorm_zero, massAdmissibleOn, GeometricCurrentOn.massOn, .mass, .massOn_mono, .le_massOn), Currents.lean (TestFormOn, GeometricCurrentOn, boundary, tsupport_exteriorDerivative_subset), CurrentLocalEquality.lean (support); grep 'abbrev Euclid' GMT/Ch07/Contract.lean (EuclideanSpace ℝ (Fin P))`
- `rg -n 'theorem exists_contDiff_support_eq_eq_one_iff' (Geometry/Manifold/PartitionOfUnity.lean:789) and 'closure_thickening_subset_cthickening' (Topology/MetricSpace/Thickening.lean:293) in SNAPSHOT/mathlib`
- `sed -n 1835,1900p and 600,625p of book/chapter-06.txt: Simon Ch. 6 §5 (26)–(33) and Remark 2.35, the sources cited in the child proofs`
- `lake env lean on /tmp/dmfrbv2/lean/{Types,Assembly,FN,MD,FTF,FC}.lean on /tmp/dmfrbv2/gen/{TypesV2,AsmV2,FNV2,MDV2,FCV2,FTFV2,E2EV2}.lean, generated by /tmp/dmfrbv2/scripts/gen_lean.py from the exact lean_statement strings of the decomposition and dag.json; and on /tmp/dmfrbv2/gen2/FTFV2NoScope.lean (explicit (⊤ : ℕ∞), no open scoped ContDiff); #print axioms reports only propext, Classical.choice and Quot.sound`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/swarm-project.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-9ba692d275/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-9ba692d275/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-fac-488f890568/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-fac-488f890568/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-fac-488f890568/lean-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-fac-488f890568/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-coo-498906c61d/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-coo-40c536ad5f/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/store.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/lean_contract.py`
- `/tmp/dmfrbv2/gen/TypesV2.lean`
- `/tmp/dmfrbv2/gen/AsmV2.lean`
- `/tmp/dmfrbv2/gen/FNV2.lean`
- `/tmp/dmfrbv2/gen/MDV2.lean`
- `/tmp/dmfrbv2/gen/FCV2.lean`
- `/tmp/dmfrbv2/gen/FTFV2.lean`
- `/tmp/dmfrbv2/gen/E2EV2.lean`
- `/tmp/dmfrbv2/gen2/FTFV2NoScope.lean`

Pins match: project b4d606db, Mathlib 25730c7c and SimonGMT 2b36630. Submission.lean is byte-identical to the frozen contract. Neither the snapshot project nor Mathlib contains lattice-face neighbourhoods, face test forms or local-mass superadditivity, so these three obligations are new. They get fresh dimred_mbl_dtfrbv_* names, which collide with nothing in the DAG, the snapshot, Mathlib, SimonGMT or the workspace. The twin's cmcdtfrbv_face_neighbourhoods and cmcdtfrbv_massOn_disjoint_sum_le have identical types but were accepted only after this attempt began, so they are not reused. cmcdtfrbv_face_covectors, cmr_cc_det_covector_exists and cmr_cc_det_covector_basis_kronecker are accepted checkpoints whose frozen types are byte-identical to the proposed ones. Their natural proofs are reproduced verbatim. face_covectors became accepted at 01:14:25Z, before this attempt began, so the attempt-1 name objection no longer applies. Every cited Mathlib or SimonGMT name resolves under the frozen imports. The generated type, assembly, leaf and end-to-end files compile with only the standard axioms.
