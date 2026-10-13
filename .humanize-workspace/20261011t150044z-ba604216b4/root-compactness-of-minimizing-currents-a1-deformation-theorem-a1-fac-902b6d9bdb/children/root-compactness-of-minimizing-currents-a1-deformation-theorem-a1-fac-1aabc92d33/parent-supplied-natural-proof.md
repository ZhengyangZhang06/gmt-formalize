# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.face_integral_current-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.face_integral_current-a1.support_faces-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 6, proof of Theorem 5.1, displays (29)–(30) and (34) (book/chapter-06.txt lines 1862–1906), as written out in the parent-supplied proof of cmcdtfr_face_integral_current (its facts (F1)–(F2) and steps 1–5). This child is step 5 of that proof.
1. Setup by contradiction. Let x ∈ spt D and suppose that x ≠ Φ_p(y) for every p ∈ s with ∫_{Q₁}|w_p| ≠ 0 and every y ∈ Cⁿ := {y : 0 ≤ y_i ≤ 1 ∀ i}. Put s* := {p ∈ s : ∫_{Q₁}|w_p| ≠ 0} and Z := ⋃_{p∈s*} Φ_p(Cⁿ). The assumption says exactly x ∉ Z.
2. Z is compact. Cⁿ is compact: under the homeomorphism ℝⁿ = EuclideanSpace ℝ (Fin n) ≅ (Fin n → ℝ) (PiLp.homeomorph) it is the preimage of the product Π_i [0,1], which is compact (isCompact_univ_pi, isCompact_Icc). Each Φ_p is continuous (a constant plus a finite sum of y ↦ y_j e_{ι(j)}), so Φ_p(Cⁿ) is compact (IsCompact.image), and the finite union Z is compact (Finset.isCompact_biUnion). Hence Z is closed, ℝ^P ∖ Z is open and contains x, and there is r > 0 with ball(x, r) ∩ Z = ∅ (Metric.isOpen_iff).
3. The ball is admissible for the zero region. W := ball(x, r) is open; its closure is contained in closedBall(x, r) (closure_ball_subset_closedBall), which is compact because ℝ^P is a proper space (isCompact_closedBall); so closure W is a closed subset of a compact set and is compact. Trivially closure W ⊆ univ.
4. D vanishes on W. Let ω be a test n-form with tsupport ω ⊆ W. By hypothesis D(ω) = Σ_{p∈s} I_p with I_p := ∫_{Q₁} w_p(y)·ω(Φ_p(y))(E_p) dy; we show I_p = 0 for every p ∈ s (Finset.sum_eq_zero).
(a) If ∫_{Q₁}|w_p| = 0: the function |w_p| is nonnegative and integrable on Q₁ (w_p is), so its zero integral forces |w_p| = 0 almost everywhere on Q₁ (integral_eq_zero_iff_of_nonneg for volume restricted to Q₁). Then the integrand w_p(y)·ω(Φ_p y)(E_p) vanishes for a.e. y ∈ Q₁, and I_p = 0 (integral_eq_zero_of_ae).
(b) If ∫_{Q₁}|w_p| ≠ 0, then p ∈ s*. For y ∈ Q₁ we have 0 < y_i < 1, hence y ∈ Cⁿ and Φ_p(y) ∈ Z. Since W ∩ Z = ∅ and tsupport ω ⊆ W, Φ_p(y) ∉ tsupport ω, so ω(Φ_p(y)) = 0 (image_eq_zero_of_notMem_tsupport) and the integrand is 0 at every y ∈ Q₁. Hence I_p = 0 (setIntegral_eq_zero_of_forall_eq_zero).
Thus D(ω) = 0 for every such ω, i.e. D vanishes on W (GeometricCurrentOn.VanishesOn).
5. Contradiction. By steps 3–4, W is one of the open sets with compact closure contained in univ on which D vanishes, and x ∈ W; so x ∈ zeroRegion D. But x ∈ spt D = univ ∖ zeroRegion D. This contradiction shows that there are p ∈ s with ∫_{Q₁}|w_p| ≠ 0 and y ∈ Cⁿ with Φ_p(y) = x. ∎

## Key steps

1. If not, x ∉ Z := ⋃_{p∈s*} Φ_p([0,1]ⁿ), s* = {p ∈ s : ∫_{Q₁}|w_p| ≠ 0}.
2. Z is compact (compact cube, continuous Φ_p, finite union), hence closed; pick ball(x, r) disjoint from Z, whose closure is compact.
3. Faces with ∫_{Q₁}|w_p| = 0 contribute 0 since w_p = 0 a.e. on Q₁; faces in s* map Q₁ into Z, where every test form supported in the ball vanishes.
4. So D vanishes on the ball, x ∈ zeroRegion D, contradicting x ∈ spt D.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); git -C local-references/123e8435b4a2469b/mathlib rev-parse HEAD (25730c7c759d108ef87ab70af2342a196760f79d, matches manifest)`
- `rg -n 'cmcdtfrfic_' project mathlib/Mathlib -g '*.lean' (no match); grep -rn cmcdtfrfic lake-packages-25730c7c/simongmt (no match); python3 scan of runs/20261011T150044Z-ba604216b4/dag.json lean_name fields (1613 nodes, no cmcdtfrfic_ name)`
- `python3 scan of dag.json lean_statement fields containing covectorEuclideanNorm (accepted cmc_fc_sc_current_of_coeff_bound, cmc_fc_sc_testForm_coeff_bound, regcomp_covector_eval_orthonormal_le, cmr_coordinate_divergence_form, codim1_zsl_fl_divergence_lift found; none states coeff_bounds (ii) or the face divergence field)`
- `rg -n 'theorem (norm_integral_le_of_norm_le|integral_eq_zero_iff_of_nonneg|setIntegral_eq_zero_of_forall_eq_zero|norm_iteratedFDeriv_zero|basisFun_apply|abs_le_sqrt)' mathlib/Mathlib`
- `grep -rn 'trace_eq_sum_inner|succAbove_left_injective|strictMono_succAbove|Finset.isCompact_biUnion|contDiff_euclidean|hasFDerivAt_apply|def homeomorph|def apply|theorem le_opNorm|Integrable.mul_bdd' mathlib/Mathlib (all found; to_additive-generated names such as HasCompactSupport.exists_bound_of_continuous, image_eq_zero_of_notMem_tsupport and Finset.sum_le_sum_of_subset_of_nonneg confirmed by #check in Api.lean/Api2.lean)`
- `grep in lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/{Forms,Currents,Mass,CurrentLocalEquality}.lean for exteriorDerivative_apply, exteriorDerivativeTestOn, GeometricCurrentOn.boundary_apply, TestFormOnConverges, covectorEuclideanNorm, massAdmissibleOn, massOn, VanishesOn, zeroRegion, support (all found)`
- `sed -n 1840,1910p book/chapter-06.txt (Simon 5.1 displays (26)-(35))`
- `lake env lean /tmp/fic_decomp_q4/Types.lean and /tmp/fic_decomp_q4/Assembly4.lean (child types elaborate in the replayed contract scope; the four child types imply the selected frozen type; #print axioms: propext, Classical.choice, Quot.sound)`
- `lake env lean /tmp/fic_decomp_q4/C1.lean, C2.lean, C3.lean, C6.lean (complete scratch proofs of all four child types, C2 from C1; only standard axioms)`
- `validate_lean_statement from verifier/lean_contract.py (identical to the flow copy) on the four child types: accepted unchanged`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/WithLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/WithLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fin/SuccPred.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Fin/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-fac-902b6d9bdb/parent-child-handoff.json`
- `/tmp/fic_decomp_q4/Types.lean`
- `/tmp/fic_decomp_q4/Assembly4.lean`
- `/tmp/fic_decomp_q4/C1.lean`
- `/tmp/fic_decomp_q4/C2.lean`
- `/tmp/fic_decomp_q4/C3.lean`
- `/tmp/fic_decomp_q4/C6.lean`

The snapshot (project b4d606d, Mathlib 25730c7c) has the same Ch07 contract as the workspace, and Submission.lean equals the contract, so no face-current lemma exists at the proof base. No declaration, SimonGMT file or DAG node uses the prefix cmcdtfrfic_. Accepted declarations in other branches overlap only in part: cmc_fc_sc_current_of_coeff_bound, cmc_fc_sc_testForm_coeff_bound and regcomp_covector_eval_orthonormal_le would give coeff_bounds (i) and shorten the continuity step of current_exists. They are not reused, because coeff_bounds (ii) and divergence_field are new anyway. Mathlib and SimonGMT supply every tool the child proofs cite: trace_eq_sum_inner, contDiff_euclidean, PiLp.hasFDerivAt_apply, ContinuousAlternatingMap.apply and le_opNorm, exteriorDerivative_apply, Integrable.mul_bdd, norm_integral_le_of_norm_le, norm_iteratedFDeriv_zero, integral_eq_zero_iff_of_nonneg, setIntegral_eq_zero_of_forall_eq_zero, PiLp.homeomorph, Finset.isCompact_biUnion, Fin.succAbove_left_injective and Fin.strictMono_succAbove. All four child types elaborate in the comparator's replayed scope and pass the workflow validator. Scratch Lean proofs of all four children, and the assembly into the selected frozen type, compile with only propext, Classical.choice and Quot.sound.
