# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.face_replacement-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.face_replacement-a1.face_representation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 6, proof of 5.1, displays (26)–(28) and (33), in the form of steps 2–3 of the parent proof: because Q is integer multiplicity, the face densities are read off from an IMRep of Q (using (IMC)(a)) instead of the constancy-theorem argument. Dependencies: FG = sibling dor_lmb_fcd_fr_face_geometry; PO = sibling dor_lmb_fcd_fr_plane_orientation; CC = sibling dor_lmb_fcd_fr_coordinate_covectors; C1 = reused sibling dor_imrep_massOn_eq_measure_and_support; IMC = reused sibling cmc_imRep_locality_restrict_sub (part (a)). For p = (z, ι) ∈ s: A_p := Φ_p(Q₁), F_p the closed face, e_p = (e_{ι(0)}, …, e_{ι(m)}).

1. Faces (FG). For p ∈ s: Φ_p(y) ∈ F_p for y in the closed cube, in particular A_p ⊆ F_p (FG(5)); F_p is closed (FG(8)) and bounded (FG(7)), hence compact; Φ_p is an isometry (FG(6)), hence a closed and measurable embedding, so A_p is Borel; for q ∈ s, q ≠ p, A_p ∩ F_q = ∅ (FG(9)), so the A_p (p ∈ s) are pairwise disjoint. By FG(3), Hⁿ⌞F_p = Φ_p#(volume⌞Q₁); hence for every Borel h : ℝ^P → ℝ, h∘Φ_p is integrable on Q₁ iff h is integrable for Hⁿ⌞F_p (MeasurableEmbedding.integrable_map_iff), and ∫_{F_p} h dHⁿ = ∫_{Q₁} h(Φ_p(y)) dy (FG(4)).

2. An IMRep and its measure. Since Q is integer multiplicity, there is an IMRep R = (M, θ, ξ) in univ representing Q: M is Borel, θ : ℝ^P → ℕ is Borel with θ ≥ 1 on M and ∫⁻_{M∩K'} θ dHⁿ < ∞ for every compact K', ξ is AE-strongly measurable for Hⁿ⌞M, and Q(ω) = ∫_M θ(x) ξ(x)(ω(x)) dHⁿ(x) for every test form ω. Let μ := R.measure = θ·Hⁿ⌞M, so μ(B) = ∫⁻_{M∩B} θ dHⁿ for Borel B. By C1 (U = univ is open), M_W(Q) = μ(W) for every open W; in particular M(Q) = M_{ℝ^P}(Q) = μ(ℝ^P). For compact K', Hⁿ(M ∩ K') ≤ ∫⁻_{M∩K'} θ dHⁿ < ∞ (θ ≥ 1 on M).

3. M is carried by the open faces. W₀ := ℝ^P ∖ E is open (E closed). If ω is admissible for M_{W₀}(Q), then tsupport ω ⊆ W₀ is disjoint from E, so Q(ω) = 0 by hypothesis; hence M_{W₀}(Q) = 0, so μ(W₀) = ∫⁻_{M∖E} θ dHⁿ = 0, and as θ ≥ 1 on M, Hⁿ(M ∖ E) = 0. By hypothesis and Borel measurability of E, Hⁿ(E ∖ ⋃_{p∈s} A_p) = 0 (Measure.restrict_apply'). Let M_p := M ∩ A_p (Borel, pairwise disjoint). Then Hⁿ(M ∖ ⋃_{p∈s} M_p) ≤ Hⁿ(M ∖ E) + Hⁿ(E ∖ ⋃_p A_p) = 0.

4. Orientation on each face. Fix p = (z, ι) ∈ s. (a) By the IMRep field orients, for Hⁿ-a.e. x ∈ M, and hence for Hⁿ-a.e. x ∈ M_p ⊆ M, there is a linear subspace Q_x such that M has approximate tangent space Q_x at x and ξ(x) is a unit orientation of Q_x. (b) By IMC(a), applied with U := univ and the Borel sets M_p ⊆ M (finiteness hypothesis from step 2), for Hⁿ-a.e. x ∈ M_p and every subspace Q', M_p has approximate tangent space Q' at x iff M does. (c) Hence for Hⁿ-a.e. x ∈ M_p, M_p has approximate tangent space Q_x at x and ξ(x) is a unit orientation of Q_x. Every a ∈ M_p ⊆ A_p ⊆ F_p satisfies a_i = z_i for i ∉ range ι, and so does x ∈ M_p; thus a_i = x_i for all a ∈ M_p and i ∉ range ι. By PO (with A := M_p), for Hⁿ-a.e. x ∈ M_p there is ε(x) ∈ {1, −1} with ξ(x)(α) = ε(x) α(e_p) for every n-covector α.

5. A Borel sign. By CC with k := n there is an n-covector α_p := dx^ι with α_p(e_p) = 1 (CC (i) with I = J = ι, ι strictly increasing). The function x ↦ ξ(x)(α_p) is AE-strongly measurable for Hⁿ⌞M (ξ is, and evaluation at the fixed covector α_p is a continuous linear map on MultiVector P n), so it agrees Hⁿ⌞M-a.e. with a Borel function h_p (AEStronglyMeasurable.mk, or AEMeasurable.mk). Let σ_p(x) := 1 if h_p(x) ≥ 0 and σ_p(x) := −1 otherwise (Borel). Hⁿ⌞M-a.e. statements hold Hⁿ⌞M_p-a.e. (M_p ⊆ M), so for Hⁿ-a.e. x ∈ M_p step 4 gives ξ(x)(α_p) = ε(x)·α_p(e_p) = ε(x) ∈ {1, −1} and h_p(x) = ξ(x)(α_p); hence σ_p(x) = ε(x) and ξ(x)(α) = σ_p(x)·α(e_p) for every α.

6. The densities. For p ∈ s define f_p(x) := θ(x) σ_p(x) 1_{M_p}(x) on ℝ^P and u_p(y) := θ(Φ_p(y)) σ_p(Φ_p(y)) 1_M(Φ_p(y)) on ℝⁿ; for p ∉ s put u_p := 0. Every value of u_p is an integer (θ ∈ ℕ, σ_p ∈ {1, −1}, indicator ∈ {0, 1}). For y ∈ Q₁, Φ_p(y) ∈ A_p, so 1_M(Φ_p(y)) = 1_{M_p}(Φ_p(y)) and u_p(y) = f_p(Φ_p(y)).

7. Integrability and the mass bound. f_p is Borel with |f_p| = θ·1_{M_p}, and since M_p ⊆ F_p, ∫⁻_{F_p} |f_p| dHⁿ = ∫⁻_{M_p} θ dHⁿ ≤ ∫⁻_{M∩F_p} θ dHⁿ < ∞ (step 2, F_p compact); so f_p is Hⁿ⌞F_p-integrable. By step 1 (with h := f_p and h := |f_p|) and step 6, u_p is integrable on Q₁ and ∫_{Q₁}|u_p(y)| dy = ∫_{F_p}|f_p| dHⁿ = ∫_{M_p} θ dHⁿ = μ(A_p).toReal, where μ(A_p) = ∫⁻_{M∩A_p} θ dHⁿ < ∞. Therefore ENNReal.ofReal(Σ_{p∈s} ∫_{Q₁}|u_p|) = Σ_{p∈s} ofReal(μ(A_p).toReal) = Σ_{p∈s} μ(A_p) (ENNReal.ofReal_sum_of_nonneg; each μ(A_p) finite) = μ(⋃_{p∈s} A_p) (disjoint Borel sets) ≤ μ(ℝ^P) = M(Q) (step 2).

8. The representation. Let ω be a test n-form and g(x) := θ(x) ξ(x)(ω(x)); g is AE-strongly measurable for Hⁿ⌞M. For p ∈ s, by step 5, g(x) = f_p(x) ω(x)(e_p) for Hⁿ-a.e. x ∈ M_p, and |ω(x)(e_p)| ≤ sup_w ‖ω(w)‖ < ∞ (ω continuous with compact support, ‖e_{ι(k)}‖ = 1), so g is integrable on M_p (θ is integrable on M_p by step 7). By step 3, M and ⋃_{p∈s} M_p differ by an Hⁿ-null set, and the M_p are pairwise disjoint Borel sets; hence Q(ω) = ∫_M g dHⁿ = ∫_{⋃_p M_p} g dHⁿ = Σ_{p∈s} ∫_{M_p} g dHⁿ (setIntegral_congr_set, integral_biUnion_finset) = Σ_{p∈s} ∫_{M_p} f_p(x) ω(x)(e_p) dHⁿ(x). Since f_p vanishes off M_p ⊆ F_p, ∫_{M_p} f_p ω(·)(e_p) dHⁿ = ∫_{F_p} f_p ω(·)(e_p) dHⁿ = ∫_{Q₁} f_p(Φ_p(y)) ω(Φ_p(y))(e_p) dy (FG(4)) = ∫_{Q₁} u_p(y) ω(Φ_p(y))(e_p) dy (step 6). Summing over p ∈ s gives Q(ω) = Σ_{p∈s} ∫_{Q₁} u_p(y) ω(Φ_p(y))(e_p) dy. Together with steps 6 and 7 this proves all claims. ∎

## Key steps

1. C1: μ_Q(ℝ^P ∖ E) = M_{ℝ^P∖E}(Q) = 0, so the carrier M of an IMRep of Q lies Hⁿ-a.e. in E, hence a.e. in the disjoint open faces A_p, p ∈ s.
2. IMC(a) transfers the approximate tangent spaces of M to M ∩ A_p ⊆ z + V_ι; plane_orientation gives ξ = ±e_p^* a.e. there; the Borel sign σ_p is read off from ξ(·)(dx^ι) with dx^ι(e_p) = 1 (coordinate_covectors).
3. u_p := (θ σ_p 1_M)∘Φ_p is integer-valued; Hⁿ⌞F_p = Φ_p#(volume⌞Q₁) gives integrability and ∫_{Q₁}|u_p| = μ_Q(A_p).
4. Σ_p μ_Q(A_p) ≤ μ_Q(ℝ^P) = M(Q) by C1.
5. Splitting ∫_M θ ξ(ω) over the faces and transporting each piece to Q₁ gives Q(ω) = Σ_p ∫_{Q₁} u_p ω(Φ_p y)(e_p) dy.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (mode local-project, project b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib 25730c7c759d108ef87ab70af2342a196760f79d); git -C local-references/123e8435b4a2469b/mathlib rev-parse HEAD (25730c7c…, matches)`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical)`
- `grep -n 'theorem' local-references/…/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (Isometry.map_euclideanHausdorffMeasure, Isometry.euclideanHausdorffMeasure_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume)`
- `grep -n 'def HasApproximateTangentSpaceAt|def blowUpMap|def CountablyRectifiable|theorem countablyRectifiable_range|theorem countablyRectifiable_iUnion|theorem CountablyRectifiable.mono' SimonGMT/Chapter03/Rectifiable.lean`
- `sed SimonGMT/Chapter06/{Forms,Currents,Mass}.lean: Covector, DifferentialForm, exteriorDerivative (= extDeriv), exteriorDerivative_apply, TestFormOn, GeometricCurrentOn.continuous', GeometricCurrentOn.boundary_apply, covectorEuclideanNorm, massAdmissibleOn, massOn, le_massOn`
- `grep -rn 'wedgeCovectors|coord|basis' SimonGMT/Chapter06 (wedgeCovectors exists only in FormsDuality.lean, outside the import closure of GMT.Ch07.Contract, whose accepted Submissions keep the contract imports)`
- `grep Mathlib for alternatization_apply_apply, ContinuousMultilinearMap.mkPiAlgebra, EuclideanSpace.proj, StrictMono.range_inj_of_wellFoundedLT, EuclideanSpace.basisFun_apply, PiLp.single_apply, ENNReal.finsetSum_iSup, ENNReal.iSup_add_iSup_le, sSup_image', Real.smoothTransition, Filter.EventuallyEq.fderiv_eq, extDeriv_apply, LinearMap.trace_eq_matrix_trace, EuclideanSpace.norm_eq (all present in the pinned snapshot)`
- `python3 -I scans of runs/20261011T150044Z-ba604216b4/dag.json (updated 2026-10-13T23:22:24Z): status/candidate_commit/lean_statement of cmcdtfr_skeleton_null, dor_imrep_massOn_eq_measure_and_support, cmc_imRep_locality_restrict_sub, dor_lmb_fcd_cube_poincare; freshness of all dor_lmb_fcd_fr_* names; replay of _existing_lean_name_problem on the final child list (passes)`
- `git for-each-ref + git grep 'dor_lmb_fcd_fr_' -- GMT/Ch07 over all 7862 refs (no match)`
- `git show 09516d6d883db6c4d6e24410e2a32da5a8ae36f4:GMT/Ch07/Submission.lean (accepted Lean proof of cmcdtfr_skeleton_null, the model for skeleton_cells step 0)`
- `sed /runtime/flows/gmt-claude-889d520655ee/_recursive_lean/runtime.py (_existing_lean_name_problem, _accepted_checkpoint, _decompose: reuse needs an accepted checkpoint; nodes at depth ≥ max_depth are not decomposed) and store.py (refresh)`
- `verifier/gmt-compare.py child_modules / contract_scope (generated the exact NodeChallenge files)`
- `lake env lean /tmp/fr-decomp/lean/AllChallenges.lean (12 child types, exit 0); lake env lean /tmp/fr-decomp/lean/Assembly.lean (#print axioms: propext, Classical.choice, Quot.sound); lake env lean /tmp/fr-decomp/cc/CC1.lean (complete proof of the coordinate_covectors type, standard axioms)`
- `sed -n 10,185p book/chapter-06.txt (Simon 6.1: 1.1, 1.2, 1.5, 1.7, 1.15)`
- `python3 -I parse of this node's decomposition-v1.json and parent-child-handoff.json, and of the parent node's decomposition-v1.json and decomposition-audit-v1.json (reuse pattern of imrep_mass and im_calculus)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Multilinear/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/WellFounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/BigOperators.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/CompleteLattice/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-ab5ee960d0/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-ab5ee960d0/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-cab3e79dc1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-cab3e79dc1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-fac-1dd1ac6935/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/runtime/flows/gmt-claude-889d520655ee/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-889d520655ee/_recursive_lean/store.py`
- `/tmp/fr-decomp/lean/AllChallenges.lean`
- `/tmp/fr-decomp/lean/Assembly.lean`
- `/tmp/fr-decomp/cc/CC1.lean`

Snapshot revisions are project b4d606db and mathlib 25730c7c. The snapshot Ch07 Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean. The snapshot and SimonGMT contain no lattice-face, deformation or polyhedral-chain results usable here. FormsDuality.wedgeCovectors exists but lies outside the contract import closure, so the coordinate covectors are a new child built from Mathlib's alternatization. Every Mathlib/SimonGMT lemma cited in the child proofs exists in the pinned snapshot. Reuse: dor_imrep_massOn_eq_measure_and_support and cmc_imRep_locality_restrict_sub are accepted, have candidate commits and have byte-identical frozen types; they are also resolved dependencies of this node. cmcdtfr_skeleton_null is not reused, as the correction requires; its accepted argument (commit 09516d6) is inlined as step 0 of skeleton_cells. The 10 new dor_lmb_fcd_fr_* names are fresh in the DAG and all git refs. Lean: all 12 child types elaborate as exact comparator challenges. The assembly from the 12 child types plus the frozen CP type proves the selected frozen type with axioms [propext, Classical.choice, Quot.sound]. The new coordinate_covectors type has a complete compiled proof.
