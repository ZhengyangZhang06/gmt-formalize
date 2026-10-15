# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.face_replacement-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.face_replacement-a1.divergence_form-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the test forms of step 4 of the parent proof (Simon Ch. 6, (28), "by the obvious modifications of the arguments in the proof of the Constancy Theorem (2.34) and in 2.35"): ω(x) := χ(x) Σ_{l=0}^{m} (−1)^l g_l(π(x)) dx^{ι(0)} ∧ ⋯ (dx^{ι(l)} omitted) ⋯ ∧ dx^{ι(m)}, with π the face coordinates and χ a normal cut-off. Here this construction is carried out and properties (i)–(iii) are verified. Dependency: CC = sibling dor_lmb_fcd_fr_coordinate_covectors. ê_k is the k-th standard basis vector of ℝⁿ, g_l(y) := (g(y))_l, e_i := EuclideanSpace.single i 1 ∈ ℝ^P and e_I := (e_{I(0)}, …, e_{I(k−1)}) for I : Fin k → Fin P; e_p = e_ι.

1. Coordinate covectors. Apply CC with k := m: there is dx : (Fin m → Fin P) → Covector(ℝ^P, m) with (CC-i) dx^J(e_I) = 1 if I = J and 0 if I ≠ J, for all strictly increasing I, J : Fin m → Fin P; and (CC-ii) covectorEuclideanNorm(Σ_{l<N} c_l·dx^{J_l}) = (Σ_l c_l²)^{1/2} for every injective family (J_l)_{l<N} of strictly increasing maps and all reals c_l.

2. The data. For l < n let J_l := ι ∘ Fin.succAbove l : Fin m → Fin P. It is strictly increasing (a composition of strictly increasing maps) with range J_l = range ι ∖ {ι(l)} (ι injective), so l ↦ J_l is injective. Let π : ℝ^P → ℝⁿ, π(x)_k := x_{ι(k)} − z_{ι(k)} (affine, C^∞), and ν(x) := Σ_{i ∉ range ι} (x_i − z_i)² (a polynomial, ≥ 0). Let η : ℝ → [0, 1] be C^∞ with η(t) = 1 for t ≤ δ²/4 and η(t) = 0 for t ≥ δ², e.g. η(t) := Real.smoothTransition((δ² − t)/(3δ²/4)) (smoothTransition is C^∞, [0, 1]-valued, 0 on (−∞, 0] and 1 on [1, ∞)). Put χ := η∘ν and ω(x) := Σ_{l<n} ((−1)^l χ(x) g_l(π(x))) • dx^{J_l}.

3. ω is a test form. ω is a finite sum of C^∞ real functions (products of χ and g_l∘π; g is C^∞ and π is affine) times constant covectors, hence C^∞ (ContDiff.smul with a constant, ContDiff.sum). If ω(x) ≠ 0 then χ(x) ≠ 0, so ν(x) < δ², and g(π(x)) ≠ 0. Hence tsupport ω ⊆ Z := {x : ν(x) ≤ δ²} ∩ π⁻¹(tsupport g), which is closed; Z is bounded, since for x ∈ Z the coordinates x_{ι(k)} = z_{ι(k)} + π(x)_k range over a bounded set (tsupport g is compact) and |x_i − z_i| ≤ δ for i ∉ range ι. So ω has compact support and ω ∈ 𝒟^m(ℝ^P) = TestFormOn univ m (tsupport ω ⊆ univ trivially).

4. (i). Fix x. By CC-ii with N := n, the injective family (J_l)_{l<n} and c_l := (−1)^l χ(x) g_l(π(x)): covectorEuclideanNorm(ω(x)) = (Σ_l χ(x)² g_l(π(x))²)^{1/2} = χ(x)·|g(π(x))| (on Euclid n, |w|² = Σ_l w_l², EuclideanSpace.norm_eq; χ ≥ 0) ≤ 1, because 0 ≤ χ ≤ 1 and |g| ≤ 1.

5. (ii). Let x ∈ tsupport ω ⊆ Z and y := π(x) ∈ tsupport g. Since ι is injective, Φ_p(y) has coordinate z_{ι(k)} + y_k = x_{ι(k)} at ι(k) and z_i at i ∉ range ι, so |x − Φ_p(y)|² = Σ_{i∉range ι} (x_i − z_i)² = ν(x) ≤ δ², i.e. dist(x, Φ_p(y)) ≤ δ.

6. (iii). Fix y ∈ ℝⁿ and x₀ := Φ_p(y); then π(x₀) = y and ν(x₀) = 0 < δ²/4. By continuity of ν, χ = 1 on an open neighbourhood O of x₀, so ω(x) = Σ_l (−1)^l g_l(π(x)) • dx^{J_l} for x ∈ O. ω is C^∞, hence differentiable at x₀, so by the exterior-derivative formula (SimonGMT exteriorDerivative = Mathlib extDeriv; exteriorDerivative_apply / extDeriv_apply) dω(x₀)(v) = Σ_{i<n} (−1)^i · D[x ↦ ω(x)(Fin.removeNth i v)](x₀)(v_i). For v = e_ι, Fin.removeNth i e_ι = (e_{ι(succAbove i c)})_{c<m} = e_{J_i} (this holds after unfolding, not syntactically: use `show` or `simp only [Fin.removeNth, Function.comp_apply]` to put it in the form fun c => EuclideanSpace.single (J_i c) 1 of CC-i before rewriting). By CC-i (J_l = J_i iff l = i), ω(x)(e_{J_i}) = Σ_l (−1)^l χ(x) g_l(π(x)) dx^{J_l}(e_{J_i}) = (−1)^i χ(x) g_i(π(x)) for every x, and = (−1)^i g_i(π(x)) for x ∈ O. A derivative at x₀ depends only on values near x₀ (Filter.EventuallyEq.fderiv_eq), and π(x₀ + t e_{ι(i)}) = y + t ê_i (ι injective), so D[x ↦ ω(x)(e_{J_i})](x₀)(e_{ι(i)}) = (−1)^i (Dg(y) ê_i)_i. Therefore dω(Φ_p(y))(e_p) = Σ_i (−1)^i (−1)^i (Dg(y) ê_i)_i = Σ_i ⟨Dg(y) ê_i, ê_i⟩ = trace(Dg(y)), the trace of a linear map being the sum of the diagonal entries of its matrix in the basis (ê_i) (LinearMap.trace_eq_matrix_trace with EuclideanSpace.basisFun and LinearMap.toMatrix_apply). ∎

## Key steps

1. Coordinate covectors dx^J (coordinate_covectors) are dual to the coordinate frames e_I, and the coefficient norm of Σ_l c_l dx^{J_l} is |c|.
2. ω := Σ_l (−1)^l χ·(g_l∘π) • dx^{ι∘succAbove l} with π the face coordinates and a smooth normal cut-off χ = η(|x_⊥ − z_⊥|²).
3. ω is smooth with compact support in {|x_⊥ − z_⊥| ≤ δ} ∩ π⁻¹(spt g), and |ω| = χ·|g∘π| ≤ 1.
4. Each x ∈ tsupport ω is within δ of Φ_p(π(x)) with π(x) ∈ spt g.
5. Near Φ_p(y), χ ≡ 1 and ω(x)(e_{J_i}) = (−1)^i g_i(π(x)); the alternating-sum formula for d gives dω(Φ_p y)(e_p) = Σ_i ∂_i g_i(y) = trace Dg(y).

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
