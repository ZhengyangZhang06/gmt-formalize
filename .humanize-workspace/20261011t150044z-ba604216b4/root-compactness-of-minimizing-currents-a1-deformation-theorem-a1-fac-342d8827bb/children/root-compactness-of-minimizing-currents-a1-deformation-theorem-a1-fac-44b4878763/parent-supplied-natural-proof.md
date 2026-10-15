# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.plane_orientation-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.plane_orientation-a1.frame_sign-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 of the parent proof, isolated as a statement about two orthonormal frames of the same subspace. Compare Simon Ch. 6, §1 and §3: an n-plane is oriented by ±τ₁ ∧ ⋯ ∧ τₙ for any orthonormal basis τ of it (book/chapter-06.txt lines 2224–2226).

Notation. An n-covector is α ∈ Covector (Euclid P) n, a continuous alternating n-linear map (ℝ^P)^n → ℝ. α(v) denotes its value on v : Fin n → ℝ^P. Let W := span(range e) ⊆ ℝ^P.

1. A basis of W from e. Since e is orthonormal, it is linearly independent (Orthonormal.linearIndependent). Hence b := Basis.span of this linear independence is a basis of W indexed by Fin n, with (b j : ℝ^P) = e j for every j (Basis.coe_span_apply). Consequently finrank W = n (finrank_span_eq_card and Fintype.card (Fin n) = n).

2. τ as a family in W. For each j, τ j ∈ span(range τ) = W by hypothesis. Let τ_W : Fin n → W be τ_W j := ⟨τ j, _⟩, so (τ_W j : ℝ^P) = τ j.

3. Reduction to one determinant. Fix an n-covector α. Let α_W be the alternating n-linear map W^n → ℝ obtained by composing the underlying alternating map of α with the inclusion W.subtype (AlternatingMap.compLinearMap). Thus α_W(w_0, …, w_{n−1}) = α(w_0, …, w_{n−1}).
 Since b is a basis of W indexed by the same type Fin n, AlternatingMap.eq_smul_basis_det gives α_W = α_W(b) • det_b, where det_b is the determinant alternating map of b. Evaluating at τ_W:
 α(τ) = α_W(τ_W) = α_W(b) · det_b(τ_W) = α(e) · c, where c := det_b(τ_W) ∈ ℝ.
 Here α_W(b) = α(e) because (b j : ℝ^P) = e j, and α_W(τ_W) = α(τ) because (τ_W j : ℝ^P) = τ j. The number c depends only on b and τ_W, not on α.

4. c = ±1. The inner product of W is the restriction of that of ℝ^P (Submodule.coe_inner). So the orthonormality of e and τ in ℝ^P transfers verbatim: b and τ_W are orthonormal families in W.
 (i) b is an orthonormal basis: oe := b.toOrthonormalBasis, with oe.toBasis = b (Basis.toBasis_toOrthonormalBasis).
 (ii) τ_W is orthonormal, hence linearly independent, and has n = finrank W members, so span(range τ_W) = W (LinearIndependent.span_eq_top_of_card_eq_finrank'). Thus oτ := OrthonormalBasis.mk is an orthonormal basis of W with ⇑oτ = τ_W (OrthonormalBasis.coe_mk).
 (iii) The change-of-basis determinant between two orthonormal bases of a finite-dimensional real inner product space is ±1. Its matrix is orthogonal, so the determinant squares to 1 (OrthonormalBasis.det_to_matrix_orthonormalBasis_real: oe.toBasis.det oτ = 1 ∨ oe.toBasis.det oτ = −1).
 By (i) and (ii), oe.toBasis.det oτ = det_b(τ_W) = c, so c = 1 or c = −1.

5. Conclusion. If c = 1, step 3 gives α(τ) = α(e) for every n-covector α. If c = −1, step 3 gives α(τ) = −α(e) for every n-covector α. Since c does not depend on α, this is the required dichotomy.

6. The case n = 0 is included. Then W = {0}, b and τ_W are the empty family, and det_b(τ_W) = 1 (the determinant of the empty matrix), so the first alternative holds. The argument above covers this case without change. ∎

## Key steps

1. W := span(range e) has the basis b = Basis.span (e linearly independent) with b_j = e_j, and finrank W = n. Each τ_j lies in span(range τ) = W.
2. For each n-covector α, restrict it to W and apply AlternatingMap.eq_smul_basis_det with the basis b. This gives α(τ) = det_b(τ_W) · α(e), where c := det_b(τ_W) does not depend on α.
3. b and τ_W are orthonormal bases of W (τ_W spans because it has n = finrank W independent members). So c = oe.toBasis.det oτ ∈ {1, −1} (det_to_matrix_orthonormalBasis_real).
4. c = 1 gives α(τ) = α(e) for all α, and c = −1 gives α(τ) = −α(e) for all α. The case n = 0 is included.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); manifest.json project_commit b4d606d…, mathlib_commit 25730c7c… (git -C local-references/123e8435b4a2469b/mathlib rev-parse HEAD matches)`
- `rg -n 'cmcdtfrpo_' project mathlib/Mathlib -g '*.lean' (no match)`
- `rg -n 'approxTangent_le|orthonormal.*sign|frame_sign|IsUnitOrientationOf' project/GMT -g '*.lean' (only the IsUnitOrientationOf definition and its uses, Contract.lean/Submission.lean lines 52, 74, 236; no tangent-inclusion or frame-sign lemma)`
- `rg -n 'theorem (AlternatingMap.eq_smul_basis_det|OrthonormalBasis.det_to_matrix_orthonormalBasis_real|EuclideanSpace.orthonormal_single|finrank_span_eq_card|setIntegral_eq_zero_of_forall_eq_zero|integral_pos_iff_support_of_nonneg|Continuous.integrable_of_hasCompactSupport)' mathlib/Mathlib (all found: Determinant.lean:650, PiL2.lean:992 and 349, Dimension/Constructions.lean:463, Bochner/Set.lean:357, Bochner/Basic.lean:790, LocallyIntegrable.lean:622)`
- `rg -n 'IsClosed.notMem_iff_infDist_pos|infDist_le_dist_of_mem|mem_support_iff_forall|OrthonormalBasis.coe_mk|Basis.toBasis_toOrthonormalBasis|Basis.coe_span_apply|Submodule.coe_inner|eq_of_le_of_finrank_eq|span_eq_top_of_card_eq_finrank' mathlib/Mathlib (all found: HausdorffDistance.lean:584 and 500, Measure/Support.lean:75, PiL2.lean:717 and 628, Basis/Basic.lean:196, InnerProductSpace/Subspace.lean:41, FiniteDimensional/Basic.lean:257, FiniteDimensional/Lemmas.lean:266)`
- `grep -n in simongmt Chapter03/Rectifiable.lean (identical to the compiled .lake/packages copy, rev 2b36630): blowUpMap l.96, HasApproximateTangentSpaceAt l.102 (finrank P = n ∧ C_c-test convergence along 𝓝[>] 0), support_euclideanHausdorffMeasure_restrict_submodule l.157, regular_euclideanHausdorffMeasure_restrict_submodule l.187; Chapter06/Forms.lean l.31: Covector E n := E [⋀^Fin n]→L[ℝ] ℝ`
- `python3 -I scan of runs/20261011T150044Z-ba604216b4/dag.json lean_name/lean_statement (1598 nodes): no name with prefix cmcdtfrpo_; zero duplicate lean_names anywhere (no reuse precedent); related but non-identical nodes: atsm_approxTangent_le_of_flat, dgcr_atg_approxTangent_le_of_flat, rsdic_unitOrientation_eq_or_eq_neg, dgcr_unitOrientation_eq_or_neg (accepted, PRs unmerged), dor_lmbsf_io_orientation_frame_sign (decomposing)`
- `grep -n 'def child_modules|def contract_scope' verifier/gmt-compare.py (replayed scope: the opens, namespace GMT.Ch07, noncomputable section/end; target `theorem _root_.HumanizeNodeComparator.target : (stmt)`)`
- `lake env lean /tmp/podecomp/lean/Types.lean and ChildChallenges.lean (both child types and the parent type elaborate in the replayed Contract scope; sorry warnings only)`
- `lake env lean /tmp/podecomp/lean/Assembly.lean (POAsm.check: child A type → child B type → frozen parent type; #print axioms: propext, Classical.choice, Quot.sound)`
- `lake env lean /tmp/podecomp/lean/ChildA.lean, ChildB.lean, EndToEnd.lean (both children proved exactly as stated along the supplied natural proofs; comparator-style target `exact Submission.cmcdtfr_plane_orientation_scratch` compiles; axioms propext, Classical.choice, Quot.sound)`
- `sed -n 70,100p book/chapter-03.txt (Simon 3.1.4 and 1.5); sed -n 1838,1862p and 2220,2230p book/chapter-06.txt (Simon 6.5 (26)–(27); 6.3: orientation ±τ₁∧⋯∧τₙ for any orthonormal basis)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Subspace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Basis/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-fac-342d8827bb/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/podecomp/lean/Types.lean`
- `/tmp/podecomp/lean/ChildChallenges.lean`
- `/tmp/podecomp/lean/Assembly.lean`
- `/tmp/podecomp/lean/ChildA.lean`
- `/tmp/podecomp/lean/ChildB.lean`
- `/tmp/podecomp/lean/EndToEnd.lean`

Snapshot facts:
- The snapshot (project b4d606d, Mathlib 25730c7c) has the same Ch07 contract as the workspace, and Submission.lean equals the contract.
- The project has no lemma about tangent-plane inclusion or orientation sign; only the IsUnitOrientationOf definition and its uses (no match).
- No snapshot declaration or DAG node uses the prefix cmcdtfrpo_.
- The DAG has zero duplicate lean_names, so there is no precedent for cross-branch reuse. Related accepted nodes (atsm_approxTangent_le_of_flat, rsdic_unitOrientation_eq_or_eq_neg, dgcr_*) have different frozen types and unmerged PRs, so fresh names are used.

Tools found:
- Mathlib 25730c7c provides every lemma both child proofs cite: eq_smul_basis_det, det_to_matrix_orthonormalBasis_real, Basis.span/coe_span_apply, OrthonormalBasis.mk/coe_mk, toBasis_toOrthonormalBasis, span_eq_top_of_card_eq_finrank', Submodule.coe_inner, IsClosed.notMem_iff_infDist_pos, infDist_le_dist_of_mem, setIntegral_eq_zero_of_forall_eq_zero (valid for non-measurable sets), Measure.mem_support_iff_forall, Continuous.integrable_of_hasCompactSupport and integral_pos_iff_support_of_nonneg.
- SimonGMT Ch. 3 supplies HasApproximateTangentSpaceAt, blowUpMap, and the support and regularity of Hⁿ restricted to an n-plane.

Lean checks:
- In the comparator's replayed scope, both child types and the parent type elaborate.
- The two child types imply the frozen parent type with only propext, Classical.choice and Quot.sound.
- Both children were proved in scratch exactly as stated, following the supplied natural proofs.
