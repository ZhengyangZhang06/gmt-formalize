# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_chart-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Step 4, (4a)–(4e), of the supplied proof of the parent node (graph chart of N at x and the orientation formula), written in orthonormal coordinates ι, ι' so that the accepted graph lemma applies. Embedded submanifolds and tangent spaces: Simon Ch. 2, §4 (4.1); orientations: Simon Ch. 6, 2.2. Sibling children used: orientation_sign (Submission.rsdic_unitOrientation_eq_or_eq_neg) and graph_orientation_jacobian (Submission.dgcr_graph_orientation_jacobian).

Notation. P := n + 1 + k; ℝ^d = Euclid d; e_0, …, e_n the standard basis of ℝ^{n+1}; for a linear L : ℝ^{n+1} → ℝ^P and an (n+1)-covector α, α(Le) := α(Le_0, …, Le_n); L* is the adjoint. B_r := ball(0, r) (in ℝ^{n+1} or ℝ^k, as indicated). If ι : ℝ^{n+1} → ℝ^P and ι' : ℝ^k → ℝ^P are linear isometries with ⟨ιv, ι'w⟩ = 0 for all v, w, then ι*ι = id, ι'*ι' = id, ι*ι' = 0 and ι'*ι = 0 (e.g. ⟨ι*ιv, v'⟩ = ⟨ιv, ιv'⟩ = ⟨v, v'⟩); if moreover every y is ιv + ι'w, then v = ι*y and w = ι'*y, so y = ιι*y + ι'ι'*y and |y|² = |ι*y|² + |ι'*y|².

1. (The tangent plane at x.) IsOrientation (n+1) N ξ_N at x ∈ N gives a subspace Q₀ with (Q₀ : Set) = tangentSpace N x and IsUnitOrientationOf (ξ_N(x)) Q₀. The orthonormal family in IsUnitOrientationOf has n + 1 vectors and spans Q₀, so dim Q₀ = n + 1, and dim Q₀^⊥ = P − (n + 1) = k (Submodule.finrank_add_finrank_orthogonal).

2. (Orthonormal coordinates.) Choose orthonormal bases of Q₀ and of Q₀^⊥ indexed by Fin(n+1) and Fin k (stdOrthonormalBasis, reindexed by the dimensions of step 1), and let ι₀ : ℝ^{n+1} → ℝ^P and ι' : ℝ^k → ℝ^P be the corresponding linear isometries v ↦ Σ_j v_j·(basis vector j). Then range ι₀ = Q₀, range ι' = Q₀^⊥, ⟨ι₀v, ι'w⟩ = 0 for all v, w, and every y equals proj_{Q₀}y + proj_{Q₀^⊥}y, which has the form ι₀v + ι'w.

3. (An orientation-compatible ι.) τ₀ := (ι₀e_0, …, ι₀e_n) is orthonormal with span Q₀, so ζ₀(α) := α(τ₀) is a unit orientation of Q₀. By orientation_sign, ξ_N(x) = ζ₀ or ξ_N(x) = −ζ₀. In the first case put ι := ι₀. In the second, let ρ be the linear isometry of ℝ^{n+1} that negates coordinate 0 and fixes the others, and put ι := ι₀∘ρ; then ιe_0 = −ι₀e_0 and ιe_j = ι₀e_j for j ≥ 1, so α(ιe) = −α(τ₀) by multilinearity. In both cases ι is a linear isometry with range Q₀, ⟨ιv, ι'w⟩ = 0, every y is ιv + ι'w, and ξ_N(x)(α) = α(ιe) for every α. This proves (a) and (d).

4. (A chart at x.) IsEmbeddedSubmanifold 2 (n+1) N at x gives an open V ⊆ ℝ^{n+1}, an open W ∋ x and ψ : ℝ^{n+1} → ℝ^P such that ψ is C² on V and injective on V, ψ(V) = W ∩ N, V ∩ ψ^{−1}(K) is compact for every compact K ⊆ W, and Dψ(z) is injective for every z ∈ V. Choose z₀ ∈ V with ψ(z₀) = x.

5. (range Dψ(z₀) = Q₀.) Let h ∈ ℝ^{n+1} and choose ε > 0 with z₀ + εth ∈ V for |t| < 1 (V is open). Then γ(t) := ψ(z₀ + εth) is C¹ on (−1, 1), takes values in ψ(V) ⊆ N, γ(0) = x and γ'(0) = εDψ(z₀)h. So εDψ(z₀)h ∈ tangentSpace N x = Q₀ and Dψ(z₀)h ∈ Q₀. Thus range Dψ(z₀) ⊆ Q₀, and both have dimension n + 1 (Dψ(z₀) is injective), so range Dψ(z₀) = Q₀ = range ι.

6. (Inverse function theorem.) Put Φ(z) := ι*(ψ(z) − x). Φ is C² on V, Φ(z₀) = 0 and DΦ(z) = ι*Dψ(z). DΦ(z₀) is injective: if ι*Dψ(z₀)h = 0, write Dψ(z₀)h = ιv (step 5); then v = ι*ιv = 0, so Dψ(z₀)h = 0 and h = 0. Hence DΦ(z₀) is a linear automorphism of ℝ^{n+1}. DΦ is continuous on V and invertibility is an open condition, so there is an open V₁ with z₀ ∈ V₁ ⊆ V on which every DΦ(z) is invertible. Φ is C¹ at z₀, so it has strict derivative DΦ(z₀) there (ContDiffAt.hasStrictFDerivAt), and the inverse function theorem (HasStrictFDerivAt.toOpenPartialHomeomorph, after shrinking the source into V₁) gives an open V₀ with z₀ ∈ V₀ ⊆ V₁ such that Φ maps V₀ homeomorphically onto an open set O ∋ 0, with inverse χ : O → V₀. At every a ∈ O, Φ is C² at χ(a) with invertible derivative, so χ is C² at a (OpenPartialHomeomorph.contDiffAt_symm); in particular χ is C¹ on O.

7. (The graph function.) Define u(v) := ι'*(ψ(χ(v)) − x) for v ∈ O (and u(v) := 0 for v ∉ O). Then u is C¹ on O, u(0) = ι'*(ψ(z₀) − x) = 0, and Du(0) = ι'*Dψ(z₀)Dχ(0) = 0 because range Dψ(z₀) = range ι and ι'*ι = 0. For v ∈ O the decomposition y = ιι*y + ι'ι'*y gives ψ(χ(v)) − x = ιΦ(χ(v)) + ι'u(v) = ιv + ι'u(v). Writing Γ(v) := x + ιv + ι'u(v), we get Γ(v) = ψ(χ(v)) ∈ N for every v ∈ O.

8. (Near x, N is covered by ψ(V₀).) The set C := ψ(V ∖ V₀) is relatively closed in W. Indeed, let y ∈ W and c_j ∈ V ∖ V₀ with ψ(c_j) → y. Choose r > 0 with K := closedBall(y, r) ⊆ W. For large j, ψ(c_j) ∈ K, so c_j lies in the compact set V ∩ ψ^{−1}(K), and a subsequence converges to some c ∈ V ∩ ψ^{−1}(K) (IsCompact.tendsto_subseq). Since V₀ is open, V ∖ V₀ is closed in V, so c ∈ V ∖ V₀; ψ is continuous at c, so y = ψ(c) ∈ C. As ψ is injective on V and x = ψ(z₀) with z₀ ∈ V₀, x ∉ C. Hence there is s > 0 with ball(x, s) ⊆ W and ball(x, s) ∩ C = ∅, and then N ∩ ball(x, s) ⊆ (W ∩ N) ∖ C = ψ(V) ∖ ψ(V ∖ V₀) ⊆ ψ(V₀).

9. (Radii; conclusion (b).) Put δ₂ := s/2. As u is continuous at 0 with u(0) = 0 and O is an open neighbourhood of 0, choose δ₁ ∈ (0, s/2] with B_{δ₁} ⊆ O and |u(v)| < δ₂ for v ∈ B_{δ₁}. Then u is C¹ on B_{δ₁}, u(0) = 0, fderiv ℝ u 0 = 0 (0 is an interior point of O, where u is differentiable with derivative 0) and u(B_{δ₁}) ⊆ B_{δ₂}: this is (b). Every point of the cylinder Z := {x + ιv + ι'w : v ∈ B_{δ₁}, w ∈ B_{δ₂}} satisfies |ιv + ι'w|² = |v|² + |w|² < δ₁² + δ₂² < s², so Z ⊆ ball(x, s).

10. (N ∩ Z = Γ(B_{δ₁}); conclusion (c).) (⊇) For v ∈ B_{δ₁}, Γ(v) ∈ N by step 7, and Γ(v) = x + ιv + ι'u(v) with |u(v)| < δ₂, so Γ(v) ∈ Z. (⊆) Let y ∈ N ∩ Z, y = x + ιv' + ι'w' with |v'| < δ₁ and |w'| < δ₂. By steps 8–9, y ∈ N ∩ ball(x, s) ⊆ ψ(V₀), so y = ψ(z) with z ∈ V₀. Then Φ(z) = ι*(y − x) = ι*(ιv' + ι'w') = v', so v' ∈ O and z = χ(v'); hence y = ψ(χ(v')) = Γ(v') with v' ∈ B_{δ₁}.

11. (Tangent planes along the graph.) Fix v ∈ B_{δ₁}. u is differentiable at v, DΓ(v) = ι + ι'Du(v) and ι*DΓ(v) = id, so DΓ(v) is injective and range DΓ(v) has dimension n + 1. For h ∈ ℝ^{n+1} and small ε > 0, t ↦ Γ(v + εth) (t ∈ (−1, 1)) is C¹, takes values in Γ(B_{δ₁}) ⊆ N and has velocity εDΓ(v)h at t = 0. IsOrientation at Γ(v) ∈ N gives a subspace Q_v with (Q_v : Set) = tangentSpace N (Γ(v)) and IsUnitOrientationOf (ξ_N(Γ(v))) Q_v, and dim Q_v = n + 1 as in step 1. Hence DΓ(v)h ∈ Q_v for every h, range DΓ(v) ⊆ Q_v, and range DΓ(v) = Q_v by dimension.

12. (Two unit orientations along the graph.) Apply graph_orientation_jacobian with n + 1 in place of n (n + 1 > 0), z := x, s := δ₁ and u (C¹ on B_{δ₁}, orthogonality from (a)): there are ξ : ℝ^P → Λ_{n+1}(ℝ^P) and β : ℝ^P → Λ^{n+1}(ℝ^P), both continuous on Σ := Γ(B_{δ₁}), with ξ(y)(β(y)) = 1 for y ∈ Σ, ξ(Γ(v)) a unit orientation of range DΓ(v), and α(DΓ(v)e) = J(v)·ξ(Γ(v))(α) for all v ∈ B_{δ₁} and all α, where J(v) := √det(DΓ(v)*DΓ(v)). By step 11 and orientation_sign, for each v ∈ B_{δ₁} either ξ_N(Γ(v)) = ξ(Γ(v)) or ξ_N(Γ(v)) = −ξ(Γ(v)). Put s(v) := ξ_N(Γ(v))(β(Γ(v))); then s(v) = 1 in the first case and s(v) = −1 in the second.

13. (The sign is constant.) s is continuous on B_{δ₁}: Γ is continuous on B_{δ₁} with values in Σ ⊆ N, ξ_N is continuous on N (IsOrientation), β is continuous on Σ, and evaluation (ζ, α) ↦ ζ(α) is continuous. B_{δ₁} is connected (convex, hence preconnected), and s maps it into the finite, hence discrete, set {1, −1}, so s is constant (IsPreconnected.constant_of_mapsTo with Set.Finite.isDiscrete).

14. (s(0) = 1.) Γ(0) = x since u(0) = 0. DΓ(0) = ι + ι'Du(0) = ι, so DΓ(0)*DΓ(0) = ι*ι = id and J(0) = √1 = 1. The identity of step 12 at v = 0 gives ξ(x)(α) = α(ιe) = ξ_N(x)(α) for every α (step 3), i.e. ξ(x) = ξ_N(x), so s(0) = ξ(x)(β(x)) = 1.

15. (Conclusion (e).) By steps 13–14, s(v) = 1 for every v ∈ B_{δ₁}, which excludes ξ_N(Γ(v)) = −ξ(Γ(v)) (that would give s(v) = −ξ(Γ(v))(β(Γ(v))) = −1). Hence ξ_N(Γ(v)) = ξ(Γ(v)), and the identity of step 12 becomes α(DΓ(v)e) = √det(DΓ(v)*DΓ(v))·ξ_N(Γ(v))(α) for every v ∈ B_{δ₁} and every α. With steps 3, 9 and 10 all conclusions (a)–(e) hold. ∎

## Key steps

1. T_xN = Q₀ has dimension n + 1; orthonormal coordinates ι (range Q₀, made orientation-compatible with ξ_N(x) via orientation_sign) and ι' (range Q₀^⊥).
2. range Dψ(z₀) = Q₀, so z ↦ ι*(ψ(z) − x) is a local C¹ diffeomorphism (inverse function theorem); u := ι'*(ψ∘χ − x) is C¹ with u(0) = 0 and Du(0) = 0, and Γ = ψ∘χ.
3. Properness of the chart makes ψ(V ∖ V₀) relatively closed, so N ∩ ball(x, s) ⊆ ψ(V₀); hence N ∩ Z = Γ(B_{δ₁}).
4. range DΓ(v) = T_{Γ(v)}N; graph_orientation_jacobian and orientation_sign give ξ_N∘Γ = ±ξ∘Γ, and the continuous sign equals 1 at v = 0, hence everywhere, which is the Jacobian orientation formula.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; grep -n simongmt -A6 local-references/123e8435b4a2469b/project/lake-manifest.json`
- `sha256sum GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `cat decomposition-audit-v1.json decomposition-review-receipt-v1.json; python3 dump of decomposition-v1.json (12 subproblems: statements, lean_statements, natural proofs, key steps, dependencies)`
- `python3 scan of dag.json: lean_name lookup of the 8 codim1_zsl_* names, the 4 reused names (status, candidate commit, lean_statement byte equality with decomposition-v1.json), dtc_hausdorff_dilation, dor_ims_unitOrientation_dual and codim1_zero_scale_limit_offset_plane; raw count of 'codim1_zsl'; keyword scan 'area formula|BV|perimeter|bvVariation|indicator' over statements and titles`
- `for r in $(git for-each-ref --format='%(objectname)' | sort -u): git grep -q -e codim1_zsl $r -- 'GMT/*.lean' (1277 commits); positive control: the same loop with dgcr_graph_orientation_jacobian; grep -rl codim1_zsl .lake/packages/simongmt/Poincare GMT`
- `grep -n 'def IsTestForm|def exteriorDerivative|theorem exteriorDerivative_apply|def covectorEuclideanNorm|def massOn|def zeroRegion|def support|def affinePullbackForm|theorem exteriorDerivative_affinePullbackForm|theorem tsupport_exteriorDerivative_subset' simongmt/Poincare/SimonGMT/Chapter06/*.lean, then sed of Forms.lean 25-135, Mass.lean 25-80, CurrentLocalEquality.lean 95-125, AffineCurrentPushforward.lean 30-50 and 145-160, Currents.lean 120-190`
- `rg -n 'theorem tsupport_eq|theorem support_eq|protected theorem neg|symmetric :' mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean; rg -n 'integral_comp_inv_smul_of_nonneg|support_convolution_subset|exists_isCompact_sdiff_lt|exists_isOpen_sdiff_lt|integral_pos_iff_support_of_nonneg|theorem lintegral_tsum' mathlib/Mathlib; rg -n 'namespace Module.Basis|def det' mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `lean -DautoImplicit=false /tmp/zsl-v2/Lib.lean and /tmp/zsl-v2/Lib2.lean (#check of about 70 Mathlib/SimonGMT lemmas cited by the children)`
- `lean -DautoImplicit=false /tmp/zsl-v2/Bump.lean (ρ := (∫b)⁻¹·b for b : ContDiffBump (0 : Euclid m) with radii 1/2, 1: ContDiff ℝ ⊤, ρ ≥ 0, ρ(−z) = ρ(z), tsupport ρ = closedBall 0 1, ∫ρ = 1)`
- `lean -DautoImplicit=false /tmp/zsl-v2/TypesV2.lean (12 child types generated from the v2 JSON plus the assembly of the selected type); lean -DautoImplicit=false /tmp/zsl-v2/AssemblyV2.lean (children as axioms, #print axioms)`
- `grep -n 'def check_source_delta' -A40 /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/leaf_verification.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-0b42d13aab/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-0b42d13aab/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-0b42d13aab/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-0b42d13aab/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-0b42d13aab/decomposition-review-receipt-v1.json`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/leaf_verification.py`
- `/tmp/zsl-v2/Lib.lean`
- `/tmp/zsl-v2/Lib2.lean`
- `/tmp/zsl-v2/Bump.lean`
- `/tmp/zsl-v2/TypesV2.lean`
- `/tmp/zsl-v2/AssemblyV2.lean`

Pins match. The snapshot manifest records project b4d606db and Mathlib 25730c7c, equal to workspace HEAD and .lake/packages/mathlib. The snapshot lake-manifest pins simongmt 2b366308, equal to .lake/packages/simongmt. The snapshot Contract.lean and the workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).
DAG.
- The selected node is 'decomposing' with the handoff's exact frozen type.
- The 4 reused declarations are accepted with types byte-identical to v1: dtc_blowUp_testForm_corr (5e184fbc), setIntegral_blowUpMap_image_eq_inv_pow_mul (713eebc5), rsdic_unitOrientation_eq_or_eq_neg (fe95347b) and dgcr_graph_orientation_jacobian (62aa1f11).
- The 8 codim1_zsl_* names have 0 occurrences in dag.json, SimonGMT, GMT/ and the 1277 commits reachable from refs. The positive control dgcr_graph_orientation_jacobian was found on 6 of those commits.
- No accepted node gives an exact graph area formula or BV compactness. The only area-formula nodes are unaccepted (dpf_area_formula_bilipschitz_rectifiable, idtp_carrier_area_formula) and have other types.
Library.
- The SimonGMT definitions match the children's proofs: exteriorDerivative = extDeriv with the alternating-sum formula, IsTestForm = ContDiff ℝ ∞ ∧ HasCompactSupport, covectorEuclideanNorm, massOn/massAdmissibleOn, zeroRegion/support and affinePullbackForm.
- In the snapshot Mathlib, ContDiffBump.tsupport_eq (BumpFunction/Basic.lean:157) gives closedBall c rOut. This confirms the v1 defect, so step 1 of bv_compactness now claims only tsupport ρ = closedBall(0, 1). ContDiffBump.neg (:132) gives evenness, and support_eq (:151) gives the open-ball support.
- Every lemma cited by the corrected proofs exists in the import closure. Examples: integral_comp_inv_smul_of_nonneg (Haar/NormedSpace.lean:129), support_convolution_subset (Convolution.lean:670), MeasurableSet.exists_isCompact_sdiff_lt/exists_isOpen_sdiff_lt (Regular.lean:843/385), exists_continuous_one_zero_of_isCompact and Module.Basis.det (Determinant.lean:591; the old name Basis.det is fixed).
Lean.
- Bump.lean compiles the corrected mollifier.
- TypesV2.lean elaborates all 12 frozen types taken verbatim from the v2 JSON and proves the selected type; lean exits 0. Its axioms are propext, sorryAx, Classical.choice and Quot.sound.
- With the children as axioms, AssemblyV2.lean depends only on propext, Classical.choice, Quot.sound and the 4 direct children.
- leaf_verification.check_source_delta forbids new declarations and imports in leaf proofs, so the deep lemmas must stay separate children.
