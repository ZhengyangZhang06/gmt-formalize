# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_retraction-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3.1 of the parent proof, which takes for π the nearest-point projection onto N given by the tubular neighbourhood theorem (cf. Simon 7.5, chapter-07.txt lines 783–786). The parent uses only properties (i)–(iv) of that projection. Here they are proved for the explicit graph retraction over T_xN, which agrees with the nearest-point projection to first order at x; this avoids the tubular neighbourhood theorem and is the only departure from the parent's text. No dependencies; Mathlib's inverse function theorem (ContDiffAt.toOpenPartialHomeomorph, ContDiffAt.localInverse) and mean value inequality (Convex.norm_image_sub_le_of_norm_fderiv_le).
1. (Chart at x.) Apply IsEmbeddedSubmanifold 2 d N at y := x to get V, W, ψ as in the statement. Since x ∈ W ∩ N = ψ(V), choose v₀ ∈ V with ψ(v₀) = x. As V is open and ψ is C² on V, ψ is differentiable on V with continuous derivative. L := Dψ(v₀) : ℝ^d → ℝ^P is an injective linear map; Q := L(ℝ^d) is a subspace and L : ℝ^d → Q is a linear isomorphism with inverse L⁻¹ : Q → ℝ^d. Let p : ℝ^P → Q be the orthogonal projection (‖p‖ ≤ 1 and p(Lw) = Lw) and A := L⁻¹∘p : ℝ^P → ℝ^d (continuous linear).
2. (Local inverse.) h : ℝ^d → ℝ^d, h(v) := A(ψ(v) − x), is C² near v₀, h(v₀) = 0 and Dh(v₀) = A∘L = id. By the inverse function theorem there are open sets V₀ ⊆ V with v₀ ∈ V₀ and O ⊆ ℝ^d with 0 ∈ O such that h maps V₀ bijectively onto O and the inverse k : O → V₀ is C¹; so k(h(v)) = v for v ∈ V₀ and h(k(u)) = u for u ∈ O.
3. (Graph parametrization.) Φ := ψ∘k : O → ℝ^P is C¹, Φ(0) = ψ(v₀) = x, Φ(O) = ψ(V₀) ⊆ N, and DΦ(0) = Dψ(v₀)∘Dk(0) = L∘(Dh(v₀))⁻¹ = L.
4. (ψ(V₀) is relatively open in N.) Let F := V ∖ V₀, a relatively closed subset of V. Then ψ(F) is relatively closed in W: if y ∈ W and y = lim ψ(f_i) with f_i ∈ F, then K := {y} ∪ {ψ(f_i) : i ∈ ℕ} is a compact subset of W, so all f_i lie in the compact set V ∩ ψ⁻¹(K); a subsequence converges to some f ∈ V ∩ ψ⁻¹(K), f ∈ F because F is closed in V, and ψ(f) = y by continuity of ψ at f. Hence W₀ := W ∖ ψ(F) is open. x ∈ W₀, because x = ψ(v₀) with v₀ ∉ F and ψ is injective on V. Moreover W₀ ∩ N = ψ(V₀): if y ∈ W₀ ∩ N then y ∈ W ∩ N = ψ(V), so y = ψ(v) with v ∈ V, and v ∉ F (otherwise y ∈ ψ(F)), i.e. v ∈ V₀; conversely ψ(V₀) ⊆ W ∩ N and ψ(V₀) ∩ ψ(F) = ∅ by injectivity.
5. (Choice of δ and π.) Choose r₀ > 0 with B^d_{r₀}(0) ⊆ O and δ > 0 with B_δ(x) ⊆ W₀ and ‖A‖δ < r₀. Define π(y) := Φ(A(y − x)) for y ∈ B_δ(x) and π(y) := y otherwise. For y ∈ B_δ(x), |A(y − x)| ≤ ‖A‖|y − x| < r₀, so A(y − x) ∈ O.
6. ((i)–(iii).) (i) On the open ball B_δ(x), π is the composition of the affine map y ↦ A(y − x) (with values in O) and the C¹ map Φ, hence C¹. (ii) π(y) ∈ Φ(O) ⊆ N for y ∈ B_δ(x). (iii) If y ∈ N ∩ B_δ(x) ⊆ N ∩ W₀ = ψ(V₀), write y = ψ(v) with v ∈ V₀; then A(y − x) = h(v) ∈ O and π(y) = ψ(k(h(v))) = ψ(v) = y. In particular π(x) = x.
7. ((iv).) For y ∈ B_δ(x), Dπ(y) = DΦ(A(y − x))∘A; hence Dπ(x) = L∘L⁻¹∘p = p and ‖Dπ(x)‖ ≤ 1. Dπ is continuous on B_δ(x) because π is C¹ there. Given η > 0 choose s ∈ (0, δ] with ‖Dπ(y) − Dπ(x)‖ ≤ η, hence ‖Dπ(y)‖ ≤ 1 + η, for all y ∈ B_s(x). B_s(x) is convex and π is differentiable on it, so the mean value inequality gives |π(y) − π(z)| ≤ (1 + η)|y − z| for all y, z ∈ B_s(x). ∎
(The case d = 0 is included: then ℝ^d is a point, L = 0 is injective, Q = {0}, p = 0, A = 0, Φ ≡ x and π ≡ x on B_δ(x), and B_δ(x) ∩ N = {x} by step 4.)

## Key steps

1. Take a chart ψ at x, L := Dψ(v₀), Q := range L, p the orthogonal projection onto Q and A := L⁻¹p.
2. Inverse function theorem for h := A(ψ − x) at v₀ gives the C¹ graph parametrization Φ := ψ∘h⁻¹ of N near x with DΦ(0) = L.
3. Properness of the chart makes ψ(V₀) relatively open in N, so N ∩ B_δ(x) ⊆ ψ(V₀) for small δ.
4. π(y) := Φ(A(y − x)) is C¹, maps into N, fixes N ∩ B_δ(x), and Dπ(x) = p has norm ≤ 1; continuity of Dπ and the mean value inequality give Lipschitz constants 1 + η on small balls.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db, mathlib 25730c7c); cmp project/GMT/Ch07/Contract.lean against workspace GMT/Ch07/Contract.lean and GMT/Ch07/Submission.lean (identical)`
- `grep -n 'def GeometricCurrentOn.massOn|massAdmissibleOn|massOn_le_liminf|massOn_mono|le_massOn' simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `grep -n 'restrictDomain|VanishesOn|zeroRegion|def GeometricCurrentOn.support' simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean; grep -n 'GeometricCurrentOn.boundary|instance .*Zero|tsupport_exteriorDerivative_subset|WeaklyConvergesOn' simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `grep -n 'affinePullbackForm|affinePushforward|boundary_affinePushforward|tsupport_affinePullbackForm_subset|exteriorDerivative_affinePullbackForm' simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `grep -n 'def CountablyRectifiable|CountablyRectifiable.mono|countablyRectifiable_range|def HasApproximateTangentSpaceAt|hasApproximateTangentSpaceAt_submodule|HasApproximateTangentSpaceAt.unique' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -rn 'ae_eq_const_of_weak_coordinate_derivatives_zero|WeakDerivativesZero' simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean; #print axioms Poincare.SimonGMT.Chapter08.ae_eq_const_of_weak_coordinate_derivatives_zero`
- `grep -n '^theorem' simongmt/Poincare/SimonGMT/Chapter02/{AreaLipschitz,AreaFormula,CoareaLinear,BV,Lipschitz}.lean simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean (no Federer–Fleming compactness, slicing, flat metric, rectifiable area/coarea formula or C¹ push-forward of currents)`
- `grep -rn 'lintegral_eq_lintegral_meas_lt|lintegral_eq_lintegral_meas_le|lintegral_liminf_le|limsup_lintegral_le|ext_of_generate_finite|isPiSystem_isOpen|tendsto_measure_thickening_of_isClosed|extraction_of_frequently_atTop|toOpenPartialHomeomorph|norm_image_sub_le_of_norm_fderiv_le|euclideanHausdorffMeasure_eq_volume|eq_smul_basis_det|det_to_matrix_orthonormalBasis_real|exists_thickening_subset_open|setIntegral_eq_integral_of_forall_compl_eq_zero|restrict_withDensity' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `grep -rl 'dtc_bc_' .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4 GMT simongmt/Poincare (no match); lean_name inventory of dag.json (198 nodes, no collision)`
- `python3 -I: verifier/gmt-compare.py contract_scope + child_modules (contract mode) and verifier/lean_contract.py validate_lean_statement on all eight child types`
- `lake env lean /tmp/dtcbc/check/Challenge_<key>.lean (8 files), /tmp/dtcbc/check/Assembly.lean, /tmp/dtcbc/check/Iface.lean, /tmp/dtcbc/check/Lib.lean, /tmp/dtcbc/check/Lib2.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Layercake.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/dtcbc/check/Assembly.lean`
- `/tmp/dtcbc/check/Iface.lean`
- `/tmp/dtcbc/stmts/stmts.py`
- `/tmp/dtcbc/stmts/children.py`

The snapshot contract (project b4d606d, Mathlib 25730c7c) is byte-identical to the workspace Contract.lean and Submission.lean. The pinned SimonGMT library provides the objects the children use: GeometricCurrentOn, boundary, massOn/massAdmissibleOn, WeaklyConvergesOn.massOn_le_liminf, support/zeroRegion, restrictDomain, affinePushforward with boundary_affinePushforward and tsupport_affinePullbackForm_subset, CountablyRectifiable with countablyRectifiable_range, and HasApproximateTangentSpaceAt with hasApproximateTangentSpaceAt_submodule. It also provides the distributional constancy theorem Chapter08.ae_eq_const_of_weak_coordinate_derivatives_zero (standard axioms), which makes the k = 0 child self-contained. The library has no Federer–Fleming compactness, slicing, flat-metric theorem, rectifiable area/coarea formula or C¹ push-forward of currents. Those Simon Ch. 6 results are cited only by truncated_compactness and local_comparison, exactly as in the accepted parent proof. Every Mathlib lemma named in the proofs exists at the pin. All eight child types elaborate in the comparator scope, and the conditional assembly of the selected type from five of them uses only propext, Classical.choice and Quot.sound. No dtc_bc_ name occurs elsewhere.
