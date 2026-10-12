# Parent-supplied natural-language proof

- Parent DAG node: `root.tangent_structure-a1.first_variation_pieces-a1.variation_bounds-a1`
- Child DAG node: `root.tangent_structure-a1.first_variation_pieces-a1.variation_bounds-a1.slice_fderiv_bounds-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1, 2, 5 (the identity Dφ_t = I off K), 6 and 9 of the supplied proof of ts_fv_compact_variation_bounds, that is, the variation of Simon Ch. 4, 2.1 together with the uniform bounds of step (3.1) of the proof of ts_first_variation_of_pieces (the Jacobian computation of Simon Ch. 2, 5.2–5.3, as used for Ch. 4, 2.2), restricted to the bounds on Dφ_t and on its inverse, with an arbitrary δ ∈ (0, ε) in place of ε/2. No errata apply.

Notation. E := Ambient n ℓ with its Euclidean norm; L(E, E) := E →L[ℝ] E with the operator norm (a complete normed ring whose multiplication is composition and whose unit 1 is the identity I); U := (−ε, ε) × E = Ioo (−ε) ε ×ˢ univ ⊆ ℝ × E; Φ : ℝ × E → E, Φ(t, y) := φ t y; ι₁ := (1, 0) ∈ ℝ × E; ι₂ := ContinuousLinearMap.inr ℝ ℝ E ∈ L(E, ℝ × E), ι₂ v = (0, v); X(y) := deriv (t ↦ φ t y) 0; Dφ_t(y) := fderiv ℝ (φ t) y. (H1)–(H6) are the fields pos, compact, smooth, diffeo, init, fixed of IsCompactVariation φ ε K. Let G(q) := fderiv ℝ (φ q.1) q.2 for q ∈ ℝ × E. Fix δ with 0 < δ < ε.

1. Preliminaries. U is open (isOpen_Ioo.prod isOpen_univ); by (H3), Φ is C^∞ at every q ∈ U (ContDiffOn.contDiffAt), hence differentiable there; DΦ := fderiv ℝ Φ is continuous on U (ContDiffOn.continuousOn_fderiv_of_isOpen, 1 ≤ ∞). By (H2), K is closed and Kᶜ is open.

2. Derivative of a time slice. Let t ∈ (−ε, ε) and y ∈ E. The map j_t(y') := (t, y') has derivative ι₂ at y (HasFDerivAt.prodMk of hasFDerivAt_const and hasFDerivAt_id; the resulting map v ↦ (0, v) is ι₂), and Φ is differentiable at (t, y) ∈ U. Since φ t = Φ ∘ j_t, the chain rule (HasFDerivAt.comp) gives HasFDerivAt (φ t) (DΦ(t, y) ∘ ι₂) y. In particular φ t is differentiable at y and Dφ_t(y) = G(t, y) = DΦ(t, y) ∘ ι₂.

3. G is continuous on U. The map q ↦ DΦ(q) ∘ ι₂ is continuous on U, being DΦ (continuous on U, step 1) followed by the continuous map A ↦ A ∘ ι₂ (ContinuousOn.clm_comp with continuousOn_const). By step 2 it agrees with G at every point of U, so G is continuous on U (ContinuousOn.congr).

4. Dφ_t(x) is a unit of L(E, E). Fix t ∈ (−ε, ε) and x ∈ E. By (H4), φ t is bijective and ψ := Function.invFun (φ t) is C^∞, hence differentiable at every point. Injectivity gives ψ (φ t y) = y for all y (Function.leftInverse_invFun), i.e. ψ ∘ φ t = id; surjectivity gives φ t (ψ y) = y for all y (Function.rightInverse_invFun), i.e. φ t ∘ ψ = id. By step 2, φ t has derivative Dφ_t(x) at x.
(i) By the chain rule at x, ψ ∘ φ t has derivative Dψ(φ t x) ∘ Dφ_t(x) at x; but ψ ∘ φ t = id has derivative I, so by uniqueness of the Fréchet derivative (HasFDerivAt.unique) Dψ(φ t x) ∘ Dφ_t(x) = I.
(ii) Since ψ(φ t x) = x, φ t has derivative Dφ_t(x) at the point ψ(φ t x). By the chain rule at φ t x, φ t ∘ ψ has derivative Dφ_t(x) ∘ Dψ(φ t x) at φ t x; as φ t ∘ ψ = id, uniqueness gives Dφ_t(x) ∘ Dψ(φ t x) = I.
Since multiplication in L(E, E) is composition and 1 = I, Dφ_t(x) is a unit of L(E, E) with two-sided inverse Dψ(φ t x).

5. Dφ_t = I off K. Let t ∈ (−ε, ε) and y ∉ K. By (H6), φ t = id on the open neighbourhood Kᶜ of y, so φ t =ᶠ[𝓝 y] id and Dφ_t(y) = fderiv ℝ id y = I (Filter.EventuallyEq.fderiv_eq, fderiv_id).

6. The compact set. Q := [−δ, δ] × K is compact (isCompact_Icc.prod, (H2)), and Q ⊆ U because −ε < −δ and δ < ε.

7. The inverse is continuous on Q. Put Inv(q) := Ring.inverse (G(q)). Let q ∈ Q. Then q ∈ U, so G(q) = Dφ_{q.1}(q.2) is a unit by step 4. In the complete normed ring L(E, E) (E is finite-dimensional, hence complete), Ring.inverse is continuous at every unit (NormedRing.inverse_continuousAt, applied to the unit whose value is G(q), rewritten with IsUnit.unit_spec). G is continuous within Q at q (step 3 and Q ⊆ U). Hence Inv = Ring.inverse ∘ G is continuous within Q at q (ContinuousAt.comp_continuousWithinAt). So Inv is continuous on Q.

8. Constants. By compactness of Q (IsCompact.exists_bound_of_continuousOn applied to G and to Inv on Q) there are B₁, B₃ ∈ ℝ with ‖G(q)‖ ≤ B₁ and ‖Inv(q)‖ ≤ B₃ for every q ∈ Q. Put B := max(1, max(B₁, B₃)); then B ≥ 1, B ≥ B₁ and B ≥ B₃.

9. Verification. Let x ∈ E and t ∈ (−δ, δ); then t ∈ (−ε, ε) because δ < ε.
(i) Case x ∈ K. Then (t, x) ∈ Q. First, ‖Dφ_t(x)‖ = ‖G(t, x)‖ ≤ B₁ ≤ B. Next, let v ∈ E. As G(t, x) is a unit (step 4), Ring.inverse (G(t, x)) * G(t, x) = 1 (Ring.inverse_mul_cancel), so Inv(t, x)(G(t, x) v) = (Inv(t, x) * G(t, x)) v = v. Therefore ‖v‖ = ‖Inv(t, x)(G(t, x) v)‖ ≤ ‖Inv(t, x)‖ · ‖G(t, x) v‖ ≤ B₃ · ‖G(t, x) v‖ ≤ B · ‖Dφ_t(x) v‖ (ContinuousLinearMap.le_opNorm; mul_le_mul_of_nonneg_right, using ‖G(t, x) v‖ ≥ 0).
(ii) Case x ∉ K. Then Dφ_t(x) = I by step 5, so ‖Dφ_t(x)‖ = ‖I‖ ≤ 1 ≤ B (ContinuousLinearMap.norm_id_le), and for v ∈ E, ‖v‖ ≤ B · ‖v‖ = B · ‖Dφ_t(x) v‖ because B ≥ 1 and ‖v‖ ≥ 0 (le_mul_of_one_le_left).

10. Conclusion. The constant B of step 8 satisfies ‖fderiv ℝ (φ t) x‖ ≤ B and ‖v‖ ≤ B · ‖fderiv ℝ (φ t) x v‖ for all v, for every x ∈ E and t ∈ (−δ, δ). ∎

Implementation note (not part of the argument): a Lean proof following exactly these steps was compiled against the pinned toolchain/Mathlib in the frozen Contract scope with no import beyond GMT.Ch04.Submission. The unit of step 4 can be given as ⟨⟨fderiv ℝ (φ t) x, fderiv ℝ ψ (φ t x), h₂, h₁⟩, rfl⟩ with h₂ : (fderiv ℝ (φ t) x).comp (fderiv ℝ ψ (φ t x)) = ContinuousLinearMap.id ℝ E and h₁ : (fderiv ℝ ψ (φ t x)).comp (fderiv ℝ (φ t) x) = ContinuousLinearMap.id ℝ E (multiplication in L(E, E) is composition definitionally). In step 7 pass the explicit argument (f := fun q : ℝ × E ↦ fderiv ℝ (φ q.1) q.2) to ContinuousAt.comp_continuousWithinAt. In step 9(i), Inv(t, x)(G(t, x) v) = (Inv(t, x) * G(t, x)) v holds by rfl.

## Key steps

1. Chain rule: Dφ_t(y) = DΦ(t, y) ∘ ι₂ for t ∈ (−ε, ε), so G(q) = Dφ_{q.1}(q.2) is continuous on U
2. Differentiating invFun (φ t) ∘ φ t = id and φ t ∘ invFun (φ t) = id shows Dφ_t(x) is a unit of L(E, E)
3. Dφ_t = I off K
4. Ring.inverse is continuous at units, so Ring.inverse ∘ G is continuous on the compact Q = [−δ, δ] × K ⊆ U
5. Compactness bounds ‖G‖ ≤ B₁, ‖Ring.inverse ∘ G‖ ≤ B₃ on Q; B := max(1, max(B₁, B₃))
6. On K: ‖v‖ = ‖G⁻¹(G v)‖ ≤ B‖G v‖; off K: G = I and B ≥ 1

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `sha256sum GMT/Ch04/Contract.lean GMT/Ch04/Submission.lean <snapshot>/project/GMT/Ch04/Contract.lean`
- `grep -n IsCompactVariation -A 20 GMT/Ch04/Contract.lean`
- `rg -n 'theorem inverse_continuousAt|theorem lipschitzWith_of_nnnorm_fderiv_le|theorem ContDiffAt.isSymmSndFDerivAt|theorem IsCompact.exists_bound_of_continuousOn|theorem leftInverse_invFun|theorem rightInverse_invFun|theorem ContDiffOn.fderiv_of_isOpen|theorem ContDiffOn.continuousOn_fderiv_of_isOpen|theorem inverse_mul_cancel|theorem mul_inverse_cancel|theorem HasDerivAt.congr_of_eventuallyEq|theorem HasDerivAt.unique|theorem Filter.EventuallyEq.fderiv_eq|theorem ContDiff.continuous_fderiv|theorem contDiff_iff_contDiffAt' <snapshot>/mathlib/Mathlib`
- `rg -n 'lipschitzWith_of_nnnorm_fderiv_le|exists_bound_of_continuousOn' <snapshot>/mathlib/Mathlib`
- `grep -n '^theorem\|^def' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/DeformationFamily.lean`
- `rg -n 'abbrev Euclidean' lake-packages-25730c7c/simongmt/Poincare/SimonGMT`
- `git show 69dc8db:GMT/Ch04/Submission.lean (accepted Submission.compactVariation_velocity_isTestField)`
- `python3 -I scan of dag.json lean_name values for ts_fv_cv_*`
- `rg -l ts_fv_cv_ lake-packages-25730c7c/simongmt/Poincare <snapshot>/project; rg -l -t lean ts_fv_cv_ <snapshot>/mathlib/Mathlib`
- `git grep -n 'ts_fv_cv_\|ts_fv_compact_variation_bounds' <all first-variation-pieces refs> -- GMT/Ch04/Submission.lean`
- `python3 -I /tmp/vb-decomp/scripts/gen.py (lean_contract.validate_lean_statement + gmt-compare.child_modules in contract mode)`
- `lean /tmp/vb-decomp/gen/Challenge_*.lean; lean /tmp/vb-decomp/test/Assembly.lean; lean /tmp/vb-decomp/test/C1.lean C2.lean C3.lean; lean /tmp/vb-decomp/test/Full.lean (#print axioms); lean /tmp/vb-decomp/test/C*_noimp.lean`
- `lean /tmp/vb-decomp/sub/GMT/Ch04/Submission.lean -o /tmp/vb-decomp/olean2/...; lean gen/Solution_*.lean against olean2 (#print axioms)`
- `grep -n '2\.1\|3\.1' book/sources/chapter-04-source.txt; grep -n '3\.1' nodes/root-tangent-structure-a1-first-variation-pieces-a1/parent-supplied-natural-proof.md`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/project/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Normed/Ring/Units.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Logic/Function/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Algebra/GroupWithZero/Units/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/DeformationFamily.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/AppendixA/Foundations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-first-variation-pieces-a1-variation-bounds-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-first-variation-pieces-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-first-variation-pieces-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-04-source.txt`
- `/tmp/vb-decomp/gen/Challenge_ts_fv_cv_first_order_regularity.lean`
- `/tmp/vb-decomp/gen/Challenge_ts_fv_cv_slice_fderiv_bounds.lean`
- `/tmp/vb-decomp/gen/Challenge_ts_fv_cv_slice_fderiv_time_deriv.lean`
- `/tmp/vb-decomp/test/Assembly.lean`
- `/tmp/vb-decomp/test/C1.lean`
- `/tmp/vb-decomp/test/C2.lean`
- `/tmp/vb-decomp/test/C3.lean`
- `/tmp/vb-decomp/test/Full.lean`

Contract and pinned state:
- The snapshot Contract.lean, the workspace Contract.lean and the workspace Submission.lean are byte-identical (sha256 6e58e5dd…0f4770b).
- The snapshot is pinned at project ff75f52a and Mathlib 25730c7c.
- IsCompactVariation has six fields: pos, compact, smooth (ContDiffOn ℝ ∞ on Ioo (-ε) ε ×ˢ univ), diffeo (Bijective and ContDiff ℝ ∞ (invFun)), init and fixed.

Snapshot Mathlib lemmas used, all present with the expected statements:
- NormedRing.inverse_continuousAt (Normed/Ring/Units.lean:183);
- Ring.inverse_mul_cancel (GroupWithZero/Units/Basic.lean:103);
- ContDiffAt.isSymmSndFDerivAt with minSmoothness ℝ 2 ≤ n (FDeriv/Symmetric.lean:533);
- ContDiffOn.fderiv_of_isOpen and ContDiffOn.continuousOn_fderiv_of_isOpen (ContDiff/Defs.lean:907, 916);
- contDiff_iff_contDiffAt and ContDiff.continuous_fderiv;
- lipschitzWith_of_nnnorm_fderiv_le (MeanValue.lean:514);
- IsCompact.exists_bound_of_continuousOn (Normed/Group/Bounded.lean:91);
- Function.leftInverse_invFun and Function.rightInverse_invFun (Logic/Function/Basic.lean:547, 550);
- HasDerivAt.unique and HasDerivAt.congr_of_eventuallyEq;
- Filter.EventuallyEq.fderiv_eq.

SimonGMT:
- Chapter08/DeformationFamily.lean provides Varifold.hasDerivAt_familySpatialDerivative, familySpatialDerivative_eq_fderiv and initialVelocity_eq_deriv. This is an alternative route for Λ'(0,x) = DX(x).
- Euclidean N is an abbrev for EuclideanSpace ℝ (Fin N), so it matches Ambient n ℓ.
- The accepted compactVariation_velocity_isTestField (commit 69dc8db) overlaps child A's part (a) only partly, with a different type.

Elaboration and assembly:
- All 3 child types pass validate_lean_statement and compile as verifier-generated NodeChallenge files in the contract scope.
- The Assembly proves the frozen parent type, byte-identical to dag.json, from the sorry'd children.
- Complete Lean proofs of all children compile.
- Full.lean depends only on [propext, Classical.choice, Quot.sound], and all NodeSolution files compile against a test Submission.
- Imports: C1 and C2 need nothing beyond GMT.Ch04.Submission; C3 needs Mathlib.Analysis.Calculus.FDeriv.Symmetric.

Names: no ts_fv_cv_* match anywhere (dag.json, simongmt, the snapshot project and Mathlib, and all git refs).

Citation: Simon Ch. 4, 2.1 defines the variation (book source line 122). The uniform bounds come from step (3.1) of the proof of ts_first_variation_of_pieces, not from Simon's 3.1.
