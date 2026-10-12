# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.c1_sard-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Introduction to GMT, Ch. 2 §6, the paragraph after 6.3 and Theorem 6.4 (p. 66-67). Readings applied (GMT/Ch02/README.md): the printed identity C = {x ∈ M : rank df_x < m} is included as a conjunct; (closed set) is read as relatively closed in M (M need not be closed in ℝᴺ); the empty set is (vacuously) a submanifold. Depends on the siblings coarea_formula (CoareaFormula) and submanifold_tangent (T_xM = range Dψ, M Borel, x ↦ P_x continuous on M).

Statement (frozen C1Sard). N, m, k ∈ ℕ, k ≥ 1, n := m + k, M ⊆ ℝᴺ an n-dimensional C¹ Simon submanifold, U ⊆ ℝᴺ open with M ⊆ U, f : ℝᴺ → ℝᵐ of class C¹ on U. With J*f(x) := coareaJacobian M f x = √det(L_xL_x*), L_x := Df(x)∘ι_{T_xM} : T_xM → ℝᵐ (ι the inclusion), and Z := {x : J*f(x) = 0}: (1) {x ∈ M : J*f(x) = 0} = {x ∈ M : finrank(range L_x) < m}; (2) for Lᵐ-a.e. y, Hᵏ(M ∩ f⁻¹{y} ∩ Z) = 0 (Hᵏ = μHE[k]); (3) for every y ∈ ℝᵐ there is a closed F ⊆ ℝᴺ with M ∩ f⁻¹{y} ∩ Z = M ∩ F, and (M ∩ f⁻¹{y})∖Z is a k-dimensional C¹ Simon submanifold of ℝᴺ.

PART I. PRINTED ARGUMENT (cleaned transcription).
An important consequence of 6.3 is that if C = {x ∈ M : J*f(x) = 0}, then (by using 6.3 with A = C) Hᵏ(C ∩ f⁻¹(y)) = 0 for Lᵐ-a.e. y ∈ ℝᵐ. Also, since J*f(x) ≠ 0 precisely when df_x has rank m, the implicit function theorem implies that either f⁻¹(y)∖C is empty or else it is a k-dimensional C¹ submanifold in the sense of §4. Theorem 6.4 (C¹ Sard-type theorem): for Lᵐ-a.e. y ∈ f(M), f⁻¹(y) decomposes into a k-dimensional C¹ submanifold and a closed set of Hᵏ-measure zero: f⁻¹(y) = (f⁻¹(y)∖C) ∪ (f⁻¹(y) ∩ C), C = {x ∈ M : J*f(x) = 0} (= {x ∈ M : rank df_x < m}), Hᵏ(f⁻¹(y) ∩ C) = 0 for Lᵐ-a.e. y, and f⁻¹(y)∖C is either empty or a k-dimensional C¹ submanifold.

PART II. COMPLETE PROOF.

Conjunct (1) (linear algebra; valid for every x).
1. Let L := L_x : T → ℝᵐ, T := T_xM with the induced inner product. LL* is self-adjoint and positive semidefinite (⟨LL*w, w⟩ = |L*w|²), so det(LL*) ≥ 0 and J*f(x) = √det(LL*) = 0 ⟺ det(LL*) = 0 (Real.sqrt d = 0 ⟺ d ≤ 0).
2. det(LL*) = 0 ⟺ LL* is not injective ⟺ ∃ w ≠ 0 with L*w = 0 (if LL*w = 0 then |L*w|² = ⟨LL*w, w⟩ = 0) ⟺ L* is not injective ⟺ L is not surjective (range L = (ker L*)^⊥) ⟺ finrank(range L) < m. Here range L = LinearMap.range ((fderiv ℝ f x).toLinearMap ∘ₗ (tangentSpace M x).subtype). Intersecting with M gives (1).

Conjunct (2) (from the coarea formula).
3. C_M := {x ∈ M : J*f(x) = 0} = M ∩ Z is a Borel set: by submanifold_tangent M is Borel and x ↦ P_x is continuous on M, and for x ∈ M, L_xL_x* = Df(x)P_xDf(x)* (ι ι* = P_x) with Df continuous on U ⊇ M, so J*f is continuous on M and C_M is relatively closed in M.
4. Apply CoareaFormula with g := indicator of C_M (Borel, hence AEMeasurable for μHE[m+k] restricted to M). Left side: ∫_M 1_{C_M} J*f dHⁿ = 0 since J*f = 0 on C_M. Right side: for each y, ∫_{M∩f⁻¹{y}} 1_{C_M} dHᵏ = Hᵏ((M ∩ f⁻¹{y}) ∩ C_M) = Hᵏ(M ∩ f⁻¹{y} ∩ Z) (C_M measurable). Hence ∫ Hᵏ(M ∩ f⁻¹{y} ∩ Z) dLᵐ(y) = 0, and the integrand is AEMeasurable (first conclusion of CoareaFormula), so it vanishes for Lᵐ-a.e. y (Mathlib lintegral_eq_zero_iff′). This is (2).

Conjunct (3a) (relative closedness).
5. Fix y. S_y := M ∩ f⁻¹{y} ∩ Z is relatively closed in M: if x_j ∈ S_y and x_j → x ∈ M, then f(x) = y (f continuous at x ∈ U) and J*f(x) = lim J*f(x_j) = 0 (continuity of J*f on M, step 3). Put F := closure S_y (closed); then M ∩ F = S_y (⊇ trivial; ⊆ by relative closedness).

Conjunct (3b) (the regular part of a fiber is a k-dimensional C¹ submanifold).
6. Let Σ_y := (M ∩ f⁻¹{y})∖Z. Since r = 1 ≥ 1 it suffices, for each p ∈ Σ_y, to produce an open D ⊆ ℝᵏ, an open W₃ ⊆ ℝᴺ with p ∈ W₃ and χ : ℝᵏ → ℝᴺ such that IsSimonLocalRepresentation 1 Σ_y D W₃ χ: χ C¹ on D, injective on D, χ(D) = W₃ ∩ Σ_y, proper relative to (D, W₃), Dχ(z) injective for z ∈ D. (If Σ_y = ∅ there is nothing to prove.)
7. Construction. Take a C¹ local representation ψ : V → W ∩ M with p ∈ W, x_p := ψ⁻¹(p), and G := f∘ψ (C¹ on V since ψ(V) ⊆ M ⊆ U). By submanifold_tangent Dψ(x_p) maps ℝⁿ onto T_pM, and L_p is surjective by steps 1-2 because J*f(p) ≠ 0 (p ∉ Z), so DG(x_p) = L_p∘Dψ(x_p) is surjective. Let K_p := ker DG(x_p) (dimension k), ι : ℝᵏ → K_p a linear isometry, π_{K_p} the orthogonal projection, and Φ(x) := (G(x), ι⁻¹π_{K_p}(x − x_p)) ∈ ℝᵐ × ℝᵏ; note Φ(x_p) = (f(p), 0) = (y, 0). DΦ(x_p) is injective (if DG(x_p)ζ = 0 and π_{K_p}ζ = 0 then ζ ∈ K_p ∩ K_p^⊥ = 0), hence invertible. By the C¹ inverse function theorem there are an open V₁ ∋ x_p, V₁ ⊆ V, and an open Ω₁ ∋ (y,0) with Φ : V₁ → Ω₁ a C¹ diffeomorphism; Λ := (Φ|V₁)⁻¹ is C¹. Shrink V₁ so that J*f > 0 on ψ(V₁) (continuity of J*f∘ψ at x_p) and choose ρ > 0 with B(y,ρ) × B(0,ρ) ⊆ Ω₁. Put D := B(0,ρ) ⊆ ℝᵏ, χ(z) := ψ(Λ(y,z)), V₃ := Λ(B(y,ρ) × B(0,ρ)) (open, ⊆ V₁), and by 4.2 (SimonGMT IsSimonLocalRepresentation.exists_open_image_eq_inter) an open W₃ ⊆ W with ψ(V₃) = W₃ ∩ M. Then p = χ(0) ∈ W₃ (Λ(y,0) = x_p).
8. χ(D) = W₃ ∩ Σ_y. (⊆) For z ∈ D, x := Λ(y,z) ∈ V₃, χ(z) = ψ(x) ∈ W₃ ∩ M, f(χ(z)) = G(x) = (Φ(x))₁ = y, and J*f(χ(z)) > 0 since x ∈ V₁; so χ(z) ∈ Σ_y. (⊇) If q ∈ W₃ ∩ Σ_y then q ∈ W₃ ∩ M = ψ(V₃), q = ψ(x) with x ∈ V₃, Φ(x) = (a, z′) ∈ B(y,ρ) × B(0,ρ) and a = G(x) = f(q) = y, so x = Λ(y,z′) and q = χ(z′) with z′ ∈ D.
9. Regularity. χ is C¹ on D; injective (Λ(y,·) and ψ injective); Dχ(z) = Dψ(Λ(y,z))∘DΛ(y,z)(0,·) is injective (DΛ invertible, Dψ injective).
10. Properness relative to (D, W₃). Let Q ⊆ W₃ be compact. V ∩ ψ⁻¹(Q) is compact (properness of ψ; Q ⊆ W) and contained in V₃ (ψ(V ∩ ψ⁻¹Q) ⊆ Q ∩ M ⊆ W₃ ∩ M = ψ(V₃), injectivity). Hence Φ(V ∩ ψ⁻¹(Q)) is a compact subset of B(y,ρ) × B(0,ρ), and D ∩ χ⁻¹(Q) = {z : (y,z) ∈ Φ(V ∩ ψ⁻¹(Q))} is compact (a closed slice of a compact set, contained in D).
11. Steps 7-10 show that (D, W₃, χ) is a C¹ Simon local representation of Σ_y around p with parameter space ℝᵏ = EuclideanSpace ℝ (Fin k); as p ∈ Σ_y was arbitrary, IsSimonSubmanifold (E := ℝᵏ) 1 Σ_y. (When m = 0 the same construction applies, with Φ = ι⁻¹π_{K_p}(· − x_p) and K_p = ℝⁿ.) Steps 1-11 prove C1Sard.

## Key steps

1. Linear algebra: √det(LL*) = 0 iff L is not surjective iff rank L < m.
2. J*f continuous on M (continuity of P), so C_M = M ∩ Z is Borel and relatively closed in M.
3. Co-area formula with g = 1_{C_M}: ∫ Hᵏ(M ∩ f⁻¹y ∩ Z) dy = ∫_{C_M} J*f = 0, hence a.e. zero.
4. Relative closedness by continuity of f and J*f; F = closure.
5. Regular fibers: chart ψ, G = f∘ψ submersion at the point, inverse function theorem for (G, projection to ker DG), slice chart χ(z) = ψ(Λ(y,z)) is a proper injective C¹ immersion onto W₃ ∩ fiber.

## Reference use

### local-project

Queries:
- `rg -n 'def BVCompactness' -A 10 project/GMT/Ch02/Contract.lean`
- `rg -n 'bvVariationOn|IsLocallyBV' project/GMT/Ch02/README.md`
- `rg -n 'theorem (IsOpen.measure_pos|IsCompact.measure_lt_top|setLIntegral_const|lintegral_add_right|le_div_iff_mul_le|div_lt_top)' mathlib/Mathlib`
- `rg -n 'theorem (_root_.)?(IsOpen.)?measure_pos' mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean; rg -n 'theorem (_root_.)?(IsCompact.)?measure_lt_top' mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/*.lean`
- `rg -n 'theorem (_root_.)?(HasCompactSupport.)?contDiff_convolution_left|theorem integral_lineDeriv_mul_eq|theorem (_root_.)?(Convex.)?addHaar_frontier|theorem convolution_tendsto_right' mathlib/Mathlib`
- `rg -n 'theorem (HasCompactSupport.contDiff_convolution_left|LipschitzWith.integral_lineDeriv_mul_eq|Convex.addHaar_frontier|mul_meas_ge_le_lintegral₀|ContDiffBump.convolution_tendsto_right)' mathlib/Mathlib`
- `rg -n 'exists_isClosed_sdiff_lt|exists_isClosed_diff_lt' mathlib/Mathlib; rg -n 'theorem LipschitzWith.ae_differentiableAt' mathlib/Mathlib/Analysis/Calculus/Rademacher.lean; rg -n 'theorem tendstoUniformlyOn_of_ae_tendsto' mathlib/Mathlib`
- `rg -il 'BoundedVariation|poincare' mathlib/Mathlib`
- `rg -n 'Submission.|theorem .*bv_compactness_poincare_extension|lipschitz_extension_and_rademacher' project`
- `grep -n '^theorem|^def|^noncomputable def' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean, then a full read of BV.lean`
- `python3 -I gen_checks.py (replays verifier gmt-compare.py contract_scope and child_modules for all 12 lean_statements); lake env lean AssemblyCheck.lean and NodeChallenge_00..11.lean against a scratch olean of GMT.Ch02.Submission`
- `#print axioms ChildCheck.unweighted_bound, ChildCheck.bvVariationOn_empty, ChildCheck.main_from_children`
- `read dag.json (active nodes) and nodes/root/decomposition-review-receipt-v1.json`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Convex/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Function/Egorov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root/decomposition-review-receipt-v1.json`
- `/tmp/gmt-ch02-decomp-v2-3S9D56/AssemblyCheck.lean`

Contract.lean:245-252 confirms that BVCompactness integrates the whole sum ‖u k x‖ₑ + bvVariationOn (u k) W over W. README row 7 describes the unweighted printed bound, but the frozen contract is authoritative, so bv_results now proves the conversion (step A0) before A1. The snapshot Mathlib supplies every fact A0 needs: _root_.IsOpen.measure_pos (OpenPos.lean:47), _root_.IsCompact.measure_lt_top (Typeclasses/Finite.lean:346), lintegral_add_right (Lebesgue/Add.lean:339), setLIntegral_const (Lebesgue/Basic.lean:121), ENNReal.le_div_iff_mul_le (ENNReal/Inv.lean:369) and ENNReal.div_lt_top (Inv.lean:214). A0 was kernel-checked as a scratch lemma against the frozen notation; it depends only on propext, Classical.choice and Quot.sound. The pinned SimonGMT BV.lean defines bvVariationOn as an iSup, over Lipschitz C_c fields with tsupport ⊆ W and sup norm ≤ 1, of ofReal ∫_W u·div g. Hence bvVariationOn u ∅ = 0, which was also kernel-checked. The same file provides ofReal_integral_le_bvVariationOn, IsC1TestField.isLipschitzTestField, bvVariationOn_le_liminf_of_locallyL1 and isLocallyBV_of_locallyL1_of_uniform_bound, which are used in A3-A4. Mathlib supplies the Section T tools: HasCompactSupport.contDiff_convolution_left, ContDiffBump.convolution_tendsto_right, LipschitzWith.integral_lineDeriv_mul_eq, Convex.addHaar_frontier and mul_meas_ge_le_lintegral₀. It also has the names cited by the unchanged children: MeasurableSet.exists_isClosed_sdiff_lt (Regular.lean:1036), LipschitzWith.ae_differentiableAt (Rademacher.lean:385) and tendstoUniformlyOn_of_ae_tendsto (Egorov.lean:205). There is no BV compactness, BV Poincaré or BV extension theorem in ℝⁿ; the BoundedVariation matches concern one-dimensional variation and vector measures. The project snapshot has no Submission.* declarations, and dag.json has only the root node, so the twelve bare lean_names do not collide. Using the comparator's own scope replay, all 12 child statements elaborate after import GMT.Ch02.Submission, the 12 generated NodeChallenge modules compile, and the 16-component constructor proves type_of% GMT.Ch02.main_theorem from the children.
