# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.carrier_area_formula-a1.piece_area_formula-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.carrier_area_formula-a1.piece_area_formula-a1.carrier_side-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 5 and 6 of the parent proof (Simon Ch. 3 §2, (2.4)–(2.5): along the parametrized piece the tangential Jacobian of F times the Jacobian of the parametrization g is the Jacobian of F∘g = G∘g; combined with the injective Lipschitz area formula of Simon Ch. 2 §3). Notation: λ := volume on ℝ^n; H^n := μHE[n] on ℝ^P; for linear maps, normDet is Mathlib's LinearMap.normDet (≥ 0, normDet_nonneg); areaJacobianAt ψ a = normDet(Dψ(a)) (SimonGMT areaJacobianAt_eq_normDet; import Poincare.SimonGMT.Chapter02.AreaLipschitz). Library facts: (A2) for a Lipschitz ψ : E → E' between finite-dimensional real inner product spaces, a Borel s ⊆ E on which ψ is injective and an arbitrary κ : E' → [0, ∞], ∫_{ψ(s)} κ dμHE[finrank ℝ E] = ∫_s ofReal(areaJacobianAt ψ a) · κ(ψ(a)) dλ(a) (Poincare.SimonGMT.Chapter02.weighted_area_formula_lipschitz_injOn); (G1) for linear L : U → W' and B : W' → W'', normDet(B ∘ L) = normDet(B.domRestrict (range L)) · normDet(L) (LinearMap.normDet_comp); (G2) for linear f : U → W' and an orthonormal basis b of U, normDet(f)^2 = det(Matrix.gram ℝ (f ∘ b)) = det(⟨f b_i, f b_j⟩)_{i,j} (LinearMap.normDet_sq_eq_det_gram; over ℝ the coercion ℝ → ℝ is the identity, RCLike.ofReal_real_eq_id); (D) normDet(f) = |det f| for an endomorphism f of a finite-dimensional real inner product space (LinearMap.normDet_eq_abs_det).
1. (Gram identity.) Let B : ℝ^P → ℝ^n be linear and S, W ⊆ ℝ^P subspaces with S = W, and let u := stdOrthonormalBasis ℝ S. Applying (G2) to f := B.domRestrict S (whose value at u_i is B u_i) and b := u gives normDet(B.domRestrict S)^2 = det(⟨B u_i, B u_j⟩)_{i,j}. As normDet ≥ 0, Real.sqrt_sq gives sqrt(det(⟨B u_i, B u_j⟩)_{i,j}) = normDet(B.domRestrict S) = normDet(B.domRestrict W).
2. (Injective area formula for g.) Apply (A2) with ψ := g (Lipschitz), s := A (Borel, g injective on A) and κ(x) := ofReal(J_T(x)) · h(x) (no measurability of κ is needed). Since finrank ℝ ℝ^n = n (finrank_euclideanSpace_fin), μHE[finrank ℝ ℝ^n] = μHE[n], and we get ∫_{g(A)} ofReal(J_T(x)) · h(x) dH^n(x) = ∫_A ofReal(areaJacobianAt g a) · (ofReal(J_T(g(a))) · h(g(a))) dλ(a).
3. (Reduction to an a.e. pointwise identity.) By lintegral_congr_ae it suffices to show, for λ⌞A-a.e. a, that ofReal(areaJacobianAt g a) · (ofReal(J_T(g(a))) · h(g(a))) = ofReal(|det D(G∘g)(a)|) · h(g(a)). By the hypothesis on T and ae_restrict_mem (A is Borel), λ⌞A-a.e. a satisfies a ∈ A and T(g(a)) = range Dg(a). Fix such an a and put x := g(a) ∈ g(A) ⊆ V, L := Dg(a), B := DF(x).
4. (G is differentiable at x with DG(x) = B.) V is open and x ∈ V, so V is a neighbourhood of x (IsOpen.mem_nhds) on which F = G; hence F and G agree eventually near x (Filter.eventuallyEq_of_mem). F is differentiable at x (x ∈ g(A)), so G is differentiable at x (DifferentiableAt.congr_of_eventuallyEq) and DG(x) = DF(x) = B (Filter.EventuallyEq.fderiv_eq).
5. (Chain rule.) g is differentiable at a (a ∈ A), so by fderiv_comp, D(G∘g)(a) = DG(x) ∘ Dg(a) = B ∘ L, also as linear maps (ContinuousLinearMap.toLinearMap_comp).
6. (Jacobian factorization.) By (D), |det D(G∘g)(a)| = normDet(B ∘ L). By (G1), normDet(B ∘ L) = normDet(B.domRestrict (range L)) · normDet(L). By step 1 with S := T(x) and W := range L (equal by the choice of a), normDet(B.domRestrict (range L)) = sqrt(det(⟨B u_i, B u_j⟩)_{i,j}) with u the standard orthonormal basis of T(x), which is J_T(x). Also areaJacobianAt g a = normDet(L). Hence |det D(G∘g)(a)| = J_T(g(a)) · areaJacobianAt g a.
7. (The integrands agree.) Since J_T(g(a)) = sqrt(…) ≥ 0, ENNReal.ofReal_mul gives ofReal(J_T(g(a)) · areaJacobianAt g a) = ofReal(J_T(g(a))) · ofReal(areaJacobianAt g a). Therefore ofReal(|det D(G∘g)(a)|) · h(g(a)) = ofReal(J_T(g(a))) · ofReal(areaJacobianAt g a) · h(g(a)), which equals ofReal(areaJacobianAt g a) · (ofReal(J_T(g(a))) · h(g(a))) by commutativity and associativity in [0, ∞] (ring).
8. (Conclusion.) By steps 3–7 the two integrands of step 2 agree λ⌞A-a.e., so ∫_{g(A)} ofReal(J_T(x)) · h(x) dH^n(x) = ∫_A ofReal(|det D(G∘g)(a)|) · h(g(a)) dλ(a). ∎

## Key steps

1. Gram identity: for u the standard orthonormal basis of S = W, sqrt(det(⟨B u_i, B u_j⟩)) = normDet(B.domRestrict W) (normDet_sq_eq_det_gram, normDet ≥ 0).
2. The injective Lipschitz area formula (A2) for g with the arbitrary weight ofReal(J_T)·h gives ∫_{g(A)} ofReal(J_T)·h dH^n = ∫_A ofReal(areaJacobianAt g)·ofReal(J_T∘g)·h∘g dλ.
3. For a.e. a ∈ A with T(g(a)) = range Dg(a): F = G near g(a), so DG(g(a)) = DF(g(a)) and D(G∘g)(a) = DF(g(a))∘Dg(a).
4. |det D(G∘g)(a)| = normDet(DF(g(a))∘Dg(a)) = normDet(DF(g(a))|_{range Dg(a)})·normDet(Dg(a)) = J_T(g(a))·areaJacobianAt g a (normDet_eq_abs_det, normDet_comp, Gram identity).
5. ENNReal.ofReal_mul and lintegral_congr_ae identify the two integrals.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (local-project; project b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib 25730c7c759d108ef87ab70af2342a196760f79d); cmp project/GMT/Ch07/Contract.lean against workspace GMT/Ch07/Contract.lean (identical)`
- `python3 -I read of nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-065b37e1ba/parent-child-handoff.json and parent-supplied-plan.md`
- `grep -n 'theorem weighted_area_formula_lipschitz_fiberSum|theorem aemeasurable_weightedAreaFiberSum_lipschitz|theorem weighted_area_formula_lipschitz_injOn|def weightedAreaFiberSum|def areaJacobianAt|theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn' -r .lake/packages/simongmt/Poincare/SimonGMT`
- `grep -n 'theorem|lemma|def ' mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean (normDet_comp, normDet_sq_eq_det_gram, normDet_eq_abs_det, normDet_nonneg)`
- `grep -rn euclideanHausdorffMeasure_eq_volume mathlib/Mathlib; grep tprod_image (to_additive tsum_image) in mathlib/Mathlib/Topology/Algebra/InfiniteSum/Basic.lean; grep exists_measurable_superset_of_null mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`
- `python3 -I scans of dag.json: nodes whose lean_statement has fibre tsums, stdOrthonormalBasis or LinearMap.det; carrier_area_formula-a1 and rectifiable_area_formula-a1 subtrees; git show c2cf4bd9 (accepted dpf_raf_piece_area_formula_gram proof)`
- `grep -c idtp_caf_paf dag.json DAG.md dag.mmd issue-workers.json; grep -rl nodes/; git grep idtp_caf_paf over all ref tips; grep in simongmt and GMT sources (all no match)`
- `lake env lean /tmp/paf_split_dec/Stmts.lean (child stubs plus assembly of the frozen parent type), Proofs.lean (full child proofs), Full.lean (end-to-end), Challenge_*.lean (exact comparator form), Bare_*/Lip_*/Noninj_c2.lean (minimal imports per child)`
- `python3 -I /tmp/paf_split_scripts/validate.py (verifier/lean_contract.py validate_lean_statement) and gen_challenge.py (verifier/gmt-compare.py child_modules, contract mode)`
- `independent reviewer subagent: /tmp/paf_split_review/indep/Implication.lean (children as axioms; #print axioms), Min_*.lean, Challenge_*.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-065b37e1ba/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-065b37e1ba/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaNoninjective.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaMultiplicity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/InfiniteSum/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/paf_split_dec/Stmts.lean`
- `/tmp/paf_split_dec/Proofs.lean`
- `/tmp/paf_split_dec/Full.lean`
- `/tmp/paf_split_review/subproblems.json`
- `/tmp/paf_split_review/indep/Implication.lean`

The pins match: snapshot project b4d606d is the workspace HEAD, mathlib is 25730c7c, and Contract.lean is identical to the snapshot copy.

Library support.
- SimonGMT provides (A1) aemeasurable_weightedAreaFiberSum_lipschitz and weighted_area_formula_lipschitz_fiberSum (Chapter02/AreaNoninjective.lean), (A2) weighted_area_formula_lipschitz_injOn with an arbitrary weight (Chapter02/AreaLipschitz.lean), areaJacobianAt_eq_normDet, and (L1) euclideanHausdorffMeasure_image_le_of_lipschitzOn, which is already in the contract import closure.
- Mathlib provides LinearMap.normDet_comp, normDet_sq_eq_det_gram, normDet_eq_abs_det, EuclideanSpace and InnerProductSpace euclideanHausdorffMeasure_eq_volume, tsum_image and exists_measurable_superset_of_null.

Statement scope. normDet, areaJacobianAt and weightedAreaFiberSum are not in the contract scope, so the child statements use |LinearMap.det|, Gram determinants and subtype tsums.

No reuse. The accepted dpf_raf_piece_area_formula_gram (commit c2cf4bd) is the closest analogue and served as a proof template, but no existing DAG declaration has a matching type, so fresh idtp_caf_paf_* names are used; none of them occurs anywhere.

Lean checks.
- All three child types elaborate in the exact comparator form.
- The frozen parent type follows from them; with the children as axioms, the only other axioms are propext, Classical.choice and Quot.sound.
- Each child has a complete proof with only the standard axioms. Extra imports: none for child 1, Chapter02.AreaNoninjective for child 2, Chapter02.AreaLipschitz for child 3.
