# Parent-supplied natural-language proof

- Parent DAG node: `root.tangent_structure-a1.first_variation_pieces-a1.image_mass_area_formula-a1`
- Child DAG node: `root.tangent_structure-a1.first_variation_pieces-a1.image_mass_area_formula-a1.piece_image_area_formula-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 3(b)–(e) of the parent proof ("The area formula on one piece", Simon Ch. 4, 1.5–1.6 with the area formula of Ch. 3 §2 / Ch. 2 §3), together with steps 0 and 3(c) for the tangential Jacobian. The parent applies the argument to its Borel hull A of M_i, with the field y ↦ range DF_i(ψ_i(y)) and the weight u = ofReal(θ ∘ f⁻¹). Here the set A, the field P and the weight w are arbitrary within the stated hypotheses. No errata apply.

Notation. Lⁿ := volume (Lebesgue measure) on ℝⁿ. For a linear map T: U → V between finite-dimensional real inner product spaces, normDet(T) ≥ 0 is Mathlib's LinearMap.normDet (LinearMap.normDet_nonneg). For a linear subspace Q of U, T|_Q := T ∘ ι_Q: Q → V is the restriction (LinearMap.domRestrict). For Φ: ℝⁿ → E, JΦ(v) := normDet(DΦ(v)), where DΦ(v) = fderiv ℝ Φ v; this is SimonGMT Chapter02.areaJacobianAt Φ v, and areaJacobianAt_eq_normDet is the unfolding lemma. For y ∈ E put jac(y) := jac(Df(y), P(y)); this is exactly the Real.sqrt (Matrix.det …) expression in the integrand of the statement. L_F and L_f denote Lipschitz constants of F and f.
Imports: the frozen scope does not contain these results. weighted_area_formula_lipschitz_injOn, areaJacobianAt and the normDet lemmas become available once Submission.lean adds `import Poincare.SimonGMT.Chapter02.AreaLipschitz`, which transitively imports Mathlib.Analysis.InnerProductSpace.NormDet; branches of this run that are already accepted add this import. The statement itself elaborates in the frozen scope.

1. The tangential Jacobian is a norm determinant: jac(Λ, Q) = normDet(Λ|_Q) for every Λ ∈ L(E, E) and every subspace Q ⊆ E. Let k := dim Q and let b be an orthonormal basis of Q indexed by Fin k (e.g. stdOrthonormalBasis ℝ Q).
- By the sibling theorem ts_fv_det_tangential_gram_eq (with N := n + ℓ, P := Q, this b and Λ), det[⟨Λpe_i, Λpe_j⟩ + ⟨e_i − pe_i, e_j − pe_j⟩]_{i,j} = det[⟨Λb_a, Λb_c⟩]_{a,c}.
- By LinearMap.normDet_sq_eq_det_gram applied to Λ|_Q and b, normDet(Λ|_Q)² = det Gram((Λ|_Q)(b_a))_a = det[⟨Λb_a, Λb_c⟩]_{a,c}. Here Matrix.gram ℝ v is by definition Matrix.of fun a c ↦ ⟨v a, v c⟩, (Λ|_Q)(b_a) = Λ(b_a), and the coercion ℝ → ℝ in that lemma is the identity.
- Hence the determinant under the square root in jac(Λ, Q) equals normDet(Λ|_Q)². Since normDet(Λ|_Q) ≥ 0, jac(Λ, Q) = √(normDet(Λ|_Q)²) = normDet(Λ|_Q).
In particular jac(y) = normDet(Df(y)|_{P(y)}) ≥ 0 for every y ∈ E.

2. The parameter set. Let B := C ∩ F⁻¹(A).
- B is Borel: F is Lipschitz, hence continuous, so F⁻¹(A) is Borel, and C is Borel.
- F(B) = A. The inclusion F(B) ⊆ A is clear. Conversely, if y ∈ A, then y ∈ F(C) because A ⊆ F(C), so y = F(v) with v ∈ C. Then v ∈ F⁻¹(A), i.e. v ∈ B, and y = F(v) ∈ F(B).
- F is injective on B, because B ⊆ C.

3. The composite map. Let G := f ∘ F.
- G is Lipschitz with constant L_f·L_F (LipschitzWith.comp).
- G is injective on B. Let v, v' ∈ B with f(F(v)) = f(F(v')). Then F(v), F(v') ∈ A and f is injective on A, so F(v) = F(v'). Since F is injective on B, v = v'.
- G(B) = f(F(B)) = f(A) by step 2.

4. Chain rule for the Jacobians. Let v ∈ B. Then v ∈ C, so F is differentiable at v; and F(v) ∈ A, so f is differentiable at F(v). By the chain rule (fderiv_comp), DG(v) = Df(F(v)) ∘ DF(v). LinearMap.normDet_comp says normDet(T₂ ∘ T₁) = normDet(T₂|_{range T₁})·normDet(T₁) for linear maps T₁: U → V and T₂: V → W. Therefore JG(v) = normDet(Df(F(v))|_{range DF(v)})·JF(v). Since v ∈ C and F(v) ∈ A, the hypothesis on P gives range DF(v) = P(F(v)). By step 1, JG(v) = jac(F(v))·JF(v).

5. The weighted area formula. SimonGMT Chapter02.weighted_area_formula_lipschitz_injOn applies to a Lipschitz map Φ: ℝⁿ → E, a Borel set S ⊆ ℝⁿ on which Φ is injective, and an arbitrary g: E → [0, ∞] (no measurability is required). It gives
∫⁻_{Φ(S)} g dμHE[finrank ℝ ℝⁿ] = ∫⁻_S ofReal(JΦ(v))·g(Φ(v)) dLⁿ(v).
Here finrank ℝ ℝⁿ = n (finrank_euclideanSpace_fin), so the measure on the left is Hⁿ.
(a) Take Φ = G, S = B, g = w; the hypotheses hold by steps 2 and 3. Since G(B) = f(A):
∫⁻_{f(A)} w dHⁿ = ∫⁻_B ofReal(JG(v))·w(f(F(v))) dLⁿ(v).
(b) Take Φ = F, S = B, g = h, where h(y) := ofReal(jac(y))·w(f(y)); the hypotheses hold by step 2. Since F(B) = A:
∫⁻_A ofReal(jac(y))·w(f(y)) dHⁿ(y) = ∫⁻_B ofReal(JF(v))·ofReal(jac(F(v)))·w(f(F(v))) dLⁿ(v).

6. Comparison of the integrands. Let v ∈ B. By step 4 and ENNReal.ofReal_mul (applicable since jac(F(v)) ≥ 0 by step 1),
ofReal(JG(v))·w(f(F(v))) = ofReal(jac(F(v)))·ofReal(JF(v))·w(f(F(v))) = ofReal(JF(v))·ofReal(jac(F(v)))·w(f(F(v))).
So the integrands of 5(a) and 5(b) agree at every point of the Borel set B, and the two integrals over B are equal (setLIntegral_congr_fun). Combining 5(a), this equality and 5(b):
∫⁻_{f(A)} w dHⁿ = ∫⁻_A ofReal(jac(y))·w(f(y)) dHⁿ(y).
This is the claim, since jac(y) is the Real.sqrt (Matrix.det …) expression of the statement with Λ = Df(y) = fderiv ℝ f y and Q = P(y).

7. Degenerate cases. No step uses n ≥ 1, ℓ ≥ 1 or A ≠ ∅, and weighted_area_formula_lipschitz_injOn has no dimension or nonemptiness hypothesis. So the argument applies verbatim when n = 0 and when A = ∅ (then both sides vanish). If n = 0, ℝⁿ is a single point and step 1 still applies, including to Q = 0, where both sides equal 1. ∎

## Key steps

1. jac(Λ, Q) = normDet(Λ|_Q): sibling ts_fv_det_tangential_gram_eq with an orthonormal basis b of Q, LinearMap.normDet_sq_eq_det_gram and normDet ≥ 0
2. B := C ∩ F⁻¹(A) is Borel with F(B) = A and F injective on B; G := f ∘ F is Lipschitz, injective on B, and G(B) = f(A)
3. For v ∈ B: fderiv_comp, LinearMap.normDet_comp and P(F v) = range DF(v) give JG(v) = jac(F v)·JF(v)
4. weighted_area_formula_lipschitz_injOn for G with weight w and for F with weight ofReal(jac)·(w ∘ f); the integrands over B agree pointwise

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; sha256sum <snapshot>/project/GMT/Ch04/Contract.lean GMT/Ch04/Contract.lean GMT/Ch04/Submission.lean`
- `git show 572b89ba951337627a042d201ea519a6496a45e9:GMT/Ch04/Submission.lean | grep -n '^import\|^theorem'`
- `grep -n 'theorem\|lemma\|def' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `grep -n 'theorem det_one_add_mul_comm' <snapshot>/mathlib/Mathlib/LinearAlgebra/Matrix/SchurComplement.lean`
- `grep -n 'starProjection_eq_sum_rankOne\|sum_inner_mul_inner' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean; grep -n '^def gram' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/GramMatrix.lean`
- `grep -rn 'theorem lintegral_iUnion₀\|theorem setLIntegral_congr\|theorem MeasurableSet.image_of_continuousOn_injOn' <snapshot>/mathlib/Mathlib/MeasureTheory`
- `grep -rn 'theorem weighted_area_formula_lipschitz_injOn\|theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn\|def areaJacobianAt\|areaJacobianAt_eq_normDet\|nullMeasurableSet_image_of_lipschitzOn' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02`
- `grep -n import Chapter02/{Lipschitz,Area,AreaLipschitz}.lean Chapter03/Rectifiable.lean (frozen import closure)`
- `lean Probe.lean (#check of MeasurableSet.image_of_continuousOn_injOn, NullMeasurableSet.exists_measurable_{subset,superset}_ae_eq, setLIntegral_congr, ae_restrict_mem₀, ae_restrict_of_ae_restrict_of_subset, Function.invFunOn_{mem,eq}, InjOn.leftInvOn_invFunOn, leftInverse_invFun, lintegral_iUnion₀, euclideanHausdorffMeasure_image_le_of_lipschitzOn, Disjoint.image, finrank_euclideanSpace_fin, fderiv_comp, ENNReal.ofReal_mul in the frozen scope)`
- `python3 -I scripts/gen.py (verifier gmt-compare.child_modules mode contract + lean_contract.validate_lean_statement); lean gen/Challenge_*.lean`
- `lean asm/AProof.lean; lean asm/BfromA.lean; lean asm/Assembly.lean; lean asm/Full.lean (#print axioms)`
- `build candidate Submission with the four proofs; lean gen2/Solution_*.lean (exact Submission.X for 3 children + parent dag.json type)`
- `python3 -I scripts/numcheck.py (3000 random instances of det S_P(Λ) = det Gram)`
- `grep dag.json, pinned packages and git grep over all 364 refs for ts_fv_det_tangential_gram_eq|ts_fv_piece_image_area_formula|ts_fv_lintegral_image_eq_of_pieces`
- `python3 scan of dag.json nodes (ts_fv_* siblings, ts_pdb_piece_area_formula, ts_pdb_linear_range_integral, ts_pdb_image_closedBall_measure_le) and parent decomposition-v1.json`
- `git show <branch>:GMT/Ch04/Submission.lean | grep 'import Poincare.SimonGMT.Chapter02.AreaLipschitz' over lipschitz-pieces branches`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/project/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/LinearAlgebra/Matrix/SchurComplement.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/InnerProductSpace/GramMatrix.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-first-variation-pieces-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-first-variation-pieces-a1-image-mass-area-formula-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/ch04-imaf/gen/Challenge_ts_fv_det_tangential_gram_eq.lean`
- `/tmp/ch04-imaf/gen/Challenge_ts_fv_piece_image_area_formula.lean`
- `/tmp/ch04-imaf/gen/Challenge_ts_fv_lintegral_image_eq_of_pieces.lean`
- `/tmp/ch04-imaf/asm/AProof.lean`
- `/tmp/ch04-imaf/asm/BfromA.lean`
- `/tmp/ch04-imaf/asm/Assembly.lean`
- `/tmp/ch04-imaf/asm/Full.lean`
- `/tmp/ch04-imaf/gen2/Solution_ts_fv_image_mass_area_formula.lean`
- `/tmp/ch04-imaf/scripts/numcheck.py`

Pinned state:
- The snapshot Contract.lean, the workspace Contract.lean and the workspace Submission.lean are byte-identical (sha256 prefix 6e58e5dddd9625cc).
- The proof base 572b89b adds no helper lemmas.
- Mathlib is at 25730c7c and SimonGMT at 2b366308.

Frozen import closure:
- Chapter03.Rectifiable imports Chapter02.Lipschitz, so euclideanHausdorffMeasure_image_le_of_lipschitzOn is available.
- Chapter02.Area (areaJacobianAt) and Mathlib NormDet are not available, so no child type mentions normDet, adjoint or Matrix.gram.

Cited results, each found with the stated meaning:
- Mathlib snapshot:
  - NormDet.lean: normDet_nonneg (l.75), normDet_sq_eq_det_gram (l.303), normDet_comp (l.324).
  - SchurComplement.lean: Matrix.det_one_add_mul_comm (l.400).
  - PiL2.lean: OrthonormalBasis.starProjection_eq_sum_rankOne (l.572), OrthonormalBasis.sum_inner_mul_inner (l.506).
  - GramMatrix.lean: Matrix.gram := of fun i j ↦ ⟪v i, v j⟫ (l.39).
  - Lebesgue/Basic.lean: lintegral_iUnion₀ (l.592), setLIntegral_congr (l.281).
  - Polish/Basic.lean: MeasurableSet.image_of_continuousOn_injOn (l.821).
- SimonGMT Chapter02:
  - weighted_area_formula_lipschitz_injOn: global LipschitzWith, MeasurableSet source, InjOn, arbitrary non-measurable weight; target measure μHE[finrank].
  - euclideanHausdorffMeasure_image_le_of_lipschitzOn.
  - areaJacobianAt and areaJacobianAt_eq_normDet.

No-match results:
- No existing declaration proves the Gram-determinant identity, the one-piece image area formula, or the image-integral gluing.
- The related ts_pdb_* nodes are unaccepted and have different statements, so nothing is reused.
- None of the three proposed names occurs in dag.json, the pinned packages, the snapshot, or any of the 364 refs.

Lean checks:
- The three child types validate and compile as comparator NodeChallenge files.
- A is proved in the frozen scope.
- B is proved from A with the AreaLipschitz import, which accepted branches of this run already use.
- C is proved.
- The parent's exact frozen type is proved from B and C.
- All four declarations compile together with axioms [propext, Classical.choice, Quot.sound].
- NodeSolution checks pass for the 3 children and for the parent.
- A numeric check of A on 3000 random instances gives max relative error 1.4e-9.
- Independent adversarial review: ACCEPT.
