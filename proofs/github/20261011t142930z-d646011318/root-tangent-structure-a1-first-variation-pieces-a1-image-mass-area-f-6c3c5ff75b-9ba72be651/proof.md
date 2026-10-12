# Parent-supplied natural-language proof

- Parent DAG node: `root.tangent_structure-a1.first_variation_pieces-a1.image_mass_area_formula-a1`
- Child DAG node: `root.tangent_structure-a1.first_variation_pieces-a1.image_mass_area_formula-a1.det_tangential_gram-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 0 of the parent proof (the tangential Jacobian identity det S_P(Λ) = J^P(Λ)², which the parent obtains from the block-diagonal form of S_P(Λ) in an orthonormal basis adapted to P ⊕ P^⊥). Here the same block computation is carried out without completing b to a basis of E. No errata apply.

Notation. ⟨·,·⟩ is the inner product of E and δ is the Kronecker delta. For matrices, Xᵀ is the transpose and 1_m the m×m identity. S denotes the N×N matrix on the left-hand side, S_{ij} = ⟨Λpe_i, Λpe_j⟩ + ⟨e_i − pe_i, e_j − pe_j⟩, and G the k×k matrix on the right-hand side, G_{ac} = ⟨Λb_a, Λb_c⟩ (b_a is regarded as a vector of E through the inclusion P ⊆ E). Let Bm be the real N×k matrix with Bm_{ia} := ⟨e_i, b_a⟩, the i-th coordinate of b_a.

1. Projection formula. For every x ∈ E, p x = Σ_a ⟨b_a, x⟩ b_a: this is the expansion of the orthogonal projection onto P in the orthonormal basis b of P (Mathlib: OrthonormalBasis.starProjection_eq_sum_rankOne, i.e. P.starProjection = Σ_a rankOne(b_a, b_a)). The real inner product is symmetric, so ⟨b_a, e_i⟩ = Bm_{ia}, and therefore p e_i = Σ_a Bm_{ia} b_a for every i.

2. Orthonormality. ⟨b_a, b_c⟩ = δ_{ac} for all a, c. Indeed b is orthonormal in P (OrthonormalBasis.orthonormal with orthonormal_iff_ite), and the inclusion P ⊆ E preserves inner products.

3. BmᵀBm = 1_k. For all a, c, (BmᵀBm)_{ac} = Σ_i ⟨e_i, b_a⟩⟨e_i, b_c⟩ = ⟨b_a, b_c⟩ = δ_{ac}. The middle equality is Parseval's identity for the orthonormal basis (e_i) of E (OrthonormalBasis.sum_inner_mul_inner for EuclideanSpace.basisFun, whose vectors are EuclideanSpace.single i 1). The last equality is step 2.

4. First summand. By step 1 and the linearity of Λ, Λpe_i = Σ_a Bm_{ia} Λb_a. By bilinearity of the inner product, ⟨Λpe_i, Λpe_j⟩ = Σ_a Σ_c Bm_{ia} Bm_{jc} ⟨Λb_a, Λb_c⟩ = Σ_a Σ_c Bm_{ia} G_{ac} Bm_{jc} = (Bm G Bmᵀ)_{ij}.

5. Second summand. Expanding, ⟨e_i − pe_i, e_j − pe_j⟩ = ⟨e_i, e_j⟩ − ⟨e_i, pe_j⟩ − ⟨pe_i, e_j⟩ + ⟨pe_i, pe_j⟩. Each term is computed separately:
- ⟨e_i, e_j⟩ = δ_{ij}.
- By step 1, ⟨e_i, pe_j⟩ = Σ_a Bm_{ja}⟨e_i, b_a⟩ = Σ_a Bm_{ia}Bm_{ja}.
- By step 1, ⟨pe_i, e_j⟩ = Σ_a Bm_{ia}⟨b_a, e_j⟩ = Σ_a Bm_{ia}Bm_{ja}.
- By steps 1 and 2, ⟨pe_i, pe_j⟩ = Σ_a Σ_c Bm_{ia}Bm_{jc}δ_{ac} = Σ_a Bm_{ia}Bm_{ja}.
Hence ⟨e_i − pe_i, e_j − pe_j⟩ = δ_{ij} − (Bm Bmᵀ)_{ij}.

6. Matrix form. By steps 4 and 5, S = Bm G Bmᵀ + 1_N − Bm Bmᵀ = 1_N + Bm Y, where Y is the k×N matrix Y := G Bmᵀ − Bmᵀ.

7. Determinant. The Weinstein–Aronszajn (Sylvester) identity states det(1_N + XW) = det(1_k + WX) for every N×k matrix X and every k×N matrix W (Mathlib: Matrix.det_one_add_mul_comm). Apply it with X = Bm and W = Y, then use step 3 (BmᵀBm = 1_k):
det S = det(1_N + Bm Y) = det(1_k + Y Bm) = det(1_k + G(BmᵀBm) − BmᵀBm) = det(1_k + G − 1_k) = det G.
This is the claim.

8. Degenerate cases. The argument is uniform in k and N.
- If k = 0 (P = 0): Bm is an N×0 matrix, so S = 1_N. Both determinants equal 1, because the determinant of the empty matrix is 1.
- If N = 0: then k = 0 as well, and both sides are empty determinants.

Imports: none beyond the frozen scope; all lemmas cited above are reachable from `import GMT.Ch04.Submission`.

Remark (relation to the parent's argument). Complete b by an orthonormal basis b' of P^⊥, and let O = [Bm | Bm'] be the resulting orthogonal matrix. Then O diag(G, 1) Oᵀ = Bm G Bmᵀ + Bm'Bm'ᵀ = Bm G Bmᵀ + 1_N − Bm Bmᵀ. By step 6 this equals S, which is the parent's block-diagonal statement det S = (det O)² det diag(G, 1) = det G. Steps 6–7 reach the same conclusion without choosing b'. ∎

## Key steps

1. Expand p e_i = Σ_a ⟨b_a, e_i⟩ b_a in the orthonormal basis b of P (starProjection_eq_sum_rankOne) and set Bm_{ia} := ⟨e_i, b_a⟩
2. BmᵀBm = 1_k by Parseval in the standard basis of E and orthonormality of b
3. Entrywise: ⟨Λpe_i, Λpe_j⟩ = (Bm G Bmᵀ)_{ij} and ⟨e_i − pe_i, e_j − pe_j⟩ = δ_{ij} − (Bm Bmᵀ)_{ij}, so S = 1_N + Bm(G Bmᵀ − Bmᵀ)
4. Weinstein–Aronszajn det(1_N + XW) = det(1_k + WX) (Matrix.det_one_add_mul_comm) with BmᵀBm = 1_k gives det S = det(1_k + G − 1_k) = det G

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
