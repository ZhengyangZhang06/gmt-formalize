# Parent-supplied natural-language proof

- Parent DAG node: `root.variation_formulas-a1.gram_det_derivatives-a1`
- Child DAG node: `root.variation_formulas-a1.gram_det_derivatives-a1.det_derivatives_at_one-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 4–6 of the parent proof of variation_gram_det_derivatives (Simon Ch. 2, p. 62). Simon quotes the general formula det(I + A) = 1 + tr A + ½(tr A)² − ½ tr(A²) + O(|A|³) without proof. Statements (1) and (2) are its derivative form, and the proof below is the parent's Leibniz-expansion argument with all details written out.

Notation.
- Perm(ι) is the finite group of permutations of ι, id its identity and sgn(σ) ∈ {1, −1} the sign of σ.
- δ_{ab} := 1 if a = b and 0 otherwise, so I_{ab} = δ_{ab}.
- For m ∈ ι, Π_{j≠m} denotes the product over the finite set ι∖{m}. For m ≠ l, Π_{j∉{m,l}} denotes the product over ι∖{m,l}.
- "f has derivative c at x" is the usual one-variable notion (HasDerivAt).

1. Leibniz expansion. For every real ι×ι matrix M, det M = Σ_{σ∈Perm(ι)} sgn(σ) Π_{i∈ι} M_{σ(i) i} (Matrix.det_apply; the unit sgn(σ) ∈ ℤˣ acts on ℝ as multiplication by the integer ±1). Hence h(t) = Σ_σ sgn(σ) Π_i G(t)_{σ(i) i} for every real t.

2. Derivative of h at a point. Let x ∈ ℝ and let H be a real ι×ι matrix such that, for all i, k, the function s ↦ G(s)_{ik} has derivative H_{ik} at x.
- Fix σ. Apply the product rule for a finite product of real functions (HasDerivAt.finsetProd) to the factors f_i(t) := G(t)_{σ(i) i}, whose derivatives at x are H_{σ(i) i}. So t ↦ Π_i G(t)_{σ(i) i} has derivative Σ_{m∈ι} (Π_{j≠m} G(x)_{σ(j) j}) · H_{σ(m) m} at x.
- Multiply by the constant sgn(σ) and sum over the finitely many σ (sum rule). By step 1, h has derivative
 L(x, H) := Σ_σ sgn(σ) Σ_m (Π_{j≠m} G(x)_{σ(j) j}) · H_{σ(m) m}
 at x.

3. Permutation facts.
(a) Let σ ≠ id and m ∈ ι. Then some j ≠ m has σ(j) ≠ j.
 Since σ ≠ id, pick y with σ(y) ≠ y. If y ≠ m, take j := y. If y = m, take j := σ(m). Then j ≠ m. Also σ(j) ≠ j, because σ(σ(m)) = σ(m) would give σ(m) = m by injectivity.
(b) Hence, for σ ≠ id and every m, Π_{j≠m} δ_{σ(j) j} = 0, since the factor at the j of (a) is 0. For σ = id every factor is 1, so the product is 1.
(c) Let m ≠ l and let τ := (m l) be the transposition. If σ ∉ {id, τ}, then some j ∉ {m, l} has σ(j) ≠ j.
 Suppose instead that σ fixes every j ∉ {m, l}. Then every point moved by σ lies in {m, l}. Also, if σ moves y, then σ moves σ(y): σ(σ(y)) = σ(y) would give σ(y) = y by injectivity.
 - Case σ(m) = m. If σ moved some y, then y ∈ {m, l} and y ≠ m, so y = l. Then σ(l) is moved, so σ(l) ∈ {m, l}. As σ(l) ≠ l, σ(l) = m = σ(m), which contradicts injectivity because l ≠ m. So σ moves nothing and σ = id, a contradiction.
 - Case σ(m) ≠ m. Then σ(m) is moved, so σ(m) ∈ {m, l}, hence σ(m) = l. Next, σ(l) ≠ l, for otherwise σ(l) = l = σ(m). So σ(l) is moved, σ(l) ∈ {m, l} and σ(l) ≠ l, hence σ(l) = m. Now σ agrees with τ at m and at l, and both fix every j ∉ {m, l}. So σ = τ, a contradiction.
(d) Hence, for m ≠ l, Π_{j∉{m,l}} δ_{σ(j) j} equals 0 if σ ∉ {id, τ} and equals 1 if σ ∈ {id, τ}, because τ fixes every j ∉ {m, l}. Moreover id ≠ τ since τ(m) = l ≠ m, sgn(id) = 1, sgn(τ) = −1, τ(l) = m and τ(m) = l.

4. The first-order sum at the identity. For every real ι×ι matrix H,
 E(H) := Σ_σ sgn(σ) Σ_m (Π_{j≠m} δ_{σ(j) j}) · H_{σ(m) m} = Σ_m H_{mm} = tr H.
 By 3(b), every summand with σ ≠ id vanishes. The summand σ = id equals 1 · Σ_m 1 · H_{mm}.

5. Proof of (1). Step 2 with x = 0 and H = G₁ shows that h has derivative L(0, G₁) at 0. Since G(0) = I, G(0)_{σ(j) j} = δ_{σ(j) j}, so L(0, G₁) = E(G₁) = tr G₁ by step 4.

6. Proof of (2): differentiability near 0. Let U be a neighbourhood of 0 such that, for every t ∈ U and all i, k, s ↦ G(s)_{ik} has derivative G′(t)_{ik} at t. For every real t define
 φ(t) := Σ_σ sgn(σ) Σ_m (Π_{j≠m} G(t)_{σ(j) j}) · G′(t)_{σ(m) m}.
 For t ∈ U, step 2 with x = t and H = G′(t) shows that h has derivative φ(t) at t. So h is differentiable at every t ∈ U, and deriv h(t) = φ(t) for every t ∈ U.

7. Derivative of φ at 0. Put B := G′(0). Since 0 ∈ U, each entry s ↦ G(s)_{ik} has derivative B_{ik} at 0. Fix σ and m.
- By the finite product rule over ι∖{m}, the function t ↦ Π_{j≠m} G(t)_{σ(j) j} has derivative Σ_{l≠m} (Π_{j∉{m,l}} G(0)_{σ(j) j}) · B_{σ(l) l} at 0.
- By hypothesis, t ↦ G′(t)_{σ(m) m} has derivative (G₂)_{σ(m) m} at 0, and its value at 0 is B_{σ(m) m}.
- By the product rule, t ↦ (Π_{j≠m} G(t)_{σ(j) j}) · G′(t)_{σ(m) m} has derivative
 [Σ_{l≠m} (Π_{j∉{m,l}} G(0)_{σ(j) j}) · B_{σ(l) l}] · B_{σ(m) m} + (Π_{j≠m} G(0)_{σ(j) j}) · (G₂)_{σ(m) m}
 at 0.
- Multiplying by sgn(σ) and summing over m and σ: φ has derivative φ₁ at 0, where φ₁ is the corresponding signed sum of these expressions.

8. Evaluation of φ₁. Use G(0)_{ab} = δ_{ab} and split φ₁ = V₁ + V₂, where
 V₂ := Σ_σ sgn(σ) Σ_m (Π_{j≠m} δ_{σ(j) j}) · (G₂)_{σ(m) m} and
 V₁ := Σ_σ sgn(σ) Σ_m Σ_{l≠m} (Π_{j∉{m,l}} δ_{σ(j) j}) · B_{σ(l) l} · B_{σ(m) m}.
- By step 4, V₂ = E(G₂) = tr G₂.
- Interchanging the finite sums, V₁ = Σ_m Σ_{l≠m} Σ_σ sgn(σ) (Π_{j∉{m,l}} δ_{σ(j) j}) · B_{σ(l) l} · B_{σ(m) m}.
- Fix m ≠ l. By 3(d), only σ = id and σ = τ = (m l) contribute, each with product 1. The term σ = id is B_{ll} B_{mm}, and the term σ = τ is −B_{ml} B_{lm}. So V₁ = Σ_m Σ_{l≠m} (B_{ll} B_{mm} − B_{ml} B_{lm}).
- At l = m the expression B_{ll} B_{mm} − B_{ml} B_{lm} is B_{mm}² − B_{mm}² = 0, so adding these terms changes nothing:
 V₁ = Σ_m Σ_l (B_{ll} B_{mm} − B_{ml} B_{lm}) = (Σ_l B_{ll})(Σ_m B_{mm}) − Σ_m (B·B)_{mm} = (tr B)² − tr(B·B),
 using (B·B)_{mm} = Σ_l B_{ml} B_{lm}.
- Hence φ₁ = tr G₂ + (tr G′(0))² − tr(G′(0)·G′(0)).

9. Conclusion of (2). By step 6, deriv h agrees with φ on the neighbourhood U of 0. By steps 7–8, φ has derivative φ₁ at 0. Therefore deriv h has derivative tr G₂ + (tr G′(0))² − tr(G′(0)·G′(0)) at 0 (HasDerivAt.congr_of_eventuallyEq). With step 6 this proves (2).

10. Remarks.
- If ι is empty, then Perm(ι) = {id}, det of the empty matrix is 1, h ≡ 1 and all traces are 0. Steps 1–9 cover this case verbatim.
- If G is twice continuously differentiable near 0 with G′(0) = B and G″(0) = C (entrywise), then (1) and (2) give h′(0) = tr B and h″(0) = tr C + (tr B)² − tr(B·B). This is the derivative form of Simon's expansion of det(I + A). The remark is not used above.

## Key steps

1. Leibniz expansion det M = Σ_σ sgn σ Π_i M_{σ(i)i} and the finite product and sum rules: if the entries of G have derivatives H at x, then h has derivative Σ_σ sgn σ Σ_m (Π_{j≠m} G(x)_{σ(j)j}) H_{σ(m)m} at x.
2. Permutation facts: a σ ≠ id moves some j ≠ m; for m ≠ l, a σ fixing every j ∉ {m,l} is id or the transposition (m l), whose sign is −1.
3. At G(0) = I only σ = id survives in the first-order sum, so h′(0) = tr G₁. This is (1).
4. Under (2), h is differentiable near 0 and deriv h = φ there, where φ(t) := Σ_σ sgn σ Σ_m (Π_{j≠m} G(t)_{σ(j)j}) G′(t)_{σ(m)m}. The product rule gives φ′(0).
5. At G(0) = I the G₂-part of φ′(0) is tr G₂. The pair part reduces, via {id, (m l)}, to Σ_{m≠l}(B_{ll}B_{mm} − B_{ml}B_{lm}) = (tr B)² − tr(B·B) with B = G′(0).
6. deriv h agrees with φ near 0, so deriv h has derivative tr G₂ + (tr G′(0))² − tr(G′(0)·G′(0)) at 0.

## Reference use

### local-project

Queries:
- `rg -n '^theorem|^lemma' mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean; sed -n 260,325p NormDet.lean (ContinuousLinearMap.normDet_sq, LinearMap.normDet_sq_eq_det_gram)`
- `rg -n 'def gram' mathlib/Mathlib (Matrix.gram in Analysis/InnerProductSpace/GramMatrix.lean)`
- `rg -n 'theorem.*(det|Det).*(Deriv|deriv|Diff|diff)|theorem.*(Deriv|deriv|Diff).*det' mathlib/Mathlib`
- `rg -n 'finset_prod|finsetProd' mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean; sed -n 380,410p and 620,640p Deriv/Mul.lean`
- `rg -n 'theorem HasDerivAt.sqrt|theorem deriv_sqrt|theorem HasDerivAt.inner|theorem HasDerivAt.clm_apply|theorem HasDerivAt.det|theorem hasDerivAt_det' mathlib/Mathlib`
- `rg -n 'starProjection.*sum|orthogonalProjection_eq_sum|starProjection_eq_sum|sum_inner_mul_inner|norm_sq_eq_sum|sum_sq_inner|Parseval' mathlib/Mathlib/Analysis/InnerProductSpace; sed -n 500,600p PiL2.lean`
- `rg -n 'starProjection_apply|coe_orthogonalProjectionOnto|inner_orthogonalProjectionOnto_eq_of_mem_left|starProjection_inner_eq_zero|norm_sq_eq_add_norm_sq_starProjection' mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `rg -n 'theorem det_apply' mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean; rg -n 'theorem HasDerivAt.fun_sum|theorem HasDerivAt.sum' mathlib/Mathlib/Analysis/Calculus/Deriv/Add.lean`
- `rg -n 'HasDerivAt.*det|det.*HasDerivAt|deriv.*\.det|trace' lake-packages-25730c7c/simongmt/Poincare; sed -n 1,130p Chapter08/FirstVariation.lean; sed -n 140,265p Chapter08/DeformationFamily.lean`
- `sed -n 1180,1275p book/sources/chapter-02-source.txt (Simon 5.2–5.4, pp. 62–63)`
- `python3 -I gen_checks.py / gen_solutions.py (gmt-compare.py child_modules contract mode + lean_contract.validate_lean_statement), then lean NodeChallenge_*/NodeSolution_* against scratch oleans of GMT.Ch02.Submission (LEAN_PATH = lake-packages-25730c7c/*/.lake/build/lib/lean)`
- `lean asm/Probe.lean; lean asm/ChildC.lean; lean asm/ChildE.lean; lean asm/Assembly.lean; lean asm/ChildA1.lean; lean asm/ChildA2.lean; lean asm/ChildB.lean; lean -o cand/olean/GMT/Ch02/Submission.olean cand/src/Submission.lean (#print axioms)`
- `python3 -I numcheck.py (exact rational power-series checks of both child formulas)`
- `python3 -I scan of dag.json lean_name fields and nodes/*/decomposition-v*.json subproblem lean_names; grep -rn of the proposed names in simongmt and GMT sources`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/GMT/Ch02/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/GramMatrix.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/Deriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/SpecialFunctions/Sqrt.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/Subspace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/FirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/DeformationFamily.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/FirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-02-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-variation-formulas-a1-gram-det-derivatives-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-variation-formulas-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-variation-formulas-a1-gram-det-identity-a1/parent-supplied-natural-proof.md`
- `/tmp/gramdet-decomp-ylURCP/checks/NodeChallenge_00_variation_matrix_det_derivatives_at_one.lean`
- `/tmp/gramdet-decomp-ylURCP/checks/NodeChallenge_01_variation_sqrt_derivatives_at_one.lean`
- `/tmp/gramdet-decomp-ylURCP/asm/Assembly.lean`
- `/tmp/gramdet-decomp-ylURCP/asm/ChildA1.lean`
- `/tmp/gramdet-decomp-ylURCP/asm/ChildA2.lean`
- `/tmp/gramdet-decomp-ylURCP/asm/ChildB.lean`
- `/tmp/gramdet-decomp-ylURCP/cand/src/Submission.lean`
- `/tmp/gramdet-decomp-ylURCP/solchk/NodeSolution_00_variation_matrix_det_derivatives_at_one.lean`
- `/tmp/gramdet-decomp-ylURCP/solchk/NodeSolution_01_variation_sqrt_derivatives_at_one.lean`
- `/tmp/gramdet-decomp-ylURCP/solchk/NodeSolution_03_variation_gram_det_derivatives.lean`
- `/tmp/gramdet-scripts/numcheck.py`

Neither the pinned Mathlib (25730c7c) nor SimonGMT (2b36630) has a derivative of Matrix.det or LinearMap.det, so there is no Jacobi formula to reuse. The rg over Mathlib for det together with Deriv/deriv/Diff matched only the measure-theoretic Jacobian lemmas in MeasureTheory/Function/Jacobian.lean. SimonGMT has only the first-order polynomial statement derivative_eval_zero_det_one_add_X_smul_add_sq_smul in Chapter08/FirstVariation.lean, and nothing second-order. The determinant child must therefore be proved from Matrix.det_apply and HasDerivAt.fun_finsetProd, which is what its proof does. Every ingredient the children and the parent assembly need exists in the snapshot and was used in the scratch proofs: Matrix.det_apply; HasDerivAt.fun_finsetProd, fun_sum, const_mul, mul, sqrt, div, congr_of_eventuallyEq, clm_apply and inner; ContinuousLinearMap.normDet_sq and LinearMap.normDet_sq_eq_det_gram; OrthonormalBasis.sum_sq_inner_right; Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left and Submodule.starProjection_inner_eq_zero; norm_add_sq_real. #print axioms of both complete child proofs shows only propext, Classical.choice and Quot.sound. Simon pp. 62–63 quote both expansions without proof, so the child proofs are taken from the supplied derivative-form Steps 4–7.
