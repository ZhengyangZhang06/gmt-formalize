# Parent-supplied natural-language proof

- Parent DAG node: `root.stationary_results-a1.stable_second_variation-a1`
- Child DAG node: `root.stationary_results-a1.stable_second_variation-a1.stable_integrand_integrable-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation.
- ℝᴺ := EuclideanSpace ℝ (Fin N) (= Rn N) and Hⁿ := μHE[n].
- X := initialVelocity φ and D(y) := DX(y) = fderiv ℝ X y.
- For y ∈ ℝᴺ: T_y := tangentSpace M y, a submodule of ℝᴺ.
- P_y := tangentProjection M y = (T_y).starProjection, the orthogonal projection of ℝᴺ onto T_y.
- q_y := (T_y).orthogonalProjectionOnto : ℝᴺ → T_y, so the vector P_y v of ℝᴺ is the coercion of q_y v. Definitionally, P_y = ι_y ∘ q_y where ι_y : T_y → ℝᴺ is the inclusion.
- b^y := stdOrthonormalBasis ℝ T_y, an orthonormal basis of T_y, and τ_i := tangentFrame M y i = (b^y_i : ℝᴺ) for i ∈ Fin (finrank ℝ T_y).
- normalPart M y v = v − P_y v and B_y(τ, η) := secondFundamentalForm M y τ η.
- S(y) := stableSecondVariationIntegrand M φ y = Σ_i ‖normalPart M y (D(y)τ_i)‖² − Σ_i Σ_j ⟨X(y), B_y(τ_i, τ_j)⟩².
- For a continuous linear A : ℝᴺ → ℝᴺ, A* := ContinuousLinearMap.adjoint A, so ⟨x, A* w⟩ = ⟨A x, w⟩.
- 'trace' is LinearMap.trace of the underlying linear map.

The hypotheses (a)-(h) are as in the statement.

Source: parent proof of Simon Ch. 2, Lemma 5.11 (C³ correction), steps 5(a) and 6. The printed proof uses this integrability tacitly.

1. (DX vanishes off K.) Let y ∉ K.
   - By (d), Kᶜ is open, hence a neighbourhood of y, and X = 0 on Kᶜ by (e).
   - So X agrees with the constant function 0 on a neighbourhood of y.
   - Hence D(y) = 0 (Filter.EventuallyEq.fderiv_eq and fderiv_const_apply).

2. (Conclusion (i).) Let y ∈ M with y ∉ K.
   - X(y) = 0 by (e) and D(y) = 0 by step 1.
   - For every i, normalPart M y (D(y)τ_i) = normalPart M y 0 = 0 − P_y 0 = 0.
   - For all i, j, ⟨X(y), B_y(τ_i, τ_j)⟩ = ⟨0, B_y(τ_i, τ_j)⟩ = 0.
   - Hence S(y) = Σ_i 0² − Σ_i Σ_j 0² = 0.

3. (Frame sums are traces.) Claim: for every y ∈ ℝᴺ and every continuous linear L : ℝᴺ → ℝᴺ, Σ_i ⟨τ_i, L τ_i⟩ = trace(L ∘ P_y).
   - L ∘ P_y = (L ∘ ι_y) ∘ q_y as linear maps.
   - Cyclicity of the trace for linear maps between the finite free modules ℝᴺ and T_y (LinearMap.trace_comp_comm') gives trace_{ℝᴺ}((L ∘ ι_y) ∘ q_y) = trace_{T_y}(q_y ∘ (L ∘ ι_y)).
   - The trace in the orthonormal basis b^y of T_y (LinearMap.trace_eq_sum_inner) is Σ_i ⟨b^y_i, q_y(L τ_i)⟩_{T_y}.
   - For u ∈ T_y and v ∈ ℝᴺ, ⟨u, q_y v⟩_{T_y} = ⟨(u : ℝᴺ), v⟩ (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left).
   - So each term equals ⟨τ_i, L τ_i⟩, which proves the claim.
   This is the argument of SimonGMT's Poincare.SimonGMT.Chapter02.submanifoldDivergenceAt_eq_sum_inner. Its module is not imported by the contract, while all cited Mathlib lemmas are.

4. (A frame-free expression.) For y ∈ ℝᴺ define
   - A1(y) := D(y)* ∘ (I − P_y) ∘ D(y),
   - A2(y) := D(y)* ∘ P_y ∘ D(y),
   - F(y) := trace(A1(y) ∘ P_y) − trace(A2(y) ∘ P_y).
   Claim: S(y) = F(y) for every y ∈ M. Fix y ∈ M and write P := P_y.
   (a) Orthogonality: ⟨Pv, v − Pv⟩ = 0 for every v. Indeed Pv ∈ T_y (Submodule.starProjection_apply_mem) and v − Pv is orthogonal to T_y (Submodule.starProjection_inner_eq_zero).
   (b) First sum. Fix i and put v := D(y)τ_i. Then
       ‖normalPart M y v‖² = ⟨v − Pv, v − Pv⟩ = ⟨v, v − Pv⟩ − ⟨Pv, v − Pv⟩ = ⟨v, (I − P)v⟩,
       using (a). On the other hand, by the adjoint identity,
       ⟨τ_i, A1(y)τ_i⟩ = ⟨τ_i, D(y)*((I − P)D(y)τ_i)⟩ = ⟨D(y)τ_i, (I − P)D(y)τ_i⟩ = ⟨v, (I − P)v⟩.
       So ‖normalPart M y (D(y)τ_i)‖² = ⟨τ_i, A1(y)τ_i⟩.
   (c) Second sum. Fix i and put v := D(y)τ_i.
       - Every τ_j lies in T_y, being the coercion of b^y_j ∈ T_y. So hypothesis (h) with τ := τ_i and η := τ_j gives ⟨τ_j, v⟩ = −⟨X(y), B_y(τ_i, τ_j)⟩, hence ⟨X(y), B_y(τ_i, τ_j)⟩² = ⟨τ_j, v⟩².
       - By step 3's pairing identity, ⟨τ_j, v⟩ = ⟨b^y_j, q_y v⟩_{T_y}.
       - Parseval for b^y (OrthonormalBasis.sum_sq_inner_right) gives Σ_j ⟨τ_j, v⟩² = ‖q_y v‖² = ‖Pv‖², since the norm of T_y is the ambient norm.
       - Then ‖Pv‖² = ⟨Pv, Pv⟩ = ⟨Pv, v⟩ = ⟨v, Pv⟩, because (a) gives ⟨Pv, v⟩ − ⟨Pv, Pv⟩ = 0, and by symmetry of the real inner product.
       - Also ⟨τ_i, A2(y)τ_i⟩ = ⟨D(y)τ_i, P D(y)τ_i⟩ = ⟨v, Pv⟩.
       So Σ_j ⟨X(y), B_y(τ_i, τ_j)⟩² = ⟨τ_i, A2(y)τ_i⟩.
   (d) Sum (b) and (c) over i and apply step 3 with L := A1(y) and L := A2(y):
       S(y) = Σ_i ⟨τ_i, A1(y)τ_i⟩ − Σ_i ⟨τ_i, A2(y)τ_i⟩ = trace(A1(y) ∘ P_y) − trace(A2(y) ∘ P_y) = F(y).

5. (F is continuous on M.)
   - By (c), y ↦ D(y) is continuous on ℝᴺ (ContDiff.continuous_fderiv; the order 1 is nonzero).
   - A ↦ A* is a linear isometric equivalence of ℝᴺ →L ℝᴺ, hence continuous, so y ↦ D(y)* is continuous.
   - By (b), y ↦ P_y is continuous on M, and so is y ↦ I − P_y.
   - Composition of continuous linear maps is jointly continuous (ContinuousOn.clm_comp), so y ↦ A1(y) ∘ P_y and y ↦ A2(y) ∘ P_y are continuous on M.
   - The map A ↦ trace(A) on ℝᴺ →L ℝᴺ is LinearMap.trace composed with the linear coercion ContinuousLinearMap.coeLM. It is linear on a finite-dimensional space, hence continuous (LinearMap.continuous_of_finiteDimensional).
   - Therefore F is continuous on M.

6. (Measurability.)
   - F is continuous on the measurable set M (a), and ℝᴺ is second countable with its Borel σ-algebra. So F is a.e.-strongly measurable for Hⁿ restricted to M (ContinuousOn.aestronglyMeasurable).
   - By step 4, S = F at every point of M, so S = F holds Hⁿ⌊M-almost everywhere (ae_restrict_iff', using that M is measurable).
   - Hence S is a.e.-strongly measurable for Hⁿ⌊M (AEStronglyMeasurable.congr).

7. (Bound.) M ∩ K ⊆ M is compact by (f), and F is continuous on it. So there is C ∈ ℝ with |F(y)| ≤ C for all y ∈ M ∩ K (IsCompact.exists_bound_of_continuousOn). By step 4, |S(y)| ≤ C for all y ∈ M ∩ K.

8. (Integrability on K ∩ M.) K is closed, hence measurable. Let μ' := Hⁿ⌊M.
   - μ'(K) = Hⁿ(K ∩ M) = Hⁿ(M ∩ K) < ∞ by (g) (Measure.restrict_apply).
   - S is a.e.-strongly measurable for μ' by step 6.
   - μ'⌊K = Hⁿ⌊(K ∩ M) (Measure.restrict_restrict, using that K is measurable).
   - |S| ≤ C at every point of the measurable set K ∩ M by step 7, hence μ'⌊K-almost everywhere.
   - Measure.integrableOn_of_bounded therefore shows that S is integrable on K for μ'. Rewriting μ'⌊K = Hⁿ⌊(K ∩ M), S is integrable on K ∩ M for Hⁿ.

9. (Conclusion (ii).) Every y ∈ M ∖ (K ∩ M) satisfies y ∈ M and y ∉ K, so S(y) = 0 by step 2. Since M is measurable (a), IntegrableOn.of_forall_sdiff_eq_zero extends integrability from K ∩ M to M with respect to Hⁿ. Together with step 2 this proves both conjuncts.

## Key steps

1. X = 0 on the open set Kᶜ, so DX = 0 off K; hence the stable integrand vanishes at every y ∈ M ∖ K.
2. Frame sums are traces: Σ_i ⟨τ_i, Lτ_i⟩ = trace(L∘P_y), by trace cyclicity with P_y = ι∘q_y and the orthonormal-basis trace formula.
3. On M, by (h), orthogonality of P_y and Parseval in T_y: stable = F := trace(DX*(I−P)DX∘P) − trace(DX*P DX∘P).
4. F is continuous on M (P is continuous on M, DX is continuous, and adjoint, composition and trace are continuous); so the stable integrand is a.e.-strongly measurable for Hⁿ⌊M (M measurable).
5. F is bounded on the compact set M∩K and Hⁿ(M∩K) < ∞, so the integrand is integrable on K∩M (integrableOn_of_bounded); it vanishes on M∖K, so integrability extends to M (of_forall_sdiff_eq_zero).

## Reference use

### local-project

Queries:
- `cat -n GMT/Ch02/Contract.lean (definitions lines 83-176, FirstVariation/SecondVariation/SecondVariationStationary lines 297-342); diff snapshot project/GMT/Ch02/Contract.lean against workspace copy (identical)`
- `grep -rn "theorem.*trace.*inner\|theorem sum_sq_inner\|sum_inner_mul_inner\|theorem.*trace_eq_sum" mathlib/Mathlib --include=*.lean; cat mathlib/Mathlib/Analysis/InnerProductSpace/Trace.lean; sed -n 495,545p mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `grep -rn "integrableOn_of_bounded\|of_forall_diff_eq_zero\|of_forall_sdiff_eq_zero\|ContinuousOn.aestronglyMeasurable\|setIntegral_congr_fun\|setIntegral_eq_zero_of_forall_eq_zero" mathlib/Mathlib; grep -n "starProjection_inner_eq_zero\|inner_orthogonalProjectionOnto_eq_of_mem_left\|adjoint_inner_right\|ContDiff.continuous_fderiv\|fderiv_const_apply" in Projection/Basic.lean, Adjoint.lean, ContDiff/Defs.lean, FDeriv/Const.lean`
- `grep -n '^theorem\|^def' simongmt/Poincare/SimonGMT/Chapter02/{Submanifold,SubmanifoldCalculus,SecondFundamentalForm,SecondFundamentalFormCalculus,SubmanifoldIntegral,SubmanifoldTopology}.lean; sed -n 180,225p SubmanifoldCalculus.lean (submanifoldDivergenceAt_eq_sum_inner)`
- `grep -rn "stableSecondVariationIntegrand\|secondVariationIntegrand" simongmt/Poincare (no match); grep -rln "IsAdmissibleDeformation\|initialVelocity" simongmt/Poincare (only Chapter08/DeformationFamily.lean, DeformationIntegral.lean)`
- `grep -rn stable_second_variation_integrand_integrableOn / second_variation_integrand_eq_div_accel_add_stable over snapshot project, simongmt, mathlib (no match); python3 -I collision check against dag.json lean_names (no collision among 110)`
- `sed -n 1365,1412p book/chapter-02.txt (printed Lemma 5.11 and its proof); read nodes/root-stationary-results-a1/decomposition-v1.json sibling lean_statements and this node's parent-child-handoff.json`
- `python3 -I gen.py (replays verifier gmt-compare.py child_modules/contract_scope and lean_contract.validate_lean_statement); lake build GMT.Ch02.Submission; lake env lean checks/{NodeChallenge_00,NodeChallenge_01,ChildA,ChildB,AssemblyCheck,FullCheck,Avail}.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Submanifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/DeformationFamily.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-stationary-results-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-stationary-results-a1-stable-second-variation-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/ssv-decomp-a1/checks/NodeChallenge_00.lean`
- `/tmp/ssv-decomp-a1/checks/NodeChallenge_01.lean`
- `/tmp/ssv-decomp-a1/checks/ChildA.lean`
- `/tmp/ssv-decomp-a1/checks/ChildB.lean`
- `/tmp/ssv-decomp-a1/checks/AssemblyCheck.lean`
- `/tmp/ssv-decomp-a1/checks/FullCheck.lean`

Contract and frame dependence:
- The frozen contract builds secondVariationIntegrand, stableSecondVariationIntegrand, tangentialDivergence and meanCurvature from tangentFrame = stdOrthonormalBasis of tangentSpace, which is chosen pointwise. Measurability of the stable integrand therefore needs a frame-free trace expression.
- The snapshot Contract.lean is byte-identical to the workspace copy.

Mathlib 25730c7c supplies everything both children need. All of it is reachable from `import GMT.Ch02.Submission` (checked with #check):
- LinearMap.trace_eq_sum_inner (InnerProductSpace/Trace.lean:25) and LinearMap.trace_comp_comm';
- OrthonormalBasis.sum_sq_inner_right (PiL2.lean:528);
- Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left (Projection/Basic.lean:642) and Submodule.starProjection_inner_eq_zero (:164);
- ContinuousLinearMap.adjoint_inner_right (Adjoint.lean:125);
- ContinuousOn.aestronglyMeasurable (IntegrableOn.lean:791);
- Measure.integrableOn_of_bounded (IntegrableOn.lean:716; it needs AEStronglyMeasurable for the ambient measure, so it is applied to Hⁿ⌊M);
- IntegrableOn.of_forall_sdiff_eq_zero (of_forall_diff_eq_zero is a deprecated alias);
- setIntegral_congr_fun and setIntegral_eq_zero_of_forall_eq_zero (Bochner/Set.lean);
- ContDiff.continuous_fderiv and fderiv_const_apply.

SimonGMT:
- Chapter02/SubmanifoldCalculus.lean:192 submanifoldDivergenceAt_eq_sum_inner proves the frame-sum = trace(DX∘P) identity. Its module is not imported by the contract, so child A inlines the same argument using the Mathlib lemmas.
- There is no match for secondVariationIntegrand or stableSecondVariationIntegrand.
- Chapter08 DeformationFamily uses an unrelated initialVelocity on ℝ×Euclidean N, so nothing there is reusable.

Name collisions: neither proposed name appears in the snapshot project, SimonGMT, Mathlib, or among the 110 DAG lean_names.

Lean checks:
- Both statements pass the validator and elaborate in the comparator-replayed scope.
- Complete proofs of both children compile with only propext, Classical.choice and Quot.sound.
- AssemblyCheck and FullCheck prove the frozen parent type from the children plus the four resolved sibling types. The only sorryAx comes from the sibling stubs.
