# Parent-supplied natural-language proof

- Parent DAG node: `root.stationary_results-a1.chart_divergence-a1`
- Child DAG node: `root.stationary_results-a1.chart_divergence-a1.coefficient_trace_identity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation. ℝᵈ := EuclideanSpace ℝ (Fin d) = Rn d with the standard inner product ⟨·,·⟩; L(E, F) := E →L[ℝ] F and L(ℝⁿ) := ℝⁿ →L[ℝ] ℝⁿ, a ring whose multiplication is composition (f * g = f ∘L g holds by rfl) with identity 1; for A ∈ L(ℝⁿ, ℝᴺ), A* := ContinuousLinearMap.adjoint A, so ⟨A* z, c⟩ = ⟨z, A c⟩ (ContinuousLinearMap.adjoint_inner_left) and ⟨c, A* z⟩ = ⟨A c, z⟩ (ContinuousLinearMap.adjoint_inner_right); G := A* ∘L A and G⁻¹ := Ring.inverse G; trace means LinearMap.trace ℝ ℝⁿ applied to the underlying linear map (.toLinearMap); e_l := EuclideanSpace.single l 1 (l ∈ Fin n) is the standard orthonormal basis of ℝⁿ (= EuclideanSpace.basisFun (Fin n) ℝ l). Every lemma cited below resolves after `import GMT.Ch02.Submission` (checked with #check).
Source: parent proof, steps 2, 4, 5 and 6 (differentiate u = A a + u^⊥ and A* u^⊥ = 0, apply G⁻¹A*, take traces).
Setting. For x′ ∈ ℝⁿ: A(x′) := fderiv ℝ ψ x′, G(x′) := A(x′)* ∘L A(x′), a(x′) := Ring.inverse G(x′) (A(x′)*(u x′)). Fix x ∈ V and abbreviate A := A(x), G⁻¹ := Ring.inverse G(x), S := fderiv ℝ (fderiv ℝ ψ) x (so S v ∈ L(ℝⁿ, ℝᴺ), S v c ∈ ℝᴺ), and p := u x − A(a x). Let adjR := (ContinuousLinearMap.adjoint (𝕜 := ℝ)).toContinuousLinearEquiv.toContinuousLinearMap, the adjoint as an ℝ-linear continuous map (adjR L = L* by rfl).
1. (Differentiability and symmetry.) V is a neighbourhood of x. fderiv ℝ ψ is C¹ on V (ContDiffOn.fderiv_of_isOpen), so x′ ↦ A(x′) is differentiable at x with derivative S. u is C¹ on the open V, hence differentiable at x. By the sibling coefficient_regularity, a is C¹ on V, hence differentiable at x. By the sibling second_derivative_symm, S v c = S c v for all v, c ∈ ℝⁿ.
2. (A(x′)* annihilates the normal part on V.) For x′ ∈ V put P(x′) := u x′ − A(x′)(a x′) and Q(x′) := A(x′)*(P(x′)). By the sibling gram_projection, G(x′) is a unit, so A(x′)*(A(x′)(a x′)) = G(x′)(Ring.inverse G(x′) (A(x′)*(u x′))) = A(x′)*(u x′) (Ring.mul_inverse_cancel), i.e. Q(x′) = 0 for all x′ ∈ V. As V is a neighbourhood of x, Q =ᶠ[𝓝 x] 0, so DQ(x) = 0 (Filter.EventuallyEq.fderiv_eq). Note P(x) = p.
3. (Derivative of P.) By the product rule for evaluation (fderiv_clm_apply): D(x′ ↦ A(x′)(a x′))(x)[v] = A(Da(x)[v]) + S v (a x). Hence DP(x)[v] = Du(x)[v] − A(Da(x)[v]) − S v (a x).
4. (Derivative of Q.) x′ ↦ A(x′)* = adjR (A x′) has derivative adjR ∘L S at x, i.e. v ↦ (S v)*. By the product rule (fderiv_clm_apply), DQ(x)[v] = A*(DP(x)[v]) + (S v)* p. By step 2, A*(DP(x)[v]) = −(S v)* p for every v ∈ ℝⁿ.
5. (Key pointwise identity.) Apply G⁻¹A* to step 3, use G⁻¹(A*(A c)) = G⁻¹(G c) = c (Ring.inverse_mul_cancel) and step 4: for every v,
   G⁻¹A*(Du(x)[v]) = Da(x)[v] + G⁻¹A*(S v (a x)) − G⁻¹((S v)* p).
   By symmetry (step 1), S v (a x) = S (a x) v.
6. (Traces.) Compute each trace in the orthonormal basis (e_l) (LinearMap.trace_eq_sum_inner) and use step 5 with v := e_l:
   trace(G⁻¹ ∘ A* ∘ Du(x)) = Σ_l ⟨e_l, Da(x) e_l⟩ + Σ_l ⟨e_l, G⁻¹A*(S (a x) e_l)⟩ − Σ_l ⟨e_l, G⁻¹((S e_l)* p)⟩
   = trace Da(x) + trace(G⁻¹ ∘ A* ∘ S(a x)) − Σ_l ⟨e_l, G⁻¹((S e_l)* p)⟩.
   For the last sum, symmetry of G⁻¹ (gram_projection) and ⟨c, L* z⟩ = ⟨L c, z⟩ (adjoint_inner_right) give ⟨e_l, G⁻¹((S e_l)* p)⟩ = ⟨G⁻¹e_l, (S e_l)* p⟩ = ⟨S e_l (G⁻¹e_l), p⟩ = ⟨p, S e_l (G⁻¹e_l)⟩, so the sum equals ⟨p, Σ_l S e_l (G⁻¹ e_l)⟩ (inner_sum).
7. (Conclusion.) Rearranging step 6 and inserting p = u x − A(a x), Du(x) = fderiv ℝ u x, Da(x) = fderiv ℝ a x and S(a x) = fderiv ℝ (fderiv ℝ ψ) x (a x):
   trace Da(x) + trace(G⁻¹ ∘L A* ∘L S(a x)) = trace(G⁻¹ ∘L A* ∘L Du(x)) + ⟨u x − A(a x), Σ_l S e_l (G⁻¹ e_l)⟩,
   which is the asserted identity. (For n = 0 all traces and the sum vanish.) ∎

## Key steps

1. On V, A*(u − A a) = A*u − G G⁻¹A*u = 0 (gram_projection), so the derivative of x′ ↦ A(x′)*(u − Aa)(x′) vanishes at x.
2. Product rule: D(u − Aa)[v] = Du[v] − A Da[v] − S v a and A* D(u − Aa)[v] = −(S v)*(u − Aa).
3. Apply G⁻¹A* and use symmetry S v a = S a v (second_derivative_symm; a differentiable by coefficient_regularity): G⁻¹A*Du[v] = Da[v] + G⁻¹A*S(a) v − G⁻¹(S v)*(u − Aa).
4. Trace in the basis e_l, with G⁻¹ symmetric: the last term traces to ⟨u − Aa, Σ_l S e_l (G⁻¹e_l)⟩, giving the identity.

## Reference use

### local-project

Queries:
- `cat -n GMT/Ch02/Contract.lean (lines 79-120: tangentSpace, tangentProjection, normalPart, tangentFrame, tangentialDivergence, secondFundamentalForm, meanCurvature)`
- `cat -n simongmt/Poincare/SimonGMT/Chapter02/{Submanifold,Area,SubmanifoldCalculus,SecondFundamentalFormCalculus,SecondFundamentalForm}.lean`
- `grep -rn 'contDiffAt_ringInverse\|hasFDerivAt_ringInverse\|contDiffAt_map_inverse' mathlib/Mathlib`
- `grep -rln Jacobi mathlib/Mathlib; grep -rn 'hasFDerivAt_det\|fderiv_det\|hasStrictFDerivAt_det\|deriv_det\|contDiff_det' mathlib/Mathlib (no derivative of det)`
- `grep -rn 'continuous_det\|det_one_add_smul\|derivative_det_one_add_X_smul' mathlib/Mathlib`
- `grep -rn 'theorem fderiv_fun_smul\|theorem fderiv_comp\|trace_smulRight\|theorem trace_comp_comm'\|inner_starProjection_left_eq_right\|trace_eq_sum_inner' mathlib/Mathlib`
- `grep -rn 'ContDiffAt.isSymmSndFDerivAt\|ContDiffOn.fderiv_of_isOpen\|ContDiffOn.clm_comp\|ContDiffOn.clm_apply\|fderiv_clm_apply\|fderiv_clm_comp\|adjoint_inner_left\|starProjection_apply_mem\|sub_starProjection_mem_orthogonal\|ContDiffAt.sqrt\|isUnit_iff_ker_eq_bot\|toContinuousLinearEquivOfDetNeZero\|norm_image_sub_le_of_norm_deriv_le_segment'' mathlib/Mathlib`
- `grep -rn 'theorem.*[Ss]ymm.*fderiv\|IsSymmSndFDerivAt\|iteratedFDeriv.*comm' mathlib/Mathlib (only FDeriv/Symmetric.lean, VectorField.lean, CurveIntegral/Poincare.lean)`
- `lake env lean Probe.lean / Probe2.lean: #check of every cited name after `import GMT.Ch02.Submission` (unknown: ContDiffAt.isSymmSndFDerivAt, second_derivative_symmetric_of_eventually, Chapter02.submanifoldDivergenceAt_eq_sum_inner, Convex.taylor_approx_two_segment; all others resolve)`
- `sed -n 60,115p /runtime/flows/gmt-claude-6e6a457c9391/_recursive_lean/leaf_verification.py (check_source_delta); grep leaf_lean_agent_review .humanize/swarm-configs/*.json`
- `python3 -I collision check of the 8 lean_names against dag.json (149 nodes) + grep over the run directory, snapshot project, SimonGMT and Mathlib (no match); python3 -I regex scan of dag.json lean_statements for D²ψ symmetry / det derivative (no node)`
- `python3 -I gen.py (lean_contract.validate_lean_statement + gmt-compare.contract_scope replay); lake build GMT.Ch02.Submission; lake env lean challenges8/NodeChallenge_00..07.lean`
- `lake env lean AssemblyCheck8.lean (frozen parent type from 8 child stubs + frozen sff_chart stub; #print axioms HumanizeNodeComparator.target)`
- `lake env lean Child4.lean, rev/Child15.lean, rev/Child2.lean, rev/Child3.lean, rev/Child6.lean (sibling-interface proofs, no sorry); lake env lean InstCheck.lean`
- `python3 -I numcheck.py; python3 -I numcheck2.py (finite-difference checks)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/LinearAlgebra/Matrix/Charpoly/Coeff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/SpecialFunctions/Sqrt.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Submanifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SecondFundamentalFormCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-6e6a457c9391/_recursive_lean/leaf_verification.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-stationary-results-a1-chart-divergence-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-stationary-results-a1-chart-divergence-a1/parent-supplied-natural-proof.md`
- `/tmp/chartdiv-decomp/AssemblyCheck8.lean`
- `/tmp/chartdiv-decomp/InstCheck.lean`
- `/tmp/chartdiv-probe/Probe.lean`
- `/tmp/chartdiv-probe/Probe2.lean`
- `/tmp/chartdiv-probe/Child4.lean`
- `/tmp/chartdiv-probe/rev/Child15.lean`
- `/tmp/chartdiv-probe/rev/Child2.lean`
- `/tmp/chartdiv-probe/rev/Child3.lean`
- `/tmp/chartdiv-probe/rev/Child6.lean`
- `/tmp/chartdiv-scripts/numcheck.py`
- `/tmp/chartdiv-scripts/numcheck2.py`

Contract.lean (lines 83-119) fixes tangentSpace/tangentProjection (starProjection)/normalPart/tangentFrame (stdOrthonormalBasis)/tangentialDivergence (frame sum of fderiv)/secondFundamentalForm (fderivWithin of tangentProjection)/meanCurvature (frame trace). In scope after `import GMT.Ch02.Submission`: SimonGMT Area.lean (areaJacobianAt_eq_normDet, areaJacobianAt_eq_sqrt_det_adjoint_comp, areaJacobianAt_sq_eq_det_adjoint_comp, areaJacobianAt_nonneg) and Submanifold.lean (IsSimonLocalRepresentation accessors); Mathlib LinearMap.normDet_ne_zero_tfae (1-based TFAE indices), contDiffAt_ringInverse, ContDiffOn.fderiv_of_isOpen/clm_comp/clm_apply, fderiv_clm_apply/fderiv_clm_comp, fderiv_fun_smul, LinearMap.trace_smulRight/trace_comp_comm'/trace_eq_sum_inner/trace_eq_matrix_trace, Matrix.det_one_add_smul, Matrix.det_apply, LinearMap.det_toMatrix, ContDiffAt.sqrt, HasFDerivAt.sqrt, norm_image_sub_le_of_norm_deriv_le_segment', ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero, Submodule.eq_starProjection_of_mem_of_inner_eq_zero. NOT in scope (no match): ContDiffAt.isSymmSndFDerivAt, second_derivative_symmetric_of_eventually, Convex.taylor_approx_two_segment (FDeriv/Symmetric.lean is not imported) and SimonGMT submanifoldDivergenceAt_eq_sum_inner (SubmanifoldCalculus.lean is not imported) — the parent handoff's claim that these are available is wrong after the frozen imports. Mathlib has no derivative of det (no hasFDerivAt_det/fderiv_det/contDiff_det). Since a childless node may only append one theorem (leaf_verification.check_source_delta), symmetry of D²ψ and Jacobi's formula for det are genuine new obligations and became children. All 8 statements validate and elaborate; AssemblyCheck8.lean proves the frozen parent type from them plus the frozen sff_chart type (axioms propext, sorryAx from stubs, Classical.choice, Quot.sound); every sibling interface compiles sorry-free; the 8 names are unused in dag.json, the run, the snapshot project, SimonGMT and Mathlib.
