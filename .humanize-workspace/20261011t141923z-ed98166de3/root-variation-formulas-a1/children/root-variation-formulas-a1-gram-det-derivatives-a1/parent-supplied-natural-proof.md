# Parent-supplied natural-language proof

- Parent DAG node: `root.variation_formulas-a1`
- Child DAG node: `root.variation_formulas-a1.gram_det_derivatives-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the printed computation in Simon Ch. 2, pp. 62–63, i.e. Steps 3.8–3.10 of the parent proof. The printed computation uses the matrix b_ij of (dψ_t)*dψ_t, det(I + B) = 1 + tr B + ½(tr B)² − ½ tr(B²) + O(|B|³), and √(1+x) = 1 + x/2 − x²/8 + O(x³). Here it is written with derivatives at t = 0 instead of O(t³) expansions, so only the stated hypotheses on A at and near 0 are used. The proof uses the sibling gram_det_identity.

Notation.
- ⟨·,·⟩ is the inner product of ℝᴺ.
- For i, k ∈ ι, put a_{ik} := ⟨b_i, A₁ b_k⟩ and D := Σ_i a_{ii} = Σ_i ⟨b_i, A₁ b_i⟩.
- G(t) is the ι×ι matrix with G(t)_{ik} := ⟨A(t) b_i, A(t) b_k⟩ (Simon's b_ij); h(t) := det G(t).

1. j = √h.
- Fix t. By gram_det_identity (with N′ = N and the linear map A(t)), j(t) = areaJacobian(A(t) ∘ ι_T).
- By Mathlib ContinuousLinearMap.normDet_sq and normDet ≥ 0, areaJacobian(L) = normDet(L) for L = A(t) ∘ ι_T.
- By LinearMap.normDet_sq_eq_det_gram with the orthonormal basis b of T, normDet(L)² = det Gram(L b_i) = det G(t) = h(t).
- Hence h(t) ≥ 0 and j(t) = √h(t) for every real t.

2. Values at 0. A(0) = I and b is orthonormal, so G(0) is the identity matrix and h(0) = 1.

3. Derivatives of the entries.
(a) Suppose A has derivative A₁ at 0. For v ∈ ℝᴺ, t ↦ A(t)v has derivative A₁v at 0. By the product rule for the bilinear inner product, G_{ik} has derivative Ġ_{ik}(0) = ⟨A₁b_i, b_k⟩ + ⟨b_i, A₁b_k⟩ = a_{ki} + a_{ik} at 0.
(b) Suppose the hypotheses of (2) hold.
- Choose ε > 0 such that A is differentiable at every t ∈ (−ε, ε), and write A′(t) := deriv A t. Then A′(0) = A₁ by uniqueness of derivatives.
- For |t| < ε, G_{ik} has derivative Ġ_{ik}(t) := ⟨A′(t)b_i, A(t)b_k⟩ + ⟨A(t)b_i, A′(t)b_k⟩ at t.
- A′ has derivative A₂ at 0, A has derivative A₁ at 0, A(0) = I and A′(0) = A₁. By the product rule, t ↦ Ġ_{ik}(t) has derivative G̈_{ik}(0) = ⟨A₂b_i, b_k⟩ + 2⟨A₁b_i, A₁b_k⟩ + ⟨b_i, A₂b_k⟩ at 0.

4. Leibniz expansion. h(t) = Σ_{σ ∈ Perm(ι)} sgn(σ) Π_{i∈ι} G_{σ(i)i}(t) (Matrix.det_apply). For a finite product of functions with derivatives, (Π_i f_i)′ = Σ_m f_m′ Π_{i≠m} f_i (HasDerivAt.finsetProd).

5. Proof of (1).
- Under 3(a), each product Π_i G_{σ(i)i} has derivative Σ_m Ġ_{σ(m)m}(0) Π_{i≠m} G_{σ(i)i}(0) at 0.
- Since G(0) = I, Π_{i≠m} δ_{σ(i)i} equals 1 if σ fixes every i ≠ m (which forces σ = id) and 0 otherwise.
- Hence h′(0) = Σ_m Ġ_{mm}(0) = tr Ġ(0) = 2D. This is Simon's det(I + B) = 1 + tr B + ….
- Since h(0) = 1 > 0, √ is differentiable at h(0) with derivative 1/(2√h(0)) = 1/2. So j = √ ∘ h has derivative h′(0)/2 = D = Σ_i ⟨b_i, A₁b_i⟩ at 0, which proves (1).

6. Second derivative of h. Assume the hypotheses of (2).
- For |t| < ε, by 3(b) and 4, h has derivative h′(t) := Σ_σ sgn(σ) Σ_m Ġ_{σ(m)m}(t) Π_{i≠m} G_{σ(i)i}(t) at t.
- Each summand is a product of functions with derivatives at 0, by 3(a) and 3(b). So this function h′ has a derivative at 0:
 h″(0) = Σ_σ sgn(σ) Σ_m [G̈_{σ(m)m}(0) Π_{i≠m} δ_{σ(i)i} + Ġ_{σ(m)m}(0) Σ_{l≠m} Ġ_{σ(l)l}(0) Π_{i∉{m,l}} δ_{σ(i)i}].
- In the first part only σ = id contributes, giving tr G̈(0).
- In the second part, for an ordered pair m ≠ l, Π_{i∉{m,l}} δ_{σ(i)i} ≠ 0 iff σ fixes every i ∉ {m, l}, i.e. σ = id or σ is the transposition (m l), whose sign is −1. This gives Σ_{m≠l} (Ġ_{mm}Ġ_{ll} − Ġ_{lm}Ġ_{ml})(0) = (tr Ġ(0))² − tr(Ġ(0)²).
- Hence h″(0) = tr G̈(0) + (tr Ġ(0))² − tr(Ġ(0)²). This is the derivative form of det(I + B) = 1 + tr B + ½(tr B)² − ½ tr(B²) + O(|B|³).

7. Second derivative of j.
- h is differentiable at 0, hence continuous there, and h(0) = 1. So there is ε′ ∈ (0, ε] with h(t) > 0 for |t| < ε′.
- For such t, j = √ ∘ h is differentiable at t with deriv j t = h′(t)/(2√h(t)).
- By the quotient and chain rules, the right-hand side has derivative h″(0)/2 − h′(0)²/4 at 0. Here t ↦ 2√h(t) has value 2 and derivative h′(0)/√h(0) = h′(0) at 0, and h′ has value h′(0) and derivative h″(0) at 0, so the derivative is (2h″(0) − h′(0)²)/4.
- Since deriv j agrees with this function on (−ε′, ε′), deriv j has derivative h″(0)/2 − h′(0)²/4 at 0 (HasDerivAt.congr_of_eventuallyEq). This is the derivative form of √(1+x) = 1 + x/2 − x²/8 + O(x³).

8. Evaluation.
- tr Ġ(0) = 2D.
- tr G̈(0) = 2 Σ_i ⟨b_i, A₂ b_i⟩ + 2 Σ_i ‖A₁ b_i‖², using ⟨A₂b_i, b_i⟩ = ⟨b_i, A₂b_i⟩.
- tr(Ġ(0)²) = Σ_{i,k} Ġ_{ik}(0)Ġ_{ki}(0) = Σ_{i,k} (a_{ik} + a_{ki})² = 2 Σ_{i,k} a_{ik}² + 2 Σ_{i,k} a_{ik}a_{ki}.
- Hence h″(0)/2 − h′(0)²/4 = Σ_i⟨b_i, A₂b_i⟩ + Σ_i‖A₁b_i‖² + 2D² − Σ_{i,k} a_{ik}² − Σ_{i,k} a_{ik}a_{ki} − D²
 = Σ_i⟨b_i, A₂b_i⟩ + D² + (Σ_k ‖A₁b_k‖² − Σ_{i,k} a_{ik}²) − Σ_{i,k} a_{ik}a_{ki}.

9. Normal parts.
- For v ∈ ℝᴺ, P v = Σ_i ⟨b_i, v⟩ b_i. Hence ‖Pv‖² = Σ_i ⟨b_i, v⟩² (Parseval in T), and ‖v‖² = ‖Pv‖² + ‖v − Pv‖² (Pythagoras, since v − Pv ⊥ T ∋ Pv).
- Taking v = A₁b_k gives Σ_i a_{ik}² = ‖P(A₁b_k)‖². So Σ_k ‖A₁b_k‖² − Σ_{i,k} a_{ik}² = Σ_k ‖A₁b_k − P(A₁b_k)‖².
- Also a_{ik}a_{ki} = ⟨b_i, A₁b_k⟩⟨b_k, A₁b_i⟩.
- Substituting into 8: deriv j has derivative Σ_i ⟨b_i, A₂b_i⟩ + (Σ_i ⟨b_i, A₁b_i⟩)² + Σ_i ‖A₁b_i − P(A₁b_i)‖² − Σ_i Σ_k ⟨b_i, A₁b_k⟩⟨b_k, A₁b_i⟩ at 0. This is (2).

If ι is empty, G is the empty matrix, so h ≡ 1, j ≡ 1, all derivatives vanish and all stated sums are 0; the argument above covers this case.

## Key steps

1. gram_det_identity, ContinuousLinearMap.normDet_sq and LinearMap.normDet_sq_eq_det_gram give j(t) = √det G(t), G(t)_{ik} = ⟨A(t)b_i, A(t)b_k⟩, G(0) = I.
2. Product rule: Ġ(0)_{ik} = a_{ik} + a_{ki}, and under (2) G̈(0)_{ik} = ⟨A₂b_i,b_k⟩ + 2⟨A₁b_i,A₁b_k⟩ + ⟨b_i,A₂b_k⟩.
3. Leibniz expansion at G(0) = I: h′(0) = tr Ġ(0), h″(0) = tr G̈(0) + (tr Ġ(0))² − tr(Ġ(0)²).
4. √-chain rule: j′(0) = h′(0)/2 = Σ⟨b_i, A₁b_i⟩, and deriv j has derivative h″(0)/2 − h′(0)²/4 at 0.
5. Parseval and Pythagoras: Σ_k‖A₁b_k‖² − Σ a_{ik}² = Σ_k‖A₁b_k − P A₁b_k‖², giving the stated second-order value.

## Reference use

### local-project

Queries:
- `grep -rn -i 'first.variation\|firstVariation\|first_variation\|secondVariation\|second_variation\|deformation\|isAdmissible' --include=*.lean lake-packages-25730c7c/simongmt`
- `grep -rli 'second variation\|secondVariation\|second_variation' --include=*.lean lake-packages-25730c7c/simongmt`
- `sed -n 1,265p Poincare/SimonGMT/Chapter08/DeformationFamily.lean; cat Chapter08/DeformationIntegral.lean; sed -n 1,246p Chapter08/FirstVariationIntegral.lean`
- `sed -n 1,700p Poincare/SimonGMT/Chapter08/Varifold.lean (Grassmannian, Varifold, tangentialJacobianReal_eq_sqrt_det_ambientGram)`
- `cat Poincare/SimonGMT/Chapter02/Submanifold.lean Chapter02/WeightedArea.lean Chapter02/SubmanifoldCalculus.lean; sed -n 20,45p Chapter02/Area.lean`
- `rg -n '^theorem|^lemma' mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean; sed -n 262,360p NormDet.lean`
- `rg -n 'theorem ContinuousOn.aestronglyMeasurable' mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean; rg -n 'theorem hasDerivAt_integral_of_dominated_loc_of_deriv_le' mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `rg -n 'starProjection_norm_le|isIdempotentElem_starProjection' mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean; rg -n 'isSymmSndFDerivAt' mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean; rg -n 'finset_prod|finsetProd' mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean; rg -n 'det_one_add_smul' mathlib/Mathlib/LinearAlgebra/Matrix/Charpoly/Coeff.lean`
- `rg -n 'contDiff.*det|det.*contDiff|ContDiff.*det' mathlib/Mathlib/Analysis/Calculus mathlib/Mathlib/Analysis/Matrix mathlib/Mathlib/Topology/Algebra/Module mathlib/Mathlib/LinearAlgebra/Matrix`
- `rg -n 'comp_aestronglyMeasurable' mathlib/Mathlib; grep -rn aestronglyMeasurable_of_tendsto_ae mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/`
- `sed -n 425,480p mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `sed -n 1160,1300p book/sources/chapter-02-source.txt (Simon Ch. 2 §5, 5.1-5.4 printed derivation)`
- `python3 -I scripts/gen_checks.py (verifier gmt-compare.py child_modules/contract_scope + lean_contract.validate_lean_statement) then lean checks/NodeChallenge_00..05 against scratch olean of GMT.Ch02.Submission (built with lean -o, LEAN_PATH = lake-packages-25730c7c/*/.lake/build/lib/lean)`
- `lean asmsrc/Assembly.lean; lean asmsrc/AxiomCheck.lean (#print axioms first_and_second_variation_check); lean asmsrc/FamilyFull.lean; lean asmsrc/GramCheck.lean; lean asmsrc/SmoothCheck.lean; lean asmsrc/InstCheck.lean; lean asmsrc/NameCheck.lean; lean solchk/AllSolutions.lean; lean asmsrc/LibAxioms.lean (#print axioms of every cited library lemma)`
- `python3 -I scripts/numcheck_pure.py (1500 random instances of the Gram identity and of both derivative formulas)`
- `python3 -I scan of dag.json lean_name fields and nodes/*/decomposition-v*.json subproblem lean_names for collisions`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/LinearAlgebra/Matrix/Charpoly/Coeff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Instances/Matrix.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Submanifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/DeformationFamily.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/DeformationIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/FirstVariationIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-02-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-variation-formulas-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-stationary-results-a1/decomposition-v1.json`
- `/tmp/varform-decomp-WPTPfS/scripts/statements.json`
- `/tmp/varform-decomp-WPTPfS/checks/NodeChallenge_00_variation_submanifold_image_area.lean`
- `/tmp/varform-decomp-WPTPfS/asmsrc/VarAsm/StandIns.lean`
- `/tmp/varform-decomp-WPTPfS/asmsrc/Assembly.lean`
- `/tmp/varform-decomp-WPTPfS/asmsrc/AxiomCheck.lean`
- `/tmp/varform-decomp-WPTPfS/asmsrc/FamilyFull.lean`
- `/tmp/varform-decomp-WPTPfS/asmsrc/GramCheck.lean`
- `/tmp/varform-decomp-WPTPfS/asmsrc/SmoothCheck.lean`
- `/tmp/varform-decomp-WPTPfS/asmsrc/InstCheck.lean`
- `/tmp/varform-decomp-WPTPfS/asmsrc/LibAxioms.lean`
- `/tmp/varform-decomp-WPTPfS/solchk/AllSolutions.lean`
- `/tmp/varform-decomp-WPTPfS/scripts/numcheck_pure.py`

Neither the pinned Mathlib (25730c7c) nor SimonGMT (2b36630) has a first or second variation formula for Hⁿ of a deformed submanifold. SimonGMT Chapter 8 proves only the varifold first variation for C² families: familyJacobian, hasDerivAt_familySpatialDerivative and hasDerivAt_integral_of_contDiffAt_on_compact. Nothing second-order exists. The reusable ingredients do exist, and #print axioms shows only propext, Classical.choice and Quot.sound for all of them. From SimonGMT: injective_area_formula_areaJacobianAt, IsSimonLocalRepresentation.weighted_area_formula, areaJacobian_comp_eq_parametrization_mul_tangential, and tangentialJacobianReal_eq_sqrt_det_ambientGram (the matrix form of gram_det_identity). From Mathlib: LinearMap.normDet_comp, ContinuousLinearMap.normDet_sq, LinearMap.normDet_sq_eq_det_gram, hasDerivAt_integral_of_dominated_loc_of_deriv_le, ContDiffAt.isSymmSndFDerivAt, HasDerivAt.finsetProd, MeasurableSet.image_of_continuousOn_injOn, Submodule.starProjection_norm_le, Submodule.isIdempotentElem_starProjection and setIntegral_eq_of_subset_of_forall_sdiff_eq_zero. Mathlib has no ContDiff lemma for det and no ContinuousOn.comp_aestronglyMeasurable. The child proofs therefore spell out those steps, and scratch Lean shows det and adjoint are smooth on Rn N →L Rn N in a few lines. All six statements pass validate_lean_statement. Their contract-mode NodeChallenge modules compile against the frozen Submission, and the `exact Submission.X` solution modules compile against stand-ins. FirstVariation ∧ SecondVariation is proved sorry-free from stand-ins of the six children plus the frozen sibling; its axioms are propext, sorryAx (stand-ins only), Classical.choice and Quot.sound. variation_jacobian_family is fully proved from its two declared dependencies. The proposed names collide with nothing in dag.json or in the other proposals.
