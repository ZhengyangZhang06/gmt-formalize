# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.cone-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.cone-a1.tangent_projection_measurable-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Sources.
- Parent step 0: the Cauchy–Binet description of the tangent projection through the orientation.
- Simon Ch. 6, 3.1 (chapter-06.txt lines 733–752): ξ is Hⁿ-measurable and, Hⁿ-a.e. on M, ξ(x) = τ₁∧⋯∧τₙ for an orthonormal basis τ of the approximate tangent space T_xM.
- Simon Ch. 6, 1.5–1.7 (lines 93–108): the induced inner products for which the basic (co)vectors are orthonormal. Step 3 below is the identity behind this.
- Simon Ch. 3, 1.4–1.5 (chapter-03.txt lines 75–90): approximate tangent space, unique if it exists.

Notation. M = R.carrier, ξ = R.orient, ν := Hⁿ⌞M = μHE[n].restrict M. e_1, …, e_P is the standard orthonormal basis of ℝ^P, so ⟨e_i, u⟩ = u(i). T_x := approxTangentPlane n M x and p_x is its starProjection. For a subspace Q, p_Q denotes the orthogonal projection onto Q. For b ∈ Fin n, succAbove_b : Fin (n−1) → Fin n is the order embedding that skips b.

1. Case n = 0. Suppose some Q satisfies HasApproximateTangentSpaceAt 0 M x Q. Then the subspace Q₀ chosen in the definition of approxTangentPlane also satisfies it, so finrank Q₀ = 0 (first conjunct of HasApproximateTangentSpaceAt) and Q₀ = ⊥. Otherwise T_x = ⊥ by definition. Hence p_x = p_⊥ = 0 for every x; a constant function is measurable. From now on n = m + 1.

2. Covectors.
- For j : Fin m → Fin P, let e^j be the m-covector e^j(u_1, …, u_m) := det(u_c(j(r)))_{r,c ∈ Fin m}; for m = 0 it is the constant 1. It is multilinear, alternating and continuous. In SimonGMT it is wedgeCovectors m (fun r ↦ EuclideanSpace.proj (j r)); see wedgeCovectors_apply_det in Chapter06/FormsDuality.lean.
- For v ∈ ℝ^P, let α_{v,j} be the n-covector α_{v,j}(u_0, …, u_m) := Σ_{b=0}^{m} (−1)^b ⟨v, u_b⟩ e^j(u_0, …, û_b, …, u_m). Equivalently, α_{v,j} = alternatizeUncurryFin((innerSL ℝ v).smulRight e^j) = wedgeCovectors n (Fin.cons (innerSL ℝ v) (fun r ↦ proj (j r))).

3. Gram identity (Cauchy–Binet). For a, b : Fin m → ℝ^P,
 Σ_{j : Fin m → Fin P} e^j(a)·e^j(b) = m!·det(⟨a_r, b_c⟩)_{r,c}.
Proof.
(i) By the Leibniz formula applied to the transpose, e^j(a) = Σ_{σ∈S_m} sgn σ Π_r a_{σ(r)}(j(r)) and e^j(b) = Σ_{π∈S_m} sgn π Π_r b_{π(r)}(j(r)).
(ii) Hence Σ_j e^j(a)e^j(b) = Σ_{σ,π} sgn σ sgn π Σ_j Π_r a_{σ(r)}(j(r)) b_{π(r)}(j(r)).
(iii) A sum over all functions j of a product of factors, the r-th depending only on j(r), equals the product of the sums. So the expression is Σ_{σ,π} sgn σ sgn π Π_r Σ_{i=1}^{P} a_{σ(r)}(i) b_{π(r)}(i).
(iv) By Parseval in the standard basis this is Σ_{σ,π} sgn σ sgn π Π_r ⟨a_{σ(r)}, b_{π(r)}⟩.
(v) Substitute r = σ⁻¹(c) in the product. It becomes Π_c ⟨a_c, b_{ρ(c)}⟩ with ρ := π∘σ⁻¹, and sgn σ sgn π = sgn ρ because sgn is multiplicative with values ±1.
(vi) For fixed σ, π ↦ ρ is a bijection of S_m. So the sum is Σ_σ Σ_ρ sgn ρ Π_c ⟨a_c, b_{ρ(c)}⟩ = m!·det((⟨a_r, b_c⟩)ᵀ) = m!·det(⟨a_r, b_c⟩).

4. Projection formula. Let Q be a subspace and ζ ∈ Λ_n(ℝ^P) = (Covector (ℝ^P) n →L ℝ) with IsUnitOrientationOf ζ Q. That is, there are an orthonormal τ : Fin n → ℝ^P with span(range τ) = Q and ε ∈ {1, −1} such that ζ(α) = ε·α(τ) for every α. Then for all v, w ∈ ℝ^P,
 Σ_{j : Fin m → Fin P} ζ(α_{v,j})·ζ(α_{w,j}) = m!·⟨p_Q v, w⟩.
Proof.
(i) Deleting the b-th entry of τ gives τ∘succAbove_b. Hence ζ(α_{v,j}) = ε Σ_b (−1)^b ⟨v, τ_b⟩ e^j(τ∘succAbove_b).
(ii) Multiply the expressions for v and w, sum over j, use ε² = 1, and apply step 3 with a = τ∘succAbove_b and b = τ∘succAbove_{b'}:
 Σ_j ζ(α_{v,j})ζ(α_{w,j}) = Σ_{b,b'∈Fin n} (−1)^{b+b'} ⟨v,τ_b⟩⟨w,τ_{b'}⟩·m!·det(⟨τ_{succAbove_b(r)}, τ_{succAbove_{b'}(c)}⟩)_{r,c}.
(iii) If b = b', the matrix is the identity (τ is orthonormal and succAbove_b is injective), so its determinant is 1.
(iv) If b ≠ b', then b' = succAbove_b(r₀) for some r₀, since succAbove_b is a bijection of Fin m onto Fin n ∖ {b}. Row r₀ of the matrix is (⟨τ_{b'}, τ_{succAbove_{b'}(c)}⟩)_c = 0, because succAbove_{b'}(c) ≠ b'. So the determinant is 0.
(v) Hence the sum is m!·Σ_b ⟨v,τ_b⟩⟨w,τ_b⟩ = m!·⟨Σ_b ⟨τ_b, v⟩τ_b, w⟩ = m!·⟨p_Q v, w⟩. The last equality holds because (τ_b) is an orthonormal basis of Q, so p_Q v = Σ_b ⟨τ_b, v⟩τ_b.

5. A continuous Π. Define Π : Λ_n(ℝ^P) → L(ℝ^P, ℝ^P) by
 Π(ζ) := Σ_{a,b=1}^{P} g_{ab}(ζ)·L_{ab},
where g_{ab}(ζ) := (1/m!) Σ_j ζ(α_{e_a,j})·ζ(α_{e_b,j}) and L_{ab}(v) := ⟨e_a, v⟩e_b, i.e. L_{ab} = (innerSL e_a).smulRight e_b.
- For each fixed α, the map ζ ↦ ζ(α) is continuous and linear. Hence each g_{ab} is continuous, and so is Π.
- If IsUnitOrientationOf ζ Q, then g_{ab}(ζ) = ⟨p_Q e_a, e_b⟩ by step 4. So for all v: Π(ζ)v = Σ_b Σ_a ⟨e_a, v⟩⟨p_Q e_a, e_b⟩e_b = Σ_b ⟨p_Q(Σ_a ⟨e_a,v⟩e_a), e_b⟩e_b = Σ_b ⟨p_Q v, e_b⟩e_b = p_Q v. That is, Π(ζ) = p_Q.

6. A.e. identification. By the field `orients`, for ν-a.e. x there is Q_x with HasApproximateTangentSpaceAt n M x Q_x and IsUnitOrientationOf (ξ x) Q_x. At such x, the condition of the `if` in approxTangentPlane holds. The chosen subspace Q' then satisfies HasApproximateTangentSpaceAt n M x Q', and HasApproximateTangentSpaceAt.unique (SimonGMT, Ch. 3 Remark 1.5(1)) gives Q' = Q_x. So T_x = Q_x and, by step 5, p_x = Π(ξ x).

7. Conclusion. ξ is AEStronglyMeasurable for ν (field aestronglyMeasurable_orient) and Π is continuous, so Π∘ξ is AEStronglyMeasurable for ν. By step 6, x ↦ p_x equals Π∘ξ ν-a.e., so it is AEStronglyMeasurable for ν. It is therefore AEMeasurable for the Borel σ-algebra of the finite-dimensional normed space L(ℝ^P, ℝ^P). ∎

## Key steps

1. n = 0: approxTangentPlane is ⊥ everywhere, so the projection is the constant 0.
2. Gram (Cauchy–Binet) identity Σ_{j:Fin m→Fin P} e^j(a)e^j(b) = m!·det(⟨a_r,b_c⟩), by Leibniz expansion, product-of-sums and Parseval.
3. If ζ = ±τ₁∧⋯∧τₙ orients Q, then Σ_j ζ(v♭∧e^j)ζ(w♭∧e^j) = m!⟨p_Q v, w⟩; this defines a continuous Π with Π(ζ) = p_Q.
4. Hⁿ-a.e. on M, ξ(x) orients the unique approximate tangent plane T_x, so p_x = Π(ξ(x)); composing the continuous Π with the AE-strongly-measurable ξ gives AEMeasurable.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical); cmp … GMT/Ch07/Submission.lean (identical); git rev-parse HEAD = b4d606db; git -C lake-packages-25730c7c/simongmt rev-parse HEAD = 2b366308; git -C lake-packages-25730c7c/mathlib rev-parse HEAD = 25730c7c`
- `grep -nE '^(theorem|def)' simongmt/Poincare/SimonGMT/Chapter04/FirstVariation.lean (IsStationaryIn.satisfiesStationaryMonotonicity, SatisfiesStationaryMonotonicity, normalizedBallMass, monotonicityDefect, radialNormalSq_eq, tangentialDivergence_integrable_of_isAdmissible); sed -n 1,230p Chapter04/Basic.lean (structure RectifiableVarifold); sed -n 1,80p Chapter04/MultiplicityBridge.lean (weight_eq_carrier_withDensity, ae_weight_iff_ae_carrier)`
- `grep -nE '^(theorem|def)' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (HasApproximateTangentSpaceAt, HasApproximateTangentSpaceAt.unique, approximateTangentField_ae_eq, IsLocallyIntegrableMultiplicity)`
- `cat simongmt/Poincare/SimonGMT/Chapter06/{Forms,Currents,AffineCurrentPushforward,CurrentLocalEquality}.lean; sed -n 100,200p Chapter06/FormsDuality.lean (wedgeCovectors, wedgeCovectors_apply_det); sed -n 20,60p Chapter06/Mass.lean (covectorEuclideanNorm)`
- `grep -rln Binet mathlib/Mathlib (only GoldenRatio, CrossProduct: no Cauchy–Binet); Mathlib/Analysis/Normed/Module/Alternating/Curry.lean (curryLeft, curryLeftLI, curryLeft_same); grep theorem Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean (alternatizeUncurryFin_apply, alternatizeUncurryFin_curryLeft, map_insertNth); grep 'def extDeriv' Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean; head Mathlib/Analysis/Calculus/DifferentialForm/VectorField.lean; grep theorem Mathlib/Analysis/InnerProductSpace/NormDet.lean; grep det_mul Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean; grep 'lemma removeNth_' Mathlib/Data/Fin/Tuple/Basic.lean`
- `inventory of all lean_name values in runs/20261011T150044Z-ba604216b4 (dag.json and node JSON files): 100 reserved names; grep -rl for each of the six proposed names: 0 hits`
- `sed -n 300,370p book/chapter-07.txt (7.3.1 and proof, lines 326-360); sed -n 85,112p, 430,480p, 540,580p, 733,760p book/chapter-06.txt (1.5-1.7, 2.25-2.27, 2.33, 3.1); sed -n 205,320p book/chapter-04.txt (3.1-3.6); grep -n 'approximate tangent' book/chapter-03.txt (1.4-1.5)`
- `python3 -I scripts/gen.py: verifier gmt-compare.contract_scope + child_modules(mode=contract) and lean_contract.validate_lean_statement on the six child types; lake env lean Check/Ch_*.lean and Check/Sol_*.lean`
- `lake env lean Check/Types.lean, Check/Assembly.lean, Check/Cartan.lean, Check/Wedge.lean, Check/Unfold.lean, Check/Mono.lean, Check/Radial.lean, each with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-tangent-projection-aemeasurable-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-radial-tangency-of-ball-ratio-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/FirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/MultiplicityBridge.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/VectorField.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/cone-decomp-iFw2Y3/proj/Check/Types.lean`
- `/tmp/cone-decomp-iFw2Y3/proj/Check/Assembly.lean`
- `/tmp/cone-decomp-iFw2Y3/proj/Check/Cartan.lean`
- `/tmp/cone-decomp-iFw2Y3/proj/Check/Wedge.lean`
- `/tmp/cone-decomp-iFw2Y3/proj/Check/Unfold.lean`
- `/tmp/cone-decomp-iFw2Y3/proj/Check/Mono.lean`
- `/tmp/cone-decomp-iFw2Y3/proj/Check/Radial.lean`
- `/tmp/cone-decomp-iFw2Y3/scripts/gen.py`
- `/tmp/cone-decomp-iFw2Y3/scripts/children.json`

The snapshot contract (project b4d606d, Mathlib 25730c7c, simongmt 2b36630) is byte-identical to the workspace Contract.lean and Submission.lean, so all six child types elaborate after `import GMT.Ch07.Submission` in the contract scope (namespace GMT.Ch07 with its opens).

SimonGMT supplies:
- the exact stationary monotonicity identity (Chapter04 RectifiableVarifold.IsStationaryIn.satisfiesStationaryMonotonicity, closed balls, all n);
- the weight bridge weight_eq_carrier_withDensity;
- HasApproximateTangentSpaceAt.unique;
- wedgeCovectors_apply_det;
- the proper affine push-forward used by blowUp.
The monotonicity results are stated for the strengthened RectifiableVarifold, whose tangent-projection measurability field is exactly what child 1 provides; a scratch bridge proved child 2 from child 1 with standard axioms. The submission may import Chapter04.FirstVariation and MultiplicityBridge (the comparator only byte-checks frozen inputs).

Mathlib supplies extDeriv = alternatizeUncurryFin ∘ fderiv, ContinuousAlternatingMap.curryLeft/curryLeftLI and alternatizeUncurryFin_curryLeft; with these the Euler-field Cartan identity (child 5) and the x ∧ ξ = 0 lemma (child 4) were proved outright. Mathlib has no Cauchy–Binet theorem and no Lie derivative or Cartan formula, so child 1 proves its Gram identity by the Leibniz expansion.

The conditional assembly of the selected type from dtc_mass_eq_measure and children 3, 4 and 6 compiles with propext, Classical.choice and Quot.sound only. None of the six names occurs anywhere else in the run.
