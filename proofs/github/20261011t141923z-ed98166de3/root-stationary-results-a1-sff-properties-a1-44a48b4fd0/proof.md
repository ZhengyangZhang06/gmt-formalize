# Parent-supplied natural-language proof

- Parent DAG node: `root.stationary_results-a1`
- Child DAG node: `root.stationary_results-a1.sff_properties-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

(TH) denotes the frozen statement of the sibling node root.submanifold_tangent-a1 (Submission.simon_submanifold_tangent_basics), taken here as an explicit hypothesis: (TH1) for all n, N, r ≥ 1, M ⊆ ℝᴺ and every Simon local representation (V, W, ψ) of M of class r, tangentSpace M (ψ x) = range Dψ(x) for every x ∈ V; (TH2) every n-dimensional C^r Simon submanifold M of ℝᴺ is a measurable set and y ↦ tangentProjection M y is continuous on M.
Notation. ℝ^d := EuclideanSpace ℝ (Fin d) (= Rn d); Hⁿ := μHE[n]. A chart of class r of M is a triple (V, W, ψ) with Chapter02.IsSimonLocalRepresentation r M V W ψ: V ⊆ ℝⁿ and W ⊆ ℝᴺ open, ψ C^r on V, ψ injective on V, ψ(V) = W ∩ M, ψ relatively proper (V ∩ ψ⁻¹(K) is compact for every compact K ⊆ W) and Dψ(x) injective for x ∈ V. For y ∈ M: T_y := tangentSpace M y, P_y := tangentProjection M y (orthogonal projection onto T_y), v^⊥ := normalPart M y v = v − P_y v, τ_i := tangentFrame M y i (an orthonormal basis of T_y), B_y(τ, η) := secondFundamentalForm M y τ η = (fderivWithin ℝ (tangentProjection M) M y τ) η, H(y) := meanCurvature M y = Σ_i B_y(τ_i, τ_i), div_M Y(y) := tangentialDivergence M Y y = Σ_i ⟨τ_i, DY(y)τ_i⟩, and D²ψ(x)[a, b] := fderiv ℝ (fderiv ℝ ψ) x a b (the derivative at x in direction a of x′ ↦ Dψ(x′)b).

Source: Simon, Ch. 2, 4.26 ("4.26 implies in particular that B_y(τ, η) = B_y(η, τ); that is B_y is a symmetric bilinear form with values in (T_yM)^⊥"), 4.27 (H(y) = Σ_i B_y(τ_i, τ_i)), and the identity used in the printed proof of 5.11 ("τ_i · D_{τ_j}X = −X · B(τ_i, τ_j) by virtue of 4.24 and the fact that X is normal to M"). Parent proof G2-G3, derived from the chart formula of the sibling sff_chart.

Setting. Assume (TH) [(TH1): T_{ψ(x)} = range Dψ(x) for every Simon local representation (V, W, ψ) of class ≥ 1 and x ∈ V]. M is an n-dimensional C² Simon submanifold of ℝᴺ. Notation as in sff_chart; S_x(a, b) := D²ψ(x)[a, b] = fderiv ℝ (fderiv ℝ ψ) x a b.

0. (Charts and the chart formula.) Let y ∈ M. By IsSimonSubmanifold 2 M there is a chart (V, W, ψ) of class 2 with y ∈ W; since W ∩ M = ψ(V), y = ψ(x) for some x ∈ V. By (TH1), T_y = range Dψ(x), so every τ, η ∈ T_y can be written τ = Dψ(x)a, η = Dψ(x)b with a, b ∈ ℝⁿ. By the sibling theorem sff_chart (Submission.second_fundamental_form_chart_formula, applied with the hypothesis (TH) and this chart):
 (*) B_y(Dψ(x)a, Dψ(x)b) = (S_x(a, b))^⊥ for all a, b ∈ ℝⁿ.
1. (Symmetry.) ψ is C² on the open set V ∋ x, so ContDiffAt ℝ 2 ψ x and its second derivative at x is symmetric: S_x(a, b) = S_x(b, a) (ContDiffAt.isSymmSndFDerivAt, with minSmoothness ℝ 2 = 2). By (*), B_y(τ, η) = (S_x(a, b))^⊥ = (S_x(b, a))^⊥ = B_y(η, τ).
2. (Normality.) For w ∈ ℝᴺ and v ∈ T_y: ⟨w^⊥, v⟩ = ⟨w, v⟩ − ⟨P_y w, v⟩ = ⟨w, v⟩ − ⟨w, P_y v⟩ = 0, because P_y is self-adjoint and P_y v = v. With w = S_x(a, b), (*) gives ⟨B_y(τ, η), v⟩ = 0 for every v ∈ T_y. Steps 1 and 2 prove the first conjunct.
3. (Normal fields; parent G3.) Let Y : ℝᴺ → ℝᴺ be differentiable at y ∈ M with ⟨Y(z), v⟩ = 0 for all z ∈ M and v ∈ T_z, and let τ = Dψ(x)a, η = Dψ(x)b ∈ T_y as in step 0. For x′ ∈ V, ψ(x′) ∈ M and Dψ(x′)b ∈ range Dψ(x′) = T_{ψ(x′)} (TH1), hence f(x′) := ⟨Y(ψ(x′)), Dψ(x′)b⟩ = 0 for all x′ in the open neighbourhood V of x, and therefore Df(x) = 0. f is differentiable at x: Y ∘ ψ is (chain rule; Y is differentiable at ψ(x) = y and ψ at x), and x′ ↦ Dψ(x′)b is (ψ is C² on the open set V). By the product rule for the inner product (HasFDerivAt.inner): 0 = Df(x)a = ⟨DY(y) Dψ(x)a, Dψ(x)b⟩ + ⟨Y(y), S_x(a, b)⟩. Write S_x(a, b) = (S_x(a, b))^⊥ + P_y S_x(a, b); since P_y S_x(a, b) ∈ T_y and Y(y) ⊥ T_y, ⟨Y(y), S_x(a, b)⟩ = ⟨Y(y), (S_x(a, b))^⊥⟩ = ⟨Y(y), B_y(τ, η)⟩ by (*). Hence ⟨η, DY(y)τ⟩ = ⟨DY(y)τ, η⟩ = −⟨Y(y), B_y(τ, η)⟩, which is the third conjunct.
4. (Mean curvature in a chart.) Fix a chart (V, W, ψ) of class 2. For x ∈ V let A(x) := Dψ(x), G(x) := A(x)*A(x) (symmetric, positive definite, invertible), Π(A) := A(A*A)⁻¹A* (the orthogonal projection onto range A; by (TH1), Π(A(x)) = P_{ψ(x)}), e_1, …, e_n the standard orthonormal basis of ℝⁿ, and g^{kl}(x) := ⟨e_k, G(x)⁻¹ e_l⟩. Put w(x) := Σ_{k,l} g^{kl}(x) S_x(e_k, e_l) and h(x) := w(x) − Π(A(x)) w(x). Claim: H(ψ(x)) = h(x) for every x ∈ V.
 Proof of the claim. Let y = ψ(x) and τ_i := tangentFrame M y i for i ∈ Fin d, d := finrank T_y; as T_y = range A(x) and A(x) is injective, d = n and (τ_i) is an orthonormal basis of range A(x). Let a_i := A(x)⁻¹ τ_i ∈ ℝⁿ (A(x) is a linear isomorphism of ℝⁿ onto T_y). By (*) and linearity of v ↦ v^⊥: H(y) = Σ_i B_y(τ_i, τ_i) = (Σ_i S_x(a_i, a_i))^⊥. The vectors a_i form a basis of ℝⁿ that is orthonormal for the inner product (u, v) ↦ ⟨G u, v⟩ = ⟨A u, A v⟩; hence every u ∈ ℝⁿ satisfies u = Σ_i ⟨G a_i, u⟩ a_i. Applying this to u = G⁻¹ e_l and using G* = G gives G⁻¹ e_l = Σ_i ⟨a_i, e_l⟩ a_i, hence g^{kl} = ⟨e_k, G⁻¹ e_l⟩ = Σ_i ⟨e_k, a_i⟩⟨e_l, a_i⟩. By bilinearity of S_x, Σ_i S_x(a_i, a_i) = Σ_{k,l} (Σ_i ⟨e_k, a_i⟩⟨e_l, a_i⟩) S_x(e_k, e_l) = w(x). Finally w(x)^⊥ = w(x) − P_y w(x) = h(x).
5. (Continuity of H.) h is continuous on V: A is continuous on V (ψ ∈ C¹), G and G⁻¹ are continuous (inversion is continuous on invertible operators), x ↦ S_x = D²ψ(x) is continuous on V (ψ ∈ C² on the open V), and Π is continuous on the open set of injective maps. By SimonGMT IsSimonLocalRepresentation.isEmbedding_chartMap, ψ restricts to a homeomorphism of V onto W ∩ M; hence H = h ∘ (ψ|_V)⁻¹ is continuous on W ∩ M. Given y₀ ∈ M, choose such a chart with y₀ ∈ W; H restricted to M ∩ W is continuous at y₀ and W is a neighbourhood of y₀, so H is continuous within M at y₀ (continuousWithinAt_inter). Hence ContinuousOn (meanCurvature M) M, the second conjunct.

## Key steps

1. For y = ψ(x) ∈ M, every τ, η ∈ T_y equal Dψ(x)a, Dψ(x)b (TH1), and B_y(τ,η) = (D²ψ(x)[a,b])^⊥ by sff_chart.
2. Symmetry of D²ψ(x) (C²) gives B_y(τ,η) = B_y(η,τ); ⟨w^⊥, v⟩ = 0 for v ∈ T_y gives normality.
3. Differentiating ⟨Y(ψ(x′)), Dψ(x′)b⟩ ≡ 0 at x gives ⟨η, DY(y)τ⟩ = −⟨Y(y), B_y(τ,η)⟩ for normal Y.
4. H(ψ(x)) = (Σ_{k,l} (G⁻¹)_{kl} D²ψ(x)[e_k,e_l])^⊥ is continuous in x; ψ is a homeomorphism onto W ∩ M, so H is continuous on M.

## Reference use

### local-project

Queries:
- `cat -n GMT/Ch02/Contract.lean; diff GMT/Ch02/Contract.lean GMT/Ch02/Submission.lean; cat GMT/Ch02/README.md`
- `grep -rn "μHE\[" mathlib/Mathlib --include=*.lean | grep -E "notation|def "; sed -n 1,140p mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `cat -n simongmt/Poincare/SimonGMT/Chapter02/{Submanifold,SubmanifoldCalculus,SecondFundamentalForm,SecondFundamentalFormCalculus,SubmanifoldIntegral,SubmanifoldTopology,WeightedArea,Area}.lean; grep -n 'injective_area_formula_of_injective_derivative' AreaFormula.lean`
- `grep -rn "theorem ContDiffAt.isSymmSndFDerivAt\|theorem HasFDerivWithinAt.unique_on\|theorem ContDiffAt.to_localInverse\|theorem LipschitzOnWith.hausdorffMeasure_image_le\|theorem HasCompactSupport.fderiv\|theorem finrank_euclideanSpace_fin" mathlib/Mathlib`
- `grep -rn tangentConeAt mathlib/Mathlib --include=*.lean | grep -E "theorem|lemma" | grep -iE "deriv|curve|segment|mem_tangentCone"; grep -rn mapsTo_tangent mathlib/Mathlib`
- `grep -rn "integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable\|integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable" mathlib/Mathlib; grep -n "theorem\|lemma" mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `grep -rn "Submission\.\|stationary_imp_mean_curvature_zero\|second_fundamental_form_chart_formula\|submanifold_divergence_identity_compact\|deformation_velocity_acceleration_regularity" project simongmt/Poincare; python3 -I lean_name collision check against dag.json`
- `python3 -I gen_checks.py (replays verifier gmt-compare.py contract_scope/child_modules and lean_contract.validate_lean_statement for the 10 lean_statements); lake build GMT.Ch02.Submission; lake env lean NodeChallenge_00..09.lean; lake env lean AssemblyCheck.lean`
- `lake env lean LibCheck.lean: #print axioms Poincare.SimonGMT.Chapter02.{integral_area_formula_of_injective_derivative, IsSimonLocalRepresentation.area_formula, IsSimonLocalRepresentation.weighted_area_formula, IsSimonLocalRepresentation.exists_open_image_eq_inter, IsSimonLocalRepresentation.isEmbedding_chartMap, submanifoldDivergenceAt_eq_sum_inner, measurable_areaJacobianAt}; #check of every cited Mathlib lemma`
- `sed -n 1030,1420p book/chapter-02.txt (printed 4.18-5.12); read dag.json and nodes/root-stationary-results-a1/parent-child-handoff.json`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Equiv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/TangentCone/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Submanifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SecondFundamentalForm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SecondFundamentalFormCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldTopology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaFormula.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-stationary-results-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/stat-decomp2/AssemblyCheck.lean`

The frozen contract (Contract.lean lines 83-176 and 297-342) defines the key notions:
- B is fderivWithin of tangentProjection;
- H is the frame trace;
- IsStationaryIn is defined variationally.

Collision checks: the snapshot project has no Submission.* declarations and no declaration with any of the ten proposed names, and dag.json (50 nodes) has no lean_name collision.

SimonGMT supplies kernel-checked tools used by the children:
- WeightedArea.lean: integral_area_formula_of_injective_derivative and IsSimonLocalRepresentation.area_formula;
- SubmanifoldTopology.lean: IsSimonLocalRepresentation.exists_open_image_eq_inter and isEmbedding_chartMap;
- SubmanifoldCalculus.lean: submanifoldDivergenceAt_eq_sum_inner;
- measurable_areaJacobianAt.
#print axioms shows only propext, Classical.choice and Quot.sound for all of them.

SimonGMT has no divergence theorem on submanifolds (integral_submanifoldDivergence_eq_curvature_sub_boundary takes it as a hypothesis), no chart formula for the frame-free B, and nothing on admissible deformations. These are therefore genuine new obligations.

Mathlib 25730c7c supplies ContDiffAt.isSymmSndFDerivAt, HasFDerivWithinAt.unique_on, HasFDerivWithinAt.mapsTo_tangent_cone, tangentConeAt_mono, tangentConeAt_of_mem_nhds, ContDiffAt.toOpenPartialHomeomorph, ContDiffAt.to_localInverse, OpenPartialHomeomorph.contDiffAt_symm, integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable, LinearMap.normDet_ne_zero_tfae, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, LipschitzOnWith.hausdorffMeasure_image_le, ContractingWith.fixedPoint, HasCompactSupport.fderiv and ContDiffBump. exists_smooth_tsupport_subset does not exist, so it is not cited. setIntegral_eq_of_subset_of_forall_diff_eq_zero is deprecated, so the _sdiff_ name is cited.

Compile checks:
- All ten lean_statements pass the workflow validator and elaborate in the comparator-replayed contract scope; NodeChallenge_00..09 compiled with only sorry warnings.
- AssemblyCheck.lean proves the frozen parent type StationaryIffMeanCurvatureZero ∧ SecondVariationStationary from the children and the sibling types. Its axioms are sorryAx from the stubs plus propext, Classical.choice and Quot.sound.
- Glue examples that instantiate the children as their proofs use them also compile.
