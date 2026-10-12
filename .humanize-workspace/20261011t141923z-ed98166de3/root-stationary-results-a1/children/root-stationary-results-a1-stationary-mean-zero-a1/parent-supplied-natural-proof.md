# Parent-supplied natural-language proof

- Parent DAG node: `root.stationary_results-a1`
- Child DAG node: `root.stationary_results-a1.stationary_mean_zero-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

(TH) denotes the frozen statement of the sibling node root.submanifold_tangent-a1 (Submission.simon_submanifold_tangent_basics), taken here as an explicit hypothesis: (TH1) for all n, N, r ≥ 1, M ⊆ ℝᴺ and every Simon local representation (V, W, ψ) of M of class r, tangentSpace M (ψ x) = range Dψ(x) for every x ∈ V; (TH2) every n-dimensional C^r Simon submanifold M of ℝᴺ is a measurable set and y ↦ tangentProjection M y is continuous on M.
Notation. ℝ^d := EuclideanSpace ℝ (Fin d) (= Rn d); Hⁿ := μHE[n]. A chart of class r of M is a triple (V, W, ψ) with Chapter02.IsSimonLocalRepresentation r M V W ψ: V ⊆ ℝⁿ and W ⊆ ℝᴺ open, ψ C^r on V, ψ injective on V, ψ(V) = W ∩ M, ψ relatively proper (V ∩ ψ⁻¹(K) is compact for every compact K ⊆ W) and Dψ(x) injective for x ∈ V. For y ∈ M: T_y := tangentSpace M y, P_y := tangentProjection M y (orthogonal projection onto T_y), v^⊥ := normalPart M y v = v − P_y v, τ_i := tangentFrame M y i (an orthonormal basis of T_y), B_y(τ, η) := secondFundamentalForm M y τ η = (fderivWithin ℝ (tangentProjection M) M y τ) η, H(y) := meanCurvature M y = Σ_i B_y(τ_i, τ_i), div_M Y(y) := tangentialDivergence M Y y = Σ_i ⟨τ_i, DY(y)τ_i⟩, and D²ψ(x)[a, b] := fderiv ℝ (fderiv ℝ ψ) x a b (the derivative at x in direction a of x′ ↦ Dψ(x′)b).

Source: Simon, Ch. 2, Lemma 5.5(2) (p. 63), direction "M stationary in U ⇒ H ≡ 0 on M ∩ U", together with the remark after 5.4 ("by the first variation formula 5.3 this is equivalent to ∫_M div_M X dHⁿ = 0 whenever X is C¹ on U with support X a compact subset of U") and 4.30. Printed proof: "In view of 4.30 we also have the following: 5.5 Lemma ..." (no further argument). This is parent proof II.2 steps 6-7. The hypothesis that Ū ∩ M is compact is not needed for this direction, because the test fields are supported in small closed balls inside a chart target, where relative properness makes M ∩ B̄ compact.

Setting. Assume (TH) and FirstVariation. M ⊆ ℝ^{n+ℓ} is an n-dimensional C² Simon submanifold, U is open, and IsStationaryIn n M U, i.e. (S1) μHE[n](M ∩ K) < ∞ for every compact K ⊆ U, and (S2) HasDerivAt (deformedArea n M K φ) 0 0 whenever IsAdmissibleDeformation 2 U K φ. Hⁿ := μHE[n], H := meanCurvature M.

1. Fix y₀ ∈ M ∩ U and suppose, for a contradiction, that H(y₀) ≠ 0. Let e := H(y₀) and c₀ := ‖H(y₀)‖²/2 > 0.
2. Choose a chart (V, W, ψ) of class 2 with y₀ ∈ W. H is continuous on M (sibling sff_properties, second conjunct), so there is δ > 0 with ‖H(y) − H(y₀)‖ ≤ ‖H(y₀)‖/2 for all y ∈ M with ‖y − y₀‖ < δ. Choose ρ > 0 with 2ρ < δ and B̄(y₀, 2ρ) ⊆ U ∩ W (U ∩ W is an open set containing y₀). For y ∈ M ∩ B̄(y₀, 2ρ), by Cauchy-Schwarz: ⟨e, H(y)⟩ = ‖H(y₀)‖² + ⟨H(y₀), H(y) − H(y₀)⟩ ≥ ‖H(y₀)‖² − ‖H(y₀)‖ · ‖H(y₀)‖/2 = c₀.
3. S := B̄(y₀, 2ρ) is compact, closed, S ⊆ U and S ⊆ W. M ∩ S = ψ(V ∩ ψ⁻¹(S)) is compact (relative properness, continuity of ψ on V, W ∩ M = ψ(V)). By sibling measure_bounds (a), Hⁿ(M ∩ S) < ∞.
4. Let ζ be the C^∞ bump function centred at y₀ with rIn = ρ, rOut = 2ρ (ContDiffBump): 0 ≤ ζ ≤ 1, ζ = 1 on B̄(y₀, ρ), ζ(x) = 0 for ‖x − y₀‖ ≥ 2ρ, and tsupport ζ = S (ContDiffBump.tsupport_eq; only tsupport ζ ⊆ S is needed). Let Y(x) := ζ(x) • e. Then Y is C^∞ (in particular C²), HasCompactSupport Y, and tsupport Y ⊆ tsupport ζ = S ⊆ U.
5. By the sibling scaled_deformation there is c > 0 such that φ t x := x + (c t) • Y(x) satisfies IsAdmissibleDeformation 2 U K φ with K := tsupport Y, and initialVelocity φ x = c • Y(x) for all x, i.e. initialVelocity φ = (x ↦ c • Y(x)).
6. By (S2), HasDerivAt (deformedArea n M K φ) 0 0. FirstVariation applies: M is a C¹ Simon submanifold (1 ≤ 1, and each class-2 chart is a class-1 chart because ContDiffOn ℝ 2 implies ContDiffOn ℝ 1); U is open; y₀ ∈ U ∩ M; for compact K′ ⊆ U, μHE[n](K′ ∩ M) = μHE[n](M ∩ K′) < ∞ by (S1); φ is admissible of class 2. It gives HasDerivAt (deformedArea n M K φ) (∫_M div_M(initialVelocity φ) dHⁿ) 0. By uniqueness of derivatives (HasDerivAt.unique), ∫_M div_M(c • Y) dHⁿ = 0.
7. Apply the sibling divergence_identity to the C¹ field c • Y and the closed set S (c • Y = 0 off S because Y = 0 off tsupport Y ⊆ S; M ∩ S is compact by step 3): the function f(y) := ⟨c • Y(y), H(y)⟩ = c ζ(y) ⟨e, H(y)⟩ is integrable on M and ∫_M div_M(c • Y) = −∫_M f. Hence ∫_M f dHⁿ = 0.
8. f ≥ 0 on M: for y ∈ M with ‖y − y₀‖ < 2ρ, ζ(y) ≥ 0, c > 0 and ⟨e, H(y)⟩ ≥ c₀ > 0 (step 2); for the other y ∈ M, ζ(y) = 0. Moreover f ≥ c c₀ on M ∩ B, B := B(y₀, ρ), since ζ = 1 there. M ∩ B is measurable (M is measurable by (TH2), B is open) and Hⁿ(M ∩ B) ≤ Hⁿ(M ∩ S) < ∞. As f is integrable and nonnegative on M: ∫_M f ≥ ∫_{M ∩ B} f ≥ c c₀ · Hⁿ(M ∩ B) (MeasureTheory.setIntegral_mono_set, then the constant lower bound on a set of finite measure).
9. By sibling measure_bounds (b) (y₀ ∈ M, B open, y₀ ∈ B), Hⁿ(M ∩ B) > 0, and it is finite; so ∫_M f ≥ c c₀ Hⁿ(M ∩ B) > 0, contradicting step 7. Hence H(y₀) = 0. As y₀ ∈ M ∩ U was arbitrary, meanCurvature M y = 0 for all y ∈ M ∩ U.

## Key steps

1. If H(y₀) ≠ 0, continuity of H on M gives ⟨H(y₀), H⟩ ≥ c₀ > 0 on M ∩ B̄(y₀,2ρ) with B̄(y₀,2ρ) ⊆ U ∩ W, and M ∩ B̄(y₀,2ρ) is compact by chart properness.
2. With a bump ζ and Y = ζH(y₀), the deformation x + ctY(x) is admissible with velocity cY (scaled_deformation).
3. Stationarity, FirstVariation and uniqueness of derivatives give ∫_M div_M(cY) = 0; the divergence identity gives ∫_M cζ⟨H(y₀),H⟩ = 0.
4. The integrand is ≥ 0 on M and ≥ c·c₀ on M ∩ B(y₀,ρ), which has positive finite Hⁿ-measure (measure_bounds): contradiction.

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
