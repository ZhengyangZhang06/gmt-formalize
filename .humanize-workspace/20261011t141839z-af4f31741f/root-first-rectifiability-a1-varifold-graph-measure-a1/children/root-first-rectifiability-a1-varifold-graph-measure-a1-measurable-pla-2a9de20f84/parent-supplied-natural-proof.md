# Parent-supplied natural-language proof

- Parent DAG node: `root.first_rectifiability-a1.varifold_graph_measure-a1`
- Child DAG node: `root.first_rectifiability-a1.varifold_graph_measure-a1.measurable_plane_selection-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 4 of the parent proof (a Borel version T̃ of x ↦ T_x built from averages of matrix entries; part of Simon, Ch. 8, proof of 1.2, p. 208, where T_x must be μ_V-measurable for the printed (1)–(2)). Here the construction is stated so that it only uses convergence of the averages, not tangent planes.

Notation: μ := V.weight; G := Grassmannian N n, the subtype of Matrix (Fin N) (Fin N) ℝ cut out by 𝒢 := {P : P.IsSymm ∧ P * P = P ∧ P.trace = n}, with the subspace topology and the induced (Borel) σ-algebra; 𝒢 is closed (Grassmannian.isClosed_projectionSet). B_r(y) := closedBall y r. For β ∈ C(G) and r ∈ ℝ, avg_r^x(β) := (∫_{B_r(x) × G} β(z.2) dV(z)) / (μ(B_r(x))).toReal.

1. Data. Fix S₀ ∈ G (G is nonempty by hypothesis). For a, b ∈ Fin N let e_{ab} ∈ C(G, ℝ), e_{ab}(S) := S.1 a b; it is continuous as the composition of the continuous inclusion Subtype.val with evaluation at the entry (a, b). For k ∈ ℕ put ρ_k := 1/(k + 1) > 0 and a_k^{ab}(x) := avg_{ρ_k}^x(e_{ab}).

2. Weight of balls. For every r ∈ ℝ, x ↦ μ(B_r(x)) is measurable: the set D_r := {(x, y) ∈ ℝ^N × ℝ^N : dist y x ≤ r} is closed, hence measurable, and Prod.mk x ⁻¹' D_r = B_r(x); μ is σ-finite (Varifold.weight.instSigmaFinite), hence s-finite, so measurable_measure_prodMk_left applies. Composing with the measurable map ENNReal.toReal, x ↦ (μ(B_r(x))).toReal is measurable.

3. Integrals over balls. For every r ∈ ℝ and β ∈ C(G, ℝ), x ↦ ∫_{B_r(x)×G} β(z.2) dV(z) is measurable. Indeed, let E_r := {(x, z) ∈ ℝ^N × (ℝ^N × G) : dist z.1 x ≤ r}, a closed and hence measurable set (all factors are second countable, so the product σ-algebra is the Borel σ-algebra), and F(x, z) := 1_{E_r}(x, z) β(z.2). F is measurable (indicator of a measurable set times a continuous function), hence strongly measurable as a real-valued function. For each x, B_r(x) ×ˢ univ is measurable and F(x, ·) is its indicator times z ↦ β(z.2), so ∫_{B_r(x)×G} β(z.2) dV(z) = ∫ F(x, z) dV(z) (integral_indicator). V.measure is σ-finite (Varifold.measure.instSigmaFinite), hence s-finite, so MeasureTheory.StronglyMeasurable.integral_prod_right' shows that x ↦ ∫ F(x, z) dV(z) is strongly measurable, hence measurable.

4. By 2, 3 (with r = ρ_k, β = e_{ab}) and measurability of division on ℝ, each a_k^{ab} : ℝ^N → ℝ is measurable, hence strongly measurable.

5. Limits. Let C^{ab} := {x : ∃ c, Tendsto (k ↦ a_k^{ab}(x)) atTop (𝓝 c)} and L^{ab}(x) := limUnder atTop (k ↦ a_k^{ab}(x)). C^{ab} is measurable (MeasureTheory.StronglyMeasurable.measurableSet_exists_tendsto; ℝ is completely metrizable) and L^{ab} is strongly measurable, hence measurable (MeasureTheory.StronglyMeasurable.limUnder). Let M(x) := Matrix.of (fun a b ↦ L^{ab}(x)); M : ℝ^N → Matrix (Fin N) (Fin N) ℝ is measurable because each entry is (Measurable.of_eval_matrix). Put Y := (⋂_{a,b} C^{ab}) ∩ M⁻¹(𝒢); it is measurable (a finite intersection of measurable sets; 𝒢 is closed, hence Borel).

6. Definition of τ. Let M'(x) := M(x) if x ∈ Y and M'(x) := S₀.1 otherwise (M' := Y.piecewise M (fun _ ↦ S₀.1)); M' is measurable (Measurable.piecewise: Y measurable, M measurable, constant measurable) and M'(x) ∈ 𝒢 for every x (for x ∈ Y by definition of Y; otherwise M'(x) = S₀.1 ∈ 𝒢). Put τ(x) := ⟨M'(x), _⟩ ∈ G; τ is measurable (Measurable.subtype_mk), and τ(x) = ⟨M(x), _⟩ for x ∈ Y, τ(x) = S₀ for x ∉ Y.

7. The property. Let x ∈ ℝ^N and T ∈ G be such that avg_ρ^x(β) → β(T) as ρ → 0⁺ for every β ∈ C(G, ℝ). Since ρ_k > 0 and ρ_k → 0, Tendsto (k ↦ ρ_k) atTop (𝓝[>] 0) (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within). Composing with the hypothesis for β = e_{ab} gives a_k^{ab}(x) → e_{ab}(T) = T.1 a b as k → ∞, for all a, b. Hence x ∈ C^{ab} and L^{ab}(x) = T.1 a b (Tendsto.limUnder_eq), so M(x) = T.1 ∈ 𝒢 and x ∈ Y. Therefore τ(x) = ⟨T.1, _⟩ = T (Subtype.ext). ∎

## Key steps

1. Matrix-entry functions e_ab(S) = S.1 a b in C(G) and averages a_k^{ab}(x) along ρ_k = 1/(k+1).
2. x ↦ μ_V(B_r(x)) is measurable (measurable_measure_prodMk_left) and x ↦ ∫_{Gₙ(B_r(x))} β dV is measurable (integral_prod_right' on a closed set), so each a_k^{ab} is measurable.
3. Convergence sets and limUnder limits are measurable; Y := {all entries converge and the limit matrix lies in G} is measurable.
4. τ := limit matrix on Y and S₀ off Y is measurable.
5. If the averages tend to β(T) for every β, then a_k^{ab}(x) → T_ab, so x ∈ Y and τ(x) = T.

## Reference use

### local-project

Queries:
- `cat manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `rg -n 'def HasTangentPlane|def rescaledMeasure|def planeVarifoldMeasure|def unitBallVolume' project/GMT/Ch08/Contract.lean`
- `rg -n 'theorem ext_of_forall_lintegral_eq_of_IsFiniteMeasure|instance .*HasOuterApproxClosed' mathlib/Mathlib`
- `rg -n 'protected theorem limUnder|theorem measurableSet_exists_tendsto' mathlib/Mathlib/MeasureTheory/Constructions/Polish/StronglyMeasurable.lean`
- `rg -n 'theorem measurable_of_tendsto_metrizable|theorem measurable_limit_of_tendsto_metrizable_ae' mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Metrizable.lean`
- `rg -n 'theorem ext_of_generateFrom_of_iUnion' mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `rg -n 'theorem measurable_measure_prodMk_left ' mathlib/Mathlib/MeasureTheory`
- `rg -n "integral_prod_right' " mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `rg -n 'theorem addHaar_closedBall ' mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `rg -n 'euclideanHausdorffMeasure_eq_volume|theorem Isometry.euclideanHausdorffMeasure_image|map_euclideanHausdorffMeasure' mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n 'theorem setLIntegral_congr_fun_ae|theorem ofReal_integral_eq_lintegral_ofReal|theorem ext_of_generate_finite|theorem borel_eq_generateFrom_isClosed|theorem tendsto_lintegral_of_dominated_convergence ' mathlib/Mathlib`
- `rg -n 'theorem iUnion_spanningSets|theorem measure_spanningSets_lt_top' mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `rg -n 'theorem volume_closedBall' mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`
- `rg -l -i 'varifold' mathlib/Mathlib | wc -l (0 files)`
- `grep -n 'structure Varifold|instance measure.instSigmaFinite|instance weight.instSigmaFinite|theorem weight_apply|abbrev Grassmannian|instCompactSpace|isClosed_projectionSet|finrank_plane' .lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `rg -n 'euclideanHausdorffMeasure.*(submodule|Submodule|closedBall)|closedBall.*euclideanHausdorffMeasure' .lake/packages/simongmt/Poincare/SimonGMT (Chapter04/TangentDensity.planeMeasure_unit_closedBall needs 0 < n; Chapter03/Rectifiable regular/support lemmas)`
- `grep -c frt_vgm dag.json (0); git grep -l frt_vgm over every local branch under GMT/ (no match)`
- `lake env lean /tmp/vgm_decomp/Probe.lean (instances on Grassmannian: Borel/PseudoMetrizable/Compact/T2; SigmaFinite weight and measure; HasOuterApproxClosed and ext_of_forall_lintegral_eq_of_IsFiniteMeasure unknown without an extra import)`
- `lake env lean /tmp/vgm_decomp/Split.lean (three child stubs + parent frozen type proved with no sorry + comparator NodeSolution emulation; #print axioms)`
- `python3 -I validate.py: verifier/lean_contract.py validate_lean_statement on the three child types (all valid, byte-identical to Split.lean)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/HasOuterApproxClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Constructions/Polish/StronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Metrizable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-varifold-graph-measure-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/vgm_decomp/Split.lean`

The snapshot is project 63436ae6 with Mathlib 25730c7c. Its Contract.lean defines HasTangentPlane, rescaledMeasure, planeVarifoldMeasure and unitBallVolume exactly as the workspace Submission does. Mathlib has no varifold theory (0 files). Every library fact the three children need exists in the pinned Mathlib/SimonGMT. Child 1 uses Isometry.euclideanHausdorffMeasure_image (Volume/Measure.lean:131), EuclideanSpace.euclideanHausdorffMeasure_eq_volume (:187), Measure.addHaar_closedBall (EqHaar.lean:500), integral_smul_measure, integral_map and Grassmannian.finrank_plane. Child 2 uses measurable_measure_prodMk_left (Measure/Prod.lean:97), StronglyMeasurable.integral_prod_right' (Integral/Prod.lean:76), StronglyMeasurable.measurableSet_exists_tendsto and StronglyMeasurable.limUnder (Polish/StronglyMeasurable.lean:35/53), Grassmannian.isClosed_projectionSet, and the SimonGMT instances Varifold.weight.instSigmaFinite and measure.instSigmaFinite. Child 3 uses ext_of_generate_finite (Typeclasses/Finite.lean:458), isPiSystem_isClosed, borel_eq_generateFrom_isClosed (BorelSpace/Basic.lean:87), tendsto_lintegral_of_dominated_convergence (DominatedConvergence.lean:48), generateFrom_prod, spanningSets (SFinite.lean:137/142) and Measure.ext_of_generateFrom_of_iUnion (Restrict.lean:491). The parent assembly uses setLIntegral_congr_fun_ae (Lebesgue/Basic.lean:290) and ofReal_integral_eq_lintegral_ofReal (Bochner/Basic.lean:739). MeasureTheory.ext_of_forall_lintegral_eq_of_IsFiniteMeasure (HasOuterApproxClosed.lean:256) would shortcut child 3 Steps 3–4, but its file is not imported by GMT.Ch08.Submission (unknown identifier in Lean), so child 3 keeps the explicit closed-set argument. SimonGMT's planeMeasure_unit_closedBall (Chapter04/TangentDensity) covers only 0 < n and unit radius, so child 1 uses the uniform-in-n isometry argument instead. In Lean, with the comparator's contract scope after import GMT.Ch08.Submission, the three child types elaborate and pass validate_lean_statement. The parent's exact frozen type is proved from the three sorry'd children with no sorry of its own (axioms: propext, sorryAx from the stubs only, Classical.choice, Quot.sound). The names frt_vgm_* collide with no DAG node or branch.
