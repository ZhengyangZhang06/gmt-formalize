# Parent-supplied natural-language proof

- Parent DAG node: `root.first_rectifiability-a1.varifold_graph_measure-a1`
- Child DAG node: `root.first_rectifiability-a1.varifold_graph_measure-a1.graph_measure_ext-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 6–7 of the parent proof, i.e. the printed passage of Simon, Ch. 8, proof of 1.2 (p. 208): "From the arbitrariness of A and β it then easily follows that (2) ∫ f(x, S) dV(x, S) = ∫_M f(x, T_x) dμ_V(x)", here in measure form with a Borel plane map τ.

Notation: μ := V.weight; G := Grassmannian N n (compact, second countable, metrizable, Borel σ-algebra); g(x) := (x, τ(x)); ν := μ.map g. The hypothesis is: (H) for every Borel A' ⊆ ℝ^N and every β ∈ C(G) with β ≥ 0, ∫⁻_{A'×G} ENNReal.ofReal(β(z.2)) dV(z) = ∫⁻_{A'} ENNReal.ofReal(β(τ(x))) dμ(x).

1. Rectangles under ν. g is measurable (measurable_id.prodMk hτ). For Borel A' ⊆ ℝ^N and Borel B ⊆ G, g⁻¹(A' ×ˢ B) = A' ∩ τ⁻¹(B), so ν(A' ×ˢ B) = μ(A' ∩ τ⁻¹(B)) (Measure.map_apply). Also V(A' ×ˢ univ) = μ(A') (Varifold.weight_apply).

2. Slice measures. Fix a Borel A' ⊆ ℝ^N with μ(A') < ∞ and define Borel measures on G: m₁ := (V.measure.restrict (A' ×ˢ univ)).map Prod.snd and m₂ := (μ.restrict A').map τ. For Borel B, m₁(B) = V((A' ×ˢ univ) ∩ (univ ×ˢ B)) = V(A' ×ˢ B) and m₂(B) = μ(τ⁻¹(B) ∩ A') = μ(A' ∩ τ⁻¹(B)). In particular m₁(univ) = V(A' ×ˢ univ) = μ(A') = m₂(univ) < ∞, so m₁ and m₂ are finite. For β ∈ C(G) with β ≥ 0, by lintegral_map (S ↦ ENNReal.ofReal(β S), Prod.snd and τ are measurable),
 ∫⁻ ENNReal.ofReal(β) dm₁ = ∫⁻_{A'×G} ENNReal.ofReal(β(z.2)) dV and ∫⁻ ENNReal.ofReal(β) dm₂ = ∫⁻_{A'} ENNReal.ofReal(β(τ(x))) dμ,
 and these are equal by (H).

3. Closed sets. Let F ⊆ G be closed. If F = ∅ then m₁(F) = 0 = m₂(F). Otherwise fix a metric d inducing the topology of G, e.g. the Frobenius distance d(S, S') := (Σ_{a,b} (S.1 a b − S'.1 a b)²)^{1/2} (the Euclidean distance of the matrix entries, which induces the subspace topology of G ⊆ Matrix (Fin N) (Fin N) ℝ); let d_F(S) := inf_{S' ∈ F} d(S, S'), a 1-Lipschitz (hence continuous) function with d_F(S) = 0 ⟺ S ∈ F since F is closed. For j ≥ 1 let β_j(S) := max(0, 1 − j · d_F(S)). Then β_j ∈ C(G), 0 ≤ β_j ≤ 1, β_j = 1 on F, and β_j(S) → 1_F(S) for every S (if S ∉ F then d_F(S) > 0 and β_j(S) = 0 as soon as j ≥ 1/d_F(S)). By 2, ∫⁻ ENNReal.ofReal(β_j) dm₁ = ∫⁻ ENNReal.ofReal(β_j) dm₂ for every j. Since ENNReal.ofReal(β_j) ≤ 1, the constant 1 has finite integral for the finite measures m₁, m₂, and ENNReal.ofReal(β_j(S)) → F.indicator 1 S for every S, dominated convergence (tendsto_lintegral_of_dominated_convergence) gives m₁(F) = lim_j ∫⁻ ENNReal.ofReal(β_j) dm₁ = lim_j ∫⁻ ENNReal.ofReal(β_j) dm₂ = m₂(F). (Implementation note: in Lean the metric can be supplied as a local instance, letI := TopologicalSpace.metrizableSpaceMetric (Grassmannian N n) (G is metrizable), with d_F := Metric.infDist · F; or d can be written explicitly as the Frobenius distance above. Steps 3–4 together are also exactly Mathlib's MeasureTheory.ext_of_forall_lintegral_eq_of_IsFiniteMeasure (Mathlib/MeasureTheory/Measure/HasOuterApproxClosed.lean:256; for f : G →ᵇ ℝ≥0 apply 2 to the continuous β := (S ↦ (f S : ℝ)) ≥ 0, for which ENNReal.ofReal(β S) = f S), but that file is not imported by GMT/Ch08/Submission.lean, so using it requires adding the import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed; the self-contained argument above is the primary route.)

4. Borel sets. The closed subsets of G form a π-system (isPiSystem_isClosed) that generates the Borel σ-algebra of G (borel_eq_generateFrom_isClosed; BorelSpace G), and univ is closed, so m₁(univ) = m₂(univ). As m₁ is finite and m₁, m₂ agree on this π-system, m₁ = m₂ (MeasureTheory.ext_of_generate_finite). Hence, by 1 and 2, for every Borel A' ⊆ ℝ^N with μ(A') < ∞ and every Borel B ⊆ G,
 V(A' ×ˢ B) = m₁(B) = m₂(B) = μ(A' ∩ τ⁻¹(B)) = ν(A' ×ˢ B).

5. Extension to all Borel sets. μ is σ-finite (Varifold.weight.instSigmaFinite; concretely ℝ^N = (ℝ^N ∖ U) ∪ ⋃_m K_m, where μ(ℝ^N ∖ U) = V(Uᶜ × G) = 0 by V.supported and μ(K_m) < ∞ by V.finite_on_compact for a compact exhaustion (K_m) of the open set U). Let E_m := spanningSets μ m; these are Borel, μ(E_m) < ∞ (measure_spanningSets_lt_top) and ⋃_m E_m = univ (iUnion_spanningSets). Let 𝓒 := {A' ×ˢ B : A' ⊆ ℝ^N Borel with μ(A') < ∞, B ⊆ G Borel}.
 (a) 𝓒 is a π-system: (A' ×ˢ B) ∩ (A'' ×ˢ B'') = (A' ∩ A'') ×ˢ (B ∩ B'') and μ(A' ∩ A'') ≤ μ(A') < ∞.
 (b) 𝓒 generates the σ-algebra of ℝ^N × G: each member of 𝓒 is a measurable rectangle; conversely each measurable rectangle A' ×ˢ B equals ⋃_m ((A' ∩ E_m) ×ˢ B), a countable union of members of 𝓒 (μ(A' ∩ E_m) ≤ μ(E_m) < ∞), so it is measurable for generateFrom 𝓒; since the measurable rectangles generate the product σ-algebra (generateFrom_prod), generateFrom 𝓒 is the product σ-algebra.
 (c) The sets E_m ×ˢ univ belong to 𝓒, their union is univ, and V(E_m ×ˢ univ) = μ(E_m) < ∞.
 (d) V.measure and ν agree on 𝓒 by 4.
 By Measure.ext_of_generateFrom_of_iUnion (Mathlib/MeasureTheory/Measure/Restrict.lean:491), V.measure = ν = V.weight.map (x ↦ (x, τ(x))). ∎

## Key steps

1. ν := μ_V.map(x ↦ (x, τ x)) satisfies ν(A'×B) = μ_V(A' ∩ τ⁻¹B), and V(A'×G) = μ_V(A').
2. For μ_V(A') < ∞ the finite slice measures m₁(B) = V(A'×B) and m₂(B) = μ_V(A' ∩ τ⁻¹B) have equal lintegrals of every continuous β ≥ 0 (hypothesis + lintegral_map).
3. Closed F: β_j = max(0, 1 − j·d_F) ↓ 1_F and dominated convergence give m₁(F) = m₂(F); π-system of closed sets gives m₁ = m₂, i.e. V(A'×B) = ν(A'×B).
4. Rectangles with finite-μ_V base form a generating π-system covered by spanningSets × G of finite measure (σ-finiteness of μ_V).
5. Measure.ext_of_generateFrom_of_iUnion: V = μ_V.map(x ↦ (x, τ x)).

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
