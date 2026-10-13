# Parent-supplied natural-language proof

- Parent DAG node: `root.density_semicontinuity-a1`
- Child DAG node: `root.density_semicontinuity-a1.weight_portmanteau-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 2 of the parent proof (portmanteau facts (P1), (P2): “approximate 1_O from below and 1_K from above by functions in C_c(U)”), with the details filled in. Regularity is replaced by continuity of measures along monotone sequences of sets, which needs no extra hypothesis.

0. Facts used. U is open (V.isOpen_domain). ℝ^N = Euclidean N is a proper, second countable metric space. G(N,n) = Grassmannian N n is compact. Every weight X.weight is a Borel measure with X.weight(K) < ∞ for every compact K ⊆ U (Varifold.weight_finite_on_compact), and X.weight = X.measure.map Prod.fst.

1. (T) Convergence against C_c(U). Let g : ℝ^N → ℝ be continuous with compact support and tsupport g ⊆ U. Then ∫ g dμ_i → ∫ g dμ.
 Proof. On the open product G_n(U) = U ×ˢ univ (a subtype of ℝ^N × G(N,n)) define F(z) := g(z.1.1). F is continuous. The set tsupport g × G(N,n) is compact and contained in U × G(N,n), which is the range of the subtype inclusion; the inclusion is an embedding, so the preimage of this set is compact (IsInducing.isCompact_preimage'). F vanishes outside that preimage, so F has compact support (HasCompactSupport.intro); thus F ∈ C_c(G_n(U), ℝ). For any varifold X on U:
 ∫ F dX.domainMeasure = ∫ g(z.1) dX.measure, because X.domainMeasure.map Subtype.val = X.measure (Varifold.map_domainMeasure) and integration along the measurable embedding Subtype.val is MeasurableEmbedding.integral_map;
 ∫ g(z.1) dX.measure = ∫ g d(X.measure.map Prod.fst) = ∫ g dX.weight (integral_map; Prod.fst is measurable and g is continuous).
 Applying the definition of RadonConverges to F gives (T).

2. Lintegral form. Such a g is integrable for every weight X.weight: g is bounded on the compact set tsupport g, it vanishes outside that set, and X.weight(tsupport g) < ∞ because tsupport g is compact and ⊆ U. If moreover g ≥ 0, then ofReal(∫ g dX.weight) = ∫⁻ ofReal(g) dX.weight (ofReal_integral_eq_lintegral_ofReal). Composing (T) with the continuous map ENNReal.ofReal gives (T⁺): ∫⁻ ofReal(g) dμ_i → ∫⁻ ofReal(g) dμ for every nonnegative g as in step 1.

3. Urysohn functions. If K is compact, O is open and K ⊆ O ⊆ U, there is a continuous g : ℝ^N → [0,1] with compact support, tsupport g ⊆ O, and g = 1 on K. To build it, take a compact L with K ⊆ interior L ⊆ L ⊆ O (exists_compact_between). Apply exists_continuous_one_zero_of_isCompact to K and the closed set (interior L)ᶜ: this gives g with g = 1 on K, g = 0 off interior L, g ∈ [0,1], and g compactly supported. Since support g ⊆ interior L ⊆ L and L is closed, tsupport g ⊆ L ⊆ O. Consequently 1_K ≤ ofReal ∘ g ≤ 1_O pointwise.

4. Proof of (P1). Let O ⊆ U be open. Write O = ⋃_m F_m with F_m closed, F_m ⊆ O and (F_m) increasing (IsOpen.exists_iUnion_isClosed). Put K_m := F_m ∩ closedBall(0, m). Each K_m is compact (a closed subset of a closed ball in a proper space). The sequence (K_m) is increasing, and ⋃_m K_m = O: a point x ∈ O lies in some F_a and in closedBall(0, b) for any natural b ≥ ‖x‖, hence in K_max(a,b). By continuity from below (Monotone.measure_iUnion), μ(O) = sup_m μ(K_m). Fix m and let g be the function of step 3 for K_m ⊆ O. Then
 μ(K_m) = ∫⁻ 1_{K_m} dμ ≤ ∫⁻ ofReal(g) dμ = lim_i ∫⁻ ofReal(g) dμ_i (by (T⁺)) = liminf_i ∫⁻ ofReal(g) dμ_i ≤ liminf_i ∫⁻ 1_O dμ_i = liminf_i μ_i(O).
 Taking the supremum over m gives μ(O) ≤ liminf_i μ_i(O).

5. Proof of (P2). Let K ⊆ U be compact. Choose δ > 0 with cthickening(δ, K) ⊆ U (IsCompact.exists_cthickening_subset_open). For m ∈ ℕ let O_m := thickening(δ/(m+1), K). Then:
 - each O_m is open and K ⊆ O_m (self_subset_thickening);
 - (O_m) is decreasing, and O_m ⊆ cthickening(δ, K) ⊆ U;
 - ⋂_m O_m = K: if x ∈ O_m for all m, then for every ε > 0 pick m with δ/(m+1) < ε, so x ∈ thickening(ε, K); hence x ∈ ⋂_{ε>0} thickening(ε, K) = closure K = K (closure_eq_iInter_thickening; K is closed);
 - μ(O_0) ≤ μ(cthickening(δ, K)) < ∞, since cthickening(δ, K) is compact (IsCompact.cthickening) and ⊆ U.
 By continuity from above (tendsto_measure_iInter_atTop), μ(O_m) → μ(K). Fix m and let g be the function of step 3 for K ⊆ O_m. Then μ_i(K) ≤ ∫⁻ ofReal(g) dμ_i for all i, so
 limsup_i μ_i(K) ≤ limsup_i ∫⁻ ofReal(g) dμ_i = ∫⁻ ofReal(g) dμ (by (T⁺)) ≤ ∫⁻ 1_{O_m} dμ = μ(O_m).
 This holds for every m and μ(O_m) → μ(K), so limsup_i μ_i(K) ≤ μ(K) (ge_of_tendsto'). ∎

## Key steps

1. (T): for g ∈ C_c(ℝ^N) with tsupport g ⊆ U, F(x,S) = g(x) lies in C_c(G_n(U)) (G(N,n) is compact), and ∫F dV_i.domainMeasure = ∫g dμ_i, so ∫g dμ_i → ∫g dμ.
2. Integrability on compact subsets of U turns (T) into convergence of ∫⁻ ofReal g.
3. Urysohn functions with 1_K ≤ g ≤ 1_O and tsupport g ⊆ O ⊆ U.
4. (P1): exhaust O by compacts K_m; μ(K_m) ≤ ∫g_m dμ = lim ∫g_m dμ_i ≤ liminf μ_i(O); then continuity from below.
5. (P2): shrink O_m = thickening(δ/(m+1), K) ↓ K; limsup μ_i(K) ≤ ∫g_m dμ ≤ μ(O_m); then continuity from above.

## Reference use

### local-project

Queries:
- `cat local-references/5a882a57db723346/manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum GMT/Ch08/Contract.lean GMT/Ch08/Submission.lean local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean (all 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487)`
- `cat simongmt Poincare/SimonGMT/Chapter08/VarifoldConvergence.lean; grep -n '^theorem\|^def' Chapter08/{Varifold,FirstVariationRiesz,BallVariationBound,StationaryMonotonicity,FirstVariationDensity,FirstVariationBounds}.lean`
- `grep -rn -i 'portmanteau\|le_liminf\|limsup_le\|liminf_le' simongmt/Poincare --include=*.lean; grep -rln RadonConverges simongmt/Poincare`
- `grep -n 'theorem exist_disjoint_covering_families' -A 12 and 'structure BallPackage' mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `grep -rn 'countable_of_nonempty_interior\|countable_of_isOpen' mathlib/Mathlib/Topology/`
- `grep -n 'theorem exists_continuous_one_zero_of_isCompact\|theorem exists_compact_between' mathlib/Mathlib/Topology/UrysohnsLemma.lean mathlib/Mathlib/Topology/Compactness/LocallyCompact.lean`
- `lake env lean Scratch/Api.lean Api2.lean Api3.lean (#check: HasBesicovitchCovering (Euclidean N), CompactSpace (Grassmannian N n), IsCompact.exists_cthickening_subset_open, IsCompact.cthickening, IsOpen.exists_iUnion_isClosed, TopologicalSpace.isOpen_iUnion_countable, closure_thickening_subset_cthickening, ball_subset_thickening, cthickening_closure, ENNReal.liminf_add_of_right_tendsto_zero, Monotone.map_liminf_of_continuousAt, ofReal_integral_eq_lintegral_ofReal, Filter.limsup_comp, limsup_le_limsup_of_le, ENNReal.inv_mul_cancel_left, measure_biUnion_null_iff; ENNReal.liminf_const_mul and ENNReal.mul_liminf: unknown constants)`
- `python3 -I gen.py: gmt-compare.contract_scope replay + lean_contract.validate_lean_statement on the 6 lean_statements; lake env lean Cmp/Challenge0..5.lean`
- `lake env lean Scratch/Small.lean, Scratch/C2.lean, Scratch/C3.lean, Scratch/C5.lean, Scratch/C6.lean, Scratch/All.lean (exact frozen statements with complete proofs + parent assembly + #print axioms)`
- `python3 dag.json lean_name collision check (15 nodes); grep -l -i portmanteau nodes/*/parent-supplied-natural-proof.md`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/UrysohnsLemma.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Compactness/LocallyCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/VarifoldConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/FirstVariationRiesz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/BallVariationBound.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/FirstVariationDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-density-semicontinuity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`

Snapshot: project 63436ae6 + Mathlib 25730c7c. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean. SimonGMT Chapter08/VarifoldConvergence.lean already proves RadonConverges.firstVariation_tendsto, firstVariationNormOn_le_liminf, hasLocallyBoundedFirstVariation and firstVariationRieszMeasure_le_liminf. FirstVariationRiesz.lean:218 firstVariationRieszMeasure_eq_norm identifies variationMeasure with firstVariationNormOn on W ⊂⊂ U. Remark 3.8(1) (child variation_lsc) therefore needs no sibling. The VarifoldConvergence module states that it does not prove the lower-density part. SimonGMT has no portmanteau for varifold weights: the only *_le_liminf lemmas are for first variation, BV and currents (Chapter06/Mass.lean WeaklyConvergesOn.massOn_le_liminf), hence the child weight_portmanteau. Mathlib supplies the needed tools: Besicovitch covering families (Covering/Besicovitch.lean:455 exist_disjoint_covering_families, whose BallPackage needs only bounded radii; HasBesicovitchCovering is inferred for Euclidean N); countability of disjoint balls (Topology/Bases.lean:493); Urysohn (UrysohnsLemma.lean:404, LocallyCompact.lean:172); and the thickening and ℝ≥0∞ liminf lemmas. ENNReal.liminf_const_mul does not exist, so the proofs use Monotone.map_liminf_of_continuousAt. All 6 child lean_statements pass validate_lean_statement and elaborate in the replayed contract scope. In a scratch copy, complete proofs of all 6 exact statements compile with axioms propext, Classical.choice and Quot.sound only, and the parent assembly via Submission.monotonicity_and_density_theorems checks against DensitySemicontinuity. dag.json has no lean_name collisions.
