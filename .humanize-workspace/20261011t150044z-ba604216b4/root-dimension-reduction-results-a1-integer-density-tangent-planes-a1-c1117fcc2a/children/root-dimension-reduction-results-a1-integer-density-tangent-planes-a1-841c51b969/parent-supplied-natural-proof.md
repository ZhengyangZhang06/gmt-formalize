# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.polygonal_current-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.polygonal_current-a1.imrep_construction-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent steps 2 (“Carrier, multiplicity, orientation”) and 3 (“R := (M, θ, ξ) is an IMRep univ 1”). Uses the ancestor dependency idtp_fons_odc_line_hausdorff (the parent's dependency line_param) and the sibling children idtp_fons_odc_pc_piece_locally_line and idtp_fons_odc_pc_local_plane_tangent.
Notation: H¹ := μHE[1] and ℒ¹ := volume on ℝ. For v ∈ ℝ^P, ev_v ∈ MultiVector P 1 is ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (fun _ : Fin 1 => v), i.e. ev_v(α) = α(fun _ => v) =: α[v].
0. (Tools.)
 (i) idtp_fons_odc_line_hausdorff, second conjunct, applied to p_k, v_k with ‖v_k‖ = 1: γ_k is a measurable embedding ℝ → ℝ^P, and for every J ⊆ ℝ, H¹⌞γ_k(J) = (γ_k)_#(ℒ¹⌞J) and H¹(γ_k(J)) = ℒ¹(J). Consequently, for every A ⊆ ℝ^P, H¹(S_k ∩ A) = H¹(γ_k(I_k ∩ γ_k⁻¹A)) = ℒ¹(I_k ∩ γ_k⁻¹A) (image_inter_preimage).
 (ii) γ_k is an isometry: dist(γ_k s, γ_k t) = |s − t|·‖v_k‖ = |s − t|. So γ_k is 1-Lipschitz and a closed embedding, and γ_k⁻¹(K) is compact for compact K.
 (iii) idtp_fons_odc_pc_piece_locally_line: assume ι finite, ‖v_k‖ = 1, I_k open, M ⊆ ⋃_j S_j, S_k ⊆ M, x ∈ S_k and x ∉ closure(S_j) for all j ≠ k. Then there is r > 0 with M ∩ B_r(x) = {y : y − x ∈ span{v_k}} ∩ B_r(x).
 (iv) idtp_fons_odc_pc_local_plane_tangent: if M is measurable, finrank Q = n, r > 0 and M ∩ B_r(x) = {y : y − x ∈ Q} ∩ B_r(x), then HasApproximateTangentSpaceAt n M x Q.
1. (Pieces and carrier.) Each S_k is measurable, being the image of the open (hence measurable) set I_k under the measurable embedding γ_k (Tool (i)). Let M := ⋃_k ⋃_{c_k ≠ 0} S_k. Then M is measurable, x ∈ M iff ∃ k, c_k ≠ 0 ∧ x ∈ S_k, S_k ⊆ M whenever c_k ≠ 0, and M ⊆ ⋃_j S_j.
2. (Multiplicity.) Let θ(x) := Σ_k 1_{S_k}(x)·|c_k| ∈ ℕ, where 1_{S_k}(x)·|c_k| is the indicator of S_k of the constant natAbs c_k. θ is measurable, as a finite sum of indicators of constants on measurable sets. For every B ⊆ ℝ^P, ∫⁻_B θ dH¹ = Σ_k |c_k|·H¹(S_k ∩ B). Indeed, the cast to ℝ≥0∞ commutes with the finite sum and with the indicators (Nat.cast_sum; case split on x ∈ S_k). The lintegral of a finite sum of measurable functions is the sum of the lintegrals (lintegral_finsetSum). Finally ∫⁻_B 1_{S_k}·|c_k| dH¹ = |c_k|·(H¹⌞B)(S_k) = |c_k|·H¹(S_k ∩ B) (lintegral_indicator_const, Measure.restrict_apply with S_k measurable).
3. (Orientation field.) Define ξ(x) := Σ_k (1_{S_k}(x)·c_k / θ(x))•ev_{v_k} ∈ MultiVector P 1. The coefficient uses the real indicator of the constant (c_k : ℝ) and real division, with r/0 = 0. Each coefficient x ↦ 1_{S_k}(x)c_k/θ(x) is a measurable real function: the measurable indicator divided by the measurable function x ↦ (θ(x) : ℝ). So each summand coefficient•ev_{v_k} is strongly measurable (StronglyMeasurable.smul_const), and the finite sum ξ is strongly measurable (Finset.stronglyMeasurable_fun_sum). If instance search does not find ContinuousAdd on MultiVector P 1, supply it as IsTopologicalAddGroup.toContinuousAdd.
4. (θ·ξ identity.) For all x and α: θ(x)·ξ(x)(α) = Σ_k 1_{S_k}(x)·c_k·α[v_k]. Evaluating the finite sum of scalar multiples of ev's gives ξ(x)(α) = Σ_k (1_{S_k}(x)c_k/θ(x))·α[v_k].
 - If θ(x) = 0: θ(x) is a sum of natural numbers, so every term 1_{S_k}(x)·|c_k| vanishes. Hence for each k either x ∉ S_k or c_k = 0, so every 1_{S_k}(x)·c_k = 0 and both sides are 0.
 - If θ(x) ≠ 0: distribute θ(x) over the sum and cancel θ(x)/θ(x) = 1 in each term.
5. (R := (M, θ, ξ) is an IMRep univ 1.) We verify the fields.
 a. measurableSet_carrier: step 1. carrier_subset: M ⊆ univ.
 b. rectifiable: let π := EuclideanSpace.proj 0 : Euclid 1 → ℝ, which is continuous linear, hence Lipschitz. Then γ_k ∘ π is Lipschitz (Tool (ii)), and S_k ⊆ range(γ_k ∘ π) because γ_k(t) = (γ_k ∘ π)(EuclideanSpace.single 0 t). By countablyRectifiable_range and CountablyRectifiable.mono, each S_k is countably 1-rectifiable. The family range S = {S_k : k ∈ ι} is countable since ι is finite, so ⋃₀ range S is countably 1-rectifiable (countablyRectifiable_sUnion). Each x ∈ M lies in some S_k, so M ⊆ ⋃₀ range S, and M is countably 1-rectifiable by mono.
 c. measurable_mult: step 2.
 d. mult_pos: if x ∈ M, pick k with c_k ≠ 0 and x ∈ S_k. Then θ(x) ≥ 1_{S_k}(x)|c_k| = |c_k| ≥ 1, since a single term of a sum of naturals is at most the sum (Finset.single_le_sum; Int.natAbs_pos).
 e. locallyIntegrable_mult: let K be compact. Step 2 with B = M ∩ K gives ∫⁻_{M∩K} θ dH¹ = Σ_k |c_k|·H¹(S_k ∩ (M ∩ K)). By Tool (i) and the compactness of γ_k⁻¹K (Tool (ii)), H¹(S_k ∩ (M ∩ K)) ≤ H¹(S_k ∩ K) = ℒ¹(I_k ∩ γ_k⁻¹K) ≤ ℒ¹(γ_k⁻¹K) < ∞. A finite sum of natural numbers times finite quantities is finite, so the integral is ≠ ∞.
 f. aestronglyMeasurable_orient: by step 3, since strongly measurable implies a.e. strongly measurable for H¹⌞M.
 g. orients: let B := ⋃_j ⋃_k ⋃_{j ≠ k} (S_j ∩ closure(S_k)). Each term is H¹-null by hypothesis, so H¹(B) = 0 (measure_iUnion_null). Hence H¹-a.e. x ∉ B (measure_eq_zero_iff_ae_notMem), so also (H¹⌞M)-a.e. (ae_restrict_of_ae); moreover (H¹⌞M)-a.e. x ∈ M (ae_restrict_mem).
  Fix x ∈ M ∖ B and choose k with c_k ≠ 0 and x ∈ S_k. For every j ≠ k, x ∉ closure(S_j): otherwise x ∈ S_k ∩ closure(S_j), which is a term of B since k ≠ j. In particular x ∉ S_j (subset_closure). Hence only the k-th term survives in the sums defining θ(x) and ξ(x) (Finset.sum_eq_single). So θ(x) = |c_k| and ξ(x) = (c_k/|c_k|)•ev_{v_k}, using (natAbs c_k : ℝ) = |(c_k : ℝ)| (Nat.cast_natAbs, Int.cast_abs).
  Tangent line: apply Tool (iii) with this k and x. Its hypotheses are ‖v_k‖ = 1, I_k open, M ⊆ ⋃_j S_j and S_k ⊆ M (step 1), x ∈ S_k, and x ∉ closure(S_j) for j ≠ k. This gives r > 0 with M ∩ B_r(x) = {y : y − x ∈ span{v_k}} ∩ B_r(x). Since ‖v_k‖ = 1, v_k ≠ 0 and finrank span{v_k} = 1 (finrank_span_singleton). Tool (iv) with n = 1, Q = span{v_k} and the measurable M then yields HasApproximateTangentSpaceAt 1 M x (span{v_k}).
  Unit orientation: τ := (fun _ : Fin 1 => v_k) is orthonormal, because ‖τ i‖ = ‖v_k‖ = 1 and the orthogonality condition for i ≠ j is vacuous on Fin 1. Also span(range τ) = span{v_k} (range_const). For every α, ξ(x)(α) = (c_k/|c_k|)·α(τ), which is α(τ) if c_k > 0 and −α(τ) if c_k < 0 (recall c_k ≠ 0). Hence IsUnitOrientationOf (ξ x) (span{v_k}), and Q := span{v_k} witnesses the orients condition at x. So orients holds (H¹⌞M)-a.e.
6. (Conclusions.) For this R, R.carrier = M = ⋃_k ⋃_{c_k ≠ 0} γ_k(I_k) and R.mult x = θ(x) = Σ_k 1_{γ_k(I_k)}(x)·|c_k| hold by construction, after unfolding S_k = γ_k(I_k). The identity R.mult x·R.orient x α = θ(x)·ξ(x)(α) = Σ_k 1_{γ_k(I_k)}(x)·c_k·α(fun _ => v_k) is step 4. ∎
Formalization note: it is convenient to introduce S, M, θ, ξ as names with defining equations, e.g. obtain ⟨S, hSdef⟩ : ∃ S : ι → Set (Euclid P), ∀ k, S k = (fun t : ℝ => p k + t • v k) '' I k := ⟨_, fun _ => rfl⟩. Then build the record with let R : IMRep (univ : Set (Euclid P)) 1 := { carrier := M, mult := θ, orient := ξ, … }, and rewrite with the defining equations at the end.

## Key steps

1. S_k is Borel (line_param measurable embedding) and M = ⋃_{c_k≠0} S_k is Borel. θ = Σ 1_{S_k}|c_k| is measurable, with ∫⁻_B θ dH¹ = Σ |c_k| H¹(S_k ∩ B).
2. ξ = Σ (1_{S_k}c_k/θ) ev_{v_k} is strongly measurable, and θ(x)ξ(x)(α) = Σ 1_{S_k}(x) c_k α(v_k) everywhere.
3. Rectifiability comes from the Lipschitz parametrizations γ_k ∘ proj; local integrability comes from line_param and the compactness of γ_k⁻¹K.
4. Off the H¹-null overlap set B, θ(x) = |c_k| and ξ(x) = (c_k/|c_k|) ev_{v_k}; piece_locally_line and local_plane_tangent give the approximate tangent line span{v_k}, which ξ(x) orients.

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; cmp <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD`
- `rg -n "theorem tendsto_integral_filter_of_dominated_convergence|theorem Isometry.euclideanHausdorffMeasure_image|theorem Isometry.map_euclideanHausdorffMeasure|theorem lintegral_indicator_const|theorem integral_finsetSum|theorem lintegral_finsetSum|theorem finrank_span_singleton|theorem eventually_all |theorem integral_indicator |theorem image_inter_preimage|theorem withDensity_apply " <snapshot>/mathlib/Mathlib`
- `rg -n "theorem _root_.MeasurableEmbedding.integral_map|_root_.MeasurableEmbedding.integrable_map_iff|theorem eventually_nhds_iff |theorem le_opNorm" <snapshot>/mathlib/Mathlib`
- `rg -n "HasApproximateTangentSpaceAt|blowUpMap" <snapshot>/mathlib/Mathlib (no match)`
- `rg -n "HasApproximateTangentSpaceAt|idtp_fons_odc|polygonal" <snapshot>/project/GMT`
- `grep -rn HasApproximateTangentSpaceAt (theorem|lemma) .lake/packages/simongmt/Poincare/SimonGMT; sed -n 50,260p Chapter03/Rectifiable.lean; sed -n 1,200p Chapter06/Currents.lean; grep Covector|DifferentialForm|IsTestForm Chapter06/Forms.lean`
- `git show 75f499358:GMT/Ch07/Submission.lean > /tmp/pc_split/draft.lean (speculative draft of the grandparent): odc_line_*, odc_polycurrent_*, odc_tangent_*, odc_approxTangent_of_locally_line, odc_polyimrep_*, odc_polygonal_imrep`
- `python3 -I scans of dag.json: nodes under the selected parent, sibling line_param-a1 frozen type, all idtp_fons_odc* lean_names, occurrences of the five proposed names, accepted statements with HasApproximateTangentSpaceAt and ball, accepted line-integral currents`
- `grep -n max_depth runtime.py (_decompose line 1393); sed -n 60,200p leaf_verification.py (check_source_delta forbidden regex); sed -n 1,140p inherited.py (cited_inherited)`
- `grep -n "1.4 Definition|3.1 Definition|1-dimensional minimizing" book/chapter-03.txt book/chapter-06.txt book/chapter-07.txt`
- `lake env lean /tmp/pc_split/{Types,Alpha,Beta,Eps,Gamma,Delta,All,AllClean}.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Image.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-c1117fcc2a/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/inherited.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/pc_split/draft.lean`
- `/tmp/pc_split/Types.lean`
- `/tmp/pc_split/Alpha.lean`
- `/tmp/pc_split/Beta.lean`
- `/tmp/pc_split/Eps.lean`
- `/tmp/pc_split/Gamma.lean`
- `/tmp/pc_split/Delta.lean`
- `/tmp/pc_split/All.lean`
- `/tmp/pc_split/AllClean.lean`

Pins match. The snapshot manifest records project b4d606db and Mathlib 25730c7c, which equal the workspace HEAD and .lake/packages/mathlib; SimonGMT is 2b366308. The snapshot Contract.lean is byte-identical to the workspace Submission.lean. Every Mathlib lemma used by the child proofs exists in the snapshot: tendsto_integral_filter_of_dominated_convergence (MeasureTheory/Integral/DominatedConvergence.lean:67), Isometry.euclideanHausdorffMeasure_image and map_euclideanHausdorffMeasure (Geometry/Euclidean/Volume/Measure.lean:131 and :141), MeasurableEmbedding.integral_map (Integral/Bochner/Basic.lean:1093), MeasurableEmbedding.integrable_map_iff (Function/L1Space/Integrable.lean:374), integral_finsetSum (Bochner/Basic.lean:248), integral_indicator (Bochner/Set.lean:185), lintegral_finsetSum (Lebesgue/Add.lean:356), lintegral_indicator_const (Lebesgue/Basic.lean:541), withDensity_apply (Measure/WithDensity.lean:44), finrank_span_singleton (LinearAlgebra/FiniteDimensional/Basic.lean:535), Filter.eventually_all (Order/Filter/Finite.lean:247), Metric.eventually_nhds_iff (Topology/MetricSpace/Pseudo/Defs.lean:779), ContinuousAlternatingMap.le_opNorm (Analysis/Normed/Module/Alternating/Basic.lean:212) and image_inter_preimage (Data/Set/Image.lean:454). The snapshot Mathlib has no HasApproximateTangentSpaceAt or blowUpMap (no match). SimonGMT Chapter03/Rectifiable.lean supplies blowUpMap (:96), HasApproximateTangentSpaceAt (:102), countablyRectifiable_range (:64), countablyRectifiable_sUnion (:416), and only the flat-model lemma hasApproximateTangentSpaceAt_submodule (:125), which covers points of a linear subspace with no locality; Chapter06/Currents.lean defines TestFormOnConverges and GeometricCurrentOn. The snapshot project GMT has no idtp_fons_odc or polygonal declaration. The DAG has no node with any of the five proposed lean_names, and no accepted statement equals any child type. The accepted codim1_ac_sat_approxTangent_of_local_eq proves locality but not the affine model, so it is not reused. The sibling line_param (idtp_fons_odc_line_hausdorff, frozen type read from dag.json) is the only external prerequisite and is cited by name in two children. Lean: all child types elaborate and the frozen parent type follows from three of them. Each child has a verified one-theorem proof that respects the leaf delta regex; the proofs are adapted from draft 75f499358. With a one-theorem proof of the line_param type, the whole chain uses only propext, Classical.choice and Quot.sound.
