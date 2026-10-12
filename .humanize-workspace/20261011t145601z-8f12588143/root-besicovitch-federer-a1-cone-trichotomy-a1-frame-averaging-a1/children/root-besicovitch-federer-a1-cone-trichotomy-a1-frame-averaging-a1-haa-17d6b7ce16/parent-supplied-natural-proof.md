# Parent-supplied natural-language proof

- Parent DAG node: `root.besicovitch_federer-a1.cone_trichotomy-a1.frame_averaging-a1`
- Child DAG node: `root.besicovitch_federer-a1.cone_trichotomy-a1.frame_averaging-a1.haar_stabilizer-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 1 of the parent-supplied proof of bf_frameAveraging_null (its supplied Step 0.2; Mattila, Geometry of Sets and Measures in Euclidean Spaces, Ch. 3; Dall'Alba, Ch. 5). Here the parent's two groups are treated as one family. U = {0} gives O(N) with θ_N, and U = (H⁰)^⊥ = span{e_{n+2}, …, e_N} gives the stabilizer G′ with θ′. The measure is built on the compact group and pushed into 𝓛.

Notation (as in the parent proof): E := ℝᴺ = EuclideanSpace ℝ (Fin N); x·y is the inner product and |·| the norm; 𝓛 := E →L[ℝ] E with the Borel σ-algebra of its operator-norm topology; gk is composition and 1 the identity; g* := ContinuousLinearMap.adjoint g; P_W := W.starProjection; gW := W.map g; Hⁿ := μHE[n].

1. Orthogonal maps. Let g ∈ 𝓛 with g*g = 1.
   - For x, y ∈ E, gx·gy = x·g*gy = x·y. In particular |gx| = |x|, so g is injective and ‖g‖ ≤ 1.
   - E is finite-dimensional, so the injective linear map g is surjective (LinearMap.surjective_of_injective).
   - Every y ∈ E is y = gx, so g(g*y) = g(g*gx) = gx = y. Hence gg* = 1 and g* is the two-sided inverse of g.
   - (g*)*g* = gg* = 1, so g* is orthogonal as well.
2. K := K_U is a group under composition.
   - 1 ∈ K.
   - If a, b ∈ K, then (ab)*(ab) = b*(a*a)b = b*b = 1 and abx = a(bx) = ax = x for x ∈ U. So ab ∈ K.
   - If a ∈ K, then a* ∈ K: (a*)*a* = aa* = 1 by step 1, and a*x = a*(ax) = x for x ∈ U. Also a*a = aa* = 1.
   - So K is a group with inverse a ↦ a*. Associativity is that of composition.
3. Topology.
   - The adjoint map g ↦ g* is a linear isometry of 𝓛 (ContinuousLinearMap.adjoint is a LinearIsometryEquiv), hence continuous.
   - Composition (g, h) ↦ gh is continuous on 𝓛 × 𝓛, since 𝓛 is a normed ring. Each evaluation g ↦ gx is continuous.
   - Hence K = {g : g*g = 1} ∩ ⋂_{x∈U} {g : gx = x} is closed in 𝓛.
   - K is bounded (‖g‖ ≤ 1 by step 1). 𝓛 is finite-dimensional, hence a proper metric space, so K is compact (Metric.isCompact_of_isClosed_isBounded).
   - On the subtype K (subspace topology, group law of step 2), multiplication and inversion are restrictions of the continuous maps above.
   - So K is a compact, Hausdorff, second-countable topological group.
   - Give K the subtype σ-algebra. It is the Borel σ-algebra of K (Subtype.borelSpace), and the inclusion ι : K → 𝓛 is continuous, hence measurable.
   Lean hint (this route was checked in Lean during review): realize K as a Subgroup of unitary 𝓛 with carrier {u : ∀ x ∈ U, (u : 𝓛) x = x}.
   - `IsTopologicalGroup (unitary R)` needs `[ContinuousStar R]` and lives in Mathlib.Topology.Algebra.Star.Unitary, which must be imported.
   - For 𝓛, `ContinuousStar` is not inferred. Supply it by rewriting `(star : 𝓛 → 𝓛) = fun g ↦ ContinuousLinearMap.adjoint g` (funext ContinuousLinearMap.star_eq_adjoint) and using the continuity of the adjoint. A plain `simpa [star_eq_adjoint]` does not close the goal.
   - Membership in unitary 𝓛 is `Unitary.mem_iff` (star g * g = 1 ∧ g * star g = 1); step 1 gives both halves.
   - CompactSpace K: the inclusion ι : K → 𝓛 is inducing (subtypeVal twice), and its range is the closed bounded set above. Use `isCompact_univ_iff`, `Topology.IsInducing.isCompact_iff` and `Metric.isCompact_of_isClosed_isBounded`.
4. Haar probability on K.
   - K is a compact group, so K₀ := K (= univ) is a compact set with nonempty interior, i.e. a positive compact.
   - Let μ := Measure.haarMeasure K₀ (in Lean K₀ = ⊤ : PositiveCompacts K). It is a left-invariant Haar measure with μ(K) = 1 (Measure.haarMeasure_self, PositiveCompacts.coe_top), hence a probability measure.
5. Right invariance of μ. Let k ∈ K, r_k(h) := hk, and ρ := (r_k)_*μ, the image of μ under r_k.
   - r_k is a homeomorphism of K. Hence ρ is a finite Borel measure, finite on compacts, with ρ(K) = μ(r_k⁻¹K) = μ(K) = 1.
   - ρ is left invariant. For k′ ∈ K, left translation by k′ commutes with r_k: k′(hk) = (k′h)k.
   - So the image of ρ under h ↦ k′h equals the image under r_k of the image of μ under h ↦ k′h, which is (r_k)_*μ = ρ.
   - By uniqueness of Haar measure on the compact group K (Measure.isMulInvariant_eq_smul_of_compactSpace), ρ = c·μ for a constant c ≥ 0. Evaluating at K gives c = 1, so ρ = μ.
   - Alternatively: ρ and μ are left-invariant Haar probability measures, so they coincide by Measure.isHaarMeasure_eq_of_isProbabilityMeasure.
6. Transfer to 𝓛. Let θ := ι_*μ.
   - θ(𝓛) = μ(K) = 1, so θ is a probability measure.
   - 𝓛 ∖ K is measurable because K is closed, and θ(𝓛 ∖ K) = μ(ι⁻¹(𝓛 ∖ K)) = μ(∅) = 0.
   - So θ-a.e. g satisfies g*g = 1 and gx = x for all x ∈ U.
7. Invariance of θ. Let k ∈ 𝓛 with k*k = 1 and kx = x for x ∈ U, i.e. k ∈ K, and let k̂ be k as an element of the group K.
   - The maps l_k(g) := kg and r_k(g) := gk on 𝓛 are continuous, hence measurable.
   - They satisfy l_k ∘ ι = ι ∘ (h ↦ k̂h) and r_k ∘ ι = ι ∘ (h ↦ hk̂).
   - By functoriality of image measures (Measure.map_map), (l_k)_*θ = ι_*((h ↦ k̂h)_*μ) = ι_*μ = θ, using left invariance of μ.
   - Likewise (r_k)_*θ = ι_*((h ↦ hk̂)_*μ) = ι_*μ = θ, by step 5.
   These are the two invariance identities, which proves the statement. ∎

## Key steps

1. Each g with g*g = 1 preserves inner products, is bijective and satisfies gg* = 1. So K_U = {g : g*g = 1, g|_U = id} is a group under composition, with inverse g ↦ g*.
2. K_U is closed and bounded in the finite-dimensional 𝓛. It is therefore a compact, second-countable topological group with continuous multiplication and inversion (the adjoint).
3. The Haar measure μ on K_U normalized by μ(K_U) = 1 is a left-invariant probability. Right invariance follows from uniqueness of Haar measure on compact groups, comparing total masses.
4. θ := ι_*μ, for the inclusion ι : K_U → 𝓛, is a probability concentrated on K_U. Translations by k ∈ K_U commute with ι, so θ is left and right K_U-invariant.

## Reference use

### local-project

Queries:
- `cat manifest.json (project d09bc8a18ce60face651f042976e8465f21f0f68, mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `rg -n "def frameProjection|def ForAlmostAllProjections|abbrev Rn" project/GMT/Ch03/Contract.lean`
- `rg -n "instance instMeasurableSpace|instBorelSpace" mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/ContinuousLinearMap.lean`
- `rg -n "isMulInvariant_eq_smul_of_compactSpace|isHaarMeasure_eq_of_isProbabilityMeasure" mathlib/Mathlib/MeasureTheory/Measure/Haar/Unique.lean`
- `rg -n "theorem haarMeasure_self|def haarMeasure " mathlib/Mathlib/MeasureTheory/Measure/Haar/Basic.lean`
- `grep -rn CompactSpace mathlib/Mathlib/MeasureTheory/Measure/Haar/*.lean mathlib/Mathlib/MeasureTheory/Group/*.lean | grep -i 'inv|right|unimod' (no right-invariance instance for compact groups)`
- `rg -n "IsTopologicalGroup \(unitary|isClosed_unitary|instance.*unitary" mathlib/Mathlib/Topology/Algebra/Star/Unitary.lean`
- `rg -n "ext_of_forall_integral_eq_of_IsFiniteMeasure" mathlib/Mathlib/MeasureTheory/Measure/HasOuterApproxClosed.lean`
- `grep -rn "LinearIsometry.extend" mathlib/Mathlib (PiL2.lean:1174 def, 1222 extend_apply)`
- `grep -n "theorem reflection_sub" mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Reflection.lean (namespace Submodule)`
- `grep -n "eq_starProjection_of_mem_of_inner_eq_zero|starProjection_apply_mem|sub_starProjection_mem_orthogonal" mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `rg -n "theorem measurePreserving" mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean; rg -n "theorem measurePreserving_pi " mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `#check Measure.ae_ae_comm, measurable_measure_prodMk_left/right, Measure.prod_apply(_symm), isOpen_setOfPred_linearIndependent, ContinuousOn.measurable_piecewise, Isometry.euclideanHausdorffMeasure_image, Submodule.finrank_add_finrank_orthogonal, Submodule.finrank_sup_add_finrank_inf_eq, Submodule.eq_of_le_of_finrank_eq, integral_integral_swap, integral_map (all resolve after import GMT.Ch03.Submission; ext_of_forall_integral_eq_of_IsFiniteMeasure and isClosed_unitary need the extra imports)`
- `inferInstance probes: ContinuousStar (Rn N →L[ℝ] Rn N) fails (must be supplied locally); SecondCountableTopology, MeasurableMul₂, ProperSpace of 𝓛 and HasOuterApproxClosed (Rn N) succeed`
- `grep bf_orthStabilizer_haar_exists|bf_stabilizerOrbit_null|bf_haar_null_of_cosetFibres_null|bf_starProjection_map_orthogonal|bf_haar_planeDirection_null|bf_haar_excPointwise_null|bf_orthogonal_exists_map_eq|bf_haar_null_to_frames in dag.json, the snapshot project and all worktree Submission.lean files (no match); child keys absent from dag.json`
- `grep -n candidate_inputs verifier/gmt-compare.py (only frozen inputs are byte-checked; Submission.lean may add imports)`
- `grep -n "3.6\|Fed69\|Ros84" book/chapter-03.txt (Thm 3.6 at lines 530-536 defers its proof to [Fed69]/[Ros84])`
- `lake env lean GMT/Scratch/FrameAveragingSplit{Decision,Assembly,Glue,Frames,Leaves,EndToEnd,Closed}.lean (all compile; Closed: e2e_parent uses only propext, Classical.choice, Quot.sound and stand-ins with the exact frozen types of the two parent siblings)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Haar/Unique.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Haar/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Algebra/Star/Unitary.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/HasOuterApproxClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Reflection.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-besicovitch-federer-a1-cone-trichotomy-a1-frame-averaging-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/FrameAveragingSplitDecision.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/FrameAveragingSplitAssembly.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/FrameAveragingSplitGlue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/FrameAveragingSplitFrames.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/FrameAveragingSplitLeaves.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/FrameAveragingSplitHaarStabilizer.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/FrameAveragingSplitOrbitNull.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/FrameAveragingSplitEndToEnd.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/FrameAveragingSplitClosed.lean`

The snapshot fixes Rn, frameProjection and ForAlmostAllProjections (Contract.lean), and the child types use them verbatim. The pinned Mathlib supplies every library ingredient the child proofs cite:
- the Borel structure on E →L[ℝ] E (ContinuousLinearMap.instMeasurableSpace / instBorelSpace);
- the Haar measure, haarMeasure_self, and uniqueness on compact groups (isMulInvariant_eq_smul_of_compactSpace, isHaarMeasure_eq_of_isProbabilityMeasure);
- the unitary topological group (IsTopologicalGroup (unitary R)), which requires a ContinuousStar instance on 𝓛 supplied locally from the continuity of the adjoint;
- ext_of_forall_integral_eq_of_IsFiniteMeasure (requires importing HasOuterApproxClosed);
- Submodule.reflection_sub, LinearIsometry.extend / extend_apply, and the orthogonal-projection characterization eq_starProjection_of_mem_of_inner_eq_zero;
- LinearIsometryEquiv.measurePreserving, measurePreserving_pi, Measure.prod_apply / prod_apply_symm, Measure.ae_ae_comm, measurable_measure_prodMk_left/right, ContinuousOn.measurable_piecewise, isOpen_setOfPred_linearIndependent and Isometry.euclideanHausdorffMeasure_image.
The searches found no right-invariance instance for compact-group Haar measure, no CompactSpace instance for orthogonal groups and no Haar measure on O(N), so those are built in haar_stabilizer. No existing declaration states any of the eight children, and all names and keys are fresh in dag.json, the snapshot and the worktrees. The verifier byte-checks only frozen inputs, so the two extra Mathlib imports needed by the leaves are permitted in Submission.lean. Lean evidence: all child types elaborate in the contract scope. The exact frozen parent type follows from the children plus the two parent siblings. Every child, including the two deep leaves, was proved in scratch, and the closed chain uses only propext, Classical.choice and Quot.sound, besides stand-ins carrying exactly the frozen types of bf_sphereCap_measure_bounds and bf_frameProjection_continuousOn.
