# Parent-supplied natural-language proof

- Parent DAG node: `root.besicovitch_federer-a1.cone_trichotomy-a1.frame_averaging-a1`
- Child DAG node: `root.besicovitch_federer-a1.cone_trichotomy-a1.frame_averaging-a1.haar_to_frames-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 8, 9 and 10 of the parent-supplied proof of bf_frameAveraging_null (its supplied Steps 1.5(b) and 5.1–5.3), for an abstract Borel set Q.
- In the parent, Q = 𝒢 = {p : μ(Exc^p) > 0}, and the Haar-null hypothesis is the output of its Step 7.
- The continuity of the frame projection, which the parent takes from the sibling bf_frameProjection_continuousOn, is a hypothesis here.

Notation (as in the parent proof): E := ℝᴺ = EuclideanSpace ℝ (Fin N); x·y is the inner product and |·| the norm; 𝓛 := E →L[ℝ] E with the Borel σ-algebra of its operator-norm topology; gk is composition and 1 the identity; g* := ContinuousLinearMap.adjoint g; P_W := W.starProjection; gW := W.map g; Hⁿ := μHE[n]. Write g·v := (gv_1, …, gv_n) for g ∈ 𝓛 and v ∈ Eⁿ, 𝒱 := {v ∈ Eⁿ : v linearly independent}, and λ := volume on Eⁿ = Measure.pi of the Lebesgue measures of the factors.

1. The bad frames form a Borel set (Step 8).
   - 𝒱 is open in Eⁿ (isOpen_setOfPred_linearIndependent).
   - Let F̃(v) := frameProjection v for v ∈ 𝒱 and F̃(v) := 0 otherwise. F̃ is measurable by ContinuousOn.measurable_piecewise: it is continuous on the measurable set 𝒱 by hypothesis and constant on the complement.
   - Hence 𝒮 := {v : v ∈ 𝒱 and frameProjection v ∈ Q} = 𝒱 ∩ F̃⁻¹(Q) is Borel.
2. Joint measurability. (g, v) ↦ g·v is continuous on 𝓛 × Eⁿ (continuous_pi with continuous evaluation). Both factors are second countable, so the map is measurable for the product σ-algebra, and
   M := {(g, v) : g·v ∈ 𝒮} is measurable.
3. Every v-fibre is θ-null (Step 9(b)): θ({g : g·v ∈ 𝒮}) = 0 for each v ∈ Eⁿ.
   (a) Case v ∉ 𝒱. If g*g = 1 then g is injective. If g·v were linearly independent, so would be v (LinearIndependent.of_comp). Hence g·v ∉ 𝒮,
       so {g : g·v ∈ 𝒮} ⊆ {g : g*g ≠ 1}, which is θ-null.
   (b) Case v ∈ 𝒱. Then dim span v = n = dim W₀ (finrank_span_eq_card).
       - By Submission.bf_orthogonal_exists_map_eq (sibling orthogonal_plane_transitive) there is h ∈ 𝓛 with h*h = 1 and hW₀ = span v.
       - Let g satisfy g*g = 1. Then (gh)*(gh) = h*g*gh = h*h = 1.
       - span(g·v) = g(span v) = g(hW₀) = (gh)W₀ (Submodule.span_image, Submodule.map_comp).
       - So frameProjection(g·v) = P_{(gh)W₀} = (gh)P₀(gh)* by Submission.bf_starProjection_map_orthogonal (sibling orthogonal_conj_projection).
       Hence {g : g·v ∈ 𝒮} ⊆ {g : g*g ≠ 1} ∪ r_h⁻¹(A), where r_h(g) := gh and A := {g′ : g′P₀g′* ∈ Q}.
       - A is Borel, because g′ ↦ g′P₀g′* is continuous.
       - By right invariance (h*h = 1), θ(r_h⁻¹A) = ((r_h)_*θ)(A) = θ(A) = 0.
       So θ({g : g·v ∈ 𝒮}) = 0.
4. Invariance of λ (Step 9(a)). Let g ∈ 𝓛 with g*g = 1.
   - g preserves norms and is injective, hence surjective (finite dimension). So it is a linear isometry equivalence of E (LinearIsometryEquiv.ofSurjective) and preserves volume on E (LinearIsometryEquiv.measurePreserving).
   - Therefore v ↦ g·v preserves λ (measurePreserving_pi), and λ({v : g·v ∈ 𝒮}) = λ(𝒮).
5. Tonelli (Step 9(c)). θ is finite and λ is σ-finite. By Measure.prod_apply_symm and step 3,
   (θ ⊗ λ)(M) = ∫_{Eⁿ} θ({g : g·v ∈ 𝒮}) dλ(v) = 0.
   By Measure.prod_apply and step 4 (valid for θ-a.e. g),
   (θ ⊗ λ)(M) = ∫_𝓛 λ({v : g·v ∈ 𝒮}) dθ(g) = ∫_𝓛 λ(𝒮) dθ = λ(𝒮)·θ(𝓛) = λ(𝒮).
   Hence λ(𝒮) = 0.
   (Equivalently: the measurable integrand λ({v : g·v ∈ 𝒮}) vanishes for θ-a.e. g. As θ ≠ 0, pick one such g with g*g = 1 and use step 4.)
6. Conclusion (Step 10). λ(𝒮) = 0 means that λ-a.e. v ∉ 𝒮: if v is linearly independent, then frameProjection v ∉ Q.
   This is ForAlmostAllProjections N n (fun p ↦ p ∉ Q). ∎

## Key steps

1. 𝒮 = {v ∈ 𝒱 : frameProjection v ∈ Q} is Borel, since frameProjection is continuous on the open set 𝒱 of linearly independent frames. M = {(g, v) : g·v ∈ 𝒮} is Borel in 𝓛 × Eⁿ.
2. For each frame v, θ{g : g·v ∈ 𝒮} = 0. If v ∈ 𝒱, take h orthogonal with hW₀ = span v (bf_orthogonal_exists_map_eq). Then frameProjection(g·v) = (gh)P₀(gh)* (bf_starProjection_map_orthogonal), and right invariance turns this into θ{g : gP₀g* ∈ Q} = 0. If v ∉ 𝒱, g·v ∉ 𝒱 for injective g.
3. For orthogonal g, v ↦ g·v preserves λ (LinearIsometryEquiv.measurePreserving, measurePreserving_pi).
4. Tonelli on θ ⊗ λ gives λ(𝒮) = ∫ λ{v : g·v ∈ 𝒮} dθ = ∫ θ{g : g·v ∈ 𝒮} dλ = 0, which is the claim.

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
