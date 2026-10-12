# Parent-supplied natural-language proof

- Parent DAG node: `root.besicovitch_federer-a1.cone_trichotomy-a1.frame_averaging-a1`
- Child DAG node: `root.besicovitch_federer-a1.cone_trichotomy-a1.frame_averaging-a1.coset_fubini-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 6 of the parent-supplied proof of bf_frameAveraging_null (its supplied Step 4.6), stated for an abstract set B. In the parent, θ = θ_N, θ′ = θ′ and B = B_1(a).

1. D := {(h, g) ∈ 𝓛 × 𝓛 : hg ∈ B} is measurable.
   - Multiplication 𝓛 × 𝓛 → 𝓛 is continuous (𝓛 is a normed ring), and 𝓛 is second countable.
   - So multiplication is measurable for the product σ-algebra (Mathlib measurable_mul via the instance MeasurableMul₂), and D is the preimage of the Borel set B.
2. First Tonelli formula. θ and θ′ are finite, hence s-finite. By Measure.prod_apply,
   (θ ⊗ θ′)(D) = ∫_𝓛 θ′(D_h) dθ(h), where D_h = {g : hg ∈ B}.
   By hypothesis θ′(D_h) = 0 for θ-a.e. h, so the integrand vanishes θ-a.e. (lintegral_congr_ae) and (θ ⊗ θ′)(D) = 0.
3. Second Tonelli formula. By Measure.prod_apply_symm,
   (θ ⊗ θ′)(D) = ∫_𝓛 θ(D^g) dθ′(g), where D^g = {h : hg ∈ B} = r_g⁻¹(B) and r_g(h) := hg.
   - r_g is continuous, hence measurable, and B is measurable. So θ(r_g⁻¹B) = ((r_g)_*θ)(B) (Measure.map_apply).
   - For θ′-a.e. g this equals θ(B), by the right-invariance hypothesis.
   - Hence (θ ⊗ θ′)(D) = ∫ θ(B) dθ′ = θ(B)·θ′(𝓛) = θ(B).
4. Comparing steps 2 and 3 gives θ(B) = 0. ∎

## Key steps

1. D = {(h, g) : hg ∈ B} is measurable because multiplication on the second-countable normed ring 𝓛 is continuous.
2. Slicing D in g first (prod_apply) gives (θ ⊗ θ′)(D) = ∫ θ′{g : hg ∈ B} dθ(h) = 0.
3. Slicing in h first (prod_apply_symm) and using right invariance for θ′-a.e. g gives (θ ⊗ θ′)(D) = θ(B)·θ′(𝓛) = θ(B); hence θ(B) = 0.

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
