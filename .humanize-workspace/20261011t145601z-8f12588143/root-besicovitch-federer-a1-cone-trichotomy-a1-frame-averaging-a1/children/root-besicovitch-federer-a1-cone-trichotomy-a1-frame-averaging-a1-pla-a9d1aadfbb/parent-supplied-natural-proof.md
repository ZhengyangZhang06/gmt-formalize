# Parent-supplied natural-language proof

- Parent DAG node: `root.besicovitch_federer-a1.cone_trichotomy-a1.frame_averaging-a1`
- Child DAG node: `root.besicovitch_federer-a1.cone_trichotomy-a1.frame_averaging-a1.plane_direction_null-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 5 and 6 of the parent-supplied proof of bf_frameAveraging_null (its supplied Steps 4.5–4.6). The (n+1)-plane V and the direction ζ ∈ V replace H⁰_1 and e_{n+1}. The parent's hypothesis (h1), specialized to the point a, is applied directly to the plane hV. The bounds 0 < Hⁿ(S(V)) < ∞ are hypotheses here. Write S(V) := {x ∈ V : |x| = 1}.

Notation (as in the parent proof): E := ℝᴺ = EuclideanSpace ℝ (Fin N); x·y is the inner product and |·| the norm; 𝓛 := E →L[ℝ] E with the Borel σ-algebra of its operator-norm topology; gk is composition and 1 the identity; g* := ContinuousLinearMap.adjoint g; P_W := W.starProjection; gW := W.map g; Hⁿ := μHE[n].

1. Stabilizer measure (Step 1). Apply Submission.bf_orthStabilizer_haar_exists (sibling haar_stabilizer) with U := V^⊥. It gives a Borel probability measure θ′ on 𝓛 such that:
   - θ′-a.e. g′ lies in K := {g′ : g′*g′ = 1, g′x = x for all x ∈ V^⊥};
   - for every k ∈ K, the images of θ′ under g ↦ kg and g ↦ gk equal θ′.
2. B := {g ∈ 𝓛 : (a, gP_Vg*, gζ) ∈ Bad} is Borel. The map g ↦ (a, gP_Vg*, gζ) from 𝓛 to E × 𝓛 × E is continuous:
   - the adjoint is a linear isometry of 𝓛;
   - composition and evaluation at ζ are continuous.
   So it is measurable for the product σ-algebra, and B is the preimage of the measurable set Bad.
3. Fubini over cosets (Step 6). Apply Submission.bf_haar_null_of_cosetFibres_null (sibling coset_fubini) to θ (a probability, hence finite), θ′ and B.
   - First hypothesis: θ′-a.e. k satisfies k*k = 1 (step 1), hence (g ↦ gk)_*θ = θ by the right-invariance hypothesis on θ.
   - Second hypothesis: θ′({g′ : hg′ ∈ B}) = 0 for θ-a.e. h. Since θ-a.e. h satisfies h*h = 1, it suffices to prove this for each fixed h with h*h = 1 (steps 4–7).
   The sibling then gives θ(B) = 0, which is the claim.
4. The plane H := hV (Step 5). By Submission.bf_starProjection_map_orthogonal (sibling orthogonal_conj_projection), P_H = hP_Vh* and dim H = dim V = n + 1.
   Moreover hx·hy = x·h*hy = x·y, so h is a linear isometry of E.
5. The fibre set Y := {y ∈ E : (a, P_H, hy) ∈ Bad}.
   - Y is Borel, as the preimage of Bad under the continuous map y ↦ (a, P_H, hy).
   - h maps Y ∩ S(V) into T := {x ∈ H : |x| = 1, (a, P_H, x) ∈ Bad}: for y ∈ Y ∩ S(V), hy ∈ hV = H, |hy| = |y| = 1 and (a, P_H, hy) ∈ Bad.
   - By isometry invariance of Hⁿ (Isometry.euclideanHausdorffMeasure_image) and monotonicity, Hⁿ(Y ∩ S(V)) = Hⁿ(h(Y ∩ S(V))) ≤ Hⁿ(T).
   - Hⁿ(T) = 0 by the hypothesis applied to the (n+1)-dimensional subspace H. So Hⁿ(Y ∩ S(V)) = 0.
6. Orbit law (Step 4). Apply Submission.bf_stabilizerOrbit_null (sibling stabilizer_orbit_null) to V, θ′ (with the properties of step 1), the hypotheses 0 < Hⁿ(S(V)) < ∞, ζ and Y.
   It gives θ′({g′ : g′ζ ∈ Y}) = 0.
7. {g′ : hg′ ∈ B} ⊆ (𝓛 ∖ K) ∪ {g′ : g′ζ ∈ Y}. Let g′ ∈ K with hg′ ∈ B.
   (a) g′V ⊆ V. For x ∈ V and y ∈ V^⊥: y·g′x = g′y·g′x = y·g′*g′x = y·x = 0, so g′x ∈ (V^⊥)^⊥ = V.
       By bf_starProjection_map_orthogonal, dim g′V = dim V, hence g′V = V (Submodule.eq_of_le_of_finrank_eq).
       So g′P_Vg′* = P_{g′V} = P_V, again by bf_starProjection_map_orthogonal.
   (b) (hg′)* = g′*h* (ContinuousLinearMap.adjoint_comp). So (hg′)P_V(hg′)* = h(g′P_Vg′*)h* = hP_Vh* = P_H.
   (c) Therefore hg′ ∈ B means (a, P_H, h(g′ζ)) ∈ Bad, i.e. g′ζ ∈ Y.
   Both sets on the right are θ′-null (steps 1 and 6). Hence θ′({g′ : hg′ ∈ B}) = 0, completing step 3. ∎

Lean hint: to rewrite an equality of subspaces W₁ = W₂ inside starProjection, prove ∀ W₁ W₂, W₁ = W₂ → W₁.starProjection = W₂.starProjection by rintro _ _ rfl; rfl. A direct rw fails because the HasOrthogonalProjection instance depends on the subspace.

## Key steps

1. Take θ′ from bf_orthStabilizer_haar_exists with U = V^⊥: a bi-invariant probability on the stabilizer K of V^⊥.
2. B = {g : (a, gP_Vg*, gζ) ∈ Bad} is Borel, and θ is right-invariant under θ′-a.e. k. So by bf_haar_null_of_cosetFibres_null it suffices that θ′{g′ : hg′ ∈ B} = 0 for every orthogonal h.
3. For orthogonal h, H := hV is an (n+1)-plane with P_H = hP_Vh* (bf_starProjection_map_orthogonal). Since h is an isometry, the hypothesis at H gives Hⁿ(Y ∩ S(V)) = 0 for Y := {y : (a, P_H, hy) ∈ Bad}.
4. Every g′ ∈ K fixes V setwise, so (hg′)P_V(hg′)* = P_H and hg′ ∈ B ⟺ g′ζ ∈ Y.
5. bf_stabilizerOrbit_null gives θ′{g′ : g′ζ ∈ Y} = 0, hence θ′{g′ : hg′ ∈ B} = 0 and θ(B) = 0.

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
