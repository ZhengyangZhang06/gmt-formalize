# Parent-supplied natural-language proof

- Parent DAG node: `root.besicovitch_federer-a1.cone_trichotomy-a1.frame_averaging-a1`
- Child DAG node: `root.besicovitch_federer-a1.cone_trichotomy-a1.frame_averaging-a1.stabilizer_orbit_null-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 4 of the parent-supplied proof of bf_frameAveraging_null (its supplied Step 4.4; Mattila, Ch. 3, uniqueness of invariant measures on the sphere), with three substitutions:
- the plane H⁰ = span{e_1, …, e_{n+1}} becomes the subspace V;
- the vector e_{n+1} becomes ζ;
- the stabilizer G′ becomes K = {g : g*g = 1, g = id on V^⊥}. For V = H⁰ this is exactly G′, because V^⊥ = span{e_{n+2}, …, e_N}.
The bounds 0 < Hⁿ(S⁰) < ∞, which the parent derives from bf_sphereCap_measure_bounds, are hypotheses here. Write S := S(V).

Notation (as in the parent proof): E := ℝᴺ = EuclideanSpace ℝ (Fin N); x·y is the inner product and |·| the norm; 𝓛 := E →L[ℝ] E with the Borel σ-algebra of its operator-norm topology; gk is composition and 1 the identity; g* := ContinuousLinearMap.adjoint g; P_W := W.starProjection; gW := W.map g; Hⁿ := μHE[n].

0. Facts about K (the parent's F2 for V). Let k ∈ K.
   (a) kx·ky = x·k*ky = x·y, so |kx| = |x| and k is an isometry of E. In particular k is injective.
       E is finite-dimensional, so k is also surjective (LinearMap.surjective_of_injective).
       For y = kx, k(k*y) = k(k*kx) = kx = y. Hence kk* = 1 and k* is the inverse of k.
       Also k* ∈ K: (k*)*k* = kk* = 1 (ContinuousLinearMap.adjoint_adjoint), and for y ∈ V^⊥, k*y = k*(ky) = y.
   (b) kV ⊆ V. For x ∈ V and y ∈ V^⊥, kx·y = kx·ky = x·y = 0, so kx ∈ (V^⊥)^⊥ = V (Submodule.orthogonal_orthogonal).
   (c) By (a) and (b), kS ⊆ S, and likewise k*S ⊆ S. Since k*k = kk* = 1, for every x ∈ E: kx ∈ S ⟺ x ∈ S, i.e. k⁻¹(S) = S.
1. The two measures.
   - ν₀ is the image of θ under the continuous map g ↦ gζ from 𝓛 to E. It is a Borel probability measure on E.
     By (c), gζ ∈ S for every g ∈ K, so ν₀(E ∖ S) = θ({g : gζ ∉ S}) ≤ θ(𝓛 ∖ K) = 0.
   - Let σ := Hⁿ(S) ∈ (0, ∞) and σ̄ := σ⁻¹·(Hⁿ restricted to S).
     S = V ∩ sphere(0, 1) is closed, hence Borel, so σ̄ is a Borel probability measure on E with σ̄(E ∖ S) = 0.
2. K-invariance. Let k ∈ K.
   (a) k_*ν₀ = ν₀. Indeed k_*ν₀ is the image of θ under g ↦ k(gζ) = (kg)ζ. That is the image under g ↦ gζ of the image of θ under g ↦ kg, which is θ by left invariance.
   (b) k_*σ̄ = σ̄. For Borel B ⊆ E, step 0(c) gives k⁻¹(B) ∩ S = k⁻¹(B) ∩ k⁻¹(S) = k⁻¹(B ∩ S) = k*(B ∩ S).
       The isometry k* preserves Hⁿ (Isometry.euclideanHausdorffMeasure_image), so σ̄(k⁻¹B) = σ⁻¹Hⁿ(k*(B ∩ S)) = σ⁻¹Hⁿ(B ∩ S) = σ̄(B).
3. Transitivity. For x, y ∈ S there is k ∈ K with ky = x.
   - If x = y, take k := 1.
   - Otherwise put d := y − x ≠ 0 and let k be the reflection in d^⊥, kz = z − 2((z·d)/|d|²)d. This is Mathlib's (ℝ ∙ d)ᗮ.reflection, a linear isometry equivalence.
   - As an element of 𝓛, k preserves inner products, so k*k = 1.
   - Since |y| = |x| = 1, ky = x (Submodule.reflection_sub: reflection (ℝ ∙ (v − w))ᗮ v = w when ‖v‖ = ‖w‖; take v = y, w = x).
   - If z ∈ V^⊥, then z·d = 0 because d ∈ V. So z ∈ (ℝd)^⊥ and kz = z. Hence k ∈ K.
4. Uniqueness. Let ν be a Borel probability measure on E with ν(E ∖ S) = 0 and k_*ν = ν for all k ∈ K.
   Let φ : E → ℝ be bounded and continuous, and Ψ(x) := ∫_𝓛 φ(gx) dθ(g). We show ∫ φ dν = Ψ(ζ).
   (a) For k ∈ K, ∫_E φ(kx) dν(x) = ∫ φ d(k_*ν) = ∫ φ dν (integral_map).
   (b) F(g, x) := φ(gx) is bounded and continuous on 𝓛 × E. Both factors are second countable, so F is measurable for the product σ-algebra and integrable for the finite measure θ ⊗ ν.
       By Fubini (integral_integral_swap), ∫_𝓛 ∫_E F dν dθ = ∫_E ∫_𝓛 F dθ dν = ∫_E Ψ dν.
   (c) By (a), the inner integral ∫_E φ(gx) dν(x) equals ∫ φ dν for θ-a.e. g (all g ∈ K).
       So the left side of (b) is (∫ φ dν)·θ(𝓛) = ∫ φ dν.
   (d) Ψ is constant on S. For k ∈ K and y ∈ E, by integral_map and right invariance:
       Ψ(ky) = ∫ φ((gk)y) dθ(g) = ∫ φ(g′y) d((g ↦ gk)_*θ)(g′) = ∫ φ(g′y) dθ(g′) = Ψ(y).
       For x ∈ S, step 3 gives k ∈ K with kζ = x, so Ψ(x) = Ψ(ζ).
   (e) Since ν(E ∖ S) = 0, Ψ = Ψ(ζ) ν-a.e., and ν(E) = 1. So ∫_E Ψ dν = Ψ(ζ) (integral_congr_ae).
       Combining (b), (c) and (e) gives ∫ φ dν = Ψ(ζ).
5. ν₀ = σ̄.
   - Both measures satisfy the hypotheses of step 4, by steps 1 and 2.
   - Hence ∫ φ dν₀ = Ψ(ζ) = ∫ φ dσ̄ for every bounded continuous φ : E → ℝ.
   - Finite Borel measures on the metric space E with equal integrals of all bounded continuous functions are equal. This is MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure in Mathlib.MeasureTheory.Measure.HasOuterApproxClosed, which must be imported; E has HasOuterApproxClosed.
   - So ν₀ = σ̄.
6. Conclusion. Let Y ⊆ E be Borel with Hⁿ(Y ∩ S) = 0. By Measure.map_apply and Measure.restrict_apply,
   θ({g : gζ ∈ Y}) = ν₀(Y) = σ̄(Y) = σ⁻¹Hⁿ(Y ∩ S) = 0. ∎

## Key steps

1. Every k ∈ K is an isometry with k* = k⁻¹ ∈ K and maps V, and hence S(V), onto itself.
2. ν₀ := law of gζ under θ and σ̄ := Hⁿ⌞S(V)/Hⁿ(S(V)) are Borel probability measures concentrated on S(V). Both are K-invariant: ν₀ by left invariance of θ, σ̄ by isometry invariance of Hⁿ.
3. K acts transitively on S(V): the reflection in (y − x)^⊥ lies in K and maps y to x.
4. Uniqueness: if ν is a K-invariant probability on S(V), then ∫φ dν = Ψ(ζ) := ∫φ(gζ) dθ(g) for bounded continuous φ. This uses Fubini on θ ⊗ ν and the fact that right invariance makes Ψ constant on S(V).
5. Hence ν₀ = σ̄ (ext_of_forall_integral_eq_of_IsFiniteMeasure), so θ{g : gζ ∈ Y} = σ̄(Y) = 0 whenever Hⁿ(Y ∩ S(V)) = 0.

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
