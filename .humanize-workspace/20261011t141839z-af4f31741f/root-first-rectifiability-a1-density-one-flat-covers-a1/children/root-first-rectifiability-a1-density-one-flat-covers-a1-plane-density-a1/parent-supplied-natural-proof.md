# Parent-supplied natural-language proof

- Parent DAG node: `root.first_rectifiability-a1.density_one_flat_covers-a1`
- Child DAG node: `root.first_rectifiability-a1.density_one_flat_covers-a1.plane_density-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 of the parent-supplied proof (Lebesgue density in the plane), made self-contained and stated for an arbitrary subset T of P.plane.

Notation:
- ℝ^N := Euclidean N = EuclideanSpace ℝ (Fin N), and H^n := μHE[n] on ℝ^N.
- ℝ^n := EuclideanSpace ℝ (Fin n), with Lebesgue measure L^n := volume.
- B_s(y) := closedBall y s.
- ω := unitBallVolume n = L^n(ball 0 1).
- For a measure μ on ℝ^N, densityRatio n μ a s = μ(B_s(a))/(ω · ofReal(s)^n). HasDensity n μ a 1 means densityRatio n μ a s → 1 along 𝓝[>] 0.

No assumption n ≥ 1 is needed. For n = 0, P.plane = {0}, ℝ^0 is a single point and ω = 1, and every step below holds verbatim.

1. On ℝ^n the measures μHE[n] and L^n coincide (EuclideanSpace.euclideanHausdorffMeasure_eq_volume n).

2. Isometric parametrization of the plane.
- finrank ℝ P.plane = n (Grassmannian.finrank_plane).
- Reindex stdOrthonormalBasis ℝ P.plane (indexed by Fin (finrank ℝ P.plane)) along finCongr of this equality. This gives an orthonormal basis b of P.plane indexed by Fin n.
- e := b.repr.symm : ℝ^n ≃ₗᵢ[ℝ] P.plane is a linear isometry equivalence.
- Define ι : ℝ^n → ℝ^N by ι y := (e y : ℝ^N). Then ι is an isometry, being the isometry e followed by the isometric subtype inclusion (isometry_subtype_coe).
- Every a ∈ P.plane has the form ι y, with y := e.symm ⟨a, h_a⟩.

3. Measure transfer. For every set B ⊆ ℝ^n, H^n(ι(B)) = μHE[n](B) = L^n(B). This follows from Isometry.euclideanHausdorffMeasure_image (valid for arbitrary sets) and step 1.

4. Put S := ι⁻¹(T) ⊆ ℝ^n. Claim: for y ∈ ℝ^n and s ∈ ℝ, ι(S ∩ B_s(y)) = T ∩ B_s(ι y).
- ⊆: if z ∈ S ∩ B_s(y), then ι z ∈ T and dist(ι z, ι y) = dist(z, y) ≤ s.
- ⊇: let a ∈ T ∩ B_s(ι y). Since T ⊆ P.plane, step 2 gives a = ι z for some z. Then z ∈ S because ι z ∈ T, and dist(z, y) = dist(ι z, ι y) ≤ s.
Hence, by step 3, H^n(T ∩ B_s(ι y)) = L^n(S ∩ B_s(y)).

5. Volume of balls. For y ∈ ℝ^n and s ≥ 0, Measure.addHaar_closedBall gives
 L^n(B_s(y)) = ofReal(s^{finrank ℝ ℝ^n}) · L^n(ball 0 1) = ofReal(s)^n · ω,
using finrank_euclideanSpace_fin and ENNReal.ofReal_pow. This holds for every n, including n = 0.

6. Lebesgue density theorem for an arbitrary set.
- ℝ^n is a finite-dimensional real normed space. So it is a second-countable Borel metric space with the Besicovitch covering property (instance Besicovitch.instHasBesicovitchCovering), and L^n is locally finite.
- Besicovitch.ae_tendsto_measure_inter_div, applied to L^n and the possibly non-measurable set S, gives: for (L^n⌞S)-a.e. y, L^n(S ∩ B_s(y))/L^n(B_s(y)) → 1 as s → 0+.
- Let Bad be the set of y where this convergence fails. Then (L^n⌞S)(Bad) = 0 (ae_iff).
- Choose a measurable E ⊇ Bad with (L^n⌞S)(E) = 0 (exists_measurable_superset_of_null).
- Since E is measurable, (L^n⌞S)(E) = L^n(E ∩ S) (Measure.restrict_apply). Hence L^n(E ∩ S) = 0.

7. Define Z := ι(E ∩ S) ⊆ ℝ^N. By step 3, H^n(Z) = L^n(E ∩ S) = 0.

8. Let a ∈ T with a ∉ Z.
- Since T ⊆ P.plane, step 2 gives y with a = ι y.
- y ∈ S, because ι y = a ∈ T.
- y ∉ E, because otherwise a = ι y ∈ ι(E ∩ S) = Z.
- Hence y ∉ Bad, that is, L^n(S ∩ B_s(y))/L^n(B_s(y)) → 1 as s → 0+.

9. Let s > 0.
- Closed balls are Borel sets, so Measure.restrict_apply gives (H^n⌞T)(B_s(a)) = H^n(B_s(a) ∩ T) = H^n(T ∩ B_s(ι y)).
- By steps 4 and 5,
 densityRatio n (H^n⌞T) a s = H^n(T ∩ B_s(ι y))/(ω · ofReal(s)^n) = L^n(S ∩ B_s(y))/L^n(B_s(y)).
- So the two functions of s agree on (0, ∞), which belongs to 𝓝[>] 0.
- By step 8 and Tendsto.congr', densityRatio n (H^n⌞T) a s → 1 along 𝓝[>] 0. This is exactly HasDensity n (H^n⌞T) a 1.

10. Steps 7–9 show that Z has the required properties: H^n(Z) = 0, and HasDensity n (H^n⌞T) a 1 for every a ∈ T with a ∉ Z. ∎

## Key steps

1. Parametrize P.plane isometrically. An orthonormal basis of P.plane indexed by Fin n (finrank_plane) gives e : ℝ^n ≃ₗᵢ P.plane and ι := Subtype.val ∘ e. Then H^n(ι B) = L^n(B) for every B (Isometry.euclideanHausdorffMeasure_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume).
2. S := ι⁻¹(T) satisfies ι(S ∩ B_s(y)) = T ∩ B_s(ι y), and L^n(B_s(y)) = ω s^n (Measure.addHaar_closedBall).
3. Besicovitch.ae_tendsto_measure_inter_div for L^n and the arbitrary set S gives density 1 at (L^n⌞S)-a.e. y. A measurable null hull E of the exceptional set satisfies L^n(E ∩ S) = 0.
4. Z := ι(E ∩ S) is H^n-null. For a = ι y ∈ T ∖ Z we have y ∈ S ∖ E, and for s > 0 densityRatio n (H^n⌞T) a s equals L^n(S ∩ B_s(y))/L^n(B_s(y)), which tends to 1.

## Reference use

### local-project

Queries:
- `cat manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum project/GMT/Ch08/Contract.lean and workspace GMT/Ch08/Contract.lean, GMT/Ch08/Submission.lean (all 2e5cd5b3…c487)`
- `rg -n 'theorem ae_tendsto_measure_inter_div|theorem ae_tendsto_rnDeriv|theorem ae_tendsto_measure_inter_div_of_measurableSet' mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `grep -n '^variable' mathlib/Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean (instHasBesicovitchCovering needs only NormedSpace ℝ E and FiniteDimensional ℝ E)`
- `sed -n 1,320p mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n 'theorem hausdorffMeasure_image_le|theorem hausdorffMeasure_zero_singleton|theorem hausdorffMeasure_apply' mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n 'theorem ae_restrict_biUnion_iff|theorem restrict_eq_self_of_ae_mem|theorem ae_restrict_mem₀|theorem restrict_restrict|theorem restrict_apply' mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `grep -n 'theorem exists_measurable_superset_of_null' mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean; grep -n 'theorem addHaar_closedBall ' mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `grep -n 'theorem tendsto_of_le_liminf_of_limsup_le' mathlib/Mathlib/Topology/Order/LiminfLimsup.lean`
- `rg -n 'theorem (norm_project|project_sub|project_eq|inner_project|continuous_project|project_apply)' .lake/packages/simongmt/Poincare/SimonGMT`
- `grep -rn 'hausdorffMeasure_image_le|euclideanHausdorffMeasure_image' .lake/packages/simongmt/Poincare/SimonGMT`
- `grep -n 'theorem finrank_plane|theorem projectionLinearMap_isSymmetric|theorem project_project' .lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `lake env lean on scratch files: child statements plus parent assembly; API #check after import GMT.Ch08.Submission; full proofs of the 3 children and the parent with #print axioms; comparator NodeChallenge form per child; solution replay via exact Submission.X`
- `python3 dag.json lean_name collision check (84 nodes)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/RadialFirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-density-one-flat-covers-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`

The snapshot is project 63436ae6 on Mathlib 25730c7c, and its Contract.lean is byte-identical to the workspace Contract and Submission. Mathlib supplies every analytic tool the children need, with no Nontrivial or n ≥ 1 assumption:
- Besicovitch.ae_tendsto_measure_inter_div for arbitrary sets (Besicovitch.lean:1105), plus the HasBesicovitchCovering instance for any finite-dimensional real normed space (BesicovitchVectorSpace.lean:499).
- Isometry.euclideanHausdorffMeasure_image (Volume/Measure.lean:131) and EuclideanSpace.euclideanHausdorffMeasure_eq_volume for every d, including 0 (:187).
- Measure.addHaar_closedBall (EqHaar.lean:500).
- exists_measurable_superset_of_null, restrict_apply, restrict_restrict, ae_restrict_mem₀, restrict_eq_self_of_ae_mem and ae_restrict_biUnion_iff (Restrict.lean:75/205/637/347/571).
- tendsto_of_le_liminf_of_limsup_le (LiminfLimsup.lean:305).
Pinned SimonGMT supplies Grassmannian.finrank_plane, projectionLinearMap_isSymmetric and project_project (Chapter08/Varifold.lean:126/98/108). It also supplies Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn (Chapter02/Lipschitz.lean:216, inside the Submission import closure), the μHE form of Mathlib's LipschitzOnWith.hausdorffMeasure_image_le. Grassmannian.project_eq_starProjection and euclideanHausdorffMeasure_image_le_of_dist_le lie outside the closure, so the child proofs re-derive the Pythagorean identity from symmetry and idempotence instead. No existing declaration states Lebesgue density on planes or graph/projection Hausdorff comparisons, and no DAG node has an identical type to reuse. All three children were proved in scratch Lean, and the parent assembly was proved from them. Only standard axioms are used, every child type passes the comparator's NodeChallenge and solution-replay forms, and all names are unique.
