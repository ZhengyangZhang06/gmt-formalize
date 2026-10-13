# Parent-supplied natural-language proof

- Parent DAG node: `root.besicovitch_federer-a1.infinite_fibres-a1`
- Child DAG node: `root.besicovitch_federer-a1.infinite_fibres-a1.projection_isometric_chart-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. This is Steps 1 and 6 of the parent proof. The printed proof of M. G. Dall'Alba, The Besicovitch–Federer Projection Theorem (Master's thesis, Università di Padova, 2020), Lemma 5.4, p. 70, applies Eilenberg's inequality (Theorem 3.15 there, stated for Lipschitz maps into ℝᵐ with Lebesgue measure Lᵐ) to the orthogonal projection onto the m-plane V^⊥ while integrating with Hᵐ over V^⊥. This tacitly identifies the plane isometrically with Euclidean space, and Hᵐ with Lᵐ. This lemma makes that identification explicit, with the n-plane W in place of V^⊥. (The parent proof writes its chart as ι : ℝⁿ ≃ W with f = ι⁻¹ ∘ π. Below, ι denotes the inverse direction W ≃ ℝⁿ, so f = ι ∘ π is the same map.)

Notation. N := n + ℓ.
- π : ℝ^N → W is the orthogonal projection viewed as a map into the subspace W (Mathlib W.orthogonalProjectionOnto).
- ↑ : W → ℝ^N is the inclusion.
- Then P x = ↑(π x) for all x, by definition (starProjection = subtypeL ∘ orthogonalProjectionOnto; Mathlib Submodule.starProjection_apply).
- W is finite-dimensional, hence complete, so the orthogonal projection exists.

1. A linear isometry ι : W ≃ ℝⁿ. W, with the inner product of ℝ^N, is a real inner product space of dimension n. Take an orthonormal basis of W indexed by Fin n: for instance Mathlib's stdOrthonormalBasis ℝ W, which is indexed by Fin (finrank ℝ W), reindexed along the bijection finCongr : Fin (finrank ℝ W) ≃ Fin n given by the hypothesis finrank ℝ W = n. Let ι : W → ℝⁿ be its coordinate map (OrthonormalBasis.repr), a linear isometric equivalence. Define
 f := ι ∘ π : ℝ^N → ℝⁿ and J := ↑ ∘ ι⁻¹ : ℝⁿ → ℝ^N.

2. (i) f is 1-Lipschitz.
- The orthogonal projection has operator norm ≤ 1, so π is 1-Lipschitz: |π x − π x′| = |π(x − x′)| ≤ |x − x′| (Mathlib Submodule.lipschitzWith_orthogonalProjectionOnto).
- ι is an isometry, hence 1-Lipschitz (LinearIsometryEquiv.lipschitzWith).
- Therefore f = ι ∘ π is (1·1 = 1)-Lipschitz (LipschitzWith.comp).

3. (ii) The fibres of f are the fibres of P.
- If f a = f b, then π a = π b because ι is injective, hence P a = ↑(π a) = ↑(π b) = P b.
- Conversely, if P a = P b, i.e. ↑(π a) = ↑(π b), then π a = π b because the inclusion is injective (Subtype.ext), hence f a = ι(π a) = ι(π b) = f b.

4. Factorization P = J ∘ f. For every x ∈ ℝ^N, J(f x) = ↑(ι⁻¹(ι(π x))) = ↑(π x) = P x. Consequently, for every S ⊆ ℝ^N, P(S) = J(f(S)), since the image under a composite is the iterated image (Set.image_image).

5. J is an isometry. ι⁻¹ : ℝⁿ → W is an isometry, and the inclusion of the subspace W (with the induced metric) into ℝ^N is an isometry (isometry_subtype_coe). A composite of isometries is an isometry.

6. (iii) Measure transfer.
- Euclidean Hausdorff measures are invariant under isometries, applied to arbitrary sets: Mathlib Isometry.euclideanHausdorffMeasure_image gives μHE[d](J(T)) = μHE[d](T).
- Take d := n and T := f(S) ⊆ ℝⁿ. By step 4, Hⁿ(P(S)) = μHE[n](J(f(S))) = μHE[n](f(S)), the latter computed in ℝⁿ.
- On ℝⁿ = EuclideanSpace ℝ (Fin n), μHE[n] = volume (Mathlib EuclideanSpace.euclideanHausdorffMeasure_eq_volume n).
Hence Hⁿ(P(S)) = Lⁿ(f(S)) for every S ⊆ ℝ^N.

7. Conclusion. The map f of step 1 satisfies (i) by step 2, (ii) by step 3, and (iii) by step 6. ∎

## Key steps

1. An orthonormal basis of W indexed by Fin n gives a linear isometric equivalence ι : W ≃ ℝⁿ. Put f := ι ∘ π with π := W.orthogonalProjectionOnto, so that P = ↑ ∘ π.
2. f is 1-Lipschitz, because π has operator norm ≤ 1 and ι is an isometry.
3. f a = f b ⟺ π a = π b ⟺ P a = P b, by injectivity of ι and of the inclusion.
4. P = J ∘ f with J := ↑ ∘ ι⁻¹ an isometry, so P(S) = J(f(S)).
5. Isometry invariance of μHE[n] and μHE[n] = volume on ℝⁿ give Hⁿ(P(S)) = Lⁿ(f(S)).

## Reference use

### local-project

Queries:
- `cat local-references/d498d77b74ea2063/manifest.json (project d09bc8a18ce60face651f042976e8465f21f0f68, mathlib 25730c7c759d108ef87ab70af2342a196760f79d); diff -q snapshot project/GMT/Ch03/Contract.lean vs workspace GMT/Ch03/Contract.lean (identical)`
- `rg -n "hausdorffMeasure_zero|euclideanHausdorffMeasure_zero|hausdorffMeasure_zero_singleton|μH\[0\]|μHE\[0\]" mathlib/Mathlib`
- `rg -n "count" mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean; rg -l "hausdorffMeasure.*count|count.*hausdorffMeasure|μH\[0\].*encard|encard.*μH" mathlib/Mathlib (no match)`
- `sed -n 60,260p mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (euclideanHausdorffMeasure_zero, Isometry.euclideanHausdorffMeasure_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume)`
- `rg -n "^(noncomputable )?def (orthogonalProjection|orthogonalProjectionOnto|starProjection)|theorem (starProjection_norm_le|orthogonalProjection_norm_le|norm_starProjection_apply_le|orthogonalProjectionOnto_norm_le|starProjection_apply)|lipschitzWith_orthogonalProjectionOnto" mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `rg -n "def finStdOrthonormalBasis|def stdOrthonormalBasis|ofFinrankEq|def reindex" mathlib/Mathlib (stdOrthonormalBasis, OrthonormalBasis.reindex in PiL2.lean)`
- `rg -n "theorem ae_lt_top\b|theorem ae_lt_top'" mathlib/Mathlib`
- `rg -n "theorem sum_measure_singleton|sum_measure_singleton|theorem measure_biUnion_finset\b|theorem Infinite.exists_subset_card_eq" mathlib/Mathlib`
- `rg -n "theorem eq_top_of_forall_nnreal_le|theorem encard_coe_eq_coe_finsetCard|theorem encard_eq_top_iff|toENNReal_top" mathlib/Mathlib`
- `rg -n "isometry_subtype_coe" mathlib/Mathlib/Topology/MetricSpace/Isometry.lean; rg -n "theorem lipschitzWith" mathlib/Mathlib/Analysis/Normed/Operator/LinearIsometry.lean; rg -n "theorem image_image\b" mathlib/Mathlib/Data/Set/Image.lean`
- `rg -n "μHE\[0\]|μH\[0\]|hausdorffMeasure_zero|encard" simongmt/Poincare`
- `rg -n "starProjection|orthogonalProjection|finStdOrthonormalBasis|stdOrthonormalBasis" simongmt/Poincare`
- `python3 -I scan of dag.json nodes[*].lean_name / lean_statement for bf_hausdorffZero_eq_encard, bf_starProjection_isometricChart, μHE[0], encard, starProjection+volume (no collision, no overlap; 85 nodes); grep -rl of both names under .humanize and GMT (no match)`
- `lake env lean /tmp/bf_if_split/FinalTypes.lean (exact child types sorry'd + parent assembly against handoff's frozen type)`
- `lake env lean /tmp/bf_if_split/Full.lean (full child proofs + assembly; #print axioms → [propext, Classical.choice, Quot.sound] for all three)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Data/Set/Finite/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Data/Set/Card.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Data/Set/Image.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Basic/Real/ENatENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/MetricSpace/Isometry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Normed/Operator/LinearIsometry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/AppendixA/Foundations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/FirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-besicovitch-federer-a1-infinite-fibres-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-besicovitch-federer-a1-cone-density-infinite-a1/decomposition-v1.json`

Pinned snapshot (project d09bc8a, Mathlib 25730c7c) plus the pinned simongmt package.

Found and used:
- Child A: MeasureTheory.Measure.euclideanHausdorffMeasure_zero (μHE[0] = μH[0]), Measure.hausdorffMeasure_zero_singleton, MeasureTheory.sum_measure_singleton, Set.encard_coe_eq_coe_finsetCard, Set.encard_eq_top_iff, ENat.toENNReal_top, ENNReal.eq_top_of_forall_nnreal_le, Set.Infinite.exists_subset_card_eq.
- Child B: Submodule.orthogonalProjectionOnto with starProjection_apply (definitional P = ↑ ∘ π), Submodule.lipschitzWith_orthogonalProjectionOnto, stdOrthonormalBasis with OrthonormalBasis.reindex (finCongr) and .repr, LinearIsometryEquiv.lipschitzWith, isometry_subtype_coe, Set.image_image, Isometry.euclideanHausdorffMeasure_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume.
- Parent assembly: ae_lt_top, ae_iff, measure_mono_null.

No match:
- Mathlib has no identity H⁰ = counting measure / encard (only singleton = 1 and 1 ≤ μH[0] s for nonempty s) and no isometric chart for starProjection.
- SimonGMT has neither. AppendixA has only dimH lemmas, Ch01 has simonHausdorffMeasure_zero_singleton, and Ch04 uses starProjection only for varifolds.
- dag.json has no name collision and no overlapping statement. The sibling cone_density_infinite children (bf_plane_closedBall_measure_eq, bf_plane_vitali_disjoint_cover) are different statements.

Lean checks:
- Both exact child types elaborate in comparator scope.
- Full child proofs and the parent assembly against the exact frozen parent type compile.
- All three declarations use only the standard axioms propext, Classical.choice and Quot.sound.
