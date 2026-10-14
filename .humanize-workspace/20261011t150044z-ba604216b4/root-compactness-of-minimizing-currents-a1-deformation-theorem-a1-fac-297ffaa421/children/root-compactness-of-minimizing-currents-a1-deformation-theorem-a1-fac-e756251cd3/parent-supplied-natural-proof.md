# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.finite_family-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the “Finite family” paragraph of step 2 of the parent proof (the finite-set part of parent E0). Simon's 5.1 chooses P = Σ β_F[[F]] with faces of L_n near spt T, and its finiteness is used in the compactness argument of 7.2.4.

Notation. Q₁^k := {y ∈ Euclid k : 0 < y_i < 1} and Cᵏ := {y : 0 ≤ y_i ≤ 1}. For p = (ι, b): Φ_p(y) := toLp(b) + Σ_j y_j e_{ι(j)}, E_p := (e_{ι(j)})_j, and [[p]](ω) := ∫_{Q₁^k} ω(Φ_p y)(E_p) dy. Coordinates: Φ_p(y)_i = b_i + y_j if i = ι(j) and b_i if i ∉ range ι (ι injective). Let 𝒬 be the set in the statement.

1. K is compact, hence bounded: there is ρ ≥ 0 with |x_i| ≤ ρ for all x ∈ K and all i.
2. S_K := {p = (ι, b) : ι strictly increasing and Φ_p(y) ∈ K for some y ∈ Cᵏ} is finite. If Φ_p(y) ∈ K with y ∈ Cᵏ, then for each i, Φ_p(y)_i − b_i ∈ [0, 1] (it is y_j if i = ι(j), else 0), so |b_i| ≤ ρ + 1. ι ranges over the finite set of maps Fin k → Fin P, and b over the finite set {b : |b_i| ≤ ρ + 1 ∀ i}.
3. If Λ < 0 then 𝒬 = ∅, because Σ|β_p| ≥ 0 > Λ; so assume Λ ≥ 0. Then Z := {z ∈ ℤ : |z| ≤ Λ} is finite and contains 0, so the set B of functions S_K → Z is finite.
4. For T ∈ 𝒬 choose witnesses (s, β). Then s ⊆ S_K, and |β_p| ≤ Σ_{q∈s}|β_q| ≤ Λ for p ∈ s. Define β̄_T ∈ B by β̄_T(p) := β_p if p ∈ s and 0 if p ∈ S_K ∖ s. Then T(ω) = Σ_{p∈S_K} β̄_T(p) [[p]](ω) for all ω, since the added terms vanish.
5. If T, T' ∈ 𝒬 have β̄_T = β̄_{T'}, then T(ω) = T'(ω) for all ω by step 4, so T = T' (GeometricCurrentOn.ext). Thus T ↦ β̄_T is an injection of 𝒬 into the finite set B, and 𝒬 is finite (Set.Finite.of_finite_image / Finite.of_injective). ∎

## Key steps

1. Faces meeting the bounded set K have lower corners b in a finite box, so the admissible pairs form a finite set S_K.
2. Each such T equals Σ_{p∈S_K} β̄_p [[p]] for some β̄ : S_K → {z ∈ ℤ : |z| ≤ Λ}, a finite set.
3. Currents are determined by their values (GeometricCurrentOn.ext), so T ↦ β̄ is injective and the set is finite.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); git -C local-references/123e8435b4a2469b/mathlib rev-parse HEAD (25730c7c759d108ef87ab70af2342a196760f79d, matches manifest)`
- `rg -n 'cmcdtfr_' project mathlib/Mathlib -g '*.lean' (no match); python3 scan of runs/20261011T150044Z-ba604216b4/dag.json lean_name fields for cmcdtfr, polyhedral, cubical, stokes, face_ (no collision among 902 nodes; only cmcdt_face_replacement itself)`
- `rg -n -i 'polyhedral|cubical|lattice|IsLatticeChain' project/GMT -g '*.lean'`
- `rg -n 'theorem integral_divergence_of_hasFDerivAt_off_countable' mathlib/Mathlib`
- `rg -n 'theorem (EuclideanSpace.euclideanHausdorffMeasure_eq_volume|Isometry.map_euclideanHausdorffMeasure|Isometry.euclideanHausdorffMeasure_image|MeasureTheory.Measure.euclideanHausdorffMeasure_zero)' mathlib/Mathlib`
- `rg -n 'theorem (hausdorffMeasure_of_dimH_lt|dimH_univ_eq_finrank|dimH_image_le)' mathlib/Mathlib`
- `rg -n 'theorem (AlternatingMap.eq_smul_basis_det|OrthonormalBasis.det_to_matrix_orthonormalBasis_real)' mathlib/Mathlib`
- `grep -rn 'exists_contDiff_support_eq_eq_one_iff|IsCompact.exists_cthickening_subset_open|PiLp.volume_preserving_ofLp|volume_euclideanSpace_eq_dirac|volume_pi_Ioo|Integrable.bdd_mul|integral_biUnion_finset' mathlib/Mathlib (all found)`
- `grep in lake-packages-25730c7c/simongmt Chapter03/Rectifiable.lean and Chapter06/{Forms,Currents,Mass,CurrentLocalEquality}.lean for HasApproximateTangentSpaceAt, blowUpMap, CountablyRectifiable, support_euclideanHausdorffMeasure_restrict_submodule, regular_euclideanHausdorffMeasure_restrict_submodule, exteriorDerivative_apply, tsupport_exteriorDerivative_subset, GeometricCurrentOn.support, zeroRegion, massAdmissibleOn, covectorEuclideanNorm, le_massOn, massOn_mono (all found)`
- `sed -n 560,700p and 1700,1935p book/chapter-06.txt (Simon 2.34–2.37 and 5.1 displays (26)–(38))`
- `lake env lean /tmp/frdecomp/lean/Types.lean (nine child types, wrapped as verifier/gmt-compare.py child_modules does after the replayed contract scope; no errors)`
- `lake env lean /tmp/frdecomp/lean/Assembly.lean (FRAsm.check: frozen CB type + nine child types imply the selected frozen type; #print axioms: propext, Classical.choice, Quot.sound)`
- `lake env lean /tmp/frdecomp/lean/InstCheck.lean and /tmp/frdecomp/lean/InstCheck2.lean (C^∞ not ω, pointwise Sub by rfl, trace coercion, coordinates of the face map, vol((0,1)^k) = 1, μHE[0]{x} = 1)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/HausdorffDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-fac-297ffaa421/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1/decomposition-v2.json`
- `/tmp/frdecomp/lean/Types.lean`
- `/tmp/frdecomp/lean/Assembly.lean`
- `/tmp/frdecomp/lean/InstCheck.lean`
- `/tmp/frdecomp/lean/InstCheck2.lean`

The snapshot (project b4d606d, Mathlib 25730c7c) has the same Ch07 contract as the workspace, and Submission.lean equals the contract. The only lattice-chain material is in the separate Ch06 problem (project/GMT/Ch06/Contract.lean: LatticeFaceIndex, latticeFace, latticeFaceAction, IsLatticeChain; main_theorem := by sorry). It lives in another module with another type (Eucl) and has no proofs, so it is not reusable. Its face convention ((Fin N → ℤ) × increasing multi-index, orientation fun j => EuclideanSpace.single (F.2 j) 1) matches the one adopted here. Mathlib has no polyhedral-chain, cubical-Stokes or deformation results (no match). It does provide every tool cited by the child proofs: the box divergence theorem, isometry invariance of μHE with μHE = volume on Euclid d, Hausdorff dimension bounds, eq_smul_basis_det, the ±1 determinant between orthonormal bases, the smooth Urysohn lemma, the measure-preserving ofLp, Integrable.bdd_mul and integral_biUnion_finset. SimonGMT supplies approximate tangent spaces, the support of Hⁿ on planes, exteriorDerivative_apply, support and mass. No declaration or DAG node uses the prefix cmcdtfr_. All nine child types elaborate in the comparator's replayed scope. The Lean assembly from the frozen CB type and the nine child types to the selected frozen type compiles with only standard axioms.
