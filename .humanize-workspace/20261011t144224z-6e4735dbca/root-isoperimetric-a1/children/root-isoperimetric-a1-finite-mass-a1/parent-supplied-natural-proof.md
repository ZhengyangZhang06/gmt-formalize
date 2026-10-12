# Parent-supplied natural-language proof

- Parent DAG node: `root.isoperimetric-a1`
- Child DAG node: `root.isoperimetric-a1.finite_mass-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 1 (Finite mass) of the parent proof, written out; it uses the sibling lemmas `Submission.isoperimetric_apply_eq_zero_of_disjoint_support` (key vanish_off_support) and `Submission.isoperimetric_abs_covector_apply_le` (key covector_eval_bound).

1. Unpack IsIntegerMultiplicity T: there are M ⊆ ℝ^P, θ : ℝ^P → ℝ and ξ : ℝ^P → NVector(ℝ^P, n) with IsRectifiableTriple univ n M θ ξ and T(η) = tauAction n M θ ξ η = ∫_M θ(x) · ξ(x)(η(x)) dμHE[n](x) for every η ∈ TestFormOn univ n. From the triple we use: (i) M is μHE[n]-null-measurable; (ii) θ(x) > 0 for x ∈ M; (iii) θ is μHE[n]-integrable on M ∩ K for every compact K ⊆ ℝ^P; (iv) for μHE[n]-a.e. x ∈ M there is an orthonormal τ : Fin n → ℝ^P with ξ(x) = simpleNVector τ or ξ(x) = −simpleNVector τ, so ξ(x)(β) = ±β(τ) for every n-covector β.
2. Cut-off. spt T is compact, hence bounded: fix R ≥ 0 with spt T ⊆ closedBall(0, R). Let χ be the smooth bump function centred at 0 with inner radius R + 1 and outer radius R + 2 (Mathlib `ContDiffBump` on the inner product space ℝ^P): χ is C^∞, 0 ≤ χ ≤ 1, χ = 1 on closedBall(0, R + 1) and χ(x) = 0 when ‖x‖ ≥ R + 2. Put K := closedBall(0, R + 2) (compact and closed, hence measurable) and B := P^n · ∫_{M∩K} θ dμHE[n], a real number by (iii).
3. Splitting. Fix ω ∈ massAdmissibleOn univ n univ, i.e. ω ∈ TestFormOn univ n with covectorEuclideanNorm(ω(x)) ≤ 1 for all x. Put ω₁(x) := χ(x) • ω(x) and ω₂(x) := (1 − χ(x)) • ω(x). Both are C^∞ and vanish wherever ω does, so they have compact support; hence ω₁, ω₂ ∈ TestFormOn univ n, and ω = ω₁ + ω₂ because χ(x) + (1 − χ(x)) = 1. By linearity, T(ω) = T(ω₁) + T(ω₂).
4. T(ω₂) = 0. For ‖x‖ < R + 1 we have χ(x) = 1, so ω₂(x) = 0: the open ball ball(0, R + 1) is disjoint from support ω₂, hence (being open) also from its closure tsupport ω₂. Since spt T ⊆ closedBall(0, R) ⊆ ball(0, R + 1), tsupport ω₂ is disjoint from spt T, and the sibling lemma vanish_off_support gives T(ω₂) = 0.
5. T(ω₁) ≤ B. By step 1 and linearity of ξ(x), T(ω₁) = ∫_M θ(x) · ξ(x)(χ(x) • ω(x)) dμHE[n] = ∫_M θ(x) χ(x) ξ(x)(ω(x)) dμHE[n]. For μHE[n]-a.e. x ∈ M take τ as in (iv); then ‖τ_j‖ = 1, and the sibling lemma covector_eval_bound gives |ξ(x)(ω(x))| = |ω(x)(τ)| ≤ P^n · covectorEuclideanNorm(ω(x)) ≤ P^n. Consequently, for a.e. x ∈ M: if x ∈ K then |θ(x) χ(x) ξ(x)(ω(x))| ≤ θ(x) · 1 · P^n = P^n · 1_K(x) θ(x) (using θ(x) > 0 and |χ| ≤ 1); if x ∉ K then χ(x) = 0 and the left side is 0 = P^n · 1_K(x) θ(x). The function P^n · 1_K θ is integrable on M, since integrability of 1_K θ on M is equivalent to integrability of θ on M ∩ K (K measurable). Therefore T(ω₁) ≤ |T(ω₁)| ≤ ∫_M P^n 1_K θ dμHE[n] = P^n ∫_{M∩K} θ dμHE[n] = B (the norm of an integral is at most the integral of an integrable a.e. dominating function, `MeasureTheory.norm_integral_le_of_norm_le`; ∫_M 1_K θ = ∫_{M∩K} θ, `setIntegral_indicator`).
6. Conclusion. By steps 3–5, T(ω) = T(ω₁) ≤ B for every mass-admissible ω, so ENNReal.ofReal(T(ω)) ≤ ENNReal.ofReal(B). Since T.mass is the supremum of ENNReal.ofReal(T(ω)) over mass-admissible ω, T.mass ≤ ENNReal.ofReal(B) < ∞.

## Key steps

1. Unpack T = τ(M, θ, ξ): θ > 0 on M, θ integrable on M ∩ K for compact K, and ξ(x) = ±simpleNVector of an orthonormal frame for a.e. x ∈ M.
2. Choose a smooth bump χ equal to 1 on a ball containing spt T and supported in a compact ball K.
3. For admissible ω, T(ω) = T(χω) + T((1−χ)ω), and T((1−χ)ω) = 0 by the locality lemma since tsupport((1−χ)ω) misses spt T.
4. Using the covector evaluation bound, |T(χω)| ≤ P^n ∫_{M∩K} θ dμHE[n].
5. Hence T.mass ≤ ofReal(P^n ∫_{M∩K} θ) < ∞.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (project_commit d8d46c9587747dee0751a1f780fcafdba16a3886, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `grep -rn "euclideanHausdorffMeasure" Mathlib (snapshot mathlib) -> Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n -i "cauchy.?binet|det_mul_eq_sum" Mathlib/LinearAlgebra/Matrix (no match)`
- `grep -rn -i -l "binet" Mathlib/LinearAlgebra Mathlib/Analysis/InnerProductSpace (only LinearAlgebra/CrossProduct.lean remark)`
- `grep -n "theorem exists_isSubordinate|theorem exists_contDiff_tsupport_subset" Mathlib/Geometry/Manifold/PartitionOfUnity.lean Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `grep -n "^theorem" Mathlib/Geometry/Manifold/PartitionOfUnity.lean | grep -i "zero_one|one_nhds|exists_contMDiff"`
- `grep -n "volume_preserving" Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `grep -n "theorem map_perm|theorem map_eq_zero_of_eq|theorem map_sum" Mathlib/Topology/Algebra/Module/Alternating/Basic.lean Mathlib/LinearAlgebra/Alternating/Basic.lean Mathlib/Topology/Algebra/Module/Multilinear/Basic.lean Mathlib/LinearAlgebra/Multilinear/Basic.lean`
- `grep -n "def sort|theorem monotone_sort" Mathlib/Data/Fin/Tuple/Sort.lean`
- `read SimonGMT Chapter06 Mass.lean, Currents.lean, CurrentLocalEquality.lean, Forms.lean, FormsDuality.lean (pinned simongmt package used by the snapshot project)`
- `sed -n 1925,2000p book/chapter-06.txt (printed 6.1 proof)`
- `python3 -I: gmt-compare.py contract_scope(Contract.lean, GMT.Ch06.main_theorem) and lean_contract.validate_lean_statement on the 5 child statements`
- `python3 -I: dag.json lean_name collision check (26 nodes, no collision with isoperimetric_* names)`
- `lake build GMT.Ch06.Submission (scratch /tmp/iso_a1_decomp_check, frozen d8d46c9, pinned packages)`
- `lake env lean Scratch/IsoStmts.lean (5 statements elaborate in comparator scope)`
- `lake env lean Scratch/IsoAsm0.lean; Scratch/IsoAsm1.lean (rw m+1+(ℓ+1)=m+2+ℓ; IsoperimetricTheorem from DeformationTheorem + 3 children; #print axioms)`
- `lake env lean Scratch/IsoC3.lean (finite_mass from vanish_off_support + covector_eval_bound; #print axioms)`
- `lake build GMT.IsoFakeSub; lake env lean Scratch/NodeChallenge{0..4}.lean Scratch/NodeSolution{0..4}.lean; Scratch/IsoParentByName.lean`
- `lake env lean Scratch/ReviewAll.lean (independent reviewer: all 5 child statements proved, iso_full : DeformationTheorem → IsoperimetricTheorem; #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Matrix`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/CrossProduct.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/Multilinear/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Multilinear/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Fin/Tuple/Sort.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-isoperimetric-a1/parent-child-handoff.json`
- `/tmp/iso_a1_decomp_check/Scratch/IsoStmts.lean`
- `/tmp/iso_a1_decomp_check/Scratch/IsoAsm1.lean`
- `/tmp/iso_a1_decomp_check/Scratch/IsoC3.lean`
- `/tmp/iso_a1_decomp_check/GMT/IsoFakeSub.lean`
- `/tmp/iso_a1_decomp_check/Scratch/IsoParentByName.lean`
- `/tmp/iso_a1_decomp_check/Scratch/ReviewAll.lean`

Snapshot findings (project d8d46c95, Mathlib 25730c7c). The frozen Contract defines IsoperimetricTheorem, DeformationTheorem, IsLatticeChain, latticeFace and latticeFaceAction as used. SimonGMT supplies covectorEuclideanNorm, massAdmissibleOn, massOn and le_massOn (Mass.lean); VanishesOn, zeroRegion, support = U \ zeroRegion and isOpen_zeroRegion (CurrentLocalEquality.lean); GeometricCurrentOn.ext and the zero current (Currents.lean); and simpleNVector and wedgeCovectors_apply_det (FormsDuality.lean). Mathlib normalises μHE[d] on EuclideanSpace ℝ (Fin d) and provides Isometry.euclideanHausdorffMeasure_image and EuclideanSpace.euclideanHausdorffMeasure_eq_volume, so a ρ-lattice k-face has μHE[k]-measure ρ^k. Mathlib also provides SmoothPartitionOfUnity.exists_isSubordinate, exists_contMDiffMap_one_nhds_of_subset_interior, PiLp.volume_preserving_ofLp, AlternatingMap.map_perm, ContinuousAlternatingMap.map_eq_zero_of_eq, multilinear map_sum, and Tuple.sort with monotone_sort. There is no Cauchy–Binet theorem in Mathlib (no match), so the covector child uses the elementary constant P^n. Kernel checks in a scratch copy of the frozen project: all five child statements elaborate in the comparator scope and pass validation; NodeSolution `exact Submission.<name>` typechecks; IsoperimetricTheorem follows from DeformationTheorem plus finite_mass, zero_mass_iff and lattice_mass_lower_bound; finite_mass follows from vanish_off_support and covector_eval_bound; and the independent reviewer's ReviewAll.lean proves all five exact statements. All checks use only propext, Classical.choice and Quot.sound. No lean_name collides with the 26 DAG nodes.
