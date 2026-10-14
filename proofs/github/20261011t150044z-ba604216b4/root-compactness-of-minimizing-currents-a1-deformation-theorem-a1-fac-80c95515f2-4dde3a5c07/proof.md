# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.skeleton_decomposition-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 6, proof of 5.1, displays (26)–(28) and (33) (chapter-06.txt lines 1841–1898), as written out in steps 3–4 of the parent proof (parent E6, E7(a)). Simon gets Q⌞F̆ = θ_F[[F̆]] from the constancy-theorem argument 2.34–2.35. Here, as in the parent proof, the face decomposition is read off from an integer multiplicity representation of Q₀, using the hypotheses (VO), (MR), (IMC) and the siblings face_geometry, skeleton_null and plane_orientation.

Notation. n := m + 1; Hⁿ := μHE[n]; Q₁ := {y ∈ Euclid n : 0 < y_i < 1}; Cⁿ := {y : 0 ≤ y_i ≤ 1}. For an index pair p = (ι, b) (ι : Fin n → Fin P strictly increasing, b : Fin P → ℤ) we use:
 - Φ_p(y) := WithLp.toLp 2 (fun i => (b i : ℝ)) + Σ_j y_j • e_{ι(j)}, with coordinates Φ_p(y)_i = b_i + y_j if i = ι(j) and b_i if i ∉ range ι;
 - E_p := (e_{ι(0)}, …, e_{ι(n−1)}), and e_p the n-vector α ↦ α(E_p);
 - F̆_p := Φ_p(Q₁), F_p := Φ_p(Cⁿ), Π_p := {x : x_i = b_i ∀ i ∉ range ι}.
 Also L_k := {x : ∃ s ⊆ Fin P, P ≤ k + |s|, x_i ∈ ℤ ∀ i ∈ s}, and Z := ℝ^P ∖ spt Q₀ (the zero region, open).

1. Representation. Q₀ is integer multiplicity; fix R = (M, θ, ξ) : IMRep univ n with Q₀(ω) = ∫_M θ(x) ξ(x)(ω(x)) dHⁿ(x) for every test n-form ω. M is Borel. θ : ℝ^P → ℕ is measurable, θ ≥ 1 on M, and ∫_{M∩K'} θ dHⁿ < ∞ for compact K'. ξ is AE-strongly measurable for Hⁿ⌞M. Let μ := R.measure = θ·Hⁿ⌞M.
2. Hⁿ(M ∩ Z) = 0. If ω is admissible for M_Z(Q₀) (tsupport ω ⊆ Z, |ω| ≤ 1), tsupport ω is disjoint from spt Q₀, so Q₀(ω) = 0 by (VO) (U = ℝ^P, S = Q₀). Thus M_Z(Q₀) = 0. (MR) with U = ℝ^P and the open W := Z gives μ(Z) = M_Z(Q₀) = 0. Since θ ≥ 1 on M, Hⁿ(M ∩ Z) ≤ ∫_{M∩Z} θ dHⁿ = μ(Z) = 0.
3. Hⁿ(L_m) = 0 by the sibling skeleton_null.
4. L_n ∖ L_m is covered by open faces. Let x ∈ L_n ∖ L_m and J := {i : x_i ∈ ℤ}. From x ∈ L_n there is s ⊆ J with P ≤ n + |s| ≤ n + |J|. From x ∉ L_m (test s := J), P > m + |J|, i.e. P ≥ n + |J|. So |Fin P ∖ J| = n. Let ι be the strictly increasing enumeration of I := Fin P ∖ J, b_i := ⌊x_i⌋ for every i, and y_j := x_{ι(j)} − ⌊x_{ι(j)}⌋. Then y_j ∈ (0, 1) because x_{ι(j)} ∉ ℤ, so y ∈ Q₁, and x = Φ_{(ι,b)}(y) (for i ∈ J, x_i = ⌊x_i⌋ = b_i).
5. The finite set s := {p = (ι, b) : ι strictly increasing and Φ_p(y) ∈ spt Q₀ for some y ∈ Q₁}. Finiteness: K is compact, so |x_i| ≤ ρ for all x ∈ K and all i, for some ρ. If Φ_p(y) ∈ spt Q₀ ⊆ K with y ∈ Q₁, then 0 ≤ Φ_p(y)_i − b_i < 1, so |b_i| ≤ ρ + 1 for every i. There are finitely many maps Fin n → Fin P and finitely many such b. By definition, every p ∈ s has ι strictly increasing and some y ∈ Q₁ ⊆ Cⁿ with Φ_p(y) ∈ spt Q₀; these are two of the required conclusions. (If n > P, s = ∅.)
6. Disjointness. For distinct p, q ∈ s, F̆_p ∩ F̆_q = ∅. If Φ_p(y) = Φ_q(y') with y, y' ∈ Q₁ ⊆ Cⁿ, the separation part of face_geometry gives dist(Φ_p y, Φ_q y') ≥ 1 or ≥ min(y_j, 1 − y_j) > 0 for some j, contradicting distance 0. Each F̆_p = {x ∈ Π_p : b_{ι(j)} < x_{ι(j)} < b_{ι(j)} + 1 ∀ j} is Borel.
7. M is covered up to a null set. Let x ∈ M ∖ ⋃_{p∈s} F̆_p. If x ∉ spt Q₀ then x ∈ M ∩ Z. Otherwise x ∈ spt Q₀ ⊆ L_n. If also x ∉ L_m, step 4 gives p with ι strictly increasing and x = Φ_p(y), y ∈ Q₁. Then p ∈ s, since x ∈ spt Q₀, contradicting x ∉ F̆_p. Hence M ∖ ⋃_{p∈s} F̆_p ⊆ (M ∩ Z) ∪ L_m, which is Hⁿ-null by steps 2 and 3.
8. Change of variables. By face_geometry, Φ_p is an isometry Euclid n → ℝ^P, hence a closed embedding and a measurable embedding. By Isometry.map_euclideanHausdorffMeasure and EuclideanSpace.euclideanHausdorffMeasure_eq_volume, the push-forward of Lebesgue measure under Φ_p is Hⁿ⌞range Φ_p. Hence ∫_{F̆_p} h dHⁿ = ∫_{Q₁} h(Φ_p y) dy for every Borel h ≥ 0 (lintegral) and every h integrable on F̆_p (MeasurableEmbedding set-integral formulas).
9. Orientation on a face. Fix p = (ι, b) ∈ s. Apply (IMC)(b) to R and the Borel set E := F̆_p (U = ℝ^P open). This gives R' : IMRep univ n with R'.carrier = M ∩ F̆_p and R'.orient = ξ. By R'.orients, for Hⁿ-a.e. x ∈ M ∩ F̆_p there is Q with HasApproximateTangentSpaceAt n (M ∩ F̆_p) x Q and IsUnitOrientationOf (ξ x) Q. Every a ∈ A := M ∩ F̆_p ⊆ Π_p satisfies a_i = b_i = x_i for i ∉ range ι. So plane_orientation (with ι, A, x, Q, ξ x) gives ξ(x) = e_p or ξ(x) = −e_p, for Hⁿ-a.e. x ∈ M ∩ F̆_p.
10. Densities. Choose a strongly measurable ξ̃ with ξ̃ = ξ Hⁿ⌞M-a.e. (AEStronglyMeasurable.mk). For p ∈ s let σ_p(x) := 1 if ξ̃(x) = e_p; σ_p(x) := −1 if ξ̃(x) ≠ e_p and ξ̃(x) = −e_p; σ_p(x) := 0 otherwise. σ_p is Borel, since {ξ̃ = ±e_p} are measurable (StronglyMeasurable.measurableSet_eq_fun against a constant). Define u_p(y) := 1_M(Φ_p y) · θ(Φ_p y) · σ_p(Φ_p y) for p ∈ s, and u_p := 0 for p ∉ s. Each u_p is Borel and u_p(y) ∈ ℤ for every y. By step 9 and ξ̃ = ξ a.e., for Hⁿ-a.e. x ∈ M ∩ F̆_p we have ξ(x) = σ_p(x) e_p. Hence θ(x) ξ(x)(ω(x)) = θ(x) σ_p(x) ω(x)(E_p) for every test form ω.
11. Integrability and mass. For p ∈ s, |u_p(y)| ≤ (1_M θ)(Φ_p y). By step 8, ∫_{Q₁} |u_p| ≤ ∫_{F̆_p} 1_M θ dHⁿ = μ(F̆_p) ≤ μ(F_p) < ∞ (F_p is compact; θ is locally integrable). So u_p is integrable on Q₁. Steps 6 and 8 and (MR) with W = ℝ^P (open) give Σ_{p∈s} ∫_{Q₁} |u_p| ≤ Σ_{p∈s} μ(F̆_p) = μ(⋃_{p∈s} F̆_p) ≤ μ(ℝ^P) = M_{ℝ^P}(Q₀) = M(Q₀). In ENNReal: ofReal(Σ_p ∫|u_p|) = Σ_p ofReal(∫|u_p|) = Σ_p ∫⁻|u_p| ≤ M(Q₀).
12. The representation. Fix a test n-form ω and let g(x) := θ(x) ξ(x)(ω(x)). g is AE-strongly measurable for Hⁿ⌞M (θ measurable, ξ AE-strongly measurable, ω continuous, evaluation continuous). By (IMC)(d), |ξ(x)(ω(x))| ≤ |ω(x)| (covectorEuclideanNorm) for Hⁿ-a.e. x ∈ M. The function x ↦ |ω(x)| is continuous and compactly supported, so it is bounded by some C_ω and vanishes off tsupport ω. Thus |g| ≤ C_ω θ 1_{tsupport ω} a.e. on M, which has finite integral, so g is Hⁿ⌞M-integrable. By step 7, ∫_M g dHⁿ = ∫_{⋃_{p∈s}(M∩F̆_p)} g dHⁿ. The sets M ∩ F̆_p are pairwise disjoint and measurable (step 6), so this equals Σ_{p∈s} ∫_{M∩F̆_p} g dHⁿ (integral_biUnion_finset). For p ∈ s, steps 10 and 8 give ∫_{M∩F̆_p} g dHⁿ = ∫_{F̆_p} 1_M θ σ_p ω(·)(E_p) dHⁿ = ∫_{Q₁} u_p(y) ω(Φ_p y)(E_p) dy. Hence Q₀(ω) = Σ_{p∈s} ∫_{Q₁} u_p(y) ω(Φ_p y)(E_p) dy.
13. Steps 5, 10, 11 and 12 give every conclusion. s is finite with ι strictly increasing. Each F_p meets spt Q₀. Each u_p is integer-valued everywhere and integrable on Q₁. The mass bound and the representation hold. ∎

## Key steps

1. Fix an IMRep (M, θ, ξ) of Q₀ and μ = θHⁿ⌞M. (VO) and (MR) give μ(ℝ^P ∖ spt Q₀) = 0, so Hⁿ(M ∖ spt Q₀) = 0; skeleton_null gives Hⁿ(L_m) = 0.
2. Every x ∈ L_n ∖ L_m equals Φ_p(y), y ∈ Q₁, with ι the non-integer coordinates and b = ⌊x⌋. The set s of faces whose open face meets spt Q₀ is finite, and distinct open faces are disjoint (face_geometry). So M ⊆ ⋃_{p∈s} Φ_p(Q₁) up to an Hⁿ-null set.
3. On M ∩ Φ_p(Q₁), (IMC)(b) and plane_orientation give ξ = ±e_ι a.e. Set u_p := (1_M θ σ_p)∘Φ_p with σ_p ∈ {0, ±1} read from a Borel version of ξ; u_p is integer-valued everywhere.
4. Change of variables (Φ_p isometry, μHE = volume on ℝⁿ) gives the representation of Q₀(ω) (IMC(d) for integrability), integrability of u_p, and Σ_p ∫|u_p| ≤ μ(ℝ^P) = M(Q₀) by (MR).

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
