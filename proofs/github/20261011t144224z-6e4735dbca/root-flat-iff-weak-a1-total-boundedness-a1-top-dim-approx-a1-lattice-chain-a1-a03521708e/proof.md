# Parent-supplied natural-language proof

- Parent DAG node: `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1`
- Child DAG node: `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.lattice_chain-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5 of the parent proof ((29) and (34) of the proof of Simon 5.1). It defines v := Σ_z β_z 1_{F̊_z} and Pc(ω) := ∫ v ω_e dL, then proves (a) IsLatticeChain and (b) integer multiplicity. Uses the siblings lattice_cubes, density_current and locally_constant_im.

Notation.
- n = m + 1, E := Eucl n, L := volume = μHE[n] (EuclideanSpace.euclideanHausdorffMeasure_eq_volume).
- e_i := EuclideanSpace.single i 1, ω_e(x) := ω(x)(e), Q_F := latticeFace ρ F.
- Call x ∈ E good if x_i ≠ ρk for all i and all k ∈ ℤ; let G be the set of good points.
By the sibling lattice_cubes (Submission.fiw_tb_tda_lattice_cubes m ρ hρ):
- (a) F.2 j = j for all F and j;
- (b) Q_F = {x : ρ F.1_i ≤ x_i ≤ ρ(F.1_i + 1) for all i};
- (c) Q_F is measurable;
- (d) L(Q_F) = ofReal(ρ^n);
- (f) L-a.e. point is good;
- (g) ∫⁻ g dL = Σ'_F ∫⁻_{Q_F} g dL for g ≥ 0;
- (h) ∫ f dL = Σ'_F ∫_{Q_F} f dL for integrable f.

1. (Definition of v.) Let α₀ : Fin n ↪o Fin n be the identity order embedding, and let z(x) := (⌊x_i/ρ⌋)_i ∈ ℤ^n. Define v(x) := β(z(x), α₀) if x ∈ G, and v(x) := 0 if x ∉ G.

2. (Integer values and measurability.)
   - β takes integer values, so v(x) ∈ ℤ for every x.
   - G = ⋂_i ⋂_k {x : x_i ≠ ρk} is a countable intersection of open sets, hence measurable.
   - x ↦ z(x) is measurable: each coordinate x ↦ ⌊x_i/ρ⌋ is Int.measurable_floor composed with a continuous map (measurable_pi_iff).
   - w ↦ β(w, α₀) is measurable on the countable discrete space ℤ^n, which has measurable singletons (measurable_of_countable).
   So v = G.indicator(β ∘ (z(·), α₀)) is measurable.

3. (Values on the cubes.) Let F be a face index and x ∈ Q_F ∩ G.
   - By (b), ρF.1_i ≤ x_i ≤ ρ(F.1_i + 1) for each i, and both equalities are impossible because x is good. So F.1_i < x_i/ρ < F.1_i + 1 and ⌊x_i/ρ⌋ = F.1_i (Int.floor_eq_iff). Thus z(x) = F.1.
   - By (a), F.2 = α₀, since order embeddings with equal values are equal. So F = (z(x), α₀) and v(x) = β_F.
   Since L-a.e. point is good (f), ∀ᵐ x ∂(L⌞Q_F), v(x) = β_F (ae_restrict_of_ae together with ae_restrict_mem, Q_F measurable).

4. (Local constancy.) Suppose v(x) ≠ 0. Then x ∈ G; put z := z(x).
   - The open box O := {y : ρz_i < y_i < ρ(z_i + 1) for all i} is a finite intersection of open sets. It contains x: ρz_i ≤ x_i < ρ(z_i + 1) by the floor, and x_i ≠ ρz_i because x is good.
   - Every y ∈ O is good, since an integer k with ρk = y_i would satisfy z_i < k < z_i + 1.
   - Every y ∈ O also satisfies ⌊y_i/ρ⌋ = z_i, so v(y) = β(z, α₀) = v(x).
   Hence v(y) = v(x) for all y in the neighbourhood O of x (IsOpen.mem_nhds).

5. (Integrability.) By (g), step 3 (lintegral_congr_ae on L⌞Q_F), setLIntegral_const and (d):
   ∫⁻ ofReal|v| dL = Σ'_F ∫⁻_{Q_F} ofReal|v| dL = Σ'_F ∫⁻_{Q_F} ofReal|β_F| dL = Σ'_F ofReal|β_F| · ofReal(ρ^n) = Σ'_F ofReal(|β_F| ρ^n) < ∞.
   The last equality is ENNReal.ofReal_mul with |β_F| ≥ 0, and finiteness is the hypothesis. Since v is measurable, v ∈ L¹(L): the lintegral of ‖v‖ₑ, which equals the lintegral of ofReal|v|, is finite.

6. (The current.) By the sibling density_current (Submission.fiw_tb_tda_density_current m v hv) there is Pc ∈ GeometricCurrentOn univ n with Pc(ω) = ∫ v ω_e dL for all ω ∈ D^n(ℝ^n).

7. (Lattice chain identity.) Let ω ∈ D^n(ℝ^n).
   - x ↦ v(x)ω_e(x) is integrable: v ∈ L¹, and ω_e is continuous with compact support, hence bounded and measurable (Integrable.mul_bdd).
   - For each F, by (a) the tuple (EuclideanSpace.single (F.2 j) 1)_j equals e, and μHE[n] = L, so latticeFaceAction ρ F ω = ∫_{Q_F} ω_e dL.
   - By step 3 (integral_congr_ae on L⌞Q_F) and integral_const_mul, ∫_{Q_F} v ω_e dL = ∫_{Q_F} β_F ω_e dL = β_F · latticeFaceAction ρ F ω.
   - By (h) applied to v ω_e: Pc(ω) = ∫ v ω_e dL = Σ'_F ∫_{Q_F} v ω_e dL = Σ'_F β_F · latticeFaceAction ρ F ω.
   This is IsLatticeChain ρ β Pc.

8. (Integer multiplicity.) Apply the sibling locally_constant_im (Submission.fiw_tb_tda_locally_constant_im m Pc v). Its hypotheses hold:
   - v is measurable (step 2);
   - v is integrable (step 5);
   - v is integer-valued (step 2);
   - v is locally constant where it is nonzero (step 4);
   - Pc(ω) = ∫ v ω_e for all ω (step 6).
   Hence Pc is integer multiplicity.

9. Pc and v have all asserted properties: steps 7, 8, 5, 3 and 6. ∎

## Key steps

1. Define v(x) := β(⌊x/ρ⌋, id) at good points (no coordinate in ρℤ) and 0 elsewhere; v is measurable and integer-valued.
2. On each closed cube v = β_F a.e. (good points of the cube have floor index F.1, and F.2 = id), and v is locally constant on the open cubes, hence where it is nonzero.
3. ∫|v| = Σ_F |β_F|ρ^n < ∞ by the cube decomposition (g) and L(Q_F) = ρ^n, so v ∈ L¹.
4. density_current gives Pc(ω) = ∫ v ω_e; the integral decomposition (h) with v = β_F on Q_F gives Pc(ω) = Σ'_F β_F latticeFaceAction ρ F ω.
5. locally_constant_im makes Pc integer multiplicity.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (local-project; project d8d46c9587747dee0751a1f780fcafdba16a3886, mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/.../project/GMT/Ch06/Contract.lean GMT/Ch06/Contract.lean; cmp Contract.lean Submission.lean; git show 48003458:GMT/Ch06/Submission.lean | cmp (all identical: the node base holds only the frozen contract)`
- `sed -n 120,364p GMT/Ch06/Submission.lean (LatticeFaceIndex, latticeFace, latticeFaceAction, IsLatticeChain, IsIntegerMultiplicity, IsRectifiableTriple, tauAction)`
- `grep -n 'def covectorEuclideanNorm|def massAdmissibleOn|def GeometricCurrentOn.massOn|def GeometricCurrentOn.mass|structure GeometricCurrentOn|def TestFormOnConverges|def GeometricCurrentOn.support|def simpleNVector|def wedgeCovectors|abbrev SimonMultiIndex|instance.*GeometricCurrentOn' simongmt/Poincare/SimonGMT (GeometricCurrentOn has only a Zero instance, no Sub)`
- `grep -n 'def blowUpMap|def HasWeightedApproximateTangentSpaceAt|def CountablyRectifiable|countablyRectifiable_range|CountablyRectifiable.mono' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -rn in local-references mathlib: EuclideanSpace.euclideanHausdorffMeasure_eq_volume, AlternatingMap.eq_smul_basis_det, OrthonormalBasis.det_to_matrix_orthonormalBasis_real, aestronglyMeasurable_iUnion_iff, lintegral_iUnion₀, integral_iUnion_ae, setIntegral_eq_integral_of_forall_compl_eq_zero, lintegral_mul_left_eq_self (to_additive lintegral_add_left_eq_self), lintegral_lintegral_swap, PiLp.volume_preserving_ofLp, volume_Icc_pi, exists_least_of_bdd, tendsto_measure_iUnion_atTop, tendsto_measure_iInter_atTop, ofReal_integral_eq_lintegral_ofReal, setLIntegral_mono', mem_cthickening_of_dist_le, EuclideanSpace.dist_eq, StrictMono.eq_id, Integrable.mul_bdd, lintegral_const_mul', Int.measurable_floor, lintegral_indicator₀ (all found)`
- `python3 scan of dag.json (360 nodes): statuses, frozen lean_statement of siblings fiw_tb_rectifiable_support_null and fiw_tb_translation_estimate, accepted declarations and candidate commits; no lean_name containing 'tda'; git log --all --oneline -S fiw_tb_tda_ (no match)`
- `git cat-file -t 52afef6d 5c248501 eefd7c3e c90a4050 e8e708e4 49ba437c 3d98b187 0561b355 d57bd370 635e85e5 (all present)`
- `git show 635e85e5 -- GMT/Ch06/Submission.lean; tail speculative-process-v3.log of root-boundary-rectifiability-a1-top-dim-lattice-approx-a1 (1060-line single theorem, 178,656 of 200,000 heartbeats)`
- `sed parent-supplied-natural-proof.md of root-boundary-rectifiability-a1-top-dim-lattice-approx-a1 and root-integrality-weak-limits-a1-top-dim-a1 (related top-dimensional arguments; not duplicated)`
- `grep -n in /runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean: def _decompose, def _solve_children, def _existing_lean_name_problem, def _install_parent_supplied_child_handoff, def _overlay prerequisites (runtime.py), def check_source_delta (leaf_verification.py), def ensure (store.py)`
- `verifier/gmt-compare.py contract_scope/child_modules; python3 -I /tmp/tda-tools/check.py (validate_lean_statement on all 8 child types: pass)`
- `lean /tmp/tda-decomp/{Stmts,Comparator,Assembly2,Assembly3,Proto,Proto2}.lean with LEAN_PATH = lake-packages-25730c7c builds + workspace .lake build of d8d46c9 (0 errors; Assembly3 #count_heartbeats 10,901)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1/decomposition-v4.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-top-dim-lattice-approx-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-top-dim-lattice-approx-a1/speculative-process-v3.log`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-top-dim-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/math-wiki/submission-fiw-ims-sc-continuous-of-bound.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/swarm-project.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Group/LIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Int/LeastGreatest.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Preorder/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/Floor.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/store.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/tda-decomp/Stmts.lean`
- `/tmp/tda-decomp/Comparator.lean`
- `/tmp/tda-decomp/Assembly2.lean`
- `/tmp/tda-decomp/Assembly3.lean`
- `/tmp/tda-decomp/Proto.lean`
- `/tmp/tda-decomp/Proto2.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) has the frozen Ch06 contract, and this node's base commit 48003458 adds no accepted declarations. Neither the project nor SimonGMT contains any of the following, so they become the 8 children:
- the top-dimensional density lemma;
- integer medians;
- the lattice-cube toolkit;
- the chain current;
- the difference-current mass bound;
- the summed Poincaré bound.

API the child proofs use:
- SimonGMT: GeometricCurrentOn (Zero instance only, so S = X − Pc is built from toCurrent subtraction), massOn/mass via massAdmissibleOn and covectorEuclideanNorm, simpleNVector_apply, wedgeCovectors_apply_det, blowUpMap, HasWeightedApproximateTangentSpaceAt, countablyRectifiable_range and CountablyRectifiable.mono.
- Mathlib: every lemma cited in the child proofs was found at the pinned revision.

Accepted declarations, cited only as adaptation pointers (all commits present locally): lpf_pic_current_of_dominated_density (52afef6d), fiw_ims_sc_continuous_of_bound (5c248501), isoperimetric_coord_box_measure (eefd7c3e), fiw_ims_frame_sign (c90a4050).

Scratch checks:
- all 8 child types elaborate in the comparator scope and pass validate_lean_statement;
- the frozen parent type is proved from them plus the two frozen sibling types (10,901 heartbeats; axioms propext, Classical.choice and Quot.sound, plus sorryAx from the stubs only);
- the riskiest child steps compile as prototypes.
