# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_triple-a1`
- Child DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_triple-a1.frame_orthonormal-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 10(c)(i) of the parent proof (orthonormality of τ̃), using the inner-product formula (F3).

Notation. equiv_n := EuclideanSpace.equiv (Fin n) ℝ; Φ(a, u) := equiv_{P+1}⁻¹(Fin.cons a (equiv_P u)) for a ∈ ℝ, u ∈ ℝ^P, so ι(v) = Φ(0, v); ⟨·,·⟩ is the Euclidean inner product.

1. (F3) For a, b ∈ ℝ and u, w ∈ ℝ^P, ⟨Φ(a,u), Φ(b,w)⟩ = ab + ⟨u, w⟩. Indeed the inner product of EuclideanSpace is the sum over coordinates, ⟨x, z⟩ = Σ_{i ∈ Fin (P+1)} x_i z_i (PiLp.inner_apply; for reals ⟨r, t⟩ = t·r). Split the sum with Fin.sum_univ_succ: the i = 0 term is a·b (coordinate 0 of Φ(a,u) is a by Fin.cons_zero) and the i = k.succ terms are u_k w_k (Fin.cons_succ), whose sum is ⟨u, w⟩ (PiLp.inner_apply again; commutativity of multiplication).
2. (e₀ in coordinates.) e₀ = Φ(1, 0): apply the injective map equiv_{P+1} and compare coordinates (Fin.cases): coordinate 0 of e₀ is 1 and coordinate k.succ is 0, and the same holds for Fin.cons 1 (equiv_P 0).
3. (Orthonormality criterion.) By orthonormal_iff_ite, τ̃ is orthonormal iff ⟨τ̃_i, τ̃_j⟩ = (if i = j then 1 else 0) for all i, j ∈ Fin (m+1), and the hypothesis gives ⟨τ_k, τ_l⟩ = (if k = l then 1 else 0) for k, l ∈ Fin m. Note τ̃_0 = e₀ = Φ(1, 0) (Fin.cons_zero, Step 2) and τ̃_{k.succ} = Φ(0, τ_k) (Fin.cons_succ).
4. (Case analysis by Fin.cases on i and j.) (i = j = 0) ⟨Φ(1,0), Φ(1,0)⟩ = 1·1 + ⟨0,0⟩ = 1. (i = 0, j = l.succ) ⟨Φ(1,0), Φ(0,τ_l)⟩ = 1·0 + ⟨0, τ_l⟩ = 0, and 0 ≠ l.succ (Fin.succ_ne_zero), so the right side is 0. (i = k.succ, j = 0) ⟨Φ(0,τ_k), Φ(1,0)⟩ = 0·1 + ⟨τ_k, 0⟩ = 0, and k.succ ≠ 0. (i = k.succ, j = l.succ) ⟨Φ(0,τ_k), Φ(0,τ_l)⟩ = 0·0 + ⟨τ_k, τ_l⟩ = (if k = l then 1 else 0) = (if k.succ = l.succ then 1 else 0) (Fin.succ_inj). Hence τ̃ is orthonormal. ∎

Formalization aid. The following tactic proof, placed after `theorem Submission.iwl_cr_ip_pt_frame_orthonormal : (<the frozen Lean type of this child, verbatim>) := by`, was kernel-checked in the contract scope (namespace GMT.Ch06 with the contract's opens) after import GMT.Ch06.Submission at the frozen commit d8d46c9 with the pinned toolchain v4.35.0-rc3 / Mathlib 25730c7c; #print axioms = [propext, Classical.choice, Quot.sound]. It uses no helper declarations.
  intro P m τ hτ
  rw [orthonormal_iff_ite] at hτ ⊢
  have hinner : ∀ (a b : ℝ) (u w : Eucl P),
      inner ℝ ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons a (EuclideanSpace.equiv (Fin P) ℝ u)))
        ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons b (EuclideanSpace.equiv (Fin P) ℝ w))) =
      a * b + inner ℝ u w := by
    intro a b u w
    rw [PiLp.inner_apply, PiLp.inner_apply, Fin.sum_univ_succ]
    simp [mul_comm]
  have he : (EuclideanSpace.single 0 1 : Eucl (P + 1)) =
      (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons 1 (EuclideanSpace.equiv (Fin P) ℝ 0)) := by
    apply (EuclideanSpace.equiv (Fin (P + 1)) ℝ).injective
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simp only [Fin.cons_zero, he, hinner]
    simp
  · simp only [Fin.cons_zero, Fin.cons_succ, he, hinner]
    simp [(Fin.succ_ne_zero j).symm]
  · simp only [Fin.cons_zero, Fin.cons_succ, he, hinner]
    simp [Fin.succ_ne_zero i]
  · simp only [Fin.cons_succ, hinner, zero_mul, zero_add, Fin.succ_inj]
    exact hτ i j

## Key steps

1. Inner product formula ⟨Φ(a,u), Φ(b,w)⟩ = ab + ⟨u,w⟩ via PiLp.inner_apply and Fin.sum_univ_succ.
2. e₀ = Φ(1, 0) by comparing coordinates.
3. orthonormal_iff_ite and Fin.cases on both indices; the (succ, succ) case reduces to orthonormality of τ via Fin.succ_inj.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean GMT/Ch06/Contract.lean; sha256sum GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean`
- `python3 -I: dag.json status/lean_name/lean_statement of all root.integrality_weak_limits-a1* nodes (incl. hausdorff_product-a1.* and interval_product-a1.* siblings) and the set of all reserved lean_names`
- `grep -rlo 'iwl_cr_ip_pt_' .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca (no match); grep -rho 'iwl_cr_ip_[A-Za-z_]*' dag.json`
- `python3 -I: parent nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a1/decomposition-v1.json (sibling types and the slice_formula/measure_identity formalization aids)`
- `grep -n 'def CountablyRectifiable|countablyRectifiable_of_measure_zero|CountablyRectifiable.mono|def HasWeightedApproximateTangentSpaceAt' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean; grep -n 'abbrev NVector|def simpleNVector|simpleNVector_apply' Chapter06/FormsDuality.lean; 'abbrev Covector' Chapter06/Forms.lean`
- `rg -n 'lemma Integrable.comp_snd|theorem quasiMeasurePreserving_snd|NullMeasurableSet.preimage|aestronglyMeasurable_map_iff|integrable_map_iff|Homeomorph.measurableEmbedding|theorem restrict_map|theorem prod_restrict|theorem prod_zero|theorem restrict_eq_zero|isFiniteMeasure_restrict_Ioo|AbsolutelyContinuous.mk|protected theorem prodMk|real_inner_comm' in the snapshot Mathlib`
- `python3 -I /tmp/ptdec-q7k2/scripts/gen.py (lean_contract.validate_lean_statement and gmt-compare.py child_modules on the 5 child types; MP/slab/frame fragments asserted verbatim against the parent and sibling frozen types)`
- `lake env lean /tmp/ptdec-q7k2/lean/Challenge_{slab_measure,slab_transfer,cylinder_null_measurable,cylinder_rectifiable,frame_orthonormal}.lean (comparator challenge layout)`
- `lake env lean /tmp/ptdec-q7k2/lean/Children.lean (complete proofs of the 5 children; #print axioms)`
- `lake env lean /tmp/ptdec-q7k2/lean/Assembly.lean and /tmp/ptdec-q7k2/lean/Full.lean (frozen parent type from the 5 children and the product_tangent stub; #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-6184ff8144/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-6184ff8144/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/QuasiMeasurePreserving.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/AbsolutelyContinuous.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/ptdec-q7k2/lean/Children.lean`
- `/tmp/ptdec-q7k2/lean/Full.lean`
- `/tmp/ptdec-q7k2/lean/Assembly.lean`

Snapshot: project d8d46c95, Mathlib 25730c7c. The snapshot's Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean (sha256 ea3ee0dd…853d).

No existing declaration states the slab measure identity, the slab transfer, cylinder null-measurability, cylinder rectifiability or the extended-frame orthonormality. The only related node is iwl_cr_hp_cylinder_null (decomposing, not accepted, different type), so nothing is reused. The names iwl_cr_ip_pt_* are unreserved.

SimonGMT Chapter03/Rectifiable.lean supplies CountablyRectifiable (l.34), countablyRectifiable_of_measure_zero (l.45), CountablyRectifiable.mono (l.55) and HasWeightedApproximateTangentSpaceAt (l.330). FormsDuality.lean supplies NVector, simpleNVector and simpleNVector_apply.

Mathlib supplies every tool used:
- Integrable.comp_snd (Integral/Prod.lean:285, needs SFinite ν);
- Measure.quasiMeasurePreserving_snd (Measure/Prod.lean:470);
- NullMeasurableSet.preimage (QuasiMeasurePreserving.lean:134) and Measure.AbsolutelyContinuous.mk;
- MeasurableEmbedding.aestronglyMeasurable_map_iff (AEStronglyMeasurable.lean:668) and MeasurableEmbedding.integrable_map_iff (Integrable.lean:374);
- Homeomorph.measurableEmbedding (BorelSpace/Basic.lean:567);
- Measure.restrict_map, Measure.restrict_eq_zero, Measure.prod_restrict and Measure.prod_zero;
- Real.isFiniteMeasure_restrict_Ioo, LipschitzWith.prodMk, ContinuousLinearMap.lipschitzWith, orthonormal_iff_ite and PiLp.inner_apply.
LipschitzWith.prodMap does not exist at this pin; prodMk is used instead.

Lean checks:
- All 5 child types elaborate in the comparator challenge layout.
- All 5 children are fully proved with axioms [propext, Classical.choice, Quot.sound].
- The frozen parent type is proved from them plus the sibling product_tangent stub; that stub is the only sorry.

Public sources for the mathematics: Simon, Introduction to GMT, Ch. 6, 3.2(2) (product current), and Federer, GMT 3.2.23 (product formula behind (MP)).
