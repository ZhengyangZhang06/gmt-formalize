# Recursive Lean task

# Simon GMT, Chapter 2: Some Further Preliminaries from Analysis

Prove `GMT.Ch02.main_theorem`, stated in the frozen contract `GMT/Ch02/Contract.lean`, by completing `GMT/Ch02/Submission.lean` (initially a byte copy of the contract). The statement is the conjunction of the chapter's headline results; `GMT/Ch02/README.md` maps each conjunct to the book.

Source: Leon Simon, *Introduction to Geometric Measure Theory* (2014), Chapter 2, printed pages 39–68. Read-only copies for workers: `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt` and `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/simon-gmt.pdf` (printed page = PDF page − 7).

The pinned `simongmt` package (`Poincare.SimonGMT.*`) contains an earlier kernel-checked partial formalization of the book; its proofs may be reused as library lemmas where they apply. Do not rely on its definitions that the chapter README marks as unfaithful. Toolchain Lean v4.35.0-rc3, Mathlib 25730c7c. Every definition used by the statement must stay byte-identical; only standard axioms are allowed.
