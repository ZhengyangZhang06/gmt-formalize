# SimonGMT library

Lean 4 (`v4.35.0-rc3`) and Mathlib (`25730c7c`) formalization of parts of Leon Simon,
*Introduction to Geometric Measure Theory* (2014 Tsinghua notes), reused as library
infrastructure by the chapter problems on this repository's `main` branch.
Only modules imported by `Poincare/SimonGMT.lean` are built. Some definitions here are
known to be unfaithful (for example `Chapter04.RectifiableVarifold` stores the a.e. existence
of approximate tangents as a field); the chapter contracts do not rely on those.
