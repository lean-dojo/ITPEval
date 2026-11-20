import Mathlib.Computability.Language
import Cslib.Computability.Languages.Language

/-- Over an empty alphabet the only possible word is the empty list. -/
theorem emptyAlphabetLanguage (L : Language Empty) : L = 0 ∨ L = 1 :=
  Language.eq_zero_or_one_ofIsEmpty L
