$(
  Statement-only formalization of Thousand Theorems corpus artifact Q2226786
  (thousand-theorems__metamath__Q2226786), "Sperner's theorem": every finite
  antichain of subsets of a finite set has cardinality at most the central
  binomial coefficient. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A finite type is represented by an arbitrary finite set A. A Finset of
  Finsets over that type is represented by a finite family F contained in
  the power set of A. The restricted universal quantifiers state exactly
  that inclusion between two members of F forces equality, which is the
  source IsAntichain hypothesis.

  The floor of ( # ` A ) / 2 is natural-number division by two, so the right
  side is the same middle-layer binomial coefficient as in the Lean source.
  The following declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d A F x y $.

  thousand-theorems-q2226786-sperner $a |-
    A. A e. Fin
      A. F e. Fin
        (
          (
            F C_ ~P A
            /\
            A. x e. F A. y e. F
              ( x C_ y -> x = y )
          )
          ->
          ( # ` F )
            <_
          (
            ( # ` A )
            _C
            ( |_ ` ( ( # ` A ) / 2 ) )
          )
        )
  $.
$}
