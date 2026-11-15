$(
  Statement-only formalization of the Logipedia corpus artifact nat.S_pred
  (logipedia__metamath__nat.S_pred), catalog title "nat.S_pred": every
  positive natural number is the successor of its predecessor. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is the source natural-number domain. The conditional is exactly the
  source total predecessor: it is zero at zero and n - 1 otherwise. Adding
  one is the source successor. The hypothesis 0 < n is the source assumption
  nat.lt nat.O n, and native equality represents source natural-number
  equality. The final declaration is Metamath's native unproved $a statement
  encoding. This artifact adds no $p proof declaration.
$)

logipedia-nat-s-pred $a |-
  A. n e. NN0
    (
      0 < n
      ->
      (
        if (
          n = 0 ,
          0 ,
          ( n - 1 )
        )
        +
        1
      )
      =
      n
    )
$.
