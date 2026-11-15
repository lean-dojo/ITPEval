$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.le_plus_minus_m_m
  (logipedia__metamath__nat.le_plus_minus_m_m), catalog title
  "nat.le_plus_minus_m_m": every natural number is at most its truncated
  difference with another natural number plus that number. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is the source natural-number domain. For natural numbers n and m, the
  term if ( m <_ n , n - m , 0 ) is exactly the source total subtraction
  nat.minus n m: ordinary subtraction when m is at most n, and zero otherwise.
  SetMM addition and non-strict order represent nat.plus and nat.le. The two
  restricted universal quantifiers preserve the source binder order and
  scopes. The final declaration is Metamath's native unproved $a statement
  encoding; this artifact adds no $p proof declaration.
$)

logipedia-nat-le-plus-minus-m-m $a |-
  A. n e. NN0
    A. m e. NN0
      n <_
      (
        if (
          m <_ n ,
          ( n - m ) ,
          0
        )
        +
        m
      )
$.
