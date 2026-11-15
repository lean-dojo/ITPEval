$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.eq_minus_S_pred (logipedia__metamath__nat.eq_minus_S_pred), catalog
  title "nat.eq_minus_S_pred": subtracting the successor of a natural number
  from another natural number equals the predecessor of subtracting the
  original number. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is the source natural-number domain, and adding one represents the
  source successor. For natural numbers u and v, the term

    if ( v <_ u , u - v , 0 )

  is exactly the source total subtraction nat.minus u v. The right-hand
  conditional exactly represents nat.pred: it returns zero at zero and
  subtracts one otherwise. Native equality represents source natural-number
  equality. The restricted universal quantifiers preserve the source binder
  order and scopes, with no assumptions. The final declaration is Metamath's
  native unproved $a statement encoding; this artifact adds no $p proof
  declaration.
$)

logipedia-nat-eq-minus-s-pred $a |-
  A. n e. NN0
    A. m e. NN0
      if (
        ( m + 1 ) <_ n ,
        ( n - ( m + 1 ) ) ,
        0
      )
      =
      if (
        if (
          m <_ n ,
          ( n - m ) ,
          0
        )
        =
        0 ,
        0 ,
        (
          if (
            m <_ n ,
            ( n - m ) ,
            0
          )
          -
          1
        )
      )
$.
