$(
  Statement-only formalization of Thousand Theorems corpus artifact Q716171
  (thousand-theorems__metamath__Q716171), catalog title
  "Erdos-Ginzburg-Ziv theorem" (ASCII rendering):
  among values in Z/nZ assigned to any finite set of at least 2 * n - 1
  indices, with values not necessarily distinct, there is an n-element
  subset of indices whose values sum to zero. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  An arbitrary Lean index type is represented by the set I, its Finset s by
  a finite subset S of I, and a : I -> ZMod n by a function into the base of
  SetMM's commutative ring Z/nZ. This ring also has the correct n = 0 case.

  The conditional expression is exactly natural-number truncated subtraction:
  it is 0 when n = 0 and otherwise is the integer 2 * n - 1. The internally
  quantified finite subset T preserves the source witness, and Z/nZ gsum is
  the finite additive sum in the same residue-class ring.

  The following declaration is the single unproved $a corpus statement; this
  root statement file contains no $p proof statement.
$)

${
  $d I S T a i n $.

  thousand-theorems-q716171-erdos-ginzburg-ziv $a |-
    A. n e. NN0
      A. I e. _V
        A. S e. ( ~P I i^i Fin )
          A. a
            (
              a : I --> ( Base ` ( Z/nZ ` n ) )
              ->
              (
                if ( n = 0 , 0 , ( ( 2 x. n ) - 1 ) )
                <_
                ( # ` S )
                ->
                E. T e. ( ~P S i^i Fin )
                  (
                    ( # ` T ) = n
                    /\
                    (
                      ( Z/nZ ` n ) gsum
                        ( i e. T |-> ( a ` i ) )
                    )
                    =
                    ( 0g ` ( Z/nZ ` n ) )
                  )
              )
            )
  $.
$}
