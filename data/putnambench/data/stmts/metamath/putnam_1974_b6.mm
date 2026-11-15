$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1974_b6: the numbers of subsets of the integers 1 through 1000
  having cardinality congruent to 0, 1, and 2 modulo 3. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  The class 1 ... 1000 is the inclusive integer interval from the sources.
  Each restricted class abstraction ranges over its full powerset and filters
  subsets by the remainder of their finite cardinality modulo 3. Replacing the
  source count variables by these three defining cardinalities turns the tuple
  conclusion into the equivalent conjunction below.

  Since 3 divides 2^1000 - 1, set.mm's exact division agrees with the natural
  quotient in the Rocq source. The final declaration is the single unproved
  $a corpus statement; this database contains no $p proof statement.
$)

putnambench-putnam-1974-b6 $a |- (
  (
    # `
      {
        S e. ~P ( 1 ... ; ; ; 1 0 0 0 )
        |
        ( ( # ` S ) mod 3 ) = 0
      }
  )
  =
  ( ( ( 2 ^ ; ; ; 1 0 0 0 ) - 1 ) / 3 )
  /\
  (
    (
      # `
        {
          S e. ~P ( 1 ... ; ; ; 1 0 0 0 )
          |
          ( ( # ` S ) mod 3 ) = 1
        }
    )
    =
    ( ( ( 2 ^ ; ; ; 1 0 0 0 ) - 1 ) / 3 )
    /\
    (
      (
        # `
          {
            S e. ~P ( 1 ... ; ; ; 1 0 0 0 )
            |
            ( ( # ` S ) mod 3 ) = 2
          }
      )
      =
      ( ( ( ( 2 ^ ; ; ; 1 0 0 0 ) - 1 ) / 3 ) + 1 )
    )
  )
) $.
