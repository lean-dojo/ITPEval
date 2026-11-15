$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1970_b3: a closed subset of the real plane contained between two
  vertical lines has a closed projection onto the second coordinate axis.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P70B3R2 is the real coordinate plane and P70B3Top is its standard finite
  product topology. The final assertion quantifies over every subset S of
  that plane and all real a and b. Its set-builder is exactly the image of S
  under the second-coordinate projection, with the witness kept internally
  existentially quantified. The declaration is an unproved $a statement;
  this database contains no $p proof statement.
$)

$c P70B3I P70B3R2 P70B3Top $.

p70b3-index-syntax $a class P70B3I $.
p70b3-plane-syntax $a class P70B3R2 $.
p70b3-topology-syntax $a class P70B3Top $.

p70b3-index-definition $a |- P70B3I = ( 1 ... 2 ) $.

p70b3-plane-definition $a |- P70B3R2 = ( RR ^m P70B3I ) $.

p70b3-topology-definition $a |- P70B3Top =
  (
    Xt_ `
      ( P70B3I X. { ( topGen ` ran (,) ) } )
  )
$.

${
  $d S a b s y $.

  putnambench-putnam-1970-b3 $a |- A. S e. ~P P70B3R2
    A. a e. RR A. b e. RR
      (
        (
          a < b
          /\
          (
            A. s e. S
              (
                a < ( s ` 1 )
                /\
                ( s ` 1 ) < b
              )
            /\
            S e. ( Clsd ` P70B3Top )
          )
        )
        ->
        { y e. RR |
          E. s e. S y = ( s ` 2 )
        }
        e. ( Clsd ` ( TopOpen ` RRfld ) )
      )
  $.
$}
