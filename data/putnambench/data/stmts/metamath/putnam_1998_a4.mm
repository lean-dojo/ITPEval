$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1998_a4: the indices for which eleven divides the decimal word
  sequence generated from 0 and 1 by concatenating the preceding two words.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  a ranges over all sequences of finite words of nonnegative integers, exactly
  representing the source type nat -> list nat without restricting words to
  finite tables or to a smaller digit type. The recurrence is imposed at every
  positive index, with singleton words representing the initial lists [0] and
  [1].

  For a word W, the finite sum of W(i) times 10^i is Isabelle's from_digits
  fold. Lean and Rocq use the reverse coefficient order for the ordinary
  left-to-right decimal value. Modulo 11, since 10 is congruent to -1,
  reversing any finite coefficient word multiplies its alternating sum by a
  sign, so the two values are divisible by 11 simultaneously. The right-hand
  set is Rocq's explicit solution n congruent to 1 modulo 6; such indices are
  automatically positive. The final declaration is a single unproved $a
  corpus statement, and this database contains no $p proof statement.
$)

${
  $d a i n $.

  putnambench-putnam-1998-a4 $a |-
    A. a e. ( Word NN0 ^m NN0 )
      (
        (
          ( a ` 1 ) = <" 0 ">
          /\
          (
            ( a ` 2 ) = <" 1 ">
            /\
            A. n e. NN
              ( a ` ( n + 2 ) ) =
              ( ( a ` ( n + 1 ) ) ++ ( a ` n ) )
          )
        )
        ->
        {
          n e. NN |
            ; 1 1
            ||
            sum_ i e. ( 0 ..^ ( # ` ( a ` n ) ) )
              ( ( ( a ` n ) ` i ) x. ( ; 1 0 ^ i ) )
        }
        =
        { n e. NN0 | ( n mod 6 ) = 1 }
      )
  $.
$}
