$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1980_b4: a finite family of 1066 subsets, each containing more than
  half of a finite set, has a 10-element hitting set. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  The index set ( 0 ..^ 1066 ) is {0, ..., 1065}, matching the Lean source
  and differing from Isabelle's {1, ..., 1066} only by a bijective relabeling.
  The function condition A : ( 0 ..^ 1066 ) --> ~P X states that every A ` i
  is a subset of X. SetMM's Fin and # give finiteness and finite cardinality;
  division by 2 is the rational comparison used in the source statements.

  The set Y and each hitting element y remain existentially quantified at
  their source scopes. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof statement.
$)

${
  $d f i s t y $.

  putnambench-putnam-1980-b4 $a |- A. s A. f
    (
      (
        (
          s e. Fin
          /\
          ; 1 0 <_ ( # ` s )
        )
        /\
        (
          f : ( 0 ..^ ; ; ; 1 0 6 6 ) --> ~P s
          /\
          A. i e. ( 0 ..^ ; ; ; 1 0 6 6 )
            ( ( # ` s ) / 2 ) < ( # ` ( f ` i ) )
        )
      )
      ->
      E. t
        (
          (
            t e. Fin
            /\
            t C_ s
          )
          /\
          (
            ( # ` t ) = ; 1 0
            /\
            A. i e. ( 0 ..^ ; ; ; 1 0 6 6 )
              E. y e. t y e. ( f ` i )
          )
        )
    )
  $.
$}
