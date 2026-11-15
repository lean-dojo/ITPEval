$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2000_a2: above every integer cutoff, three consecutive integers
  exist that are each sums of two integer squares. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  The assertion directly follows the Isabelle formulation, with the cutoff,
  the three consecutive values, and all six square witnesses in ZZ. This is
  equivalent to the Lean formulation with natural cutoffs and natural square
  witnesses: absolute values replace integer square witnesses by natural
  ones, and the case of cutoff zero supplies a positive triple above every
  negative integer cutoff. It is also equivalent to Rocq's non-strict cutoff
  form by shifting the universally quantified cutoff by one.

  Every witness remains internally existentially quantified. The final
  declaration is the single unproved $a corpus statement; this database
  contains no $p proof statement.
$)

${
  $d a b c d e f m n $.

  putnambench-putnam-2000-a2 $a |- A. n e. ZZ
    E. m e. ZZ
      (
        n < m
        /\
        E. a e. ZZ E. b e. ZZ
          E. c e. ZZ E. d e. ZZ
            E. e e. ZZ E. f e. ZZ
              (
                m = ( ( a ^ 2 ) + ( b ^ 2 ) )
                /\
                (
                  ( m + 1 ) = ( ( c ^ 2 ) + ( d ^ 2 ) )
                  /\
                  ( m + 2 ) = ( ( e ^ 2 ) + ( f ^ 2 ) )
                )
              )
      )
  $.
$}
