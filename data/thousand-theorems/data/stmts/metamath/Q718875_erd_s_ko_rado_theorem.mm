$(
  Statement-only formalization of Thousand Theorems corpus artifact Q718875
  (thousand-theorems__metamath__Q718875),
  "Erd&odblac;s&ndash;Ko&ndash;Rado theorem": an intersecting family of
  uniformly r-sized subsets of an n-element set, with r at most the natural
  quotient n / 2, has cardinality at most n - 1 choose r - 1. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  The finite type Fin n is represented by the half-open natural interval
  0 ..^ n. Thus F is exactly a finite family of subsets of Fin n. The two
  restricted universal quantifiers state that all members have cardinality r
  and that every pair has nonempty intersection.

  Floor of n / 2 is natural-number division by two. Each conditional
  predecessor is natural-number truncated subtraction, including the n = 0
  and r = 0 cases from the Lean source. The following declaration is the
  single unproved $a corpus statement; this database contains no $p proof
  statement.
$)

${
  $d F n r x y $.

  thousand-theorems-q718875-erdos-ko-rado $a |-
    A. n e. NN0
      A. r e. NN0
        A. F e. Fin
          (
            (
              (
                F C_ ~P ( 0 ..^ n )
                /\
                A. x e. F ( # ` x ) = r
              )
              /\
              (
                A. x e. F A. y e. F
                  ( x i^i y ) =/= (/)
                /\
                r <_ ( |_ ` ( n / 2 ) )
              )
            )
            ->
            ( # ` F )
              <_
            (
              if ( n = 0 , 0 , ( n - 1 ) )
              _C
              if ( r = 0 , 0 , ( r - 1 ) )
            )
          )
  $.
$}
