$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2022_b4: classification of lengths of cyclic sequences of distinct
  real numbers whose consecutive triples form three-term arithmetic
  progressions when increasingly ordered. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P22B4AP3 expands the source predicate ap3. For an increasing triple
  x < y < z, the six displayed alternatives say exactly that its underlying
  three-element set is { A, B, C }; the conclusion says that y is the
  arithmetic mean of its neighbors.

  P22B4XProg expands the source predicate xprog. RR ^m NN0 preserves the
  source's total real sequence, while 0 ..^ N is the Fin N index carrier.
  Pairwise distinctness is imposed on precisely those N entries, and mod N
  gives the two cyclic successor indices.

  Inlining these two predicates and the annotated solution set makes the
  final biconditional definitionally equivalent to the ground-truth theorem:
  under N >= 4, such a sequence exists exactly when 3 divides N and N >= 9.
  Every declaration is an unproved $a statement encoding; this database
  contains no $p proof declaration.
$)

$c P22B4AP3 P22B4XProg $.

p22b4-ap3-syntax $a wff ( P22B4AP3 A B C ) $.
p22b4-xprog-syntax $a wff ( P22B4XProg N A ) $.

${
  $d A B C x y z $.

  p22b4-ap3-definition $a |- (
    ( P22B4AP3 A B C )
    <->
    A. x e. RR A. y e. RR A. z e. RR
      (
        (
          (
            x < y
            /\
            y < z
          )
          /\
          (
            (
              (
                A = x
                /\
                B = y
              )
              /\
              C = z
            )
            \/
            (
              (
                A = x
                /\
                B = z
              )
              /\
              C = y
            )
            \/
            (
              (
                A = y
                /\
                B = x
              )
              /\
              C = z
            )
            \/
            (
              (
                A = y
                /\
                B = z
              )
              /\
              C = x
            )
            \/
            (
              (
                A = z
                /\
                B = x
              )
              /\
              C = y
            )
            \/
            (
              (
                A = z
                /\
                B = y
              )
              /\
              C = x
            )
          )
        )
        ->
        ( y - x ) = ( z - y )
      )
  ) $.
$}

${
  $d A N i j $.

  p22b4-xprog-definition $a |- (
    ( P22B4XProg N A )
    <->
    (
      A. i e. ( 0 ..^ N )
        A. j e. ( 0 ..^ N )
          (
            i =/= j
            ->
            ( A ` i ) =/= ( A ` j )
          )
      /\
      A. i e. ( 0 ..^ N )
        (
          P22B4AP3
          ( A ` i )
          ( A ` ( ( i + 1 ) mod N ) )
          ( A ` ( ( i + 2 ) mod N ) )
        )
    )
  ) $.
$}

${
  $d N x $.

  putnambench-putnam-2022-b4 $a |- A. N e. NN0
    (
      4 <_ N
      ->
      (
        E. x e. ( RR ^m NN0 )
          ( P22B4XProg N x )
        <->
        (
          3 || N
          /\
          9 <_ N
        )
      )
    )
  $.
$}
