$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/queens_NQueensSets_t3qtvc: the finite-integer-set verification
  condition for one recursive iteration of the N-queens solution enumerator,
  including its loop invariant and recursive postcondition. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  NQ3FSet is exactly the source carrier of finite sets of integers, while
  all column maps and solution arrays are total maps on the full unbounded
  integer domain ZZ. NQ3Update is exact pointwise function update, and
  NQ3MinElt is restricted definite description of the unique least member
  of a finite nonempty integer set.

  NQ3EqPrefix, NQ3PartialSolution, NQ3LtSolution, and NQ3Sorted are direct
  biconditional definitions of the predicates in the source Solution theory.
  The remaining named predicates factor the call precondition, loop
  invariant, recursive-call contract, and final postcondition without
  changing any quantifier scope. Finite-set insertion, deletion, difference,
  subset, cardinality, and the succ/pred specifications use their exact
  SetMM counterparts. Proposition-valued conditionals are represented by
  equivalent pairs of exhaustive guarded implications.

  Expanding the definitions recovers the original Why3 verification
  condition and the agreeing Lean, Rocq, and Isabelle exports. Every
  auxiliary $a below is syntax or an explicit faithful definition required
  by the target. The final $a declaration is Metamath's native unproved
  statement encoding; this database contains no $p proof declaration.
$)

$c
  NQ3FSet NQ3Update NQ3MinElt
  NQ3EqPrefix NQ3PartialSolution NQ3LtSolution NQ3Sorted
  NQ3AvailableColumns NQ3UnusedAscending NQ3UnusedDescending
  NQ3CallPreconditions NQ3InsertCondition NQ3RemoveCondition
  NQ3PredCondition NQ3SuccCondition NQ3CardinalityDecrease
  NQ3LoopInvariant NQ3Postcondition NQ3RecursiveIteration
  NQ3LoopResult NQ3AllLoopStates
$.

nq3-fset-syntax $a class NQ3FSet $.
nq3-update-syntax $a class ( NQ3Update A B C ) $.
nq3-min-elt-syntax $a class ( NQ3MinElt A ) $.

nq3-eq-prefix-syntax $a wff ( NQ3EqPrefix A B C ) $.
nq3-partial-solution-syntax
  $a wff ( NQ3PartialSolution A B C ) $.
nq3-lt-solution-syntax
  $a wff ( NQ3LtSolution A B C ) $.
nq3-sorted-syntax $a wff ( NQ3Sorted A B C D ) $.
nq3-available-columns-syntax
  $a wff ( NQ3AvailableColumns A B C D ) $.
nq3-unused-ascending-syntax
  $a wff ( NQ3UnusedAscending A B C ) $.
nq3-unused-descending-syntax
  $a wff ( NQ3UnusedDescending A B C ) $.
nq3-call-preconditions-syntax
  $a wff ( NQ3CallPreconditions A B C D E F G ) $.
nq3-insert-condition-syntax
  $a wff ( NQ3InsertCondition A B C ) $.
nq3-remove-condition-syntax
  $a wff ( NQ3RemoveCondition A B C ) $.
nq3-pred-condition-syntax
  $a wff ( NQ3PredCondition A B ) $.
nq3-succ-condition-syntax
  $a wff ( NQ3SuccCondition A B ) $.
nq3-cardinality-decrease-syntax
  $a wff ( NQ3CardinalityDecrease A B ) $.
nq3-loop-invariant-syntax
  $a wff ( NQ3LoopInvariant A B C D E F G H I J K L M ) $.
nq3-postcondition-syntax
  $a wff ( NQ3Postcondition A B C D E F G H ) $.
nq3-recursive-iteration-syntax
  $a wff ( NQ3RecursiveIteration A B C D E F G H I J K L M N ) $.
nq3-loop-result-syntax
  $a wff ( NQ3LoopResult A B C D E F G H I J K L M ) $.
nq3-all-loop-states-syntax
  $a wff ( NQ3AllLoopStates A B C D E F G H I ) $.

${
  nq3-fset-definition $a |- NQ3FSet = {
    x e. Fin | x C_ ZZ
  } $.
$}

${
  $d x A B C $.

  nq3-update-definition $a |- (
    NQ3Update A B C
  ) = (
    x e. ZZ |->
      if ( x = B , C , ( A ` x ) )
  ) $.
$}

${
  $d d x A $.

  nq3-min-elt-definition $a |- (
    NQ3MinElt A
  ) = (
    iota_ d e. A A. x e. A d <_ x
  ) $.
$}

${
  $d i A B C $.

  nq3-eq-prefix-definition $a |- (
    NQ3EqPrefix A B C
  ) <-> (
    A. i e. ZZ
      (
        (
          0 <_ i
          /\
          i < C
        )
        ->
        ( A ` i ) = ( B ` i )
      )
  ) $.
$}

${
  $d i j A B C $.

  nq3-partial-solution-definition $a |- (
    NQ3PartialSolution A B C
  ) <-> (
    A. i e. ZZ
      (
        (
          0 <_ i
          /\
          i < B
        )
        ->
        (
          (
            0 <_ ( C ` i )
            /\
            ( C ` i ) < A
          )
          /\
          A. j e. ZZ
            (
              (
                0 <_ j
                /\
                j < i
              )
              ->
              (
                ( C ` i ) =/= ( C ` j )
                /\
                (
                  ( ( C ` i ) - ( C ` j ) ) =/= ( i - j )
                  /\
                  ( ( C ` i ) - ( C ` j ) ) =/= ( j - i )
                )
              )
            )
        )
      )
  ) $.
$}

${
  $d i A B C $.

  nq3-lt-solution-definition $a |- (
    NQ3LtSolution A B C
  ) <-> (
    E. i e. ZZ
      (
        (
          0 <_ i
          /\
          i < A
        )
        /\
        (
          ( NQ3EqPrefix B C i )
          /\
          ( B ` i ) < ( C ` i )
        )
      )
  ) $.
$}

${
  $d i j A B C D $.

  nq3-sorted-definition $a |- (
    NQ3Sorted A B C D
  ) <-> (
    A. i e. ZZ A. j e. ZZ
      (
        (
          B <_ i
          /\
          (
            i < j
            /\
            j < C
          )
        )
        ->
        ( NQ3LtSolution A ( D ` i ) ( D ` j ) )
      )
  ) $.
$}

${
  $d i j A B C D $.

  nq3-available-columns-definition $a |- (
    NQ3AvailableColumns A B C D
  ) <-> (
    A. i e. ZZ
      (
        i e. C
        <->
        (
          (
            0 <_ i
            /\
            i < A
          )
          /\
          A. j e. ZZ
            (
              (
                0 <_ j
                /\
                j < B
              )
              ->
              ( D ` j ) =/= i
            )
        )
      )
  ) $.
$}

${
  $d i j A B C $.

  nq3-unused-ascending-definition $a |- (
    NQ3UnusedAscending A B C
  ) <-> (
    A. i e. ZZ
      (
        0 <_ i
        ->
        (
          -. i e. B
          <->
          A. j e. ZZ
            (
              (
                0 <_ j
                /\
                j < A
              )
              ->
              ( C ` j ) =/= ( ( i + j ) - A )
            )
        )
      )
  ) $.
$}

${
  $d i j A B C $.

  nq3-unused-descending-definition $a |- (
    NQ3UnusedDescending A B C
  ) <-> (
    A. i e. ZZ
      (
        0 <_ i
        ->
        (
          -. i e. B
          <->
          A. j e. ZZ
            (
              (
                0 <_ j
                /\
                j < A
              )
              ->
              ( C ` j ) =/= ( ( i + A ) - j )
            )
        )
      )
  ) $.
$}

nq3-call-preconditions-definition $a |- (
  NQ3CallPreconditions A B C D E F G
) <-> (
  0 <_ B
  /\
  (
    ( B + ( # ` C ) ) = A
    /\
    (
      0 <_ D
      /\
      (
        ( NQ3AvailableColumns A B C E )
        /\
        (
          ( NQ3UnusedAscending B F E )
          /\
          (
            ( NQ3UnusedDescending B G E )
            /\
            ( NQ3PartialSolution A B E )
          )
        )
      )
    )
  )
) $.

nq3-insert-condition-definition $a |- (
  NQ3InsertCondition A B C
) <-> (
  C = ( B u. { A } )
  /\
  (
    (
      A e. B
      ->
      ( # ` C ) = ( # ` B )
    )
    /\
    (
      -. A e. B
      ->
      ( # ` C ) = ( ( # ` B ) + 1 )
    )
  )
) $.

nq3-remove-condition-definition $a |- (
  NQ3RemoveCondition A B C
) <-> (
  C = ( B \ { A } )
  /\
  (
    (
      A e. B
      ->
      ( # ` C ) = ( ( # ` B ) - 1 )
    )
    /\
    (
      -. A e. B
      ->
      ( # ` C ) = ( # ` B )
    )
  )
) $.

${
  $d i A B $.

  nq3-pred-condition-definition $a |- (
    NQ3PredCondition A B
  ) <-> (
    A. i e. ZZ
      (
        i e. B
        <->
        (
          0 <_ i
          /\
          ( i + 1 ) e. A
        )
      )
  ) $.
$}

${
  $d i A B $.

  nq3-succ-condition-definition $a |- (
    NQ3SuccCondition A B
  ) <-> (
    A. i e. ZZ
      (
        i e. B
        <->
        (
          1 <_ i
          /\
          ( i - 1 ) e. A
        )
      )
  ) $.
$}

nq3-cardinality-decrease-definition $a |- (
  NQ3CardinalityDecrease A B
) <-> (
  0 <_ ( # ` A )
  /\
  ( # ` B ) < ( # ` A )
) $.

${
  $d i j t A B C D E F G H I J K L M $.

  nq3-loop-invariant-definition $a |- (
    NQ3LoopInvariant A B C D E F G H I J K L M
  ) <-> (
    0 <_ ( K - F )
    /\
    (
      J C_ ( ( C \ D ) \ E )
      /\
      (
        ( NQ3PartialSolution A B L )
        /\
        (
          ( NQ3Sorted A F K M )
          /\
          (
            A. i e. ZZ A. j e. ZZ
              (
                i e. ( I \ J )
                ->
                (
                  j e. J
                  ->
                  i < j
                )
              )
            /\
            (
              A. i e. ZZ
                (
                  (
                    F <_ i
                    /\
                    i < K
                  )
                  ->
                  (
                    ( NQ3PartialSolution A A ( M ` i ) )
                    /\
                    (
                      ( NQ3EqPrefix L ( M ` i ) B )
                      /\
                      ( ( M ` i ) ` B ) e. ( I \ J )
                    )
                  )
                )
              /\
              (
                A. t e. ( ZZ ^m ZZ )
                  (
                    (
                      ( NQ3PartialSolution A A t )
                      /\
                      (
                        ( NQ3EqPrefix L t B )
                        /\
                        ( t ` B ) e. ( I \ J )
                      )
                    )
                    ->
                    (
                      ( t ` B ) e. I
                      /\
                      (
                        -. ( t ` B ) e. J
                        /\
                        E. i e. ZZ
                          (
                            (
                              F <_ i
                              /\
                              i < K
                            )
                            /\
                            ( NQ3EqPrefix t ( M ` i ) A )
                          )
                      )
                    )
                  )
                /\
                (
                  ( NQ3EqPrefix G L B )
                  /\
                  ( NQ3EqPrefix H M F )
                )
              )
            )
          )
        )
      )
    )
  ) $.
$}

${
  $d i t A B C D E F G H $.

  nq3-postcondition-definition $a |- (
    NQ3Postcondition A B C D E F G H
  ) <-> (
    0 <_ ( F - E )
    /\
    (
      ( NQ3Sorted A E F H )
      /\
      (
        A. t e. ( ZZ ^m ZZ )
          (
            (
              ( NQ3PartialSolution A A t )
              /\
              ( NQ3EqPrefix G t B )
            )
            <->
            E. i e. ZZ
              (
                (
                  E <_ i
                  /\
                  i < F
                )
                /\
                ( NQ3EqPrefix t ( H ` i ) A )
              )
          )
        /\
        (
          ( NQ3EqPrefix C G B )
          /\
          ( NQ3EqPrefix D H E )
        )
      )
    )
  ) $.
$}

${
  $d o p q r u v w x y z A B C D E F G H I J K L M N $.

  nq3-recursive-iteration-definition $a |- (
    NQ3RecursiveIteration A B C D E F G H I J K L M N
  ) <-> (
    A. o e. NQ3FSet
      (
        ( NQ3InsertCondition N E o )
        ->
        A. p e. NQ3FSet
          (
            ( NQ3PredCondition o p )
            ->
            A. q e. NQ3FSet
              (
                ( NQ3InsertCondition N D q )
                ->
                A. r e. NQ3FSet
                  (
                    ( NQ3SuccCondition q r )
                    ->
                    A. u e. NQ3FSet
                      (
                        ( NQ3RemoveCondition N C u )
                        ->
                        (
                          (
                            ( NQ3CardinalityDecrease C u )
                            /\
                            (
                              NQ3CallPreconditions
                                A ( B + 1 ) u K
                                ( NQ3Update L B N ) r p
                            )
                          )
                          /\
                          A. v e. ZZ
                            A. w e. ( ( ZZ ^m ZZ ) ^m ZZ )
                              A. x e. ( ZZ ^m ZZ )
                                (
                                  (
                                    NQ3Postcondition
                                      A ( B + 1 )
                                      ( NQ3Update L B N ) M
                                      K v x w
                                  )
                                  ->
                                  A. y e. NQ3FSet
                                    (
                                      ( NQ3RemoveCondition N J y )
                                      ->
                                      (
                                        ( NQ3CardinalityDecrease J y )
                                        /\
                                        (
                                          (
                                            ( K - F ) + ( v - K )
                                          )
                                          =
                                          ( v - F )
                                          /\
                                          (
                                            ( B + 1 ) - 1
                                          )
                                          =
                                          B
                                        )
                                        /\
                                        (
                                          NQ3LoopInvariant
                                            A ( ( B + 1 ) - 1 )
                                            C D E F G H I y
                                            v x w
                                        )
                                      )
                                    )
                                )
                        )
                      )
                  )
              )
          )
      )
  ) $.
$}

nq3-loop-result-definition $a |- (
  NQ3LoopResult A B C D E F G H I J K L M
) <-> (
  (
    J =/= (/)
    ->
    (
      J =/= (/)
      /\
      (
        NQ3RecursiveIteration
          A B C D E F G H I J K L M
          ( NQ3MinElt J )
      )
    )
  )
  /\
  (
    J = (/)
    ->
    (
      NQ3Postcondition
        A B G H F K L M
    )
  )
) $.

${
  $d p q r s A B C D E F G H I $.

  nq3-all-loop-states-definition $a |- (
    NQ3AllLoopStates A B C D E F G H I
  ) <-> (
    A. p e. NQ3FSet
      A. q e. ZZ
        A. r e. ( ( ZZ ^m ZZ ) ^m ZZ )
          A. s e. ( ZZ ^m ZZ )
            (
              (
                NQ3LoopInvariant
                  A B C D E F G H I p q s r
              )
              ->
              (
                NQ3LoopResult
                  A B C D E F G H I p q s r
              )
            )
  ) $.
$}

${
  $d i j p q r s t u v w x y z
     A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.

  $( Source theorem parameters A=n, B=k, C=a, D=s, E=col, F=b,
     G=c, and H=sol. $)
  nq3-n-integer $e |- A e. ZZ $.
  nq3-k-integer $e |- B e. ZZ $.
  nq3-a-fset $e |- C e. NQ3FSet $.
  nq3-s-integer $e |- D e. ZZ $.
  nq3-col-map $e |- E e. ( ZZ ^m ZZ ) $.
  nq3-b-fset $e |- F e. NQ3FSet $.
  nq3-c-fset $e |- G e. NQ3FSet $.
  nq3-sol-map $e |- H e. ( ( ZZ ^m ZZ ) ^m ZZ ) $.

  nq3-fact0 $e |- 0 <_ B $.
  nq3-fact1 $e |- ( B + ( # ` C ) ) = A $.
  nq3-fact2 $e |- 0 <_ D $.
  nq3-fact3 $e |- ( NQ3AvailableColumns A B C E ) $.
  nq3-fact4 $e |- ( NQ3UnusedAscending B F E ) $.
  nq3-fact5 $e |- ( NQ3UnusedDescending B G E ) $.
  nq3-fact6 $e |- ( NQ3PartialSolution A B E ) $.

  nq3-pearl-queens-nqueens-sets-t3-vc $a |- (
    (
      C =/= (/)
      ->
      A. p e. NQ3FSet
        (
          p = ( C \ F )
          ->
          A. q e. NQ3FSet
            (
              q = ( p \ G )
              ->
              (
                (
                  0 = ( D - D )
                  /\
                  (
                    NQ3LoopInvariant
                      A B C F G D E H q q D E H
                  )
                )
                /\
                (
                  NQ3AllLoopStates
                    A B C F G D E H q
                )
              )
            )
        )
    )
    /\
    (
      C = (/)
      ->
      (
        1 = ( ( D + 1 ) - D )
        /\
        (
          NQ3Postcondition
            A B E H D ( D + 1 ) E
            ( NQ3Update H D E )
        )
      )
    )
  ) $.
$}
