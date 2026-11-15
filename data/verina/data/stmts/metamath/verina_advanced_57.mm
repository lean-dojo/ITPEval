$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_57 (verina__metamath__verina_advanced_57), catalog title
  nextGreaterElement: the exact monotonic-stack program computes, for every
  entry of an arbitrary finite distinct integer query list whose values occur
  in a distinct integer reference list, the first greater reference-list value
  to its right, or -1 when none exists, together with its complete correctness
  contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer lists. For a word
  w, # ` w is its natural-number length, w ` i is zero-based lookup,
  ran w is its membership set, and 0 ..^ ( # ` w ) is its complete index set.

  VERINA57GetDInt is Lean List.get! on an integer list, including its zero
  default outside the list. VERINA57ConsNat, VERINA57ConsInt, and
  VERINA57ReverseInt are exact list operations.

  VERINA57ProcessStackGraph is the local processStack recursion. Its witness r
  is exactly the number of consecutive stack heads whose source values are
  smaller than the current value. The remaining stack is the corresponding
  suffix, while the popped key-value pairs are prepended to the old map in
  recursive order. VERINA57FinalizeMapGraph is the terminal stack.foldl that
  prepends a pair with value -1 for every unresolved position.

  VERINA57MapStepGraph performs one nonterminal mapLoop iteration:
  processStack followed by pushing the current source index.
  VERINA57MapLoopGraph records every such deterministic state transition from
  arbitrary helper arguments and then performs the terminal fold.
  VERINA57BuildNextGreaterMap is the source invocation at index zero with
  empty stack and map.

  VERINA57FindInMapGraph is the exact first matching-pair search with default
  -1. VERINA57ResultLoopGraph records the source accumulator recursion from
  arbitrary index and accumulator arguments and reverses the final
  accumulator. VERINA57NextGreaterElement explicitly composes the exact map
  construction and result loop, so its output is fixed independently of the
  postcondition.

  VERINA57Nodup and VERINA57Pre reproduce the two List.Nodup assumptions and
  the all-membership subset assumption. VERINA57FindIndex is findIdx?, and
  VERINA57ExpectedAt reproduces the range/find? search for the first greater
  value strictly to the right, including the -1 case. VERINA57Post is the
  complete three-part source postcondition. The proof-valued precondition
  arguments are computationally and propositionally unused and are represented
  by the explicit antecedent of the final correctness assertion. Every earlier
  $a is syntax or a faithful definition, and this database has no $p
  declaration.
$)

$c
  VERINA57GetDInt
  VERINA57ConsNatGraph VERINA57ConsNat
  VERINA57ConsIntGraph VERINA57ConsInt
  VERINA57ReverseIntGraph VERINA57ReverseInt
  VERINA57ProcessStackGraph
  VERINA57FinalizeMapGraph VERINA57FinalizeMap
  VERINA57MapStepGraph VERINA57MapLoopGraph VERINA57MapLoop
  VERINA57BuildNextGreaterMap
  VERINA57FindInMapGraph VERINA57FindInMap
  VERINA57ResultLoopGraph VERINA57ResultLoop VERINA57NextGreaterElement
  VERINA57Nodup VERINA57Pre
  VERINA57FindIndex VERINA57ExpectedAt VERINA57Post
$.

verina57-get-default-int-syntax
  $a class ( VERINA57GetDInt A B ) $.
verina57-cons-nat-graph-syntax
  $a wff ( VERINA57ConsNatGraph A B C ) $.
verina57-cons-nat-syntax
  $a class ( VERINA57ConsNat A B ) $.
verina57-cons-int-graph-syntax
  $a wff ( VERINA57ConsIntGraph A B C ) $.
verina57-cons-int-syntax
  $a class ( VERINA57ConsInt A B ) $.
verina57-reverse-int-graph-syntax
  $a wff ( VERINA57ReverseIntGraph A B ) $.
verina57-reverse-int-syntax
  $a class ( VERINA57ReverseInt A ) $.
verina57-process-stack-graph-syntax
  $a wff ( VERINA57ProcessStackGraph A B C D E F ) $.
verina57-finalize-map-graph-syntax
  $a wff ( VERINA57FinalizeMapGraph A B C D ) $.
verina57-finalize-map-syntax
  $a class ( VERINA57FinalizeMap A B C ) $.
verina57-map-step-graph-syntax
  $a wff ( VERINA57MapStepGraph A B C D E F ) $.
verina57-map-loop-graph-syntax
  $a wff ( VERINA57MapLoopGraph A B C D E ) $.
verina57-map-loop-syntax
  $a class ( VERINA57MapLoop A B C D ) $.
verina57-build-map-syntax
  $a class ( VERINA57BuildNextGreaterMap A ) $.
verina57-find-in-map-graph-syntax
  $a wff ( VERINA57FindInMapGraph A B C ) $.
verina57-find-in-map-syntax
  $a class ( VERINA57FindInMap A B ) $.
verina57-result-loop-graph-syntax
  $a wff ( VERINA57ResultLoopGraph A B C D E ) $.
verina57-result-loop-syntax
  $a class ( VERINA57ResultLoop A B C D ) $.
verina57-next-greater-element-syntax
  $a class ( VERINA57NextGreaterElement A B ) $.
verina57-nodup-syntax
  $a wff ( VERINA57Nodup A ) $.
verina57-precondition-syntax
  $a wff ( VERINA57Pre A B ) $.
verina57-find-index-syntax
  $a wff ( VERINA57FindIndex A B C ) $.
verina57-expected-at-syntax
  $a wff ( VERINA57ExpectedAt A B C ) $.
verina57-postcondition-syntax
  $a wff ( VERINA57Post A B C ) $.

verina57-get-default-int-definition $a |- (
  VERINA57GetDInt A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

${
  $d j A B C $.

  verina57-cons-nat-graph-definition $a |- (
    VERINA57ConsNatGraph A B C
  ) <-> (
    (
      (
        A e. NN0
        /\
        B e. Word NN0
      )
      /\
      C e. Word NN0
    )
    /\
    (
      ( # ` C ) = ( ( # ` B ) + 1 )
      /\
      (
        ( C ` 0 ) = A
        /\
        A. j e. ( 0 ..^ ( # ` B ) )
          ( C ` ( j + 1 ) ) = ( B ` j )
      )
    )
  ) $.
$}

${
  $d y A B $.

  verina57-cons-nat-definition $a |- (
    VERINA57ConsNat A B
  ) = (
    iota_ y e. Word NN0
      ( VERINA57ConsNatGraph A B y )
  ) $.
$}

${
  $d j A B C $.

  verina57-cons-int-graph-definition $a |- (
    VERINA57ConsIntGraph A B C
  ) <-> (
    (
      (
        A e. ZZ
        /\
        B e. Word ZZ
      )
      /\
      C e. Word ZZ
    )
    /\
    (
      ( # ` C ) = ( ( # ` B ) + 1 )
      /\
      (
        ( C ` 0 ) = A
        /\
        A. j e. ( 0 ..^ ( # ` B ) )
          ( C ` ( j + 1 ) ) = ( B ` j )
      )
    )
  ) $.
$}

${
  $d y A B $.

  verina57-cons-int-definition $a |- (
    VERINA57ConsInt A B
  ) = (
    iota_ y e. Word ZZ
      ( VERINA57ConsIntGraph A B y )
  ) $.
$}

${
  $d i A B $.

  verina57-reverse-int-graph-definition $a |- (
    VERINA57ReverseIntGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    (
      ( # ` B ) = ( # ` A )
      /\
      A. i e. ( 0 ..^ ( # ` A ) )
        (
          B ` i
        ) = (
          A ` ( ( ( # ` A ) - 1 ) - i )
        )
    )
  ) $.
$}

${
  $d y A $.

  verina57-reverse-int-definition $a |- (
    VERINA57ReverseInt A
  ) = (
    iota_ y e. Word ZZ
      ( VERINA57ReverseIntGraph A y )
  ) $.
$}

${
  $d j q r A B C D E F $.

  verina57-process-stack-graph-definition $a |- (
    VERINA57ProcessStackGraph A B C D E F
  ) <-> (
    (
      (
        (
          A e. Word ZZ
          /\
          B e. ZZ
        )
        /\
        (
          C e. Word NN0
          /\
          D e. Word ( ZZ X. ZZ )
        )
      )
      /\
      (
        E e. Word NN0
        /\
        F e. Word ( ZZ X. ZZ )
      )
    )
    /\
    E. r e. ( 0 ..^ ( ( # ` C ) + 1 ) )
      (
        (
          A. q e. ( 0 ..^ r )
            (
              VERINA57GetDInt A ( C ` q )
            ) < B
          /\
          (
            r = ( # ` C )
            \/
            (
              r < ( # ` C )
              /\
              B <_ ( VERINA57GetDInt A ( C ` r ) )
            )
          )
        )
        /\
        (
          (
            ( # ` E ) = ( ( # ` C ) - r )
            /\
            A. j e. ( 0 ..^ ( # ` E ) )
              ( E ` j ) = ( C ` ( r + j ) )
          )
          /\
          (
            ( # ` F ) = ( r + ( # ` D ) )
            /\
            (
              A. j e. ( 0 ..^ r )
                (
                  F ` j
                ) = <.
                  (
                    VERINA57GetDInt
                      A
                      ( C ` ( ( r - 1 ) - j ) )
                  ) ,
                  B
                >.
              /\
              A. j e. ( 0 ..^ ( # ` D ) )
                ( F ` ( r + j ) ) = ( D ` j )
            )
          )
        )
      )
  ) $.
$}

${
  $d j A B C D $.

  verina57-finalize-map-graph-definition $a |- (
    VERINA57FinalizeMapGraph A B C D
  ) <-> (
    (
      (
        (
          A e. Word ZZ
          /\
          B e. Word NN0
        )
        /\
        C e. Word ( ZZ X. ZZ )
      )
      /\
      D e. Word ( ZZ X. ZZ )
    )
    /\
    (
      ( # ` D ) = ( ( # ` B ) + ( # ` C ) )
      /\
      (
        A. j e. ( 0 ..^ ( # ` B ) )
          (
            D ` j
          ) = <.
            (
              VERINA57GetDInt
                A
                ( B ` ( ( ( # ` B ) - 1 ) - j ) )
            ) ,
            ( -u 1 )
          >.
        /\
        A. j e. ( 0 ..^ ( # ` C ) )
          ( D ` ( ( # ` B ) + j ) ) = ( C ` j )
      )
    )
  ) $.
$}

${
  $d y A B C $.

  verina57-finalize-map-definition $a |- (
    VERINA57FinalizeMap A B C
  ) = (
    iota_ y e. Word ( ZZ X. ZZ )
      ( VERINA57FinalizeMapGraph A B C y )
  ) $.
$}

${
  $d s A B C D E F $.

  verina57-map-step-graph-definition $a |- (
    VERINA57MapStepGraph A B C D E F
  ) <-> (
    (
      (
        (
          A e. Word ZZ
          /\
          B e. NN0
        )
        /\
        (
          C e. Word NN0
          /\
          D e. Word ( ZZ X. ZZ )
        )
      )
      /\
      (
        E e. Word NN0
        /\
        F e. Word ( ZZ X. ZZ )
      )
    )
    /\
    (
      B < ( # ` A )
      /\
      E. s e. Word NN0
        (
          (
            VERINA57ProcessStackGraph
              A
              ( VERINA57GetDInt A B )
              C
              D
              s
              F
          )
          /\
          E = ( VERINA57ConsNat B s )
        )
    )
  ) $.
$}

${
  $d k t A B C D E $.

  verina57-map-loop-graph-definition $a |- (
    VERINA57MapLoopGraph A B C D E
  ) <-> (
    (
      (
        (
          A e. Word ZZ
          /\
          B e. NN0
        )
        /\
        (
          C e. Word NN0
          /\
          D e. Word ( ZZ X. ZZ )
        )
      )
      /\
      E e. Word ( ZZ X. ZZ )
    )
    /\
    (
      (
        ( # ` A ) <_ B
        /\
        E = ( VERINA57FinalizeMap A C D )
      )
      \/
      (
        B < ( # ` A )
        /\
        E. t e. Word
          ( ( Word NN0 ) X. ( Word ( ZZ X. ZZ ) ) )
          (
            (
              (
                # ` t
              ) = (
                ( ( # ` A ) - B ) + 1
              )
              /\
              ( t ` 0 ) = <. C , D >.
            )
            /\
            (
              A. k e. ( 0 ..^ ( ( # ` A ) - B ) )
                (
                  VERINA57MapStepGraph
                    A
                    ( B + k )
                    ( 1st ` ( t ` k ) )
                    ( 2nd ` ( t ` k ) )
                    ( 1st ` ( t ` ( k + 1 ) ) )
                    ( 2nd ` ( t ` ( k + 1 ) ) )
                )
              /\
              E = (
                VERINA57FinalizeMap
                  A
                  (
                    1st ` (
                      t ` ( ( # ` A ) - B )
                    )
                  )
                  (
                    2nd ` (
                      t ` ( ( # ` A ) - B )
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
  $d y A B C D $.

  verina57-map-loop-definition $a |- (
    VERINA57MapLoop A B C D
  ) = (
    iota_ y e. Word ( ZZ X. ZZ )
      ( VERINA57MapLoopGraph A B C D y )
  ) $.
$}

verina57-build-map-definition $a |- (
  VERINA57BuildNextGreaterMap A
) = (
  VERINA57MapLoop A 0 (/) (/)
) $.

${
  $d i j A B C $.

  verina57-find-in-map-graph-definition $a |- (
    VERINA57FindInMapGraph A B C
  ) <-> (
    (
      (
        A e. Word ( ZZ X. ZZ )
        /\
        B e. ZZ
      )
      /\
      C e. ZZ
    )
    /\
    (
      E. i e. ( 0 ..^ ( # ` A ) )
        (
          (
            ( 1st ` ( A ` i ) ) = B
            /\
            A. j e. ( 0 ..^ i )
              ( 1st ` ( A ` j ) ) =/= B
          )
          /\
          C = ( 2nd ` ( A ` i ) )
        )
      \/
      (
        (
          A. i e. ( 0 ..^ ( # ` A ) )
            ( 1st ` ( A ` i ) ) =/= B
        )
        /\
        C = ( -u 1 )
      )
    )
  ) $.
$}

${
  $d y A B $.

  verina57-find-in-map-definition $a |- (
    VERINA57FindInMap A B
  ) = (
    iota_ y e. ZZ
      ( VERINA57FindInMapGraph A B y )
  ) $.
$}

${
  $d k t A B C D E $.

  verina57-result-loop-graph-definition $a |- (
    VERINA57ResultLoopGraph A B C D E
  ) <-> (
    (
      (
        (
          A e. Word ZZ
          /\
          B e. Word ( ZZ X. ZZ )
        )
        /\
        (
          C e. NN0
          /\
          D e. Word ZZ
        )
      )
      /\
      E e. Word ZZ
    )
    /\
    (
      (
        ( # ` A ) <_ C
        /\
        E = ( VERINA57ReverseInt D )
      )
      \/
      (
        C < ( # ` A )
        /\
        E. t e. Word ( Word ZZ )
          (
            (
              (
                # ` t
              ) = (
                ( ( # ` A ) - C ) + 1
              )
              /\
              ( t ` 0 ) = D
            )
            /\
            (
              A. k e. ( 0 ..^ ( ( # ` A ) - C ) )
                (
                  t ` ( k + 1 )
                ) = (
                  VERINA57ConsInt
                    (
                      VERINA57FindInMap
                        B
                        (
                          VERINA57GetDInt
                            A
                            ( C + k )
                        )
                    )
                    ( t ` k )
                )
              /\
              E = (
                VERINA57ReverseInt
                  (
                    t ` ( ( # ` A ) - C )
                  )
              )
            )
          )
      )
    )
  ) $.
$}

${
  $d y A B C D $.

  verina57-result-loop-definition $a |- (
    VERINA57ResultLoop A B C D
  ) = (
    iota_ y e. Word ZZ
      ( VERINA57ResultLoopGraph A B C D y )
  ) $.
$}

verina57-next-greater-element-definition $a |- (
  VERINA57NextGreaterElement A B
) = (
  VERINA57ResultLoop
    A
    ( VERINA57BuildNextGreaterMap B )
    0
    (/)
) $.

${
  $d i j A $.

  verina57-nodup-definition $a |- (
    VERINA57Nodup A
  ) <-> (
    (
      A e. Word ZZ
      /\
      A. i e. ( 0 ..^ ( # ` A ) )
        A. j e. ( 0 ..^ ( # ` A ) )
          (
            i < j
            ->
            ( A ` i ) =/= ( A ` j )
          )
    )
  ) $.
$}

${
  $d i A B $.

  verina57-precondition-definition $a |- (
    VERINA57Pre A B
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. Word ZZ
      )
      /\
      (
        ( VERINA57Nodup A )
        /\
        ( VERINA57Nodup B )
      )
    )
    /\
    A. i e. ( 0 ..^ ( # ` A ) )
      ( A ` i ) e. ran B
  ) $.
$}

${
  $d i j A B C $.

  verina57-find-index-definition $a |- (
    VERINA57FindIndex A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. ZZ
      )
      /\
      C e. NN0
    )
    /\
    (
      (
        C < ( # ` A )
        /\
        ( A ` C ) = B
      )
      /\
      A. i e. ( 0 ..^ C )
        ( A ` i ) =/= B
    )
  ) $.
$}

${
  $d j k q A B C $.

  verina57-expected-at-definition $a |- (
    VERINA57ExpectedAt A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. ZZ
      )
      /\
      C e. ZZ
    )
    /\
    E. j e. ( 0 ..^ ( # ` A ) )
      (
        ( VERINA57FindIndex A B j )
        /\
        (
          (
            A. k e. ( ( j + 1 ) ..^ ( # ` A ) )
              ( A ` k ) <_ B
            /\
            C = ( -u 1 )
          )
          \/
          E. k e. ( ( j + 1 ) ..^ ( # ` A ) )
            (
              (
                B < ( A ` k )
                /\
                A. q e. ( ( j + 1 ) ..^ k )
                  ( A ` q ) <_ B
              )
              /\
              C = ( A ` k )
            )
        )
      )
  ) $.
$}

${
  $d i A B C $.

  verina57-postcondition-definition $a |- (
    VERINA57Post A B C
  ) <-> (
    (
      (
        (
          A e. Word ZZ
          /\
          B e. Word ZZ
        )
        /\
        C e. Word ZZ
      )
      /\
      ( # ` C ) = ( # ` A )
    )
    /\
    (
      A. i e. ( 0 ..^ ( # ` A ) )
        (
          VERINA57ExpectedAt
            B
            ( A ` i )
            ( C ` i )
        )
      /\
      A. i e. ( 0 ..^ ( # ` C ) )
        (
          ( C ` i ) = ( -u 1 )
          \/
          ( C ` i ) e. ran B
        )
    )
  ) $.
$}

verina-advanced-57-next-greater-element
  $a |- A. a e. Word ZZ
    A. b e. Word ZZ
      (
        ( VERINA57Pre a b )
        ->
        (
          VERINA57Post
            a
            b
            ( VERINA57NextGreaterElement a b )
        )
      )
  $.
