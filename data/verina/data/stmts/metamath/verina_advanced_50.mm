$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_50 (verina__metamath__verina_advanced_50), catalog title
  mergeSorted: the exact indexed merge loop and two suffix drains combine
  arbitrary finite pairwise nondecreasing natural-number arrays into a
  pairwise nondecreasing permutation of their concatenation. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN0 is the full natural-number domain, and Word NN0 is exactly the
  type of arbitrary finite natural-number arrays. For a word w, # ` w is its
  natural-number length, w ` k is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete index set. The empty word (/) represents
  the empty array.

  VERINA50NatSub restores Lean's truncated Nat.sub on natural arguments.
  VERINA50ConcatGraph and VERINA50Concat give exact array/list concatenation.

  VERINA50MergeLoopGraph is an exact operational graph for mergeLoop with all
  five arbitrary helper arguments. Its state trace contains the two current
  indices, starts at the supplied indices, and continues exactly while both
  are in bounds. Each transition emits the first-array entry exactly when it
  is <= the second-array entry, matching the source tie behavior, and advances
  only that entry's index. The final state is the first state at which either
  input is exhausted. Concatenating the supplied result with the emitted word
  is exactly the repeated Array.push accumulator. VERINA50MergeLoop selects
  the unique returned index-index-array triple.

  VERINA50DrainGraph appends precisely the suffix beginning at its arbitrary
  natural index, with the empty suffix when that index is at least the array
  length. VERINA50Drain selects this unique output. VERINA50MergeSorted runs
  mergeLoop at indices zero with the empty result, then drains the first input
  and the second input in the source order. The proof-valued precondition
  argument is computationally unused and is omitted from the target function.

  VERINA50Pairwise is List.Pairwise with natural-number <=. VERINA50Pre is its
  conjunction for the two typed inputs. VERINA50Perm is List.isPerm,
  represented by equality of the multiplicity of every natural number, and
  VERINA50Post requires the computed result to be pairwise nondecreasing and
  a permutation of the concatenated inputs. The postcondition's proof-valued
  precondition argument is propositionally unused and is likewise omitted.
  The final $a declaration is the source correctness proposition. Every
  earlier $a is syntax or a faithful definition, and this database has no $p
  declaration.
$)

$c
  VERINA50NatSub
  VERINA50ConcatGraph VERINA50Concat
  VERINA50MergeLoopGraph VERINA50MergeLoop
  VERINA50DrainGraph VERINA50Drain
  VERINA50Pairwise VERINA50Pre
  VERINA50MergeSorted
  VERINA50Perm VERINA50Post
$.

verina50-nat-sub-syntax
  $a class ( VERINA50NatSub A B ) $.
verina50-concat-graph-syntax
  $a wff ( VERINA50ConcatGraph A B C ) $.
verina50-concat-syntax
  $a class ( VERINA50Concat A B ) $.
verina50-merge-loop-graph-syntax
  $a wff ( VERINA50MergeLoopGraph A B C D E F ) $.
verina50-merge-loop-syntax
  $a class ( VERINA50MergeLoop A B C D E ) $.
verina50-drain-graph-syntax
  $a wff ( VERINA50DrainGraph A B C D ) $.
verina50-drain-syntax
  $a class ( VERINA50Drain A B C ) $.
verina50-pairwise-syntax
  $a wff ( VERINA50Pairwise A ) $.
verina50-precondition-syntax
  $a wff ( VERINA50Pre A B ) $.
verina50-merge-sorted-syntax
  $a class ( VERINA50MergeSorted A B ) $.
verina50-permutation-syntax
  $a wff ( VERINA50Perm A B ) $.
verina50-postcondition-syntax
  $a wff ( VERINA50Post A B C ) $.

verina50-nat-sub-definition $a |- (
  VERINA50NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

${
  $d k A B C $.

  verina50-concat-graph-definition $a |- (
    VERINA50ConcatGraph A B C
  ) <-> (
    (
      (
        A e. Word NN0
        /\
        B e. Word NN0
      )
      /\
      C e. Word NN0
    )
    /\
    (
      ( # ` C ) = ( ( # ` A ) + ( # ` B ) )
      /\
      (
        A. k e. ( 0 ..^ ( # ` A ) )
          ( C ` k ) = ( A ` k )
        /\
        A. k e. ( 0 ..^ ( # ` B ) )
          (
            C ` ( ( # ` A ) + k )
          ) = (
            B ` k
          )
      )
    )
  ) $.
$}

${
  $d y A B $.

  verina50-concat-definition $a |- (
    VERINA50Concat A B
  ) = (
    iota_ y e. Word NN0
      ( VERINA50ConcatGraph A B y )
  ) $.
$}

${
  $d k t u A B C D E F $.

  verina50-merge-loop-graph-definition $a |- (
    VERINA50MergeLoopGraph A B C D E F
  ) <-> (
    (
      (
        (
          A e. Word NN0
          /\
          B e. Word NN0
        )
        /\
        (
          C e. NN0
          /\
          D e. NN0
        )
      )
      /\
      (
        E e. Word NN0
        /\
        F e. ( NN0 X. ( NN0 X. Word NN0 ) )
      )
    )
    /\
    E. t e. Word ( NN0 X. NN0 )
      E. u e. Word NN0
        (
          (
            ( # ` t ) = ( ( # ` u ) + 1 )
            /\
            ( t ` 0 ) = <. C , D >.
          )
          /\
          (
            A. k e. ( 0 ..^ ( # ` u ) )
              (
                (
                  ( 1st ` ( t ` k ) ) < ( # ` A )
                  /\
                  ( 2nd ` ( t ` k ) ) < ( # ` B )
                )
                /\
                (
                  (
                    u ` k
                  ) = if (
                    (
                      A ` ( 1st ` ( t ` k ) )
                    ) <_ (
                      B ` ( 2nd ` ( t ` k ) )
                    ) ,
                    ( A ` ( 1st ` ( t ` k ) ) ) ,
                    ( B ` ( 2nd ` ( t ` k ) ) )
                  )
                  /\
                  (
                    t ` ( k + 1 )
                  ) = if (
                    (
                      A ` ( 1st ` ( t ` k ) )
                    ) <_ (
                      B ` ( 2nd ` ( t ` k ) )
                    ) ,
                    <.
                      ( ( 1st ` ( t ` k ) ) + 1 ) ,
                      ( 2nd ` ( t ` k ) )
                    >. ,
                    <.
                      ( 1st ` ( t ` k ) ) ,
                      ( ( 2nd ` ( t ` k ) ) + 1 )
                    >.
                  )
                )
              )
            /\
            (
              (
                ( # ` A ) <_ ( 1st ` ( t ` ( # ` u ) ) )
                \/
                ( # ` B ) <_ ( 2nd ` ( t ` ( # ` u ) ) )
              )
              /\
              F = <.
                ( 1st ` ( t ` ( # ` u ) ) ) ,
                <.
                  ( 2nd ` ( t ` ( # ` u ) ) ) ,
                  ( VERINA50Concat E u )
                >.
              >.
            )
          )
        )
  ) $.
$}

${
  $d y A B C D E $.

  verina50-merge-loop-definition $a |- (
    VERINA50MergeLoop A B C D E
  ) = (
    iota_ y e. ( NN0 X. ( NN0 X. Word NN0 ) )
      ( VERINA50MergeLoopGraph A B C D E y )
  ) $.
$}

${
  $d k u A B C D $.

  verina50-drain-graph-definition $a |- (
    VERINA50DrainGraph A B C D
  ) <-> (
    (
      (
        (
          A e. Word NN0
          /\
          B e. NN0
        )
        /\
        C e. Word NN0
      )
      /\
      D e. Word NN0
    )
    /\
    E. u e. Word NN0
      (
        (
          ( # ` u ) = ( VERINA50NatSub ( # ` A ) B )
          /\
          A. k e. ( 0 ..^ ( # ` u ) )
            ( u ` k ) = ( A ` ( B + k ) )
        )
        /\
        D = ( VERINA50Concat C u )
      )
  ) $.
$}

${
  $d y A B C $.

  verina50-drain-definition $a |- (
    VERINA50Drain A B C
  ) = (
    iota_ y e. Word NN0
      ( VERINA50DrainGraph A B C y )
  ) $.
$}

${
  $d i j A $.

  verina50-pairwise-definition $a |- (
    VERINA50Pairwise A
  ) <-> (
    (
      A e. Word NN0
      /\
      A. i e. ( 0 ..^ ( # ` A ) )
        A. j e. ( 0 ..^ ( # ` A ) )
          (
            i < j
            ->
            ( A ` i ) <_ ( A ` j )
          )
    )
  ) $.
$}

verina50-precondition-definition $a |- (
  VERINA50Pre A B
) <-> (
  (
    A e. Word NN0
    /\
    B e. Word NN0
  )
  /\
  (
    ( VERINA50Pairwise A )
    /\
    ( VERINA50Pairwise B )
  )
) $.

verina50-merge-sorted-definition $a |- (
  VERINA50MergeSorted A B
) = (
  VERINA50Drain
    B
    (
      1st ` (
        2nd ` ( VERINA50MergeLoop A B 0 0 (/) )
      )
    )
    (
      VERINA50Drain
        A
        ( 1st ` ( VERINA50MergeLoop A B 0 0 (/) ) )
        (
          2nd ` (
            2nd ` ( VERINA50MergeLoop A B 0 0 (/) )
          )
        )
    )
) $.

${
  $d i j x A B $.

  verina50-permutation-definition $a |- (
    VERINA50Perm A B
  ) <-> (
    (
      A e. Word NN0
      /\
      B e. Word NN0
    )
    /\
    A. x e. NN0
      (
        # ` {
          i e. ( 0 ..^ ( # ` A ) )
          |
          ( A ` i ) = x
        }
      ) = (
        # ` {
          j e. ( 0 ..^ ( # ` B ) )
          |
          ( B ` j ) = x
        }
      )
  ) $.
$}

verina50-postcondition-definition $a |- (
  VERINA50Post A B C
) <-> (
  (
    (
      A e. Word NN0
      /\
      B e. Word NN0
    )
    /\
    C e. Word NN0
  )
  /\
  (
    ( VERINA50Pairwise C )
    /\
    (
      VERINA50Perm
        C
        ( VERINA50Concat A B )
    )
  )
) $.

verina-advanced-50-merge-sorted $a |- A. a e. Word NN0
  A. b e. Word NN0
    (
      ( VERINA50Pre a b )
      ->
      (
        VERINA50Post
          a
          b
          ( VERINA50MergeSorted a b )
      )
    )
$.
