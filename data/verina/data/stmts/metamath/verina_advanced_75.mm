$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_75 (verina__metamath__verina_advanced_75), catalog title
  task_code: the exact pair-state Kadane fold computes the maximum sum of a
  nonempty contiguous subarray of an arbitrary nonempty finite integer list,
  together with its independently enumerated correctness contract. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer lists. For a word
  w, # ` w is its natural-number length, w ` k is zero-based lookup, and
  i ..^ j is the half-open natural interval from i through j - 1.

  VERINA75IntMax is the source integer maximum operation.
  VERINA75FoldGraph is the exact trace of the source List.foldl on the tail
  of a nonempty input. Its c and m words record the pair components cur and
  maxSoFar before and after every consumed entry. Each transition computes
    newCur = if cur + x >= x then cur + x else x
  and then
    newMax = if maxSoFar >= newCur then maxSoFar else newCur.
  VERINA75Fold selects the final maxSoFar from that unique trace.

  VERINA75NatSub is Lean's truncated natural subtraction.
  VERINA75TailGraph and VERINA75Tail give List.tail, including the empty-list
  case. VERINA75TaskCode is the exact source match: it returns integer zero
  on the empty word, and otherwise folds the tail with both initial pair
  components equal to the head. The proof-valued precondition argument is
  computationally unused, so the target function is defined on every typed
  word and is invoked under VERINA75Pre in the final assertion.

  VERINA75PrefixGraph records the unique integer prefix sums starting at
  zero. VERINA75SubarraySumsGraph reproduces the postcondition's outer
  List.range (length + 1), inner List.range (length - start + 1), drop/take,
  filter of the empty subarrays, and map of List.sum. After that filter its
  index-pair word contains, in increasing start and then increasing length,
  exactly the pairs with start below the input length and positive length at
  most length - start. Prefix differences are exactly the corresponding
  drop/take sums, and duplicate sum values are retained.

  VERINA75Pre is precisely the typed nonempty-list precondition.
  VERINA75Post says that the result occurs in the independently generated
  subarray-sum word and every entry of that word is at most the result,
  exactly reproducing List.contains and List.all. The final $a declaration is
  the source correctness proposition. Every earlier $a is syntax or a
  faithful definition required by this rendering, and this database has no
  $p declaration.
$)

$c
  VERINA75IntMax
  VERINA75FoldGraph VERINA75Fold
  VERINA75NatSub
  VERINA75TailGraph VERINA75Tail
  VERINA75Pre VERINA75TaskCode
  VERINA75PrefixGraph VERINA75Prefix
  VERINA75SubarraySumsGraph VERINA75SubarraySums
  VERINA75Post
$.

verina75-int-max-syntax
  $a class ( VERINA75IntMax A B ) $.
verina75-fold-graph-syntax
  $a wff ( VERINA75FoldGraph A B C D ) $.
verina75-fold-syntax
  $a class ( VERINA75Fold A B C ) $.
verina75-nat-sub-syntax
  $a class ( VERINA75NatSub A B ) $.
verina75-tail-graph-syntax
  $a wff ( VERINA75TailGraph A B ) $.
verina75-tail-syntax
  $a class ( VERINA75Tail A ) $.
verina75-precondition-syntax
  $a wff ( VERINA75Pre A ) $.
verina75-task-code-syntax
  $a class ( VERINA75TaskCode A ) $.
verina75-prefix-graph-syntax
  $a wff ( VERINA75PrefixGraph A B ) $.
verina75-prefix-syntax
  $a class ( VERINA75Prefix A ) $.
verina75-subarray-sums-graph-syntax
  $a wff ( VERINA75SubarraySumsGraph A B ) $.
verina75-subarray-sums-syntax
  $a class ( VERINA75SubarraySums A ) $.
verina75-postcondition-syntax
  $a wff ( VERINA75Post A B ) $.

verina75-int-max-definition $a |- (
  VERINA75IntMax A B
) = if (
  A < B ,
  B ,
  A
) $.

${
  $d k c m A B C D $.

  verina75-fold-graph-definition $a |- (
    VERINA75FoldGraph A B C D
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. ZZ
      )
      /\
      (
        C e. ZZ
        /\
        D e. ZZ
      )
    )
    /\
    E. c e. Word ZZ
      E. m e. Word ZZ
        (
          (
            (
              ( # ` c ) = ( ( # ` A ) + 1 )
              /\
              ( # ` m ) = ( ( # ` A ) + 1 )
            )
            /\
            (
              ( c ` 0 ) = B
              /\
              ( m ` 0 ) = C
            )
          )
          /\
          (
            A. k e. ( 0 ..^ ( # ` A ) )
              (
                (
                  c ` ( k + 1 )
                ) = (
                  VERINA75IntMax
                    ( ( c ` k ) + ( A ` k ) )
                    ( A ` k )
                )
                /\
                (
                  m ` ( k + 1 )
                ) = (
                  VERINA75IntMax
                    ( m ` k )
                    ( c ` ( k + 1 ) )
                )
              )
            /\
            D = ( m ` ( # ` A ) )
          )
        )
  ) $.
$}

${
  $d y A B C $.

  verina75-fold-definition $a |- (
    VERINA75Fold A B C
  ) = (
    iota_ y e. ZZ
      ( VERINA75FoldGraph A B C y )
  ) $.
$}

verina75-nat-sub-definition $a |- (
  VERINA75NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

${
  $d j A B $.

  verina75-tail-graph-definition $a |- (
    VERINA75TailGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    (
      ( # ` B ) = ( VERINA75NatSub ( # ` A ) 1 )
      /\
      A. j e. ( 0 ..^ ( # ` B ) )
        ( B ` j ) = ( A ` ( j + 1 ) )
    )
  ) $.
$}

${
  $d y A $.

  verina75-tail-definition $a |- (
    VERINA75Tail A
  ) = (
    iota_ y e. Word ZZ
      ( VERINA75TailGraph A y )
  ) $.
$}

verina75-precondition-definition $a |- (
  VERINA75Pre A
) <-> (
  A e. Word ZZ
  /\
  0 < ( # ` A )
) $.

verina75-task-code-definition $a |- (
  VERINA75TaskCode A
) = if (
  ( # ` A ) = 0 ,
  0 ,
  (
    VERINA75Fold
      ( VERINA75Tail A )
      ( A ` 0 )
      ( A ` 0 )
  )
) $.

${
  $d i A B $.

  verina75-prefix-graph-definition $a |- (
    VERINA75PrefixGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    (
      (
        ( # ` B ) = ( ( # ` A ) + 1 )
        /\
        ( B ` 0 ) = 0
      )
      /\
      A. i e. ( 0 ..^ ( # ` A ) )
        (
          B ` ( i + 1 )
        ) = (
          ( B ` i ) + ( A ` i )
        )
    )
  ) $.
$}

${
  $d y A $.

  verina75-prefix-definition $a |- (
    VERINA75Prefix A
  ) = (
    iota_ y e. Word ZZ
      ( VERINA75PrefixGraph A y )
  ) $.
$}

${
  $d i j l p q s A B $.

  verina75-subarray-sums-graph-definition $a |- (
    VERINA75SubarraySumsGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    E. p e. Word ( NN0 X. NN0 )
      (
        (
          ( # ` p ) = ( # ` B )
          /\
          A. i e. ( 0 ..^ ( # ` p ) )
            (
              (
                (
                  ( 1st ` ( p ` i ) ) < ( # ` A )
                  /\
                  0 < ( 2nd ` ( p ` i ) )
                )
                /\
                ( 2nd ` ( p ` i ) ) <_ (
                  ( # ` A ) - ( 1st ` ( p ` i ) )
                )
              )
              /\
              (
                B ` i
              ) = (
                (
                  VERINA75Prefix A
                ) ` (
                  ( 1st ` ( p ` i ) ) +
                  ( 2nd ` ( p ` i ) )
                )
                -
                (
                  VERINA75Prefix A
                ) ` (
                  1st ` ( p ` i )
                )
              )
            )
        )
        /\
        (
          A. i e. ( 0 ..^ ( # ` p ) )
            A. j e. ( 0 ..^ ( # ` p ) )
              (
                i < j
                ->
                (
                  (
                    1st ` ( p ` i )
                  ) < (
                    1st ` ( p ` j )
                  )
                  \/
                  (
                    (
                      1st ` ( p ` i )
                    ) = (
                      1st ` ( p ` j )
                    )
                    /\
                    (
                      2nd ` ( p ` i )
                    ) < (
                      2nd ` ( p ` j )
                    )
                  )
                )
              )
          /\
          A. s e. NN0
            A. l e. NN0
              (
                (
                  (
                    s < ( # ` A )
                    /\
                    0 < l
                  )
                  /\
                  l <_ ( ( # ` A ) - s )
                )
                ->
                E. q e. ( 0 ..^ ( # ` p ) )
                  ( p ` q ) = <. s , l >.
              )
        )
      )
  ) $.
$}

${
  $d y A $.

  verina75-subarray-sums-definition $a |- (
    VERINA75SubarraySums A
  ) = (
    iota_ y e. Word ZZ
      ( VERINA75SubarraySumsGraph A y )
  ) $.
$}

${
  $d i A B $.

  verina75-postcondition-definition $a |- (
    VERINA75Post A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. ZZ
    )
    /\
    (
      B e. ran ( VERINA75SubarraySums A )
      /\
      A. i e. (
        0 ..^ ( # ` ( VERINA75SubarraySums A ) )
      )
        (
          ( VERINA75SubarraySums A ) ` i
        ) <_ B
    )
  ) $.
$}

verina-advanced-75-task-code
  $a |- A. w e. Word ZZ
    (
      ( VERINA75Pre w )
      ->
      (
        VERINA75Post
          w
          ( VERINA75TaskCode w )
      )
    )
  $.
