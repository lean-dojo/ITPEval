$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_49 (verina__metamath__verina_advanced_49), catalog title
  mergeSortedLists: the exact executable recursive merge of two arbitrary
  finite nondecreasing integer lists returns a nondecreasing permutation of
  their concatenation. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain, and Word ZZ is exactly the type of
  arbitrary finite integer lists. For a word w, # ` w is its length, w ` k
  is zero-based lookup, and 0 ..^ ( # ` w ) is its complete index set.

  VERINA49Next and VERINA49Pick encode one exact step of the source local
  merge recursion. A state is the pair of current zero-based positions in
  the two input words. If the first input is exhausted, the next element is
  taken from the second; if only the second is exhausted, it is taken from
  the first; otherwise the first element is taken exactly when it is <= the
  second, matching the source's tie behavior.

  VERINA49MergeGraph records the unique complete state trace and every
  emitted integer for exactly #A + #B steps. Processing an exhausted
  remainder one element at a time has exactly the same output as the source
  base cases returning that remainder. VERINA49Merge selects the unique
  output of this graph, and VERINA49MergeSortedLists is the source executable
  implementation. Thus it is not an unconstrained function and is not
  selected from the postcondition.

  VERINA49Pairwise is List.Pairwise with integer <=. VERINA49Pre is the
  conjunction of that property for the two typed inputs. VERINA49Concat is
  exact word concatenation, and VERINA49Perm is List.isPerm, represented by
  equality of the multiplicity of every integer. VERINA49Post requires the
  result to be pairwise nondecreasing and a permutation of the concatenated
  inputs. The proof-valued precondition argument is computationally unused
  and is omitted from the target function; the postcondition's corresponding
  proof argument is propositionally unused and is likewise omitted. The
  final $a declaration is the source correctness proposition. Every earlier
  $a is syntax or a faithful definition, and this database has no $p
  declaration.
$)

$c
  VERINA49Next VERINA49Pick
  VERINA49MergeGraph VERINA49Merge VERINA49MergeSortedLists
  VERINA49Pairwise VERINA49Pre
  VERINA49ConcatGraph VERINA49Concat
  VERINA49Perm VERINA49Post
$.

verina49-next-syntax
  $a class ( VERINA49Next A B C ) $.
verina49-pick-syntax
  $a class ( VERINA49Pick A B C ) $.
verina49-merge-graph-syntax
  $a wff ( VERINA49MergeGraph A B C ) $.
verina49-merge-syntax
  $a class ( VERINA49Merge A B ) $.
verina49-merge-sorted-lists-syntax
  $a class ( VERINA49MergeSortedLists A B ) $.
verina49-pairwise-syntax
  $a wff ( VERINA49Pairwise A ) $.
verina49-precondition-syntax
  $a wff ( VERINA49Pre A B ) $.
verina49-concat-graph-syntax
  $a wff ( VERINA49ConcatGraph A B C ) $.
verina49-concat-syntax
  $a class ( VERINA49Concat A B ) $.
verina49-permutation-syntax
  $a wff ( VERINA49Perm A B ) $.
verina49-postcondition-syntax
  $a wff ( VERINA49Post A B C ) $.

verina49-next-definition $a |- (
  VERINA49Next A B C
) = if (
  ( # ` A ) = ( 1st ` C ) ,
  <. ( 1st ` C ) , ( ( 2nd ` C ) + 1 ) >. ,
  if (
    ( # ` B ) = ( 2nd ` C ) ,
    <. ( ( 1st ` C ) + 1 ) , ( 2nd ` C ) >. ,
    if (
      ( A ` ( 1st ` C ) ) <_ ( B ` ( 2nd ` C ) ) ,
      <. ( ( 1st ` C ) + 1 ) , ( 2nd ` C ) >. ,
      <. ( 1st ` C ) , ( ( 2nd ` C ) + 1 ) >.
    )
  )
) $.

verina49-pick-definition $a |- (
  VERINA49Pick A B C
) = if (
  ( # ` A ) = ( 1st ` C ) ,
  ( B ` ( 2nd ` C ) ) ,
  if (
    ( # ` B ) = ( 2nd ` C ) ,
    ( A ` ( 1st ` C ) ) ,
    if (
      ( A ` ( 1st ` C ) ) <_ ( B ` ( 2nd ` C ) ) ,
      ( A ` ( 1st ` C ) ) ,
      ( B ` ( 2nd ` C ) )
    )
  )
) $.

${
  $d k t A B C $.

  verina49-merge-graph-definition $a |- (
    VERINA49MergeGraph A B C
  ) <-> (
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
    E. t e. Word ( NN0 X. NN0 )
      (
        (
          ( # ` t ) = ( ( ( # ` A ) + ( # ` B ) ) + 1 )
          /\
          ( t ` 0 ) = <. 0 , 0 >.
        )
        /\
        (
          (
            ( # ` C ) = ( ( # ` A ) + ( # ` B ) )
            /\
            A. k e. ( 0 ..^ ( # ` C ) )
              (
                (
                  t ` ( k + 1 )
                ) = (
                  VERINA49Next A B ( t ` k )
                )
                /\
                (
                  C ` k
                ) = (
                  VERINA49Pick A B ( t ` k )
                )
              )
          )
          /\
          (
            t ` ( # ` C )
          ) = <. ( # ` A ) , ( # ` B ) >.
        )
      )
  ) $.
$}

${
  $d y A B $.

  verina49-merge-definition $a |- (
    VERINA49Merge A B
  ) = (
    iota_ y e. Word ZZ
      ( VERINA49MergeGraph A B y )
  ) $.
$}

verina49-merge-sorted-lists-definition $a |- (
  VERINA49MergeSortedLists A B
) = (
  VERINA49Merge A B
) $.

${
  $d i j A $.

  verina49-pairwise-definition $a |- (
    VERINA49Pairwise A
  ) <-> (
    (
      A e. Word ZZ
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

verina49-precondition-definition $a |- (
  VERINA49Pre A B
) <-> (
  (
    A e. Word ZZ
    /\
    B e. Word ZZ
  )
  /\
  (
    ( VERINA49Pairwise A )
    /\
    ( VERINA49Pairwise B )
  )
) $.

${
  $d k A B C $.

  verina49-concat-graph-definition $a |- (
    VERINA49ConcatGraph A B C
  ) <-> (
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

  verina49-concat-definition $a |- (
    VERINA49Concat A B
  ) = (
    iota_ y e. Word ZZ
      ( VERINA49ConcatGraph A B y )
  ) $.
$}

${
  $d i j x A B $.

  verina49-permutation-definition $a |- (
    VERINA49Perm A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    A. x e. ZZ
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

verina49-postcondition-definition $a |- (
  VERINA49Post A B C
) <-> (
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
  (
    ( VERINA49Pairwise C )
    /\
    (
      VERINA49Perm
        ( VERINA49Concat A B )
        C
    )
  )
) $.

verina-advanced-49-merge-sorted-lists $a |- A. a e. Word ZZ
  A. b e. Word ZZ
    (
      ( VERINA49Pre a b )
      ->
      (
        VERINA49Post
          a
          b
          ( VERINA49MergeSortedLists a b )
      )
    )
$.
