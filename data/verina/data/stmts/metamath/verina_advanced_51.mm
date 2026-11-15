$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_51 (verina__metamath__verina_advanced_51), catalog title
  mergeSorted: the exact executable recursive merge of two arbitrary finite
  nondecreasing integer lists returns a nondecreasing permutation of their
  concatenation. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain, and Word ZZ is exactly the type of
  arbitrary finite integer lists. For a word w, # ` w is its length, w ` k
  is zero-based lookup, and 0 ..^ ( # ` w ) is its complete index set.

  VERINA51Next and VERINA51Pick encode one exact step of mergeSortedAux. A
  state is the pair of current zero-based positions in the two input words.
  If the first input is exhausted, the next element is taken from the second;
  if only the second is exhausted, it is taken from the first; otherwise the
  first element is taken exactly when it is <= the second, matching the
  source tie behavior.

  VERINA51MergeAuxGraph records the unique complete state trace and every
  emitted integer for exactly #A + #B steps. Processing an exhausted
  remainder one element at a time has exactly the same output as the source
  base cases returning that remainder. VERINA51MergeSortedAux selects the
  unique output of this graph, exactly representing the source helper, and
  VERINA51MergeSorted is the source executable wrapper. Thus neither is an
  unconstrained function or selected from the postcondition.

  VERINA51Pairwise is List.Pairwise with integer <=. VERINA51Pre is the
  conjunction of that property for the two typed inputs. VERINA51Concat is
  exact word concatenation, and VERINA51Perm is List.isPerm, represented by
  equality of the multiplicity of every integer. VERINA51Post requires the
  result to be pairwise nondecreasing and a permutation of the concatenated
  inputs. The proof-valued precondition argument is computationally unused
  and is omitted from the target function; the postcondition's corresponding
  proof argument is propositionally unused and is likewise omitted. The
  final $a declaration is the source correctness proposition. Every earlier
  $a is syntax or a faithful definition, and this database has no $p
  declaration.
$)

$c
  VERINA51Next VERINA51Pick
  VERINA51MergeAuxGraph VERINA51MergeSortedAux VERINA51MergeSorted
  VERINA51Pairwise VERINA51Pre
  VERINA51ConcatGraph VERINA51Concat
  VERINA51Perm VERINA51Post
$.

verina51-next-syntax
  $a class ( VERINA51Next A B C ) $.
verina51-pick-syntax
  $a class ( VERINA51Pick A B C ) $.
verina51-merge-aux-graph-syntax
  $a wff ( VERINA51MergeAuxGraph A B C ) $.
verina51-merge-sorted-aux-syntax
  $a class ( VERINA51MergeSortedAux A B ) $.
verina51-merge-sorted-syntax
  $a class ( VERINA51MergeSorted A B ) $.
verina51-pairwise-syntax
  $a wff ( VERINA51Pairwise A ) $.
verina51-precondition-syntax
  $a wff ( VERINA51Pre A B ) $.
verina51-concat-graph-syntax
  $a wff ( VERINA51ConcatGraph A B C ) $.
verina51-concat-syntax
  $a class ( VERINA51Concat A B ) $.
verina51-permutation-syntax
  $a wff ( VERINA51Perm A B ) $.
verina51-postcondition-syntax
  $a wff ( VERINA51Post A B C ) $.

verina51-next-definition $a |- (
  VERINA51Next A B C
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

verina51-pick-definition $a |- (
  VERINA51Pick A B C
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

  verina51-merge-aux-graph-definition $a |- (
    VERINA51MergeAuxGraph A B C
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
                  VERINA51Next A B ( t ` k )
                )
                /\
                (
                  C ` k
                ) = (
                  VERINA51Pick A B ( t ` k )
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

  verina51-merge-sorted-aux-definition $a |- (
    VERINA51MergeSortedAux A B
  ) = (
    iota_ y e. Word ZZ
      ( VERINA51MergeAuxGraph A B y )
  ) $.
$}

verina51-merge-sorted-definition $a |- (
  VERINA51MergeSorted A B
) = (
  VERINA51MergeSortedAux A B
) $.

${
  $d i j A $.

  verina51-pairwise-definition $a |- (
    VERINA51Pairwise A
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

verina51-precondition-definition $a |- (
  VERINA51Pre A B
) <-> (
  (
    A e. Word ZZ
    /\
    B e. Word ZZ
  )
  /\
  (
    ( VERINA51Pairwise A )
    /\
    ( VERINA51Pairwise B )
  )
) $.

${
  $d k A B C $.

  verina51-concat-graph-definition $a |- (
    VERINA51ConcatGraph A B C
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

  verina51-concat-definition $a |- (
    VERINA51Concat A B
  ) = (
    iota_ y e. Word ZZ
      ( VERINA51ConcatGraph A B y )
  ) $.
$}

${
  $d i j x A B $.

  verina51-permutation-definition $a |- (
    VERINA51Perm A B
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

verina51-postcondition-definition $a |- (
  VERINA51Post A B C
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
    ( VERINA51Pairwise C )
    /\
    (
      VERINA51Perm
        C
        ( VERINA51Concat A B )
    )
  )
) $.

verina-advanced-51-merge-sorted $a |- A. a e. Word ZZ
  A. b e. Word ZZ
    (
      ( VERINA51Pre a b )
      ->
      (
        VERINA51Post
          a
          b
          ( VERINA51MergeSorted a b )
      )
    )
$.
