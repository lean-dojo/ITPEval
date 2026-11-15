$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_63 (verina__metamath__verina_advanced_63), catalog title
  removeDuplicates: the exact recursive adjacent-change counter computes the
  number of distinct entries in an arbitrary finite nondecreasing integer
  list, with the stated eraseDups-length correctness contract. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer lists. For a word
  w, # ` w is its natural-number length, w ` i is zero-based lookup, ran w
  is its set of entries, and 0 ..^ ( # ` w ) is its complete index set.

  VERINA63NatSub is Lean's truncated natural subtraction. VERINA63State stores
  the previous integer and the current natural count. VERINA63Update is one
  exact source countUniques step: an entry equal to the previous one leaves
  the state unchanged, while a different entry becomes the new previous one
  and increments the count. VERINA63CountUniquesGraph records the complete
  deterministic trace for arbitrary helper arguments, and
  VERINA63CountUniques selects its unique result.

  VERINA63TailGraph and VERINA63Tail reproduce List.tail.
  VERINA63RemoveDuplicates preserves the source match: it returns zero for
  the empty word, and otherwise scans the tail from the head and count one.
  Thus the implementation result is fixed independently of the postcondition.

  VERINA63Pairwise is exactly List.Pairwise with integer <=, and VERINA63Pre
  is the source nondecreasing-list precondition. VERINA63EraseDupsLengthGraph
  characterizes the length of List.eraseDups: a duplicate-free finite word
  with exactly the same entry set has one position for each distinct input
  value, so every witness has exactly eraseDups.length positions.
  VERINA63EraseDupsLength selects that unique natural length.

  VERINA63Post is the source conjunction of truncated subtraction being zero
  and eraseDups.length being at most the result. The proof-valued precondition
  argument is computationally and propositionally unused and is represented
  by the explicit antecedent of the final correctness assertion. Every
  earlier $a is syntax or a faithful definition, and this database has no
  $p declaration.
$)

$c
  VERINA63NatSub
  VERINA63State VERINA63Update
  VERINA63CountUniquesGraph VERINA63CountUniques
  VERINA63TailGraph VERINA63Tail
  VERINA63Pairwise VERINA63Pre
  VERINA63RemoveDuplicates
  VERINA63EraseDupsLengthGraph VERINA63EraseDupsLength
  VERINA63Post
$.

verina63-nat-sub-syntax
  $a class ( VERINA63NatSub A B ) $.
verina63-state-syntax
  $a class VERINA63State $.
verina63-update-syntax
  $a class ( VERINA63Update A B ) $.
verina63-count-uniques-graph-syntax
  $a wff ( VERINA63CountUniquesGraph A B C D ) $.
verina63-count-uniques-syntax
  $a class ( VERINA63CountUniques A B C ) $.
verina63-tail-graph-syntax
  $a wff ( VERINA63TailGraph A B ) $.
verina63-tail-syntax
  $a class ( VERINA63Tail A ) $.
verina63-pairwise-syntax
  $a wff ( VERINA63Pairwise A ) $.
verina63-precondition-syntax
  $a wff ( VERINA63Pre A ) $.
verina63-program-syntax
  $a class ( VERINA63RemoveDuplicates A ) $.
verina63-erase-dups-length-graph-syntax
  $a wff ( VERINA63EraseDupsLengthGraph A B ) $.
verina63-erase-dups-length-syntax
  $a class ( VERINA63EraseDupsLength A ) $.
verina63-postcondition-syntax
  $a wff ( VERINA63Post A B ) $.

verina63-nat-sub-definition $a |- (
  VERINA63NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

verina63-state-definition $a |- VERINA63State = (
  ZZ X. NN0
) $.

verina63-update-definition $a |- (
  VERINA63Update A B
) = if (
  A = ( 1st ` B ) ,
  B ,
  <. A , ( ( 2nd ` B ) + 1 ) >.
) $.

${
  $d i t A B C D $.

  verina63-count-uniques-graph-definition $a |- (
    VERINA63CountUniquesGraph A B C D
  ) <-> (
    (
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
      D e. NN0
    )
    /\
    E. t e. Word VERINA63State
      (
        (
          ( # ` t ) = ( ( # ` A ) + 1 )
          /\
          ( t ` 0 ) = <. B , C >.
        )
        /\
        (
          A. i e. ( 0 ..^ ( # ` A ) )
            (
              t ` ( i + 1 )
            ) = (
              VERINA63Update
                ( A ` i )
                ( t ` i )
            )
          /\
          D = ( 2nd ` ( t ` ( # ` A ) ) )
        )
      )
  ) $.
$}

${
  $d y A B C $.

  verina63-count-uniques-definition $a |- (
    VERINA63CountUniques A B C
  ) = (
    iota_ y e. NN0
      ( VERINA63CountUniquesGraph A B C y )
  ) $.
$}

${
  $d j A B $.

  verina63-tail-graph-definition $a |- (
    VERINA63TailGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    (
      ( # ` B ) = ( VERINA63NatSub ( # ` A ) 1 )
      /\
      A. j e. ( 0 ..^ ( # ` B ) )
        ( B ` j ) = ( A ` ( j + 1 ) )
    )
  ) $.
$}

${
  $d y A $.

  verina63-tail-definition $a |- (
    VERINA63Tail A
  ) = (
    iota_ y e. Word ZZ
      ( VERINA63TailGraph A y )
  ) $.
$}

${
  $d i j A $.

  verina63-pairwise-definition $a |- (
    VERINA63Pairwise A
  ) <-> (
    A e. Word ZZ
    /\
    A. i e. ( 0 ..^ ( # ` A ) )
      A. j e. ( 0 ..^ ( # ` A ) )
        (
          i < j
          ->
          ( A ` i ) <_ ( A ` j )
        )
  ) $.
$}

verina63-precondition-definition $a |- (
  VERINA63Pre A
) <-> (
  VERINA63Pairwise A
) $.

verina63-program-definition $a |- (
  VERINA63RemoveDuplicates A
) = if (
  ( # ` A ) = 0 ,
  0 ,
  (
    VERINA63CountUniques
      ( VERINA63Tail A )
      ( A ` 0 )
      1
  )
) $.

${
  $d i j u A B $.

  verina63-erase-dups-length-graph-definition $a |- (
    VERINA63EraseDupsLengthGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. NN0
    )
    /\
    E. u e. Word ZZ
      (
        (
          ( # ` u ) = B
          /\
          ran u = ran A
        )
        /\
        A. i e. ( 0 ..^ ( # ` u ) )
          A. j e. ( 0 ..^ ( # ` u ) )
            (
              i < j
              ->
              ( u ` i ) =/= ( u ` j )
            )
      )
  ) $.
$}

${
  $d y A $.

  verina63-erase-dups-length-definition $a |- (
    VERINA63EraseDupsLength A
  ) = (
    iota_ y e. NN0
      ( VERINA63EraseDupsLengthGraph A y )
  ) $.
$}

verina63-postcondition-definition $a |- (
  VERINA63Post A B
) <-> (
  (
    A e. Word ZZ
    /\
    B e. NN0
  )
  /\
  (
    (
      VERINA63NatSub
        B
        ( VERINA63EraseDupsLength A )
    ) = 0
    /\
    ( VERINA63EraseDupsLength A ) <_ B
  )
) $.

verina-advanced-63-remove-duplicates $a |- A. w e. Word ZZ
  (
    ( VERINA63Pre w )
    ->
    (
      VERINA63Post
        w
        ( VERINA63RemoveDuplicates w )
    )
  )
$.
