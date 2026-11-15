$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_12, catalog title firstDuplicate: an executable
  left-to-right scan of a finite integer list returns the first value whose
  occurrence repeats, or none when the list has no duplicate, together with
  its count and second-occurrence correctness contract. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain, and Word ZZ is exactly the type of
  arbitrary finite integer lists. For a word w, # ` w is its length, w ` k
  is zero-based lookup, and 0 ..^ ( # ` w ) is its complete index set.

  VERINA12None, VERINA12Some, and VERINA12OptionInt give a disjoint tagged
  encoding of Option Int. VERINA12Count is List.count. The predicate
  VERINA12DuplicateAt seen rem k says that rem[k] is already in seen or
  occurs earlier in rem. Consequently VERINA12HelperGraph selects the least
  such k and returns some rem[k], or returns none exactly when no such k
  exists. VERINA12Helper is the unique output of that graph, and
  VERINA12FirstDuplicate applies it to the empty seen word and the input
  word. This is the exact graph of the source recursion on every pair of
  typed seen and remaining lists, not merely an output satisfying the
  postcondition.

  VERINA12SecondOccGraph is exactly secondOccIdx. With at least two
  occurrences it returns the least index that has an earlier equal entry;
  with exactly one occurrence it returns the list length; and with no
  occurrence it returns length plus one, matching idxOf and drop/idxOf in
  every case. VERINA12Nodup and VERINA12Post reproduce List.Nodup and the
  Option match, duplicate-count clause, and list-wide comparison of second
  occurrence indices. The proof-valued True precondition argument is
  computationally unused and is omitted from the target function. The final
  $a declaration applies that executable result to the complete
  postcondition under the source precondition. Every earlier $a is syntax or
  a faithful definition, and this database has no $p declaration.
$)

$c
  VERINA12None VERINA12Some VERINA12OptionInt
  VERINA12Count VERINA12DuplicateAt
  VERINA12HelperGraph VERINA12Helper VERINA12FirstDuplicate
  VERINA12Pre VERINA12Nodup
  VERINA12SecondOccGraph VERINA12SecondOccIdx VERINA12Post
$.

verina12-none-syntax $a class VERINA12None $.
verina12-some-syntax $a class ( VERINA12Some A ) $.
verina12-option-int-syntax $a class VERINA12OptionInt $.
verina12-count-syntax $a class ( VERINA12Count A B ) $.
verina12-duplicate-at-syntax
  $a wff ( VERINA12DuplicateAt A B C ) $.
verina12-helper-graph-syntax
  $a wff ( VERINA12HelperGraph A B C ) $.
verina12-helper-syntax $a class ( VERINA12Helper A B ) $.
verina12-first-duplicate-syntax
  $a class ( VERINA12FirstDuplicate A ) $.
verina12-precondition-syntax $a wff ( VERINA12Pre A ) $.
verina12-nodup-syntax $a wff ( VERINA12Nodup A ) $.
verina12-second-occ-graph-syntax
  $a wff ( VERINA12SecondOccGraph A B C ) $.
verina12-second-occ-idx-syntax
  $a class ( VERINA12SecondOccIdx A B ) $.
verina12-postcondition-syntax $a wff ( VERINA12Post A B ) $.

verina12-none-definition $a |- VERINA12None = (/) $.

verina12-some-definition $a |- (
  VERINA12Some A
) = <. 1 , A >. $.

${
  $d x y $.

  verina12-option-int-definition $a |- VERINA12OptionInt =
    { x |
      (
        x = VERINA12None
        \/
        E. y e. ZZ x = ( VERINA12Some y )
      )
    } $.
$}

${
  $d k A B $.

  verina12-count-definition $a |- (
    VERINA12Count A B
  ) = (
    # ` {
      k e. ( 0 ..^ ( # ` B ) )
      |
      ( B ` k ) = A
    }
  ) $.
$}

${
  $d j A B C $.

  verina12-duplicate-at-definition $a |- (
    VERINA12DuplicateAt A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. Word ZZ
      )
      /\
      C e. ( 0 ..^ ( # ` B ) )
    )
    /\
    (
      ( B ` C ) e. ran A
      \/
      E. j e. ( 0 ..^ C )
        ( B ` j ) = ( B ` C )
    )
  ) $.
$}

${
  $d k m A B C $.

  verina12-helper-graph-definition $a |- (
    VERINA12HelperGraph A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. Word ZZ
      )
      /\
      C e. VERINA12OptionInt
    )
    /\
    (
      E. k e. ( 0 ..^ ( # ` B ) )
        (
          ( VERINA12DuplicateAt A B k )
          /\
          (
            C = ( VERINA12Some ( B ` k ) )
            /\
            A. m e. ( 0 ..^ k )
              -. ( VERINA12DuplicateAt A B m )
          )
        )
      \/
      (
        -.
        E. k e. ( 0 ..^ ( # ` B ) )
          ( VERINA12DuplicateAt A B k )
        /\
        C = VERINA12None
      )
    )
  ) $.
$}

${
  $d o A B $.

  verina12-helper-definition $a |- (
    VERINA12Helper A B
  ) = (
    iota_ o e. VERINA12OptionInt
      ( VERINA12HelperGraph A B o )
  ) $.
$}

verina12-first-duplicate-definition $a |- (
  VERINA12FirstDuplicate A
) = (
  VERINA12Helper (/) A
) $.

verina12-precondition-definition $a |- (
  VERINA12Pre A
) <-> (
  A e. Word ZZ
) $.

${
  $d i j A $.

  verina12-nodup-definition $a |- (
    VERINA12Nodup A
  ) <-> (
    (
      A e. Word ZZ
      /\
      A. i e. ( 0 ..^ ( # ` A ) )
        A. j e. ( 0 ..^ ( # ` A ) )
          (
            i =/= j
            ->
            ( A ` i ) =/= ( A ` j )
          )
    )
  ) $.
$}

${
  $d i j k A B C $.

  verina12-second-occ-graph-definition $a |- (
    VERINA12SecondOccGraph A B C
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
        (
          C e. ( 0 ..^ ( # ` A ) )
          /\
          (
            ( A ` C ) = B
            /\
            E. j e. ( 0 ..^ C )
              ( A ` j ) = B
          )
        )
        /\
        A. k e. ( 0 ..^ C )
          -.
          (
            ( A ` k ) = B
            /\
            E. i e. ( 0 ..^ k )
              ( A ` i ) = B
          )
      )
      \/
      (
        ( VERINA12Count B A ) = 1
        /\
        C = ( # ` A )
      )
      \/
      (
        ( VERINA12Count B A ) = 0
        /\
        C = ( ( # ` A ) + 1 )
      )
    )
  ) $.
$}

${
  $d n A B $.

  verina12-second-occ-idx-definition $a |- (
    VERINA12SecondOccIdx A B
  ) = (
    iota_ n e. NN0
      ( VERINA12SecondOccGraph A B n )
  ) $.
$}

${
  $d k x A B $.

  verina12-postcondition-definition $a |- (
    VERINA12Post A B
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. VERINA12OptionInt
      )
      /\
      (
        (
          B = VERINA12None
          /\
          ( VERINA12Nodup A )
        )
        \/
        E. x e. ZZ
          (
            B = ( VERINA12Some x )
            /\
            (
              1 < ( VERINA12Count x A )
              /\
              A. k e. ( 0 ..^ ( # ` A ) )
                (
                  ( VERINA12Count ( A ` k ) A ) = 1
                  \/
                  (
                    VERINA12SecondOccIdx A x
                  ) <_ (
                    VERINA12SecondOccIdx A ( A ` k )
                  )
                )
            )
          )
      )
    )
  ) $.
$}

verina-advanced-12-first-duplicate $a |- A. w e. Word ZZ
  (
    ( VERINA12Pre w )
    ->
    (
      VERINA12Post
        w
        ( VERINA12FirstDuplicate w )
    )
  )
$.
