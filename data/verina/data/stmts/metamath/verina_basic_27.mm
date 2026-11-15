$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_27
  (verina__metamath__verina_basic_27), catalog title findFirstRepeatedChar:
  the exact executable left-to-right Unicode-string scan returns the first
  character encountered for a second time, or none when all characters are
  distinct, and satisfies its repetition-and-distinct-prefix correctness
  contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  VERINAB27Char is exactly Lean's Char domain of Unicode scalar values, and
  Word VERINAB27Char represents arbitrary Lean strings extensionally through
  String.toList. VERINAB27ToList is therefore the source conversion and is
  extensionally the identity on this representation. VERINAB27None and
  VERINAB27Some give a disjoint tagged representation of Option Char.

  VERINAB27LoopGraph is the least relation closed under the source loop's
  three exact branches after replacing its index by the equivalent
  unprocessed suffix. An empty suffix returns none. On a nonempty suffix,
  membership of its head in ran seen is exactly Std.HashSet.contains and
  returns that head immediately. Otherwise the head is inserted into seen
  and the tail is scanned recursively. Prepending a newly inserted character
  represents the hash set extensionally because only contains and insert are
  observable. VERINAB27Loop selects the unique result, and
  VERINAB27FindFirstRepeatedChar invokes it on the complete character word
  with the empty seen set. Thus the executable output is fixed independently
  of the postcondition and admits no extra results.

  VERINAB27Count is List.count. VERINAB27IdxOfGraph gives List.idxOf,
  returning the least matching index or the word length when absent.
  VERINAB27SecondIdxGraph gives zipIdx.findIdx for the predicate that the
  character matches while the index differs from idxOf: it returns the least
  such index or the word length when absent. VERINAB27PairwiseDistinctPrefix
  is List.Pairwise inequality on take of that prefix length.

  VERINAB27Pre is the source True precondition together with the String input
  type. VERINAB27Post is the exact source option match: some c requires at
  least two occurrences and a pairwise-distinct prefix before the second
  occurrence, while none requires the whole string to be pairwise distinct.
  The proof-valued precondition argument is computationally and
  propositionally unused and is represented by the explicit antecedent in
  the final correctness assertion. Every earlier $a is syntax or a faithful
  definition required by this rendering, and this database has no $p
  declaration.
$)

$c
  VERINAB27Char VERINAB27ToList
  VERINAB27None VERINAB27Some VERINAB27OptionChar
  VERINAB27LoopGraph VERINAB27Loop
  VERINAB27Pre VERINAB27FindFirstRepeatedChar
  VERINAB27Count
  VERINAB27IdxOfGraph VERINAB27IdxOf
  VERINAB27SecondIdxGraph VERINAB27SecondIdx
  VERINAB27PairwiseDistinctPrefix
  VERINAB27Post
$.

verinab27-char-syntax
  $a class VERINAB27Char $.
verinab27-to-list-syntax
  $a class ( VERINAB27ToList A ) $.
verinab27-none-syntax
  $a class VERINAB27None $.
verinab27-some-syntax
  $a class ( VERINAB27Some A ) $.
verinab27-option-char-syntax
  $a class VERINAB27OptionChar $.
verinab27-loop-graph-syntax
  $a wff ( VERINAB27LoopGraph A B C ) $.
verinab27-loop-syntax
  $a class ( VERINAB27Loop A B ) $.
verinab27-precondition-syntax
  $a wff ( VERINAB27Pre A ) $.
verinab27-program-syntax
  $a class ( VERINAB27FindFirstRepeatedChar A ) $.
verinab27-count-syntax
  $a class ( VERINAB27Count A B ) $.
verinab27-idx-of-graph-syntax
  $a wff ( VERINAB27IdxOfGraph A B C ) $.
verinab27-idx-of-syntax
  $a class ( VERINAB27IdxOf A B ) $.
verinab27-second-idx-graph-syntax
  $a wff ( VERINAB27SecondIdxGraph A B C ) $.
verinab27-second-idx-syntax
  $a class ( VERINAB27SecondIdx A B ) $.
verinab27-pairwise-distinct-prefix-syntax
  $a wff ( VERINAB27PairwiseDistinctPrefix A B ) $.
verinab27-postcondition-syntax
  $a wff ( VERINAB27Post A B ) $.

verinab27-char-definition $a |- VERINAB27Char =
  { x e. NN0 |
    (
      x < ; ; ; ; ; ; 1 1 1 4 1 1 2
      /\
      (
        x < ; ; ; ; 5 5 2 9 6
        \/
        ; ; ; ; 5 7 3 4 3 < x
      )
    )
  } $.

verinab27-to-list-definition $a |- (
  VERINAB27ToList A
) = A $.

verinab27-none-definition $a |- VERINAB27None = (/) $.

verinab27-some-definition $a |- (
  VERINAB27Some A
) = <. 1 , A >. $.

${
  $d x y $.

  verinab27-option-char-definition $a |- VERINAB27OptionChar = {
    x |
    (
      x = VERINAB27None
      \/
      E. y e. VERINAB27Char
        x = ( VERINAB27Some y )
    )
  } $.
$}

${
  $d R A B C h t s y $.

  verinab27-loop-graph-definition $a |- (
    VERINAB27LoopGraph A B C
  ) <-> (
    (
      (
        A e. Word VERINAB27Char
        /\
        B e. Word VERINAB27Char
      )
      /\
      C e. VERINAB27OptionChar
    )
    /\
    A. R
      (
        (
          (
            A. s e. Word VERINAB27Char
              <.
                <. (/) , s >.
                ,
                VERINAB27None
              >. e. R
            /\
            A. h e. VERINAB27Char
              A. t e. Word VERINAB27Char
                A. s e. Word VERINAB27Char
                  (
                    h e. ran s
                    ->
                    <.
                      <. ( <" h "> ++ t ) , s >.
                      ,
                      ( VERINAB27Some h )
                    >. e. R
                  )
          )
          /\
          A. h e. VERINAB27Char
            A. t e. Word VERINAB27Char
              A. s e. Word VERINAB27Char
                A. y e. VERINAB27OptionChar
                  (
                    (
                      h e/ ran s
                      /\
                      <.
                        <. t , ( <" h "> ++ s ) >.
                        ,
                        y
                      >. e. R
                    )
                    ->
                    <.
                      <. ( <" h "> ++ t ) , s >.
                      ,
                      y
                    >. e. R
                  )
        )
        ->
        <. <. A , B >. , C >. e. R
      )
  ) $.
$}

${
  $d y A B $.

  verinab27-loop-definition $a |- (
    VERINAB27Loop A B
  ) = (
    iota_ y e. VERINAB27OptionChar
      ( VERINAB27LoopGraph A B y )
  ) $.
$}

verinab27-precondition-definition $a |- (
  VERINAB27Pre A
) <-> (
  A e. Word VERINAB27Char
) $.

verinab27-program-definition $a |- (
  VERINAB27FindFirstRepeatedChar A
) = (
  VERINAB27Loop
    ( VERINAB27ToList A )
    (/)
) $.

${
  $d i A B $.

  verinab27-count-definition $a |- (
    VERINAB27Count A B
  ) = (
    # ` {
      i e. ( 0 ..^ ( # ` A ) )
      |
      ( A ` i ) = B
    }
  ) $.
$}

${
  $d i j A B C $.

  verinab27-idx-of-graph-definition $a |- (
    VERINAB27IdxOfGraph A B C
  ) <-> (
    (
      (
        A e. Word VERINAB27Char
        /\
        B e. VERINAB27Char
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
          ( A ` C ) = B
        )
        /\
        A. j e. ( 0 ..^ C )
          ( A ` j ) =/= B
      )
      \/
      (
        C = ( # ` A )
        /\
        A. i e. ( 0 ..^ ( # ` A ) )
          ( A ` i ) =/= B
      )
    )
  ) $.
$}

${
  $d y A B $.

  verinab27-idx-of-definition $a |- (
    VERINAB27IdxOf A B
  ) = (
    iota_ y e. NN0
      ( VERINAB27IdxOfGraph A B y )
  ) $.
$}

${
  $d i j A B C $.

  verinab27-second-idx-graph-definition $a |- (
    VERINAB27SecondIdxGraph A B C
  ) <-> (
    (
      (
        A e. Word VERINAB27Char
        /\
        B e. VERINAB27Char
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
            C =/= ( VERINAB27IdxOf A B )
          )
        )
        /\
        A. j e. ( 0 ..^ C )
          -.
          (
            ( A ` j ) = B
            /\
            j =/= ( VERINAB27IdxOf A B )
          )
      )
      \/
      (
        C = ( # ` A )
        /\
        A. i e. ( 0 ..^ ( # ` A ) )
          -.
          (
            ( A ` i ) = B
            /\
            i =/= ( VERINAB27IdxOf A B )
          )
      )
    )
  ) $.
$}

${
  $d y A B $.

  verinab27-second-idx-definition $a |- (
    VERINAB27SecondIdx A B
  ) = (
    iota_ y e. NN0
      ( VERINAB27SecondIdxGraph A B y )
  ) $.
$}

${
  $d i j A B $.

  verinab27-pairwise-distinct-prefix-definition $a |- (
    VERINAB27PairwiseDistinctPrefix A B
  ) <-> (
    (
      (
        A e. Word VERINAB27Char
        /\
        B e. NN0
      )
      /\
      B <_ ( # ` A )
    )
    /\
    A. i e. ( 0 ..^ B )
      A. j e. ( 0 ..^ B )
        (
          i < j
          ->
          ( A ` i ) =/= ( A ` j )
        )
  ) $.
$}

${
  $d c A B $.

  verinab27-postcondition-definition $a |- (
    VERINAB27Post A B
  ) <-> (
    (
      A e. Word VERINAB27Char
      /\
      B e. VERINAB27OptionChar
    )
    /\
    (
      (
        B = VERINAB27None
        /\
        (
          VERINAB27PairwiseDistinctPrefix
            A
            ( # ` A )
        )
      )
      \/
      E. c e. VERINAB27Char
        (
          B = ( VERINAB27Some c )
          /\
          (
            2 <_ ( VERINAB27Count A c )
            /\
            (
              VERINAB27PairwiseDistinctPrefix
                A
                ( VERINAB27SecondIdx A c )
            )
          )
        )
    )
  ) $.
$}

verina-basic-27-find-first-repeated-char
  $a |- A. s e. Word VERINAB27Char
    (
      ( VERINAB27Pre s )
      ->
      (
        VERINAB27Post
          s
          ( VERINAB27FindFirstRepeatedChar s )
      )
    )
  $.
