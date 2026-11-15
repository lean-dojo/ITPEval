$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_55 (verina__metamath__verina_advanced_55), catalog title
  mostFrequent: the exact frequency-map computation returns the most frequent
  integer in an arbitrary nonempty finite integer list, breaking ties by the
  first occurrence in the original list, with its full correctness contract.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer lists. For a word
  w, # ` w is its natural-number length, w ` i is zero-based lookup, ran w
  is its membership set, and 0 ..^ ( # ` w ) is its complete index set.
  VERINA55Count is the source countP with integer equality.

  A Std HashMap is represented extensionally by a canonical word of
  key-count pairs, ordered by the keys' first occurrences in the input.
  VERINA55CountMapGraph and VERINA55CountMap give exactly the finite map
  produced by the source fold: every distinct input integer occurs once,
  paired with its total multiplicity. This canonical ordering replaces only
  unobservable HashMap bucket order.

  VERINA55MaxFrequencyGraph and VERINA55GetMaxFrequency reproduce the fold
  maximum over the map values, including zero for an empty map.
  VERINA55CandidatesGraph and VERINA55GetCandidates reproduce filter followed
  by key extraction on the canonical map. The source HashMap.toList may order
  these same distinct keys differently, but getFirstWithFreq observes its
  candidates argument only through List.contains, so the canonical list has
  exactly the same membership and gives a bidirectionally equivalent program
  computation. VERINA55FirstWithFreqGraph selects the least original-list
  index whose value belongs to the candidate list, or zero when none exists,
  exactly matching find? and its default. VERINA55MostFrequent explicitly
  composes these four helper computations, fixing the implementation result
  independently of the postcondition.

  VERINA55Pre is the source nonempty-list precondition. VERINA55Post states
  that the result occurs in the input, has frequency at least that of every
  input entry, and is the head of the input filtered to entries having the
  result's frequency. The last clause is expressed by the least qualifying
  original index and is bidirectionally equivalent to the source head? =
  some result equation. The proof-valued precondition argument is
  computationally unused and is represented by the explicit antecedent of
  the final correctness assertion. Every earlier $a is syntax or a faithful
  definition, and this database has no $p declaration.
$)

$c
  VERINA55Count
  VERINA55CountMapGraph VERINA55CountMap
  VERINA55MaxFrequencyGraph VERINA55GetMaxFrequency
  VERINA55CandidatesGraph VERINA55GetCandidates
  VERINA55FirstWithFreqGraph VERINA55GetFirstWithFreq
  VERINA55Pre VERINA55MostFrequent VERINA55Post
$.

verina55-count-syntax
  $a class ( VERINA55Count A B ) $.
verina55-count-map-graph-syntax
  $a wff ( VERINA55CountMapGraph A B ) $.
verina55-count-map-syntax
  $a class ( VERINA55CountMap A ) $.
verina55-max-frequency-graph-syntax
  $a wff ( VERINA55MaxFrequencyGraph A B ) $.
verina55-get-max-frequency-syntax
  $a class ( VERINA55GetMaxFrequency A ) $.
verina55-candidates-graph-syntax
  $a wff ( VERINA55CandidatesGraph A B C ) $.
verina55-get-candidates-syntax
  $a class ( VERINA55GetCandidates A B ) $.
verina55-first-with-freq-graph-syntax
  $a wff ( VERINA55FirstWithFreqGraph A B C ) $.
verina55-get-first-with-freq-syntax
  $a class ( VERINA55GetFirstWithFreq A B ) $.
verina55-precondition-syntax
  $a wff ( VERINA55Pre A ) $.
verina55-most-frequent-syntax
  $a class ( VERINA55MostFrequent A ) $.
verina55-postcondition-syntax
  $a wff ( VERINA55Post A B ) $.

${
  $d i A B $.

  verina55-count-definition $a |- (
    VERINA55Count A B
  ) = (
    # ` {
      i e. ( 0 ..^ ( # ` A ) )
      |
      ( A ` i ) = B
    }
  ) $.
$}

${
  $d i j k p A B $.

  verina55-count-map-graph-definition $a |- (
    VERINA55CountMapGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ( ZZ X. NN0 )
    )
    /\
    E. p e. Word NN0
      (
        ( # ` p ) = ( # ` B )
        /\
        (
          A. j e. ( 0 ..^ ( # ` B ) )
            (
              (
                ( p ` j ) < ( # ` A )
                /\
                A. i e. ( 0 ..^ ( p ` j ) )
                  ( A ` i ) =/= ( A ` ( p ` j ) )
              )
              /\
              (
                B ` j
              ) = <.
                ( A ` ( p ` j ) ) ,
                ( VERINA55Count A ( A ` ( p ` j ) ) )
              >.
            )
          /\
          (
            A. j e. ( 0 ..^ ( # ` B ) )
              A. k e. ( 0 ..^ ( # ` B ) )
                (
                  j < k
                  ->
                  ( p ` j ) < ( p ` k )
                )
            /\
            A. i e. ( 0 ..^ ( # ` A ) )
              E. j e. ( 0 ..^ ( # ` B ) )
                ( A ` i ) = ( 1st ` ( B ` j ) )
          )
        )
      )
  ) $.
$}

${
  $d y A $.

  verina55-count-map-definition $a |- (
    VERINA55CountMap A
  ) = (
    iota_ y e. Word ( ZZ X. NN0 )
      ( VERINA55CountMapGraph A y )
  ) $.
$}

${
  $d i j A B $.

  verina55-max-frequency-graph-definition $a |- (
    VERINA55MaxFrequencyGraph A B
  ) <-> (
    (
      A e. Word ( ZZ X. NN0 )
      /\
      B e. NN0
    )
    /\
    (
      (
        ( # ` A ) = 0
        /\
        B = 0
      )
      \/
      E. i e. ( 0 ..^ ( # ` A ) )
        (
          B = ( 2nd ` ( A ` i ) )
          /\
          A. j e. ( 0 ..^ ( # ` A ) )
            ( 2nd ` ( A ` j ) ) <_ B
        )
    )
  ) $.
$}

${
  $d y A $.

  verina55-get-max-frequency-definition $a |- (
    VERINA55GetMaxFrequency A
  ) = (
    iota_ y e. NN0
      ( VERINA55MaxFrequencyGraph A y )
  ) $.
$}

${
  $d i j k p A B C $.

  verina55-candidates-graph-definition $a |- (
    VERINA55CandidatesGraph A B C
  ) <-> (
    (
      (
        A e. Word ( ZZ X. NN0 )
        /\
        B e. NN0
      )
      /\
      C e. Word ZZ
    )
    /\
    E. p e. Word NN0
      (
        ( # ` p ) = ( # ` C )
        /\
        (
          A. j e. ( 0 ..^ ( # ` C ) )
            (
              (
                ( p ` j ) < ( # ` A )
                /\
                ( 2nd ` ( A ` ( p ` j ) ) ) = B
              )
              /\
              ( C ` j ) = ( 1st ` ( A ` ( p ` j ) ) )
            )
          /\
          (
            A. j e. ( 0 ..^ ( # ` C ) )
              A. k e. ( 0 ..^ ( # ` C ) )
                (
                  j < k
                  ->
                  ( p ` j ) < ( p ` k )
                )
            /\
            A. i e. ( 0 ..^ ( # ` A ) )
              (
                ( 2nd ` ( A ` i ) ) = B
                ->
                E. j e. ( 0 ..^ ( # ` C ) )
                  ( p ` j ) = i
              )
          )
        )
      )
  ) $.
$}

${
  $d y A B $.

  verina55-get-candidates-definition $a |- (
    VERINA55GetCandidates A B
  ) = (
    iota_ y e. Word ZZ
      ( VERINA55CandidatesGraph A B y )
  ) $.
$}

${
  $d i j A B C $.

  verina55-first-with-freq-graph-definition $a |- (
    VERINA55FirstWithFreqGraph A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. Word ZZ
      )
      /\
      C e. ZZ
    )
    /\
    (
      E. i e. ( 0 ..^ ( # ` A ) )
        (
          ( A ` i ) e. ran B
          /\
          (
            C = ( A ` i )
            /\
            A. j e. ( 0 ..^ i )
              -. ( ( A ` j ) e. ran B )
          )
        )
      \/
      (
        -.
        E. i e. ( 0 ..^ ( # ` A ) )
          ( A ` i ) e. ran B
        /\
        C = 0
      )
    )
  ) $.
$}

${
  $d y A B $.

  verina55-get-first-with-freq-definition $a |- (
    VERINA55GetFirstWithFreq A B
  ) = (
    iota_ y e. ZZ
      ( VERINA55FirstWithFreqGraph A B y )
  ) $.
$}

verina55-precondition-definition $a |- (
  VERINA55Pre A
) <-> (
  (
    A e. Word ZZ
    /\
    0 < ( # ` A )
  )
) $.

verina55-most-frequent-definition $a |- (
  VERINA55MostFrequent A
) = (
  VERINA55GetFirstWithFreq
    A
    (
      VERINA55GetCandidates
        ( VERINA55CountMap A )
        (
          VERINA55GetMaxFrequency
            ( VERINA55CountMap A )
        )
    )
) $.

${
  $d i j A B $.

  verina55-postcondition-definition $a |- (
    VERINA55Post A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. ZZ
    )
    /\
    (
      B e. ran A
      /\
      (
        A. i e. ( 0 ..^ ( # ` A ) )
          (
            VERINA55Count A ( A ` i )
          ) <_ (
            VERINA55Count A B
          )
        /\
        E. i e. ( 0 ..^ ( # ` A ) )
          (
            ( A ` i ) = B
            /\
            A. j e. ( 0 ..^ i )
              (
                VERINA55Count A ( A ` j )
              ) =/= (
                VERINA55Count A B
              )
          )
      )
    )
  ) $.
$}

verina-advanced-55-most-frequent
  $a |- A. w e. Word ZZ
    (
      ( VERINA55Pre w )
      ->
      (
        VERINA55Post
          w
          ( VERINA55MostFrequent w )
      )
    )
  $.
