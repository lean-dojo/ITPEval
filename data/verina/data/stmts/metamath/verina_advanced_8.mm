$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_8 (verina__metamath__verina_advanced_8), catalog title
  canCompleteCircuit: the exact greedy gas-station circuit computation on
  equal nonempty finite integer lists, with its impossibility-or-least-valid-
  start correctness contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains. Word ZZ
  is exactly the type of arbitrary finite integer lists, and
  Word ( ZZ X. ZZ ) is the type of arbitrary finite lists of integer pairs.
  For a word w, # ` w is its natural-number length, w ` k is zero-based
  lookup, and 0 ..^ ( # ` w ) is its complete index set.

  VERINA8Sum is the source integer foldl addition from zero. VERINA8ZipGraph
  and VERINA8Zip reproduce List.zip, including truncation to the shorter
  input. VERINA8LoopGraph preserves the source's unused local loop helper on
  all typed arguments: it consumes paired heads, resets the tank and advances
  the candidate start after a negative tank, returns the start when both
  lists end together, and returns -1 on a length mismatch.

  VERINA8WalkGraph is the exact execution trace of the local walk helper used
  by the program. Its integer-tank and natural-start traces process the zipped
  pairs from left to right with precisely the source reset rule.
  VERINA8CanCompleteCircuit first compares the two source sums and returns -1
  when total gas is smaller; otherwise it invokes walk on the exact zip with
  initial index, tank, and start all zero. Thus the executable result is fixed
  independently of the postcondition and no extra output is admitted.

  VERINA8GetBang is Lean's zero-default List.get! indexing.
  VERINA8PrefixGraph exactly records the postcondition's foldl over
  List.range (i + 1), using the circular index (start + j) modulo the gas-list
  length. VERINA8Valid requires every such prefix accumulator through one
  complete circuit to be nonnegative. VERINA8Pre preserves the nonempty,
  equal-length input condition. VERINA8Post preserves the lower result bound,
  the universal impossibility condition for -1, and the valid least-index
  condition for every nonnegative result. The proof-valued precondition
  arguments are computationally and propositionally unused inside the source
  program and postcondition, and the final assertion supplies the complete
  precondition as its explicit antecedent.

  The final $a declaration is the complete source correctness proposition.
  Every earlier $a is syntax or a faithful definition required by this
  rendering, and this database has no $p declaration.
$)

$c
  VERINA8NatMin VERINA8Sum
  VERINA8ZipGraph VERINA8Zip
  VERINA8LoopGraph VERINA8Loop
  VERINA8WalkGraph VERINA8Walk
  VERINA8CanCompleteCircuit
  VERINA8GetBang VERINA8PrefixGraph VERINA8Prefix VERINA8Valid
  VERINA8Pre VERINA8Post
$.

verina8-nat-min-syntax
  $a class ( VERINA8NatMin A B ) $.
verina8-sum-syntax
  $a class ( VERINA8Sum A ) $.
verina8-zip-graph-syntax
  $a wff ( VERINA8ZipGraph A B C ) $.
verina8-zip-syntax
  $a class ( VERINA8Zip A B ) $.
verina8-loop-graph-syntax
  $a wff ( VERINA8LoopGraph A B C D E F ) $.
verina8-loop-syntax
  $a class ( VERINA8Loop A B C D E ) $.
verina8-walk-graph-syntax
  $a wff ( VERINA8WalkGraph A B C D E ) $.
verina8-walk-syntax
  $a class ( VERINA8Walk A B C D ) $.
verina8-program-syntax
  $a class ( VERINA8CanCompleteCircuit A B ) $.
verina8-get-bang-syntax
  $a class ( VERINA8GetBang A B ) $.
verina8-prefix-graph-syntax
  $a wff ( VERINA8PrefixGraph A B C D E ) $.
verina8-prefix-syntax
  $a class ( VERINA8Prefix A B C D ) $.
verina8-valid-syntax
  $a wff ( VERINA8Valid A B C ) $.
verina8-precondition-syntax
  $a wff ( VERINA8Pre A B ) $.
verina8-postcondition-syntax
  $a wff ( VERINA8Post A B C ) $.

verina8-nat-min-definition $a |- (
  VERINA8NatMin A B
) = if (
  A < B ,
  A ,
  B
) $.

${
  $d k A $.

  verina8-sum-definition $a |- (
    VERINA8Sum A
  ) = (
    sum_ k e. ( 0 ..^ ( # ` A ) )
      ( A ` k )
  ) $.
$}

${
  $d k A B C $.

  verina8-zip-graph-definition $a |- (
    VERINA8ZipGraph A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. Word ZZ
      )
      /\
      C e. Word ( ZZ X. ZZ )
    )
    /\
    (
      (
        # ` C
      ) = (
        VERINA8NatMin
          ( # ` A )
          ( # ` B )
      )
      /\
      A. k e. ( 0 ..^ ( # ` C ) )
        (
          C ` k
        ) = <.
          ( A ` k )
          ,
          ( B ` k )
        >.
    )
  ) $.
$}

${
  $d y A B $.

  verina8-zip-definition $a |- (
    VERINA8Zip A B
  ) = (
    iota_ y e. Word ( ZZ X. ZZ )
      ( VERINA8ZipGraph A B y )
  ) $.
$}

${
  $d k m s t A B C D E F $.

  verina8-loop-graph-definition $a |- (
    VERINA8LoopGraph A B C D E F
  ) <-> (
    (
      (
        (
          A e. Word ZZ
          /\
          B e. Word ZZ
        )
        /\
        (
          C e. NN0
          /\
          D e. ZZ
        )
      )
      /\
      (
        E e. NN0
        /\
        F e. ZZ
      )
    )
    /\
    E. m e. NN0 E. t e. Word ZZ E. s e. Word NN0
      (
        m = (
          VERINA8NatMin
            ( # ` A )
            ( # ` B )
        )
        /\
        (
          (
            (
              ( # ` t ) = ( m + 1 )
              /\
              ( # ` s ) = ( m + 1 )
            )
            /\
            (
              ( t ` 0 ) = D
              /\
              ( s ` 0 ) = E
            )
          )
          /\
          (
            A. k e. ( 0 ..^ m )
              (
                (
                  t ` ( k + 1 )
                ) = if (
                  (
                    (
                      ( t ` k ) + ( A ` k )
                    ) - ( B ` k )
                  ) < 0 ,
                  0 ,
                  (
                    ( t ` k ) + ( A ` k )
                  ) - ( B ` k )
                )
                /\
                (
                  s ` ( k + 1 )
                ) = if (
                  (
                    (
                      ( t ` k ) + ( A ` k )
                    ) - ( B ` k )
                  ) < 0 ,
                  ( ( C + k ) + 1 ) ,
                  ( s ` k )
                )
              )
            /\
            F = if (
              ( # ` A ) = ( # ` B ) ,
              ( s ` m ) ,
              ( -u 1 )
            )
          )
        )
      )
  ) $.
$}

${
  $d y A B C D E $.

  verina8-loop-definition $a |- (
    VERINA8Loop A B C D E
  ) = (
    iota_ y e. ZZ
      ( VERINA8LoopGraph A B C D E y )
  ) $.
$}

${
  $d k s t A B C D E $.

  verina8-walk-graph-definition $a |- (
    VERINA8WalkGraph A B C D E
  ) <-> (
    (
      (
        (
          A e. Word ( ZZ X. ZZ )
          /\
          B e. NN0
        )
        /\
        (
          C e. ZZ
          /\
          D e. NN0
        )
      )
      /\
      E e. ZZ
    )
    /\
    E. t e. Word ZZ E. s e. Word NN0
      (
        (
          (
            ( # ` t ) = ( ( # ` A ) + 1 )
            /\
            ( # ` s ) = ( ( # ` A ) + 1 )
          )
          /\
          (
            ( t ` 0 ) = C
            /\
            ( s ` 0 ) = D
          )
        )
        /\
        (
          A. k e. ( 0 ..^ ( # ` A ) )
            (
              (
                t ` ( k + 1 )
              ) = if (
                (
                  (
                    ( t ` k )
                    +
                    ( 1st ` ( A ` k ) )
                  )
                  -
                  ( 2nd ` ( A ` k ) )
                ) < 0 ,
                0 ,
                (
                  (
                    ( t ` k )
                    +
                    ( 1st ` ( A ` k ) )
                  )
                  -
                  ( 2nd ` ( A ` k ) )
                )
              )
              /\
              (
                s ` ( k + 1 )
              ) = if (
                (
                  (
                    ( t ` k )
                    +
                    ( 1st ` ( A ` k ) )
                  )
                  -
                  ( 2nd ` ( A ` k ) )
                ) < 0 ,
                ( ( B + k ) + 1 ) ,
                ( s ` k )
              )
            )
          /\
          E = ( s ` ( # ` A ) )
        )
      )
  ) $.
$}

${
  $d y A B C D $.

  verina8-walk-definition $a |- (
    VERINA8Walk A B C D
  ) = (
    iota_ y e. ZZ
      ( VERINA8WalkGraph A B C D y )
  ) $.
$}

verina8-program-definition $a |- (
  VERINA8CanCompleteCircuit A B
) = if (
  ( VERINA8Sum A ) < ( VERINA8Sum B ) ,
  ( -u 1 ) ,
  (
    VERINA8Walk
      ( VERINA8Zip A B )
      0
      0
      0
  )
) $.

verina8-get-bang-definition $a |- (
  VERINA8GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

${
  $d j t A B C D E $.

  verina8-prefix-graph-definition $a |- (
    VERINA8PrefixGraph A B C D E
  ) <-> (
    (
      (
        (
          A e. Word ZZ
          /\
          B e. Word ZZ
        )
        /\
        (
          C e. NN0
          /\
          D e. NN0
        )
      )
      /\
      E e. ZZ
    )
    /\
    E. t e. Word ZZ
      (
        (
          ( # ` t ) = ( ( D + 1 ) + 1 )
          /\
          ( t ` 0 ) = 0
        )
        /\
        (
          A. j e. ( 0 ..^ ( D + 1 ) )
            (
              t ` ( j + 1 )
            ) = (
              (
                ( t ` j )
                +
                (
                  VERINA8GetBang
                    A
                    (
                      ( C + j )
                      mod
                      ( # ` A )
                    )
                )
              )
              -
              (
                VERINA8GetBang
                  B
                  (
                    ( C + j )
                    mod
                    ( # ` A )
                  )
              )
            )
          /\
          E = ( t ` ( D + 1 ) )
        )
      )
  ) $.
$}

${
  $d y A B C D $.

  verina8-prefix-definition $a |- (
    VERINA8Prefix A B C D
  ) = (
    iota_ y e. ZZ
      ( VERINA8PrefixGraph A B C D y )
  ) $.
$}

${
  $d i A B C $.

  verina8-valid-definition $a |- (
    VERINA8Valid A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. Word ZZ
      )
      /\
      C e. NN0
    )
    /\
    A. i e. ( 0 ..^ ( # ` A ) )
      0 <_ (
        VERINA8Prefix A B C i
      )
  ) $.
$}

verina8-precondition-definition $a |- (
  VERINA8Pre A B
) <-> (
  (
    A e. Word ZZ
    /\
    B e. Word ZZ
  )
  /\
  (
    0 < ( # ` A )
    /\
    ( # ` A ) = ( # ` B )
  )
) $.

${
  $d s A B C $.

  verina8-postcondition-definition $a |- (
    VERINA8Post A B C
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
      ( -u 1 ) <_ C
      /\
      (
        (
          C = ( -u 1 )
          ->
          A. s e. ( 0 ..^ ( # ` A ) )
            -. ( VERINA8Valid A B s )
        )
        /\
        (
          0 <_ C
          ->
          (
            C < ( # ` A )
            /\
            (
              ( VERINA8Valid A B C )
              /\
              A. s e. ( 0 ..^ C )
                -. ( VERINA8Valid A B s )
            )
          )
        )
      )
    )
  ) $.
$}

verina-advanced-8-can-complete-circuit $a |- A. g e. Word ZZ
  A. c e. Word ZZ
    (
      ( VERINA8Pre g c )
      ->
      (
        VERINA8Post
          g
          c
          ( VERINA8CanCompleteCircuit g c )
      )
    )
$.
