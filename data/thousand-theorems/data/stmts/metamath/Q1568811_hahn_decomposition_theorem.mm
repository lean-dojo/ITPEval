$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1568811
  (thousand-theorems__metamath__Q1568811), "Hahn decomposition theorem":
  every real-valued signed measure on an arbitrary measurable space admits
  complementary measurable positive and negative sets. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  Q1568811SignedMeasure M S says that M is a sigma-algebra and S is a
  real-valued function on every subset of its carrier. It vanishes on
  nonmeasurable sets, as Lean's bundled SignedMeasure does, and is countably
  additive on every NN0-indexed pairwise-disjoint sequence of measurable sets,
  including convergence of the real series.

  Q1568811Positive and Q1568811Negative say respectively that every subset of
  the indicated set has nonnegative or nonpositive signed measure. Because S
  vanishes off M, this is exactly Lean's restriction-order predicate.
  Q1568811Complementary says that the two sets are disjoint and have union
  equal to the carrier U. M.

  The final declaration is the single unproved corpus $a statement. All
  preceding $a declarations are syntax or faithful definitions, and this
  database contains no $p proof statement.
$)

$c Q1568811SignedMeasure Q1568811Positive Q1568811Negative
   Q1568811Complementary $.

q1568811-signed-measure-syntax
  $a wff ( Q1568811SignedMeasure M S ) $.
q1568811-positive-syntax
  $a wff ( Q1568811Positive M S I ) $.
q1568811-negative-syntax
  $a wff ( Q1568811Negative M S J ) $.
q1568811-complementary-syntax
  $a wff ( Q1568811Complementary M I J ) $.

${
  $d A F M S m n $.

  q1568811-signed-measure-definition $a |- (
    ( Q1568811SignedMeasure M S )
    <->
    (
      M e. U. ran sigAlgebra
      /\
      (
        S : ~P U. M --> RR
        /\
        (
          ( S ` (/) ) = 0
          /\
          (
            A. A e. ( ~P U. M \ M )
              ( S ` A ) = 0
            /\
            A. F e. ( M ^m NN0 )
              (
                (
                  A. n e. NN0 A. m e. NN0
                    (
                      n =/= m
                      ->
                      ( ( F ` n ) i^i ( F ` m ) ) = (/)
                    )
                )
                ->
                (
                  seq 0
                    (
                      + ,
                      ( n e. NN0 |-> ( S ` ( F ` n ) ) )
                    )
                    e. dom ~~>
                  /\
                  ( S ` U. ran F )
                  =
                  sum_ n e. NN0 ( S ` ( F ` n ) )
                )
              )
          )
        )
      )
    )
  ) $.
$}

${
  $d A I M S $.

  q1568811-positive-definition $a |- (
    ( Q1568811Positive M S I )
    <->
    A. A e. ~P U. M
      (
        A C_ I
        ->
        0 <_ ( S ` A )
      )
  ) $.
$}

${
  $d A J M S $.

  q1568811-negative-definition $a |- (
    ( Q1568811Negative M S J )
    <->
    A. A e. ~P U. M
      (
        A C_ J
        ->
        ( S ` A ) <_ 0
      )
  ) $.
$}

${
  $d I J M $.

  q1568811-complementary-definition $a |- (
    ( Q1568811Complementary M I J )
    <->
    (
      ( I i^i J ) = (/)
      /\
      ( I u. J ) = U. M
    )
  ) $.
$}

${
  $d I J M S $.

  thousand-theorems-q1568811-hahn-decomposition $a |-
    A. M e. U. ran sigAlgebra
      A. S
        (
          ( Q1568811SignedMeasure M S )
          ->
          E. I e. M E. J e. M
            (
              ( Q1568811Positive M S I )
              /\
              (
                ( Q1568811Negative M S J )
                /\
                ( Q1568811Complementary M I J )
              )
            )
        )
  $.
$}
