$(
  Statement-only formalization of Thousand Theorems corpus artifact Q33481
  (thousand-theorems__metamath__Q33481), "Arrow's impossibility theorem":
  every social welfare function on a finite electorate and at least three
  designated alternatives that satisfies weak Pareto and independence of
  irrelevant alternatives is a dictatorship on those alternatives. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  A preference order on A is represented by a reflexive, total, transitive
  relation on A. Q33481PrefOrders A is the set of all such relations, and
  Q33481Profiles A I is the full set of I-indexed preference profiles.
  Strict preference is the asymmetric part of a preference order.

  Weak Pareto, independence of irrelevant alternatives, and dictatorship
  are expanded with the same quantifier scopes as the Lean source and are
  restricted only to the finite set X of designated alternatives. The
  ambient alternative set A remains arbitrary. All declarations before the
  final assertion are syntax or faithful definitions; the final $a is the
  unproved corpus statement, and there are no $p declarations.
$)

$c Q33481PrefOrder Q33481PrefOrders Q33481Profiles Q33481Strict
   Q33481SameOrder Q33481WeakPareto Q33481IIA Q33481Dictatorship $.

q33481-pref-order-syntax $a
  wff ( Q33481PrefOrder A R ) $.
q33481-pref-orders-syntax $a
  class ( Q33481PrefOrders A ) $.
q33481-profiles-syntax $a
  class ( Q33481Profiles A I ) $.
q33481-strict-syntax $a
  wff ( Q33481Strict R A B ) $.
q33481-same-order-syntax $a
  wff ( Q33481SameOrder R Q A B ) $.
q33481-weak-pareto-syntax $a
  wff ( Q33481WeakPareto A I X F ) $.
q33481-iia-syntax $a
  wff ( Q33481IIA A I X F ) $.
q33481-dictatorship-syntax $a
  wff ( Q33481Dictatorship A I X F ) $.

${
  $d A R x y z $.

  q33481-pref-order-definition $a |- (
    ( Q33481PrefOrder A R )
    <->
    (
      R C_ ( A X. A )
      /\
      (
        A. x e. A x R x
        /\
        (
          A. x e. A A. y e. A ( x R y \/ y R x )
          /\
          A. x e. A A. y e. A A. z e. A
            ( ( x R y /\ y R z ) -> x R z )
        )
      )
    )
  ) $.
$}

${
  $d A r $.

  q33481-pref-orders-definition $a |- (
    ( Q33481PrefOrders A )
    =
    { r e. ~P ( A X. A ) | ( Q33481PrefOrder A r ) }
  ) $.
$}

${
  $d A I $.

  q33481-profiles-definition $a |- (
    ( Q33481Profiles A I ) = ( ( Q33481PrefOrders A ) ^m I )
  ) $.
$}

${
  $d A B R $.

  q33481-strict-definition $a |- (
    ( Q33481Strict R A B )
    <->
    ( A R B /\ -. B R A )
  ) $.
$}

${
  $d A B Q R $.

  q33481-same-order-definition $a |- (
    ( Q33481SameOrder R Q A B )
    <->
    (
      ( ( Q33481Strict R A B ) <-> ( Q33481Strict Q A B ) )
      /\
      ( ( Q33481Strict R B A ) <-> ( Q33481Strict Q B A ) )
    )
  ) $.
$}

${
  $d A F I X i r x y $.

  q33481-weak-pareto-definition $a |- (
    ( Q33481WeakPareto A I X F )
    <->
    A. x e. X A. y e. X A. r e. ( Q33481Profiles A I )
      (
        A. i e. I ( Q33481Strict ( r ` i ) x y )
        ->
        ( Q33481Strict ( F ` r ) x y )
      )
  ) $.
$}

${
  $d A F I X i q r x y $.

  q33481-iia-definition $a |- (
    ( Q33481IIA A I X F )
    <->
    A. r e. ( Q33481Profiles A I )
      A. q e. ( Q33481Profiles A I )
        A. x e. X A. y e. X
          (
            A. i e. I
              ( Q33481SameOrder ( r ` i ) ( q ` i ) x y )
            ->
            ( Q33481SameOrder ( F ` r ) ( F ` q ) x y )
          )
  ) $.
$}

${
  $d A F I X i r x y $.

  q33481-dictatorship-definition $a |- (
    ( Q33481Dictatorship A I X F )
    <->
    E. i e. I A. x e. X A. y e. X
      A. r e. ( Q33481Profiles A I )
        (
          ( Q33481Strict ( r ` i ) x y )
          ->
          ( Q33481Strict ( F ` r ) x y )
        )
  ) $.
$}

${
  $d a f j s $.

  thousand-theorems-q33481-arrow-impossibility $a |- (
    A. a A. j A. s A. f
      (
        (
          (
            (
              j e. Fin
              /\
              ( s e. Fin /\ s C_ a )
            )
            /\
            (
              3 <_ ( # ` s )
              /\
              f : ( Q33481Profiles a j ) --> ( Q33481PrefOrders a )
            )
          )
          /\
          (
            ( Q33481WeakPareto a j s f )
            /\
            ( Q33481IIA a j s f )
          )
        )
        ->
        ( Q33481Dictatorship a j s f )
      )
  ) $.
$}
