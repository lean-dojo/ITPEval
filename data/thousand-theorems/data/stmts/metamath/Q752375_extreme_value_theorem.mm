$(
  Statement-only formalization of Thousand Theorems corpus artifact Q752375
  (thousand-theorems__metamath__Q752375), "Extreme value theorem": a continuous
  function from a nonempty compact subset of an arbitrary topological space
  into a linearly ordered topological space whose lower order intervals are
  closed attains its minimum on that subset. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q752375LinearOrder states that R is a reflexive, antisymmetric, transitive,
  total relation on Y. Q752375ClosedIicTopology states that K is a topology on
  Y and every lower interval {b in Y | b R a} is K-closed, exactly the
  ClosedIicTopology assumption of the Lean source.

  In the final assertion, (J |`t S) e. Comp expresses compactness of S with
  its subspace topology, and membership of F restricted to S in the SetMM Cn
  class expresses ContinuousOn F S. The conclusion retains the source's
  internal witness x in S and says that F(x) is below F(y) for every y in S.

  The final declaration is the single unproved corpus $a statement. All
  preceding $a declarations are syntax or faithful definitions, and this
  database contains no $p proof statement.
$)

$c Q752375LinearOrder Q752375ClosedIicTopology $.

q752375-linear-order-syntax
  $a wff ( Q752375LinearOrder R Y ) $.
q752375-closed-iic-topology-syntax
  $a wff ( Q752375ClosedIicTopology R Y K ) $.

${
  $d R Y a b c $.

  q752375-linear-order-definition $a |- (
    ( Q752375LinearOrder R Y )
    <->
    (
      R C_ ( Y X. Y )
      /\
      A. a e. Y A. b e. Y A. c e. Y
        (
          a R a
          /\
          (
            ( ( a R b /\ b R a ) -> a = b )
            /\
            (
              ( ( a R b /\ b R c ) -> a R c )
              /\
              ( a R b \/ b R a )
            )
          )
        )
    )
  ) $.
$}

${
  $d K R Y a b $.

  q752375-closed-iic-topology-definition $a |- (
    ( Q752375ClosedIicTopology R Y K )
    <->
    (
      K e. ( TopOn ` Y )
      /\
      A. a e. Y
        { b e. Y | b R a } e. ( Clsd ` K )
    )
  ) $.
$}

${
  $d F J K R S X Y a b c x y $.

  thousand-theorems-q752375-extreme-value-theorem $a |-
    A. X A. Y A. J A. K A. R A. S A. F
      (
        (
          (
            J e. ( TopOn ` X )
            /\
            (
              ( Q752375LinearOrder R Y )
              /\
              ( Q752375ClosedIicTopology R Y K )
            )
          )
          /\
          (
            S C_ X
            /\
            F : X --> Y
          )
        )
        ->
        (
          (
            (
              ( J |`t S ) e. Comp
              /\
              S =/= (/)
            )
            /\
            (
              F |` S
            )
            e.
            (
              ( J |`t S )
              Cn
              K
            )
          )
          ->
          E. x e. S
            A. y e. S
              ( F ` x ) R ( F ` y )
        )
      )
  $.
$}
