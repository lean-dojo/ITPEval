$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1752621
  (thousand-theorems__metamath__Q1752621), "Sylvester's law of inertia":
  every quadratic form on a finite-dimensional real vector space is linearly
  equivalent to a weighted sum of coordinate squares whose weights are
  minus one, zero, or one. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q1752621Quadratic V Q says that Q is a real quadratic form on V. Its
  internally existential symmetric bilinear polarization B is additive and
  real-homogeneous in the first argument; symmetry supplies the corresponding
  laws in the second argument, and Q is the diagonal of B. Over the reals this
  is bidirectionally equivalent to mathlib's QuadraticForm structure.

  For finite-dimensional V, RRfld freeLMod ( 1 ... ( dim ` V ) ) is the full
  real coordinate module of the same dimension. Membership of F in LMIso is
  precisely a bijective real-linear map. The final equality therefore states
  exactly that Q is equivalent along F to the weighted sum of squares. Both
  the weight function and the equivalence remain internally existential, and
  the zero-dimensional case is retained.

  The definition below is a faithful bidirectional definition. The final $a
  declaration is the single unproved corpus statement; this database contains
  no $p proof statement.
$)

$c Q1752621Quadratic $.

q1752621-quadratic-syntax
  $a wff ( Q1752621Quadratic V Q ) $.

${
  $d B Q V a x y z $.

  q1752621-quadratic-definition $a |- (
    ( Q1752621Quadratic V Q )
    <->
    (
      Q : ( Base ` V ) --> RR
      /\
      E. B
        (
          B : ( ( Base ` V ) X. ( Base ` V ) ) --> RR
          /\
          (
            A. x e. ( Base ` V )
              A. y e. ( Base ` V )
                A. z e. ( Base ` V )
                  (
                    B ` <. ( x ( +g ` V ) y ) , z >.
                  )
                  =
                  (
                    ( B ` <. x , z >. )
                    +
                    ( B ` <. y , z >. )
                  )
            /\
            (
              A. a e. RR
                A. x e. ( Base ` V )
                  A. y e. ( Base ` V )
                    (
                      B ` <. ( a ( .s ` V ) x ) , y >.
                    )
                    =
                    (
                      a
                      x.
                      ( B ` <. x , y >. )
                    )
              /\
              (
                A. x e. ( Base ` V )
                  A. y e. ( Base ` V )
                    (
                      B ` <. x , y >.
                    )
                    =
                    (
                      B ` <. y , x >.
                    )
                /\
                A. x e. ( Base ` V )
                  ( Q ` x ) = ( B ` <. x , x >. )
              )
            )
          )
        )
    )
  ) $.
$}

${
  $d F Q V i v w x $.

  thousand-theorems-q1752621-sylvester-law-of-inertia $a |- (
    A. V e. { v e. LMod | ( Scalar ` v ) = RRfld }
      A. Q
        (
          (
            ( dim ` V ) e. NN0
            /\
            ( Q1752621Quadratic V Q )
          )
          ->
          E. w
            (
              (
                w : ( 1 ... ( dim ` V ) ) --> RR
                /\
                A. i e. ( 1 ... ( dim ` V ) )
                  (
                    ( w ` i ) = ( -u 1 )
                    \/
                    (
                      ( w ` i ) = 0
                      \/
                      ( w ` i ) = 1
                    )
                  )
              )
              /\
              E. F e.
                (
                  V
                  LMIso
                  (
                    RRfld
                    freeLMod
                    ( 1 ... ( dim ` V ) )
                  )
                )
                A. x e. ( Base ` V )
                  (
                    Q ` x
                  )
                  =
                  (
                    sum_ i e. ( 1 ... ( dim ` V ) )
                      (
                        ( w ` i )
                        x.
                        (
                          (
                            ( F ` x )
                            ` i
                          )
                          ^ 2
                        )
                      )
                  )
            )
        )
  ) $.
$}
