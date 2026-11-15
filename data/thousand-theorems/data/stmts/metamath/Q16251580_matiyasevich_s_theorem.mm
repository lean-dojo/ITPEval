$(
  Statement-only formalization of Thousand Theorems corpus artifact Q16251580
  (thousand-theorems__metamath__Q16251580), "Matiyasevich's theorem": a
  natural pair lies at a given index of the Pell sequence with parameter a
  exactly when the stated system of Pell equations, divisibility conditions,
  inequalities, and congruences has a solution. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The source's proof-valued parameter a1 : 1 < a is represented by the
  proposition 1 < a. The functions f and g on 0 ... k expand the mutually
  recursive definitions of Pell.xn and Pell.yn: they start at (1,0), use
  d = a*a-1, and end at (x,y). Existence of these finite recursive graphs is
  bidirectionally equivalent to the source Pell-sequence equalities.

  Q16251580NatSub is Lean's truncated subtraction on natural numbers.
  Q16251580ModEq is Lean's total Nat.ModEq: at modulus zero it compares the
  original naturals, and at a positive modulus it compares SetMM remainders.
  The existential multiplier q is exactly the natural divisibility condition
  y*y divides v. Every auxiliary $a is syntax or a faithful definition; the
  final $a is the unproved corpus statement, and this database has no $p
  proof statement.
$)

$c Q16251580NatSub Q16251580ModEq $.

q16251580-nat-sub-syntax
  $a class ( Q16251580NatSub A B ) $.
q16251580-mod-eq-syntax
  $a wff ( Q16251580ModEq A B M ) $.

q16251580-nat-sub-definition $a |- (
  Q16251580NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

q16251580-mod-eq-definition $a |- (
  ( Q16251580ModEq A B M )
  <->
  if (
    M = 0 ,
    A ,
    ( A mod M )
  )
  =
  if (
    M = 0 ,
    B ,
    ( B mod M )
  )
) $.

${
  $d a b f g k n q s t u v x y $.

  thousand-theorems-q16251580-matiyasevich $a |-
    A. a e. NN0
      A. k e. NN0
        A. x e. NN0
          A. y e. NN0
            (
              (
                1 < a
                /\
                E. f e. ( NN0 ^m ( 0 ... k ) )
                  E. g e. ( NN0 ^m ( 0 ... k ) )
                    (
                      (
                        (
                          ( f ` 0 ) = 1
                          /\
                          ( g ` 0 ) = 0
                        )
                        /\
                        A. n e. ( 0 ..^ k )
                          (
                            (
                              f ` ( n + 1 )
                            )
                            =
                            (
                              (
                                ( f ` n )
                                x.
                                a
                              )
                              +
                              (
                                ( Q16251580NatSub ( a x. a ) 1 )
                                x.
                                ( g ` n )
                              )
                            )
                            /\
                            (
                              g ` ( n + 1 )
                            )
                            =
                            (
                              ( f ` n )
                              +
                              (
                                ( g ` n )
                                x.
                                a
                              )
                            )
                          )
                      )
                      /\
                      (
                        ( f ` k ) = x
                        /\
                        ( g ` k ) = y
                      )
                    )
              )
              <->
              (
                1 < a
                /\
                (
                  k <_ y
                  /\
                  (
                    (
                      x = 1
                      /\
                      y = 0
                    )
                    \/
                    E. u e. NN0
                      E. v e. NN0
                        E. s e. NN0
                          E. t e. NN0
                            E. b e. NN0
                              (
                              (
                                Q16251580NatSub
                                ( x x. x )
                                (
                                  (
                                    ( Q16251580NatSub ( a x. a ) 1 )
                                    x.
                                    y
                                  )
                                    x.
                                    y
                                  )
                                )
                                =
                                1
                                /\
                                (
                                  Q16251580NatSub
                                  ( u x. u )
                                  (
                                    (
                                      ( Q16251580NatSub ( a x. a ) 1 )
                                      x.
                                      v
                                    )
                                    x.
                                    v
                                  )
                                  =
                                  1
                                  /\
                                  (
                                    Q16251580NatSub
                                    ( s x. s )
                                    (
                                      (
                                        ( Q16251580NatSub ( b x. b ) 1 )
                                        x.
                                        t
                                      )
                                      x.
                                      t
                                    )
                                    =
                                    1
                                    /\
                                    (
                                      1 < b
                                      /\
                                      (
                                        ( Q16251580ModEq b 1 ( 4 x. y ) )
                                        /\
                                        (
                                          ( Q16251580ModEq b a u )
                                          /\
                                          (
                                            0 < v
                                            /\
                                            (
                                              E. q e. NN0
                                                v
                                                =
                                                (
                                                  ( y x. y )
                                                  x.
                                                  q
                                              )
                                              /\
                                              (
                                                ( Q16251580ModEq s x u )
                                                /\
                                                ( Q16251580ModEq
                                                  t k ( 4 x. y )
                                                )
                                              )
                                            )
                                          )
                                        )
                                      )
                                    )
                                  )
                                )
                              )
                  )
                )
              )
            )
  $.
$}
