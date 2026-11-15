$(
  Statement-only formalization of Thousand Theorems corpus artifact Q848375
  (thousand-theorems__metamath__Q848375), "Implicit function theorem": for
  bundled strictly differentiable maps between arbitrary complete normed
  spaces over an arbitrary nontrivially normed field, with surjective
  derivatives and complementary kernels, the implicit function is the curry
  of the total inverse of the associated local open partial homeomorphism.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q848375HasStrictFDerivAt is the two-point epsilon-delta definition of a
  strict Frechet derivative between arbitrary normed spaces. The derivative
  is required to be both linear and continuous. Q848375IsCompl says that the
  two derivative kernels are complementary: every vector has a unique
  decomposition as the sum of one vector from each kernel.

  Q848375ValidData explicitly unpacks the data fields and proof fields of
  Lean's ImplicitFunctionData structure. Passing these fields separately is
  equivalent to structure packaging; no witness has been moved outside the
  statement. Completeness is expressed by membership in CMetSp, and the
  existential scalar of norm greater than one is SetMM's explicit rendering
  of the nontrivially normed field assumption.

  Q848375ProdDerivInv is the unique inverse of x |-> (L x, M x), and
  Q848375ProdDerivInvNorm is its operator norm for the max product norm.
  Q848375OpenApproxNeighborhoods is the collection used by
  HasStrictFDerivAt.approximates_deriv_on_open_nhds: open sets containing a
  on which x |-> (f x, g x) approximates x |-> (L x, M x) with constant
  ||(L,M)^-1||^-1 / 2.

  The approximation neighborhood N, a default point d of E, and a choice
  function h are existentially scoped inside the final assertion. For each
  target p, Q848375InverseFiber is its preimage in N when nonempty and the
  singleton {d} otherwise. Q848375InverseFiberFamily is the set-sized range of
  this family, and Q848375ChoiceFunction has exactly SetMM's ac5 form on that
  set. Thus Q848375InvFunOn expands Function.invFunOn without introducing a
  global choice selector. Q848375ToOpenPartialHomeomorphSymm is definitionally
  this total function.

  Q848375LocalOpenPartialHomeomorph states the actual local inverse theorem:
  N and T are open neighborhoods of a and (f(a),g(a)); the product map
  restricted to N is a SetMM homeomorphism onto T; and the constructed inverse
  restricted to T is its relational converse. Values of the total inverse
  outside T are deliberately irrelevant, as they are in Lean's bundled open
  partial homeomorphism.

  The final unproved $a assertion also preserves the source declaration's
  defining form: Q848375ImplicitFunction is the curry of this total inverse
  and has the full function type F -> G -> E. This database contains no $p
  proof statement.
$)

$c Q848375HasStrictFDerivAt Q848375IsCompl Q848375ValidData
   Q848375ProdFun Q848375ProdNorm
   Q848375ProdDerivInv Q848375ProdDerivInvNorm
   Q848375ApproximatesOn Q848375OpenApproxNeighborhoods
   Q848375InverseFiber Q848375InverseFiberMap
   Q848375InverseFiberFamily Q848375ChoiceFunction Q848375InvFunOn
   Q848375ToOpenPartialHomeomorphSymm
   Q848375ImplicitFunction Q848375LocalOpenPartialHomeomorph $.

q848375-has-strict-fderiv-at-syntax $a wff
  ( Q848375HasStrictFDerivAt V W f L a ) $.
q848375-is-compl-syntax $a wff
  ( Q848375IsCompl E F G L M ) $.
q848375-valid-data-syntax $a wff
  ( Q848375ValidData K E F G f L g M a ) $.
q848375-prod-fun-syntax $a class
  ( Q848375ProdFun E F G f g ) $.
q848375-prod-norm-syntax $a class
  ( Q848375ProdNorm F G p ) $.
q848375-prod-deriv-inv-syntax $a class
  ( Q848375ProdDerivInv E F G L M ) $.
q848375-prod-deriv-inv-norm-syntax $a class
  ( Q848375ProdDerivInvNorm E F G L M ) $.
q848375-approximates-on-syntax $a wff
  ( Q848375ApproximatesOn E F G f L g M S c ) $.
q848375-open-approx-neighborhoods-syntax $a class
  ( Q848375OpenApproxNeighborhoods E F G f L g M a ) $.
q848375-inverse-fiber-syntax $a class
  ( Q848375InverseFiber E F G f g N d p ) $.
q848375-inverse-fiber-map-syntax $a class
  ( Q848375InverseFiberMap E F G f g N d ) $.
q848375-inverse-fiber-family-syntax $a class
  ( Q848375InverseFiberFamily E F G f g N d ) $.
q848375-choice-function-syntax $a wff
  ( Q848375ChoiceFunction E F G f g N d h ) $.
q848375-inv-fun-on-syntax $a class
  ( Q848375InvFunOn E F G f g N d h ) $.
q848375-to-open-partial-homeomorph-symm-syntax $a class
  ( Q848375ToOpenPartialHomeomorphSymm E F G f g N d h ) $.
q848375-implicit-function-syntax $a class
  ( Q848375ImplicitFunction E F G f g N d h ) $.
q848375-local-open-partial-homeomorph-syntax $a wff
  ( Q848375LocalOpenPartialHomeomorph E F G f g a N T u ) $.

${
  $d L V W a d e f x y $.

  q848375-has-strict-fderiv-at-definition $a |- (
    ( Q848375HasStrictFDerivAt V W f L a )
    <->
    (
      (
        f e. ( ( Base ` W ) ^m ( Base ` V ) )
        /\
        a e. ( Base ` V )
        /\
        L e. ( V LMHom W )
        /\
        L e. ( ( TopOpen ` V ) Cn ( TopOpen ` W ) )
      )
      /\
      A. e e. RR+
        E. d e. RR+
          A. x e. ( Base ` V )
            A. y e. ( Base ` V )
              (
                (
                  (
                    ( norm ` V )
                    `
                    (
                      x
                      ( +g ` V )
                      ( ( -g ` V ) ` a )
                    )
                  )
                  <
                  d
                  /\
                  (
                    ( norm ` V )
                    `
                    (
                      y
                      ( +g ` V )
                      ( ( -g ` V ) ` a )
                    )
                  )
                  <
                  d
                )
                ->
                (
                  ( norm ` W )
                  `
                  (
                    (
                      ( f ` y )
                      ( +g ` W )
                      ( ( -g ` W ) ` ( f ` x ) )
                    )
                    ( +g ` W )
                    (
                      ( -g ` W )
                      `
                      (
                        L
                        `
                        (
                          y
                          ( +g ` V )
                          ( ( -g ` V ) ` x )
                        )
                      )
                    )
                  )
                )
                <_
                (
                  e
                  x.
                  (
                    ( norm ` V )
                    `
                    (
                      y
                      ( +g ` V )
                      ( ( -g ` V ) ` x )
                    )
                  )
                )
              )
    )
  ) $.
$}

${
  $d E F G L M u v x $.

  q848375-is-compl-definition $a |- (
    ( Q848375IsCompl E F G L M )
    <->
    A. x e. ( Base ` E )
      E! u e. ( `' L " { ( 0g ` F ) } )
        E! v e. ( `' M " { ( 0g ` G ) } )
          x
          =
          (
            u
            ( +g ` E )
            v
          )
  ) $.
$}

${
  $d E F G K L M a c f g $.

  q848375-valid-data-definition $a |- (
    ( Q848375ValidData K E F G f L g M a )
    <->
    (
      (
        K e. ( NrmRing i^i Field )
        /\
        E e. { e e. NrmVec | ( Scalar ` e ) = K }
        /\
        F e. { e e. NrmVec | ( Scalar ` e ) = K }
        /\
        G e. { e e. NrmVec | ( Scalar ` e ) = K }
      )
      /\
      (
        E. c e. ( Base ` K )
          1 < ( ( norm ` K ) ` c )
        /\
        E e. CMetSp
        /\
        F e. CMetSp
        /\
        G e. CMetSp
      )
      /\
      (
        Q848375HasStrictFDerivAt E F f L a
      )
      /\
      (
        Q848375HasStrictFDerivAt E G g M a
      )
      /\
      ran L = ( Base ` F )
      /\
      ran M = ( Base ` G )
      /\
      (
        Q848375IsCompl E F G L M
      )
    )
  ) $.
$}

${
  $d E F G f g x $.

  q848375-prod-fun-definition $a |- (
    Q848375ProdFun E F G f g
  ) =
    (
      x e. ( Base ` E ) |->
      <. ( f ` x ) , ( g ` x ) >.
    )
  $.
$}

${
  $d F G p $.

  q848375-prod-norm-definition $a |- (
    Q848375ProdNorm F G p
  ) =
    if
    (
      ( ( norm ` F ) ` ( 1st ` p ) )
      <
      ( ( norm ` G ) ` ( 2nd ` p ) ) ,
      ( ( norm ` G ) ` ( 2nd ` p ) ) ,
      ( ( norm ` F ) ` ( 1st ` p ) )
    )
  $.
$}

${
  $d E F G L M p x $.

  q848375-prod-deriv-inv-definition $a |- (
    Q848375ProdDerivInv E F G L M
  ) =
    (
      p e. ( ( Base ` F ) X. ( Base ` G ) ) |->
      (
        iota_ x e. ( Base ` E )
          <. ( L ` x ) , ( M ` x ) >. = p
      )
    )
  $.
$}

${
  $d E F G L M p r $.

  q848375-prod-deriv-inv-norm-definition $a |- (
    Q848375ProdDerivInvNorm E F G L M
  ) =
    sup
    (
      { r e. RR |
        E. p e. ( ( Base ` F ) X. ( Base ` G ) )
          (
            ( Q848375ProdNorm F G p ) <_ 1
            /\
            r
            =
            (
              ( norm ` E )
              `
              ( ( Q848375ProdDerivInv E F G L M ) ` p )
            )
          )
      } ,
      RR* ,
      <
    )
  $.
$}

${
  $d E F G L M S c f g x y $.

  q848375-approximates-on-definition $a |- (
    ( Q848375ApproximatesOn E F G f L g M S c )
    <->
    A. x e. S
      A. y e. S
        (
          Q848375ProdNorm F G
          <.
            (
              (
                ( f ` y )
                ( +g ` F )
                ( ( -g ` F ) ` ( f ` x ) )
              )
              ( +g ` F )
              (
                ( -g ` F )
                `
                (
                  L
                  `
                  (
                    y
                    ( +g ` E )
                    ( ( -g ` E ) ` x )
                  )
                )
              )
            ) ,
            (
              (
                ( g ` y )
                ( +g ` G )
                ( ( -g ` G ) ` ( g ` x ) )
              )
              ( +g ` G )
              (
                ( -g ` G )
                `
                (
                  M
                  `
                  (
                    y
                    ( +g ` E )
                    ( ( -g ` E ) ` x )
                  )
                )
              )
            )
          >.
          <_
          (
            c
            x.
            (
              ( norm ` E )
              `
              (
                y
                ( +g ` E )
                ( ( -g ` E ) ` x )
              )
            )
          )
        )
  ) $.
$}

${
  $d E F G L M a f g s $.

  q848375-open-approx-neighborhoods-definition $a |- (
    Q848375OpenApproxNeighborhoods E F G f L g M a
  ) =
    { s e. ~P ( Base ` E ) |
      (
        a e. s
        /\
        s e. ( TopOpen ` E )
        /\
        (
          Q848375ApproximatesOn E F G f L g M s
          (
            (
              1
              /
              ( Q848375ProdDerivInvNorm E F G L M )
            )
            /
            2
          )
        )
      )
    }
  $.
$}

${
  $d E F G N d f g p x $.

  q848375-inverse-fiber-definition $a |- (
    Q848375InverseFiber E F G f g N d p
  ) =
    if
    (
      { x e. N | <. ( f ` x ) , ( g ` x ) >. = p } =/= (/) ,
      { x e. N | <. ( f ` x ) , ( g ` x ) >. = p } ,
      { d }
    )
  $.
$}

${
  $d E F G N d f g p $.

  q848375-inverse-fiber-map-definition $a |- (
    Q848375InverseFiberMap E F G f g N d
  ) =
    (
      p e. ( ( Base ` F ) X. ( Base ` G ) ) |->
      ( Q848375InverseFiber E F G f g N d p )
    )
  $.
$}

${
  $d E F G N d f g $.

  q848375-inverse-fiber-family-definition $a |- (
    Q848375InverseFiberFamily E F G f g N d
  ) =
    ran ( Q848375InverseFiberMap E F G f g N d )
  $.
$}

${
  $d E F G N S d f g h $.

  q848375-choice-function-definition $a |- (
    Q848375ChoiceFunction E F G f g N d h
  )
  <->
    (
      h Fn ( Q848375InverseFiberFamily E F G f g N d )
      /\
      A. S e. ( Q848375InverseFiberFamily E F G f g N d )
        ( h ` S ) e. S
    )
  $.
$}

${
  $d E F G N d f g h p $.

  q848375-inv-fun-on-definition $a |- (
    Q848375InvFunOn E F G f g N d h
  ) =
    (
      p e. ( ( Base ` F ) X. ( Base ` G ) ) |->
      (
        h
        `
        ( Q848375InverseFiber E F G f g N d p )
      )
    )
  $.
$}

${
  $d E F G N d f g h $.

  q848375-to-open-partial-homeomorph-symm-definition $a |- (
    Q848375ToOpenPartialHomeomorphSymm E F G f g N d h
  ) =
    ( Q848375InvFunOn E F G f g N d h )
  $.
$}

${
  $d E F G N d f g h $.

q848375-implicit-function-definition $a |- (
    Q848375ImplicitFunction E F G f g N d h
  ) =
    curry
    (
      Q848375ToOpenPartialHomeomorphSymm E F G f g N d h
  )
  $.
$}

${
  $d E F G N T a f g u $.

  q848375-local-open-partial-homeomorph-definition $a |- (
    (
      Q848375LocalOpenPartialHomeomorph E F G f g a N T u
    )
    <->
    (
      N e. ( TopOpen ` E )
      /\
      T e. ( ( TopOpen ` F ) tX ( TopOpen ` G ) )
      /\
      a e. N
      /\
      <. ( f ` a ) , ( g ` a ) >. e. T
      /\
      (
        ( ( Q848375ProdFun E F G f g ) |` N )
        e.
        (
          ( ( TopOpen ` E ) |`t N )
          Homeo
          (
            ( ( TopOpen ` F ) tX ( TopOpen ` G ) )
            |`t T
          )
        )
      )
      /\
      (
        ( u |` T )
        =
        `'
        ( ( Q848375ProdFun E F G f g ) |` N )
      )
    )
  ) $.
$}

${
  $d a d f g h k l m n t v w z $.

  thousand-theorems-q848375-implicit-function $a |-
    A. k A. v A. w A. z A. f A. l A. g A. m A. a
      (
        (
          Q848375ValidData k v w z f l g m a
        )
        ->
        E. n e.
          ( Q848375OpenApproxNeighborhoods v w z f l g m a )
          E. d e. ( Base ` v )
            E. h
              E. t e.
                ( ( TopOpen ` w ) tX ( TopOpen ` z ) )
                (
                  (
                    Q848375ChoiceFunction v w z f g n d h
                  )
                  /\
                  (
                    Q848375LocalOpenPartialHomeomorph
                    v w z f g a n t
                    (
                      Q848375ToOpenPartialHomeomorphSymm
                      v w z f g n d h
                    )
                  )
                  /\
                  (
                    Q848375ToOpenPartialHomeomorphSymm
                    v w z f g n d h
                  )
                  e.
                  (
                    ( Base ` v )
                    ^m
                    ( ( Base ` w ) X. ( Base ` z ) )
                  )
                  /\
                  (
                    Q848375ImplicitFunction v w z f g n d h
                  )
                  =
                  curry
                  (
                    Q848375ToOpenPartialHomeomorphSymm
                    v w z f g n d h
                  )
                  /\
                  (
                    Q848375ImplicitFunction v w z f g n d h
                  )
                  e.
                  (
                    ( ( Base ` v ) ^m ( Base ` z ) )
                    ^m
                    ( Base ` w )
                  )
                )
      )
  $.
$}
