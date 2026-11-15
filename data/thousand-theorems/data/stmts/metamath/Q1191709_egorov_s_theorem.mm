$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1191709
  (thousand-theorems__metamath__Q1191709), "Egorov's theorem": an almost
  everywhere convergent family of strongly measurable functions on a
  measurable set of finite measure converges uniformly outside a measurable
  subset of arbitrarily small measure. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q1191709SemilatticeSup says that R is a partial order on the nonempty set I
  and U chooses the binary least upper bound. The separate cardinal comparison
  I ~<_ NN0 is SetMM's assertion that I is countable.

  D e. ( PsMet ` B ) is SetMM's native extended nonnegative pseudometric on
  the arbitrary carrier B; distinct points may have distance zero and distance
  may be +oo. Its induced topology is
  unifTop ` ( metUnif ` D ).

  Q1191709StronglyMeasurable uses the defining characterization by pointwise
  limits of finite-range simple functions whose singleton fibers are
  measurable. Q1191709AEConverges expands convergence along the at-top filter
  outside a measurable null set, and Q1191709UniformlyOn expands uniform
  convergence along that same filter. Positive real radii give the usual
  convergence criterion for an extended pseudometric.

  The final declaration is the single unproved corpus $a statement. All
  preceding $a declarations are syntax or faithful definitions, and this
  database contains no $p proof statement.
$)

$c Q1191709SemilatticeSup Q1191709StronglyMeasurable
   Q1191709AEConverges Q1191709UniformlyOn $.

q1191709-semilattice-sup-syntax
  $a wff ( Q1191709SemilatticeSup I R U ) $.
q1191709-strongly-measurable-syntax
  $a wff ( Q1191709StronglyMeasurable M B D H ) $.
q1191709-ae-converges-syntax
  $a wff ( Q1191709AEConverges M B D I R F G S ) $.
q1191709-uniformly-on-syntax
  $a wff ( Q1191709UniformlyOn B D I R F G S ) $.

${
  $d I R U x y z $.

  q1191709-semilattice-sup-definition $a |- (
    ( Q1191709SemilatticeSup I R U )
    <->
    (
      I =/= (/)
      /\
      (
        R C_ ( I X. I )
        /\
        (
          U : ( I X. I ) --> I
          /\
          (
            A. x e. I <. x , x >. e. R
            /\
            (
              A. x e. I A. y e. I
                (
                  (
                    <. x , y >. e. R
                    /\
                    <. y , x >. e. R
                  )
                  ->
                  x = y
                )
              /\
              (
                A. x e. I A. y e. I A. z e. I
                  (
                    (
                      <. x , y >. e. R
                      /\
                      <. y , z >. e. R
                    )
                    ->
                    <. x , z >. e. R
                  )
                /\
                A. x e. I A. y e. I
                  (
                    (
                      <. x , ( U ` <. x , y >. ) >. e. R
                      /\
                      <. y , ( U ` <. x , y >. ) >. e. R
                    )
                    /\
                    A. z e. I
                      (
                        (
                          <. x , z >. e. R
                          /\
                          <. y , z >. e. R
                        )
                        ->
                        <. ( U ` <. x , y >. ) , z >. e. R
                      )
                  )
              )
            )
          )
        )
      )
    )
  ) $.
$}

${
  $d B D H M P a k n x y $.

  q1191709-strongly-measurable-definition $a |- (
    ( Q1191709StronglyMeasurable M B D H )
    <->
    (
      H e. ( B ^m U. dom M )
      /\
      E. P e. ( ( B ^m U. dom M ) ^m NN0 )
        (
          A. n e. NN0
            (
              A. y e. B
                ( `' ( P ` n ) " { y } ) e. dom M
              /\
              ran ( P ` n ) e. Fin
            )
          /\
          A. x e. U. dom M A. a e. RR+
            E. n e. NN0 A. k e. NN0
              (
                n <_ k
                ->
                (
                  ( ( P ` k ) ` x )
                  D
                  ( H ` x )
                )
                <
                a
              )
        )
    )
  ) $.
$}

${
  $d B D F G I M N R S a j k x $.

  q1191709-ae-converges-definition $a |- (
    ( Q1191709AEConverges M B D I R F G S )
    <->
    E. N e. dom M
      (
        ( M ` N ) = 0
        /\
        A. x e. ( S \ N ) A. a e. RR+
          E. j e. I A. k e. I
            (
              <. j , k >. e. R
              ->
              (
                ( ( F ` k ) ` x )
                D
                ( G ` x )
              )
              <
              a
            )
      )
  ) $.
$}

${
  $d B D F G I R S a j k x $.

  q1191709-uniformly-on-definition $a |- (
    ( Q1191709UniformlyOn B D I R F G S )
    <->
    A. a e. RR+
      E. j e. I A. k e. I
        (
          <. j , k >. e. R
          ->
          A. x e. S
            (
              ( ( F ` k ) ` x )
              D
              ( G ` x )
            )
            <
            a
        )
  ) $.
$}

${
  $d B D F G H I M N P R S T U a e j k n x y z $.

  thousand-theorems-q1191709-egorov $a |-
    A. M e. U. ran measures
      A. B A. D A. I A. R A. U A. F A. G A. S A. e
        (
          (
            (
              D e. ( PsMet ` B )
              /\
              (
                ( Q1191709SemilatticeSup I R U )
                /\
                I ~<_ NN0
              )
            )
            /\
            (
              F e. ( ( B ^m U. dom M ) ^m I )
              /\
              (
                G e. ( B ^m U. dom M )
                /\
                (
                  S e. ~P ( U. dom M )
                  /\
                  e e. RR+
                )
              )
            )
          )
          ->
          (
            (
              (
                A. n e. I
                  ( Q1191709StronglyMeasurable M B D ( F ` n ) )
                /\
                ( Q1191709StronglyMeasurable M B D G )
              )
              /\
              (
                S e. dom M
                /\
                (
                  ( M ` S ) =/= +oo
                  /\
                  ( Q1191709AEConverges M B D I R F G S )
                )
              )
            )
            ->
            E. T
              (
                T C_ S
                /\
                (
                  T e. dom M
                  /\
                  (
                    ( M ` T ) <_ e
                    /\
                    (
                      Q1191709UniformlyOn
                      B D I R F G ( S \ T )
                    )
                  )
                )
              )
          )
        )
  $.
$}
