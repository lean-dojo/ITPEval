$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2012_b1: closure under pointwise multiplication for a class of
  nonnegative real-valued functions on the nonnegative reals containing the
  specified exponential and logarithmic functions and closed under addition,
  composition, and ordered subtraction. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P12B1D is the full nonnegative real ray. Thus P12B1D ^m P12B1D is
  exactly the set of functions from [0,+infinity) to itself. Requiring S to
  be a subclass of this function space preserves both the source domain and
  its nonnegative codomain condition.

  The two explicit maps are x |-> exp(x) - 1 and x |-> log(x + 1).
  The three following conjuncts state closure under pointwise addition,
  composition, and pointwise subtraction when the first function dominates
  the second everywhere. The conclusion states closure under pointwise
  multiplication. Inlining the source variables f1 and f2 is definitionally
  equivalent to retaining their equality hypotheses.

  The domain declaration below is a definitional abbreviation. The final
  declaration is the unproved $a corpus statement; there are no $p proof
  statements in this database.
$)

$c P12B1D $.

p12b1-domain-syntax $a class P12B1D $.

${
  p12b1-domain-definition $a |- P12B1D =
    { t e. RR | 0 <_ t }
  $.
$}

${
  $d S f g x $.

  putnambench-putnam-2012-b1 $a |- A. S
    (
      (
        S C_ ( P12B1D ^m P12B1D )
        /\
        (
          (
            x e. P12B1D |->
              ( ( exp ` x ) - 1 )
          )
          e. S
          /\
          (
            (
              x e. P12B1D |->
                ( log ` ( x + 1 ) )
            )
            e. S
            /\
            (
              A. f e. S A. g e. S
                (
                  x e. P12B1D |->
                    ( ( f ` x ) + ( g ` x ) )
                )
                e. S
              /\
              (
                A. f e. S A. g e. S
                  (
                    x e. P12B1D |->
                      ( f ` ( g ` x ) )
                  )
                  e. S
                /\
                A. f e. S A. g e. S
                  (
                    A. x e. P12B1D
                      ( g ` x ) <_ ( f ` x )
                    ->
                    (
                      x e. P12B1D |->
                        ( ( f ` x ) - ( g ` x ) )
                    )
                    e. S
                  )
              )
            )
          )
        )
      )
      ->
      A. f e. S A. g e. S
        (
          x e. P12B1D |->
            ( ( f ` x ) x. ( g ` x ) )
        )
        e. S
    )
  $.
$}
