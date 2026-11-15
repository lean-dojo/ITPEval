$(
  Statement-only formalization of Hundred Theorems artifact 059, "The Laws
  of Large Numbers". It states the strong law for identically distributed
  integrable real-valued random variables, both for a mutually independent
  sequence on a probability space and for the pairwise-independent form over
  an arbitrary measure, where the latter starts from arbitrary functions and
  uses measurable versions equal outside measurable null sets. Almost-sure
  convergence is likewise stated outside an internally quantified measurable
  null set. This file contains no proof.
$)

$[ library/set.mm $]

$(
  All probability-theory notions below are the defined set.mm notions.
  A sequence X is represented by an actual function on NN0. Real random
  variables are measurable functions into BrSiga. Integrability means
  membership in the domain of the real Bochner integral RRfld itgm M.

  Mutual independence is expanded as the finite-family product identity for
  arbitrary Borel preimages. In the pairwise form, X ranges over arbitrary
  real-valued functions. An internally quantified sequence Y supplies Borel
  measurable versions. For each index, an internally quantified measurable
  null set contains every sample point where X_i and Y_i differ. Pairwise
  independence is the extended-real product identity for every two distinct
  indices, and identical distribution is equality of the measures of all
  Borel preimages. Membership of Y_0 in the domain of the real Bochner
  integral expresses integrability of X_0 up to equality off a null set.

  For each sample point x, the map

    n |-> ( sum_ i e. ( 0 ..^ n ) ( ( X ` i ) ` x ) ) / n

  is the sequence of sample averages. Each conclusion internally quantifies a
  measurable null set and states convergence at every sample point outside
  that set.
$)

${
  $d N a f i n s x P X $.
  $d N a f i n s x $.
  $d N f i n s x $.
  $d N i n s x $.
  $d N n x $.
  $d a f i n s x $.
  $d f i n s x $.
  $d i n s x $.
  $d n x $.

  ht059-slln-iid $a |- (
    (
      P e. Prob
      /\
      (
        X : NN0 --> ( rRndVar ` P )
        /\
        (
          A. s e. ( Fin i^i ~P NN0 )
            A. f e. ( BrSiga ^m s )
              ( P ` (
                U. dom P i^i
                |^|_ i e. s ( `' ( X ` i ) " ( f ` i ) )
              ) )
              =
              prod_ i e. s ( P ` ( `' ( X ` i ) " ( f ` i ) ) )
          /\
          (
            A. i e. NN0 A. a e. BrSiga
              ( P ` ( `' ( X ` i ) " a ) )
              =
              ( P ` ( `' ( X ` 0 ) " a ) )
            /\
            ( X ` 0 ) e. dom ( RRfld itgm P )
          )
        )
      )
    )
    ->
    E. N e. dom P
      (
        ( P ` N ) = 0
        /\
        A. x e. ( U. dom P \ N )
        (
          (
            n e. NN0 |->
            (
              sum_ i e. ( 0 ..^ n ) ( ( X ` i ) ` x )
            ) / n
          )
          ~~>
          ( ( RRfld itgm P ) ` ( X ` 0 ) )
        )
      )
  ) $.
$}

${
  $d N a b i j n x M X Y $.
  $d N a b i j n x X Y $.
  $d N b i j n x X Y $.
  $d N i j n x X Y $.
  $d N j n x X Y $.
  $d N n x X Y $.
  $d N n x Y $.

  ht059-slln-pairwise $a |- (
    (
      M e. U. ran measures
      /\
      (
        X : NN0 --> ( RR ^m U. dom M )
        /\
        E. Y
          (
            Y : NN0 --> ( dom M MblFnM BrSiga )
            /\
            (
              A. i e. NN0
                E. N e. dom M
                  (
                    ( M ` N ) = 0
                    /\
                    A. x e. ( U. dom M \ N )
                      ( ( X ` i ) ` x ) = ( ( Y ` i ) ` x )
                  )
              /\
              (
                A. i e. NN0 A. j e. NN0
                  (
                    i =/= j
                    ->
                    A. a e. BrSiga A. b e. BrSiga
                      ( M ` (
                        ( `' ( Y ` i ) " a )
                        i^i
                        ( `' ( Y ` j ) " b )
                      ) )
                      =
                      (
                        ( M ` ( `' ( Y ` i ) " a ) )
                        *e
                        ( M ` ( `' ( Y ` j ) " b ) )
                      )
                  )
                /\
                (
                  A. i e. NN0 A. a e. BrSiga
                    ( M ` ( `' ( Y ` i ) " a ) )
                    =
                    ( M ` ( `' ( Y ` 0 ) " a ) )
                  /\
                  ( Y ` 0 ) e. dom ( RRfld itgm M )
                )
              )
            )
          )
      )
    )
    ->
    E. Y
      (
        Y : NN0 --> ( dom M MblFnM BrSiga )
        /\
        (
          A. i e. NN0
            E. N e. dom M
              (
                ( M ` N ) = 0
                /\
                A. x e. ( U. dom M \ N )
                  ( ( X ` i ) ` x ) = ( ( Y ` i ) ` x )
              )
          /\
          (
            A. i e. NN0 A. j e. NN0
              (
                i =/= j
                ->
                A. a e. BrSiga A. b e. BrSiga
                  ( M ` (
                    ( `' ( Y ` i ) " a )
                    i^i
                    ( `' ( Y ` j ) " b )
                  ) )
                  =
                  (
                    ( M ` ( `' ( Y ` i ) " a ) )
                    *e
                    ( M ` ( `' ( Y ` j ) " b ) )
                  )
              )
            /\
            (
              A. i e. NN0 A. a e. BrSiga
                ( M ` ( `' ( Y ` i ) " a ) )
                =
                ( M ` ( `' ( Y ` 0 ) " a ) )
              /\
              (
                ( Y ` 0 ) e. dom ( RRfld itgm M )
                /\
                E. N e. dom M
                  (
                    ( M ` N ) = 0
                    /\
                    A. x e. ( U. dom M \ N )
                    (
                      (
                        n e. NN0 |->
                        (
                          sum_ i e. ( 0 ..^ n ) ( ( X ` i ) ` x )
                        ) / n
                      )
                      ~~>
                      ( ( RRfld itgm M ) ` ( Y ` 0 ) )
                    )
                  )
              )
            )
          )
        )
      )
  ) $.
$}
