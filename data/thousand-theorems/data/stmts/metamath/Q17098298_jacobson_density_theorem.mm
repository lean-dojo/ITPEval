$(
  Statement-only formalization of Thousand Theorems corpus artifact Q17098298
  (thousand-theorems__metamath__Q17098298), "Jacobson density theorem": on
  every finite subset of a semisimple module, an endomorphism commuting with
  all module endomorphisms agrees with scalar multiplication by one ring
  element. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  R is an arbitrary ring and M is an arbitrary SetMM left R-module.
  Q17098298Semisimple M says that every submodule N has a complementary
  submodule P: their intersection is zero and every element of M is a sum of
  an element of N and an element of P. This is exactly the complemented
  submodule-lattice definition of Mathlib's IsSemisimpleModule R M.

  Q17098298EndLinear M f says that f is an additive endomorphism of M and
  commutes with every R-linear endomorphism g of M. The endomorphism ring
  Module.End R M acts on M by evaluation, so this condition is
  bidirectionally equivalent to f belonging to
  Module.End (Module.End R M) M.

  A SetMM member of Fin i^i ~P ( Base ` M ) is precisely a finite subset of
  M, matching Lean's Finset M. The witness r remains existentially quantified
  after that finite subset is chosen.

  All declarations preceding the final one are syntax or faithful
  bidirectional definitions. The final $a declaration is the single unproved
  corpus statement, and this database contains no $p proof statement.
$)

$c Q17098298Semisimple Q17098298EndLinear $.

q17098298-semisimple-syntax $a
  wff ( Q17098298Semisimple M ) $.

q17098298-end-linear-syntax $a
  wff ( Q17098298EndLinear M f ) $.

${
  $d M N P m n p $.

  q17098298-semisimple-definition $a |- (
    ( Q17098298Semisimple M )
    <->
    (
      M e. LMod
      /\
      A. N e. ( LSubSp ` M )
        E. P e. ( LSubSp ` M )
          (
            ( N i^i P ) = { ( 0g ` M ) }
            /\
            A. m e. ( Base ` M )
              E. n e. N
                E. p e. P
                  m = ( n ( +g ` M ) p )
          )
    )
  ) $.
$}

${
  $d M f g m $.

  q17098298-end-linear-definition $a |- (
    ( Q17098298EndLinear M f )
    <->
    (
      f e. ( M GrpHom M )
      /\
      A. g e. ( M LMHom M )
        A. m e. ( Base ` M )
          ( f ` ( g ` m ) ) = ( g ` ( f ` m ) )
    )
  ) $.
$}

${
  $d M R S f m r $.

  thousand-theorems-q17098298-jacobson-density-theorem $a |- (
    A. R e. Ring
      A. M
        (
          (
            ( Scalar ` M ) = R
            /\
            ( Q17098298Semisimple M )
          )
          ->
          A. f
            (
              ( Q17098298EndLinear M f )
              ->
              A. S e. ( Fin i^i ~P ( Base ` M ) )
                E. r e. ( Base ` R )
                  A. m e. S
                    ( f ` m ) = ( r ( .s ` M ) m )
            )
        )
  ) $.
$}
