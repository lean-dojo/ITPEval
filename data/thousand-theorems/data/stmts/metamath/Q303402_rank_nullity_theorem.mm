$(
  Statement-only formalization of Thousand Theorems corpus artifact Q303402
  (thousand-theorems__metamath__Q303402), "Rank-nullity theorem": for a
  linear map between arbitrary modules over a ring satisfying
  HasRankNullity, the cardinal rank of its range plus the cardinal rank of
  its kernel equals the cardinal rank of its domain. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  Q303402Rank M is the supremum of the SetMM card values of all linearly
  independent subsets of the SetMM left module M. This is the universe-free
  set-theoretic rendering of mathlib's cardinal-valued Module.rank. Cardinal
  addition is represented by card applied to the tagged disjoint union |_| .

  Q303402HasRankNullity R retains both fields of mathlib's HasRankNullity:
  every set-sized left R-module has a linearly independent subset attaining
  its rank, and for every submodule N of M the cardinal rank of M / N plus
  the rank of N equals the rank of M. SetMM's restricted structures M |`s N,
  U |`s ran F, and M |`s ( `' F " { ( 0g ` U ) } ) represent respectively
  a submodule, the range of F, and the kernel of F with their inherited
  module structures.

  The two definitions and the final theorem are unproved $a assertions.
  This database contains no $p proof statement.
$)

$c Q303402Rank Q303402HasRankNullity $.

q303402-rank-syntax
  $a class ( Q303402Rank M ) $.

q303402-has-rank-nullity-syntax
  $a wff ( Q303402HasRankNullity R ) $.

q303402-rank-definition $a |- (
  Q303402Rank M
  )
  =
  U. ( card " ( LIndS ` M ) ) $.

${
  $d M N R S v $.

  q303402-has-rank-nullity-definition $a |- (
    ( Q303402HasRankNullity R )
    <->
    (
      R e. Ring
      /\
      (
        A. M e. { v e. LMod | ( Scalar ` v ) = R }
          E. S e. ( LIndS ` M )
            ( card ` S ) = ( Q303402Rank M )
        /\
        A. M e. { v e. LMod | ( Scalar ` v ) = R }
          A. N e. ( LSubSp ` M )
            (
              card
              `
              (
                (
                  Q303402Rank
                  ( M /s ( M ~QG N ) )
                )
                |_|
                (
                  Q303402Rank
                  ( M |`s N )
                )
              )
            )
            =
            ( Q303402Rank M )
      )
    )
  ) $.
$}

${
  $d F M R U $.

  thousand-theorems-q303402-rank-nullity-theorem $a |- (
    A. R A. M A. U A. F
      (
        (
          ( Q303402HasRankNullity R )
          /\
          (
            M e. { v e. LMod | ( Scalar ` v ) = R }
            /\
            (
              U e. { v e. LMod | ( Scalar ` v ) = R }
              /\
              F e. ( M LMHom U )
            )
          )
        )
        ->
        (
          card
          `
          (
            (
              Q303402Rank
              ( U |`s ran F )
            )
            |_|
            (
              Q303402Rank
              (
                M |`s
                ( `' F " { ( 0g ` U ) } )
              )
            )
          )
        )
        =
        ( Q303402Rank M )
      )
  ) $.
$}
