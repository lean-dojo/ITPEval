$(
  @{
    @d N x $@
    @d ph x y $@
    induction-ineq-nsqlefactn.0 @e |- ( ph -> N e. ( ZZ>= ` 4 ) ) $@
    @( (Contributed by Stanislas Polu, 12-Oct-2020.) @)
    induction-ineq-nsqlefactn @p |- ( ph -> ( N ^ 2 ) <_ ( ! ` N ) ) @=
      ? @.
  @}
$)
