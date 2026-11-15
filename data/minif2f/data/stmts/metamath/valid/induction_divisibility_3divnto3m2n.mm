$(
  @{
    @d N x $@
    @d ph x y $@
    induction-divisibility-3divnto3m2n.0 @e |- ( ph -> N e. NN0 ) $@
    @( (Contributed by Stanislas Polu, 9-Oct-2020.) @)
    induction-divisibility-3divnto3m2n @p |- ( ph -> 3 || ( ( N ^ 3 ) + ( 2 x. N 
  ) ) ) @=
      ? @.
  @}
$)
