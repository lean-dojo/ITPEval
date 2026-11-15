$(
  @{
    @d B x $@
    @d F x $@
    @d ph x $@
    mathd-algebra-159.0 @e |- ( ph -> F : RR --> RR ) $@
    mathd-algebra-159.1 @e |- ( ( ph /\ x e. RR ) -> ( F ` x ) = ( ( ( ( ( 3 x. ( 
  x ^ 4 ) ) - ( 7 x. ( x ^ 3 ) ) ) + ( 2 x. ( x ^ 2 ) ) ) - ( B x. x ) ) + 1 ) ) 
  $@
    mathd-algebra-159.2 @e |- ( ph -> B e. RR ) $@
    mathd-algebra-159.3 @e |- ( ph -> ( F ` 1 ) = 1 ) $@
    @( (Contributed by Kunhao Zheng, 31-May-2021.) @)
    mathd-algebra-159 @p |- ( ph -> B = -u 2 ) @=
      ? @.
  @}
$)
