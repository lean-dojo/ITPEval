$(
  @{
    aime-1996-p5.0 @e |- ( ph -> A e. CC ) $@
    aime-1996-p5.1 @e |- ( ph -> B e. CC ) $@
    aime-1996-p5.2 @e |- ( ph -> C e. CC ) $@
    aime-1996-p5.3 @e |- ( ph -> R e. CC ) $@
    aime-1996-p5.4 @e |- ( ph -> S e. CC ) $@
    aime-1996-p5.5 @e |- ( ph -> T e. CC ) $@
    aime-1996-p5.6 @e |- F = ( x e. CC |-> ( ( ( ( x ^ 3 ) + ( 3 x. ( x ^ 2 ) ) ) + ( 4 x. x ) ) - ; 1 1 ) ) $@
    aime-1996-p5.7 @e |- G = ( x e. CC |-> ( ( ( ( x ^ 3 ) + ( R x. ( x ^ 2 ) ) ) + ( S x. x ) ) + T ) ) $@
    aime-1996-p5.8 @e |- ( ph -> ( F ` A ) = 0 ) $@
    aime-1996-p5.9 @e |- ( ph -> ( F ` B ) = 0 ) $@
    aime-1996-p5.10 @e |- ( ph -> ( F ` C ) = 0 ) $@
    aime-1996-p5.11 @e |- ( ph -> ( G ` ( A + B ) ) = 0 ) $@
    aime-1996-p5.12 @e |- ( ph -> ( G ` ( B + C ) ) = 0 ) $@
    aime-1996-p5.13 @e |- ( ph -> ( G ` ( C + A ) ) = 0 ) $@
    aime-1996-p5.14 @e |- ( ph -> A =/= B ) $@
    aime-1996-p5.15 @e |- ( ph -> B =/= C ) $@
    aime-1996-p5.16 @e |- ( ph -> C =/= A ) $@
    @( (Contributed by Kunhao Zheng, 9-Aug-2021.) @)
    aime-1996-p5 @p |- ( ph -> T = ; 2 3 ) @=
      ? @.
  @}
$)
