(*
  L'Hopital's rule for finite endpoints.

  The source development exposes 18 variants: approach from the right or
  left; denominator limit 0, +infinity, or -infinity; and derivative-ratio
  limit finite, +infinity, or -infinity.  This file states all 18 variants
  with their differentiability, continuity, and nonvanishing hypotheses.
*)

From Stdlib Require Import Reals.

Local Open Scope R_scope.

Definition limit_div_pos
    (f : R -> R) (domain : R -> Prop) (point : R) : Prop :=
  forall bound,
    bound > 0 ->
    exists delta,
      delta > 0 /\
      forall x,
        domain x ->
        R_dist x point < delta ->
        bound < f x.

Definition limit_div_neg
    (f : R -> R) (domain : R -> Prop) (point : R) : Prop :=
  forall bound,
    bound > 0 ->
    exists delta,
      delta > 0 /\
      forall x,
        domain x ->
        R_dist x point < delta ->
        - bound > f x.

Record hopital_context
    (f g : R -> R) (a b : R) : Type := {
  hopital_interval_nonempty : a < b;
  hopital_num_derivable :
    forall x, open_interval a b x -> derivable_pt f x;
  hopital_den_derivable :
    forall x, open_interval a b x -> derivable_pt g x;
  hopital_num_continuous :
    forall x, a <= x <= b -> continuity_pt f x;
  hopital_den_continuous :
    forall x, a <= x <= b -> continuity_pt g x
}.

Arguments hopital_num_derivable {f g a b} _ _ _.
Arguments hopital_den_derivable {f g a b} _ _ _.

Definition derivative_ratio
    {f g a b} (context : hopital_context f g a b)
    (x : R) (inside : open_interval a b x) : R :=
  derive_pt f x (hopital_num_derivable context x inside) /
  derive_pt g x (hopital_den_derivable context x inside).

Definition denominator_and_derivative_nonzero
    {f g a b} (context : hopital_context f g a b) : Prop :=
  forall x (inside : open_interval a b x),
    derive_pt g x (hopital_den_derivable context x inside) <> 0 /\
    g x <> 0.

Definition denominator_derivative_nonzero
    {f g a b} (context : hopital_context f g a b) : Prop :=
  forall x (inside : open_interval a b x),
    derive_pt g x (hopital_den_derivable context x inside) <> 0.

Definition derivative_ratio_finite_limit
    {f g a b} (context : hopital_context f g a b)
    (point limit : R) : Prop :=
  forall eps,
    eps > 0 ->
    exists delta,
      delta > 0 /\
      forall x (inside : open_interval a b x),
        R_dist x point < delta ->
        R_dist (derivative_ratio context x inside) limit < eps.

Definition derivative_ratio_pos_infinite
    {f g a b} (context : hopital_context f g a b)
    (point : R) : Prop :=
  forall bound,
    bound > 0 ->
    exists delta,
      delta > 0 /\
      forall x (inside : open_interval a b x),
        R_dist x point < delta ->
        bound < derivative_ratio context x inside.

Definition derivative_ratio_neg_infinite
    {f g a b} (context : hopital_context f g a b)
    (point : R) : Prop :=
  forall bound,
    bound > 0 ->
    exists delta,
      delta > 0 /\
      forall x (inside : open_interval a b x),
        R_dist x point < delta ->
        - bound > derivative_ratio context x inside.

Section HopitalStatements.

Variables (f g : R -> R) (a b : R).

Theorem Hopital_g0_Lfin_right
    (context : hopital_context f g a b)
    (Zf : limit1_in f (open_interval a b) 0 a)
    (Zg : limit1_in g (open_interval a b) 0 a)
    (g_nonzero : denominator_and_derivative_nonzero context)
    (L : R)
    (Hratio_L : derivative_ratio_finite_limit context a L) :
  limit1_in (fun x => f x / g x) (open_interval a b) L a.
Proof.
Admitted.

Theorem Hopital_g0_Lfin_left
    (context : hopital_context f g a b)
    (Zf : limit1_in f (open_interval a b) 0 b)
    (Zg : limit1_in g (open_interval a b) 0 b)
    (g_nonzero : denominator_and_derivative_nonzero context)
    (L : R)
    (Hratio : derivative_ratio_finite_limit context b L) :
  limit1_in (fun x => f x / g x) (open_interval a b) L b.
Proof.
Admitted.

Theorem Hopital_gpinf_Lfin_right
    (context : hopital_context f g a b)
    (Zg : limit_div_pos g (open_interval a b) a)
    (g_nonzero : denominator_derivative_nonzero context)
    (L : R)
    (Hratio : derivative_ratio_finite_limit context a L) :
  limit1_in (fun x => f x / g x) (open_interval a b) L a.
Proof.
Admitted.

Theorem Hopital_gpinf_Lfin_left
    (context : hopital_context f g a b)
    (Zg : limit_div_pos g (open_interval a b) b)
    (g_nonzero : denominator_derivative_nonzero context)
    (L : R)
    (Hratio : derivative_ratio_finite_limit context b L) :
  limit1_in (fun x => f x / g x) (open_interval a b) L b.
Proof.
Admitted.

Theorem Hopital_gninf_Lfin_right
    (context : hopital_context f g a b)
    (Zg : limit_div_neg g (open_interval a b) a)
    (g_nonzero : denominator_derivative_nonzero context)
    (L : R)
    (Hratio : derivative_ratio_finite_limit context a L) :
  limit1_in (fun x => f x / g x) (open_interval a b) L a.
Proof.
Admitted.

Theorem Hopital_gninf_Lfin_left
    (context : hopital_context f g a b)
    (Zg : limit_div_neg g (open_interval a b) b)
    (g_nonzero : denominator_derivative_nonzero context)
    (L : R)
    (Hratio : derivative_ratio_finite_limit context b L) :
  limit1_in (fun x => f x / g x) (open_interval a b) L b.
Proof.
Admitted.

Theorem Hopital_g0_Lpinf_right
    (context : hopital_context f g a b)
    (Zf : limit1_in f (open_interval a b) 0 a)
    (Zg : limit1_in g (open_interval a b) 0 a)
    (g_nonzero : denominator_and_derivative_nonzero context)
    (Hratio : derivative_ratio_pos_infinite context a) :
  limit_div_pos (fun x => f x / g x) (open_interval a b) a.
Proof.
Admitted.

Theorem Hopital_g0_Lpinf_left
    (context : hopital_context f g a b)
    (Zf : limit1_in f (open_interval a b) 0 b)
    (Zg : limit1_in g (open_interval a b) 0 b)
    (g_nonzero : denominator_and_derivative_nonzero context)
    (Hratio : derivative_ratio_pos_infinite context b) :
  limit_div_pos (fun x => f x / g x) (open_interval a b) b.
Proof.
Admitted.

Theorem Hopital_g0_Lninf_right
    (context : hopital_context f g a b)
    (Zf : limit1_in f (open_interval a b) 0 a)
    (Zg : limit1_in g (open_interval a b) 0 a)
    (g_nonzero : denominator_and_derivative_nonzero context)
    (Hratio : derivative_ratio_neg_infinite context a) :
  limit_div_neg (fun x => f x / g x) (open_interval a b) a.
Proof.
Admitted.

Theorem Hopital_g0_Lninf_left
    (context : hopital_context f g a b)
    (Zf : limit1_in f (open_interval a b) 0 b)
    (Zg : limit1_in g (open_interval a b) 0 b)
    (g_nonzero : denominator_and_derivative_nonzero context)
    (Hratio : derivative_ratio_neg_infinite context b) :
  limit_div_neg (fun x => f x / g x) (open_interval a b) b.
Proof.
Admitted.

Theorem Hopital_gpinf_Lpinf_right
    (context : hopital_context f g a b)
    (Zg : limit_div_pos g (open_interval a b) a)
    (g_nonzero : denominator_derivative_nonzero context)
    (Hratio : derivative_ratio_pos_infinite context a) :
  limit_div_pos (fun x => f x / g x) (open_interval a b) a.
Proof.
Admitted.

Theorem Hopital_gpinf_Lpinf_left
    (context : hopital_context f g a b)
    (Zg : limit_div_pos g (open_interval a b) b)
    (g_nonzero : denominator_derivative_nonzero context)
    (Hratio : derivative_ratio_pos_infinite context b) :
  limit_div_pos (fun x => f x / g x) (open_interval a b) b.
Proof.
Admitted.

Theorem Hopital_gpinf_Lninf_right
    (context : hopital_context f g a b)
    (Zg : limit_div_pos g (open_interval a b) a)
    (g_nonzero : denominator_derivative_nonzero context)
    (Hratio : derivative_ratio_neg_infinite context a) :
  limit_div_neg (fun x => f x / g x) (open_interval a b) a.
Proof.
Admitted.

Theorem Hopital_gpinf_Lninf_left
    (context : hopital_context f g a b)
    (Zg : limit_div_pos g (open_interval a b) b)
    (g_nonzero : denominator_derivative_nonzero context)
    (Hratio : derivative_ratio_neg_infinite context b) :
  limit_div_neg (fun x => f x / g x) (open_interval a b) b.
Proof.
Admitted.

Theorem Hopital_gninf_Lpinf_right
    (context : hopital_context f g a b)
    (Zg : limit_div_neg g (open_interval a b) a)
    (g_nonzero : denominator_derivative_nonzero context)
    (Hratio : derivative_ratio_pos_infinite context a) :
  limit_div_pos (fun x => f x / g x) (open_interval a b) a.
Proof.
Admitted.

Theorem Hopital_gninf_Lpinf_left
    (context : hopital_context f g a b)
    (Zg : limit_div_neg g (open_interval a b) b)
    (g_nonzero : denominator_derivative_nonzero context)
    (Hratio : derivative_ratio_pos_infinite context b) :
  limit_div_pos (fun x => f x / g x) (open_interval a b) b.
Proof.
Admitted.

Theorem Hopital_gninf_Lninf_right
    (context : hopital_context f g a b)
    (Zg : limit_div_neg g (open_interval a b) a)
    (g_nonzero : denominator_derivative_nonzero context)
    (Hratio : derivative_ratio_neg_infinite context a) :
  limit_div_neg (fun x => f x / g x) (open_interval a b) a.
Proof.
Admitted.

Theorem Hopital_gninf_Lninf_left
    (context : hopital_context f g a b)
    (Zg : limit_div_neg g (open_interval a b) b)
    (g_nonzero : denominator_derivative_nonzero context)
    (Hratio : derivative_ratio_neg_infinite context b) :
  limit_div_neg (fun x => f x / g x) (open_interval a b) b.
Proof.
Admitted.

End HopitalStatements.
