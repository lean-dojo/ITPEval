(*
  Statement-only formalization of thousand-theorems corpus artifact Q1687147,
  "Sprague–Grundy theorem": every set-sized well-founded game that is
  recursively impartial with separate Left and Right options is
  Conway-equivalent to the Nim game indexed by its ordinal Grundy value. This
  file contains no proof.
*)

theory Q1687147_sprague_grundy_theorem
  imports "ZF.WF" "ZF.Sum" "ZF.Ordinal"
begin

definition q1687147_grundy_assignment :: "[i, i, i] \<Rightarrow> o" where
  "q1687147_grundy_assignment(V, right_moves, grundy) \<equiv>
    function(grundy) \<and>
    domain(grundy) = V \<and>
    (\<forall>v\<in>V.
      Ord(grundy`v) \<and>
      (\<forall>y\<in>V.
        \<langle>y,v\<rangle> \<in> right_moves \<longrightarrow> grundy`y \<noteq> grundy`v) \<and>
      (\<forall>\<beta>\<in>grundy`v.
        \<exists>y\<in>V. \<langle>y,v\<rangle> \<in> right_moves \<and> grundy`y = \<beta>))"

definition q1687147_game_left_move :: "[i, i, i, i] \<Rightarrow> o" where
  "q1687147_game_left_move(left_moves, right_moves, p, q) \<equiv>
    (\<exists>y v.
      p = Inl(y) \<and> q = Inl(v) \<and> \<langle>y,v\<rangle> \<in> left_moves) \<or>
    (\<exists>y v.
      p = Inr(y) \<and> q = Inr(v) \<and> \<langle>y,v\<rangle> \<in> right_moves)"

definition q1687147_game_right_move :: "[i, i, i, i] \<Rightarrow> o" where
  "q1687147_game_right_move(left_moves, right_moves, p, q) \<equiv>
    (\<exists>y v.
      p = Inl(y) \<and> q = Inl(v) \<and> \<langle>y,v\<rangle> \<in> right_moves) \<or>
    (\<exists>y v.
      p = Inr(y) \<and> q = Inr(v) \<and> \<langle>y,v\<rangle> \<in> left_moves)"

definition q1687147_game_conway_order :: "[i, i, i, i] \<Rightarrow> o" where
  "q1687147_game_conway_order(V, left_moves, right_moves, leq) \<equiv>
    leq \<subseteq> (V + V) * (V + V) \<and>
    (\<forall>p\<in>V + V. \<forall>q\<in>V + V.
      (\<langle>p,q\<rangle> \<in> leq) \<longleftrightarrow>
        ((\<forall>p'\<in>V + V.
            q1687147_game_left_move(left_moves, right_moves, p', p)
            \<longrightarrow> \<langle>q,p'\<rangle> \<notin> leq) \<and>
         (\<forall>q'\<in>V + V.
            q1687147_game_right_move(left_moves, right_moves, q', q)
            \<longrightarrow> \<langle>q',p\<rangle> \<notin> leq)))"

definition q1687147_impartial_assignment :: "[i, i, i, i, i] \<Rightarrow> o" where
  "q1687147_impartial_assignment(V, left_moves, right_moves, leq, impartial) \<equiv>
    impartial \<subseteq> V \<and>
    (\<forall>v\<in>V.
      (v \<in> impartial) \<longleftrightarrow>
        (\<langle>Inr(v),Inl(v)\<rangle> \<in> leq \<and>
         \<langle>Inl(v),Inr(v)\<rangle> \<in> leq \<and>
         (\<forall>y\<in>V.
           (\<langle>y,v\<rangle> \<in> left_moves \<or>
            \<langle>y,v\<rangle> \<in> right_moves)
           \<longrightarrow> y \<in> impartial)))"

definition q1687147_impartial :: "[i, i, i, i] \<Rightarrow> o" where
  "q1687147_impartial(V, left_moves, right_moves, x) \<equiv>
    (\<exists>leq impartial.
      q1687147_game_conway_order(V, left_moves, right_moves, leq) \<and>
      q1687147_impartial_assignment(
        V, left_moves, right_moves, leq, impartial) \<and>
      x \<in> impartial)"

definition q1687147_tagged_left_move :: "[i, i, i, i] \<Rightarrow> o" where
  "q1687147_tagged_left_move(left_moves, right_moves, p, q) \<equiv>
    (\<exists>y v.
      p = Inl(Inl(y)) \<and> q = Inl(Inl(v)) \<and>
      \<langle>y,v\<rangle> \<in> left_moves) \<or>
    (\<exists>y v.
      p = Inl(Inr(y)) \<and> q = Inl(Inr(v)) \<and>
      \<langle>y,v\<rangle> \<in> right_moves) \<or>
    (\<exists>\<beta> \<alpha>. p = Inr(\<beta>) \<and> q = Inr(\<alpha>) \<and> \<beta> \<in> \<alpha>)"

definition q1687147_tagged_right_move :: "[i, i, i, i] \<Rightarrow> o" where
  "q1687147_tagged_right_move(left_moves, right_moves, p, q) \<equiv>
    (\<exists>y v.
      p = Inl(Inl(y)) \<and> q = Inl(Inl(v)) \<and>
      \<langle>y,v\<rangle> \<in> right_moves) \<or>
    (\<exists>y v.
      p = Inl(Inr(y)) \<and> q = Inl(Inr(v)) \<and>
      \<langle>y,v\<rangle> \<in> left_moves) \<or>
    (\<exists>\<beta> \<alpha>. p = Inr(\<beta>) \<and> q = Inr(\<alpha>) \<and> \<beta> \<in> \<alpha>)"

definition q1687147_conway_order :: "[i, i, i, i, i] \<Rightarrow> o" where
  "q1687147_conway_order(V, left_moves, right_moves, \<alpha>, leq) \<equiv>
    leq \<subseteq> ((V + V) + succ(\<alpha>)) * ((V + V) + succ(\<alpha>)) \<and>
    (\<forall>p\<in>(V + V) + succ(\<alpha>). \<forall>q\<in>(V + V) + succ(\<alpha>).
      (\<langle>p,q\<rangle> \<in> leq) \<longleftrightarrow>
        ((\<forall>p'\<in>(V + V) + succ(\<alpha>).
            q1687147_tagged_left_move(left_moves, right_moves, p', p)
            \<longrightarrow>
            \<langle>q,p'\<rangle> \<notin> leq) \<and>
         (\<forall>q'\<in>(V + V) + succ(\<alpha>).
            q1687147_tagged_right_move(left_moves, right_moves, q', q)
            \<longrightarrow>
            \<langle>q',p\<rangle> \<notin> leq)))"

theorem q1687147_sprague_grundy:
  assumes "x \<in> V"
    and "left_moves \<subseteq> V * V"
    and "right_moves \<subseteq> V * V"
    and "wf(left_moves \<union> right_moves)"
    and "q1687147_impartial(V, left_moves, right_moves, x)"
  shows
    "\<exists>grundy leq.
      q1687147_grundy_assignment(V, right_moves, grundy) \<and>
      q1687147_conway_order(
        V, left_moves, right_moves, grundy`x, leq) \<and>
      \<langle>Inr(grundy`x), Inl(Inl(x))\<rangle> \<in> leq \<and>
      \<langle>Inl(Inl(x)), Inr(grundy`x)\<rangle> \<in> leq"
  sorry

end
