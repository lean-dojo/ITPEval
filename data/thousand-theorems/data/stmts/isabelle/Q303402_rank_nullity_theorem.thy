(* Statement-only formalization of thousand-theorems artifact Q303402,
   "Rank–nullity theorem": cardinal-valued rank additivity for the range and
   kernel of a linear map of modules over an arbitrary unital ring, within one
   fixed cumulative type universe. This file contains no proof. *)

theory Q303402_rank_nullity_theorem
  imports ZF.Cardinal_AC ZF.List ZF.Univ
begin

definition q303402_type_universe :: "i => o" where
  "q303402_type_universe(kappa) \<equiv>
     InfCard(kappa) \<and>
     nat < kappa \<and>
     (\<forall>I\<in>Vset(kappa). \<forall>F\<in>I -> Vset(kappa).
        \<Union>(F``I) \<in> Vset(kappa))"

definition q303402_add_comm_group ::
  "[i, i, i, i] => o" where
  "q303402_add_comm_group(A, z, gplus, gneg) \<equiv>
     z \<in> A \<and>
     gplus \<in> A*A -> A \<and>
     gneg \<in> A -> A \<and>
     (\<forall>x\<in>A. gplus`\<langle>z,x\<rangle> = x \<and> gplus`\<langle>x,z\<rangle> = x) \<and>
     (\<forall>x\<in>A. gplus`\<langle>gneg`x,x\<rangle> = z \<and>
                gplus`\<langle>x,gneg`x\<rangle> = z) \<and>
     (\<forall>x\<in>A. \<forall>y\<in>A. gplus`\<langle>x,y\<rangle> = gplus`\<langle>y,x\<rangle>) \<and>
     (\<forall>x\<in>A. \<forall>y\<in>A. \<forall>z\<in>A.
        gplus`\<langle>gplus`\<langle>x,y\<rangle>,z\<rangle> =
        gplus`\<langle>x,gplus`\<langle>y,z\<rangle>\<rangle>)"

definition q303402_ring ::
  "[i, i, i, i, i, i] => o" where
  "q303402_ring(A, zr, unitR, rplus, rneg, rtimes) \<equiv>
     q303402_add_comm_group(A, zr, rplus, rneg) \<and>
     unitR \<in> A \<and>
     rtimes \<in> A*A -> A \<and>
     (\<forall>x\<in>A. rtimes`\<langle>unitR,x\<rangle> = x \<and> rtimes`\<langle>x,unitR\<rangle> = x) \<and>
     (\<forall>x\<in>A. \<forall>y\<in>A. \<forall>z\<in>A.
        rtimes`\<langle>rtimes`\<langle>x,y\<rangle>,z\<rangle> =
        rtimes`\<langle>x,rtimes`\<langle>y,z\<rangle>\<rangle>) \<and>
     (\<forall>x\<in>A. \<forall>y\<in>A. \<forall>z\<in>A.
        rtimes`\<langle>x,rplus`\<langle>y,z\<rangle>\<rangle> =
        rplus`\<langle>rtimes`\<langle>x,y\<rangle>,rtimes`\<langle>x,z\<rangle>\<rangle>) \<and>
     (\<forall>x\<in>A. \<forall>y\<in>A. \<forall>z\<in>A.
        rtimes`\<langle>rplus`\<langle>x,y\<rangle>,z\<rangle> =
        rplus`\<langle>rtimes`\<langle>x,z\<rangle>,rtimes`\<langle>y,z\<rangle>\<rangle>)"

definition q303402_module ::
  "[i, i, i, i, i, i, i, i, i, i, i] => o" where
  "q303402_module(A, zeroR, unitR, addR, negR, mulR, M, zeroM, addM, negM, smul) \<equiv>
     q303402_ring(A, zeroR, unitR, addR, negR, mulR) \<and>
     q303402_add_comm_group(M, zeroM, addM, negM) \<and>
     smul \<in> A*M -> M \<and>
     (\<forall>x\<in>M. smul`\<langle>unitR,x\<rangle> = x) \<and>
     (\<forall>a\<in>A. \<forall>b\<in>A. \<forall>x\<in>M.
        smul`\<langle>mulR`\<langle>a,b\<rangle>,x\<rangle> =
        smul`\<langle>a,smul`\<langle>b,x\<rangle>\<rangle>) \<and>
     (\<forall>a\<in>A. \<forall>b\<in>A. \<forall>x\<in>M.
        smul`\<langle>addR`\<langle>a,b\<rangle>,x\<rangle> =
        addM`\<langle>smul`\<langle>a,x\<rangle>,smul`\<langle>b,x\<rangle>\<rangle>) \<and>
     (\<forall>a\<in>A. \<forall>x\<in>M. \<forall>y\<in>M.
        smul`\<langle>a,addM`\<langle>x,y\<rangle>\<rangle> =
        addM`\<langle>smul`\<langle>a,x\<rangle>,smul`\<langle>a,y\<rangle>\<rangle>)"

definition q303402_lincomb ::
  "[i, i, i, i] => i" where
  "q303402_lincomb(zeroM, addM, smul, ps) \<equiv>
     list_rec(zeroM,
       \<lambda>p ps r. addM`\<langle>smul`p,r\<rangle>,
       ps)"

definition q303402_nodup :: "i => o" where
  "q303402_nodup(xs) \<equiv>
     \<forall>i\<in>length(xs). \<forall>j\<in>length(xs).
       nth(i,xs) = nth(j,xs) \<longrightarrow> i = j"

definition q303402_independent ::
  "[i, i, i, i, i, i, i] => o" where
  "q303402_independent(A, zeroR, M, zeroM, addM, smul, S) \<equiv>
     S \<subseteq> M \<and>
     (\<forall>xs\<in>list(S).
        q303402_nodup(xs) \<longrightarrow>
        (\<forall>cs\<in>list(A).
          length(cs) = length(xs) \<longrightarrow>
          q303402_lincomb(zeroM, addM, smul, zip(cs,xs)) = zeroM \<longrightarrow>
          (\<forall>i\<in>length(cs). nth(i,cs) = zeroR)))"

definition q303402_rank ::
  "[i, i, i, i, i, i] => i" where
  "q303402_rank(A, zeroR, M, zeroM, addM, smul) \<equiv>
     \<Union>{|S|. S \<in> {T \<in> Pow(M).
       q303402_independent(A, zeroR, M, zeroM, addM, smul, T)}}"

definition q303402_submodule ::
  "[i, i, i, i, i, i, i] => o" where
  "q303402_submodule(A, M, zeroM, addM, negM, smul, N) \<equiv>
     N \<subseteq> M \<and>
     zeroM \<in> N \<and>
     (\<forall>x\<in>N. negM`x \<in> N) \<and>
     (\<forall>x\<in>N. \<forall>y\<in>N. addM`\<langle>x,y\<rangle> \<in> N) \<and>
     (\<forall>a\<in>A. \<forall>x\<in>N. smul`\<langle>a,x\<rangle> \<in> N)"

definition q303402_coset ::
  "[i, i, i] => i" where
  "q303402_coset(N, addM, x) \<equiv>
     {addM`\<langle>x,n\<rangle>. n\<in>N}"

definition q303402_quotient ::
  "[i, i, i] => i" where
  "q303402_quotient(M, N, addM) \<equiv>
     {q303402_coset(N, addM, x). x\<in>M}"

definition q303402_quotient_zero ::
  "[i, i, i] => i" where
  "q303402_quotient_zero(N, addM, zeroM) \<equiv>
     q303402_coset(N, addM, zeroM)"

definition q303402_quotient_add ::
  "[i, i, i] => i" where
  "q303402_quotient_add(M, N, addM) \<equiv>
     let Q = q303402_quotient(M, N, addM) in
     {p \<in> (Q*Q)*Q.
       \<exists>X\<in>Q. \<exists>Y\<in>Q. \<exists>Z\<in>Q.
       p = \<langle>\<langle>X,Y\<rangle>,Z\<rangle> \<and>
       (\<exists>x\<in>M. \<exists>y\<in>M.
          X = q303402_coset(N, addM, x) \<and>
          Y = q303402_coset(N, addM, y) \<and>
          Z = q303402_coset(N, addM, addM`\<langle>x,y\<rangle>))}"

definition q303402_quotient_neg ::
  "[i, i, i, i] => i" where
  "q303402_quotient_neg(M, N, addM, negM) \<equiv>
     let Q = q303402_quotient(M, N, addM) in
     {p \<in> Q*Q.
       \<exists>X\<in>Q. \<exists>Z\<in>Q.
       p = \<langle>X,Z\<rangle> \<and>
       (\<exists>x\<in>M.
          X = q303402_coset(N, addM, x) \<and>
          Z = q303402_coset(N, addM, negM`x))}"

definition q303402_quotient_smul ::
  "[i, i, i, i, i] => i" where
  "q303402_quotient_smul(A, M, N, addM, smul) \<equiv>
     let Q = q303402_quotient(M, N, addM) in
     {p \<in> (A*Q)*Q.
       \<exists>a\<in>A. \<exists>X\<in>Q. \<exists>Z\<in>Q.
       p = \<langle>\<langle>a,X\<rangle>,Z\<rangle> \<and>
       (\<exists>x\<in>M.
          X = q303402_coset(N, addM, x) \<and>
          Z = q303402_coset(N, addM, smul`\<langle>a,x\<rangle>))}"

definition q303402_quotient_rank ::
  "[i, i, i, i, i, i, i] => i" where
  "q303402_quotient_rank(A, zeroR, M, zeroM, addM, smul, N) \<equiv>
     q303402_rank(
       A, zeroR,
       q303402_quotient(M, N, addM),
       q303402_quotient_zero(N, addM, zeroM),
       q303402_quotient_add(M, N, addM),
       q303402_quotient_smul(A, M, N, addM, smul))"

definition q303402_has_rank_nullity ::
  "[i, i, i, i, i, i, i] => o" where
  "q303402_has_rank_nullity(kappa, A, zeroR, unitR, addR, negR, mulR) \<equiv>
     \<forall>M zeroM addM negM smul.
       M \<in> Vset(kappa) \<and>
       q303402_module(A, zeroR, unitR, addR, negR, mulR,
                      M, zeroM, addM, negM, smul)
       \<longrightarrow>
       ((\<exists>S\<in>Pow(M).
           q303402_independent(A, zeroR, M, zeroM, addM, smul, S) \<and>
           |S| = q303402_rank(A, zeroR, M, zeroM, addM, smul)) \<and>
        (\<forall>N\<in>Pow(M).
           q303402_submodule(A, M, zeroM, addM, negM, smul, N)
           \<longrightarrow>
           q303402_quotient_rank(A, zeroR, M, zeroM, addM, smul, N) \<oplus>
           q303402_rank(A, zeroR, N, zeroM, addM, smul) =
           q303402_rank(A, zeroR, M, zeroM, addM, smul)))"

definition q303402_linear_map ::
  "[i, i, i, i, i, i, i, i] => o" where
  "q303402_linear_map(A, M, addM, smulM, N, addN, smulN, f) \<equiv>
     f \<in> M -> N \<and>
     (\<forall>x\<in>M. \<forall>y\<in>M.
        f`(addM`\<langle>x,y\<rangle>) = addN`\<langle>f`x,f`y\<rangle>) \<and>
     (\<forall>a\<in>A. \<forall>x\<in>M.
        f`(smulM`\<langle>a,x\<rangle>) = smulN`\<langle>a,f`x\<rangle>)"

definition q303402_kernel ::
  "[i, i, i] => i" where
  "q303402_kernel(M, zeroN, f) \<equiv>
     {x \<in> M. f`x = zeroN}"

definition q303402_range ::
  "[i, i] => i" where
  "q303402_range(M, f) \<equiv> f``M"

theorem Q303402_rank_nullity:
  assumes "q303402_type_universe(kappa)"
      and "M \<in> Vset(kappa)"
      and "N \<in> Vset(kappa)"
      and "q303402_ring(A, zeroR, unitR, addR, negR, mulR)"
      and "q303402_module(A, zeroR, unitR, addR, negR, mulR,
                          M, zeroM, addM, negM, smulM)"
      and "q303402_module(A, zeroR, unitR, addR, negR, mulR,
                          N, zeroN, addN, negN, smulN)"
      and "q303402_has_rank_nullity(kappa, A, zeroR, unitR, addR, negR, mulR)"
      and "q303402_linear_map(A, M, addM, smulM, N, addN, smulN, f)"
  shows
    "q303402_rank(A, zeroR,
       q303402_range(M, f), zeroN, addN, smulN) \<oplus>
     q303402_rank(A, zeroR,
       q303402_kernel(M, zeroN, f), zeroM, addM, smulM) =
     q303402_rank(A, zeroR, M, zeroM, addM, smulM)"
  oops

end
