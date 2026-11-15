(*  Title:      HOL/Set.thy
    Author:     Tobias Nipkow
    Author:     Lawrence C Paulson
    Author:     Markus Wenzel
*)

section \<open>Set theory for higher-order logic\<close>

theory Set
  imports Lattices Boolean_Algebras
begin

subsection \<open>Sets as predicates\<close>

typedecl 'a set

axiomatization Collect :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set" \<comment> \<open>comprehension\<close>
  and member :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" \<comment> \<open>membership\<close>
  where mem_Collect_eq [iff, code_unfold]: "member a (Collect P) = P a"
    and Collect_mem_eq [simp, code_unfold]: "Collect (\<lambda>x. member x A) = A"

notation
  member  (\<open>'(\<in>')\<close>) and
  member  (\<open>(\<open>notation=\<open>infix \<in>\<close>\<close>_/ \<in> _)\<close> [51, 51] 50)

abbreviation not_member
  where "not_member x A \<equiv> \<not> (x \<in> A)" \<comment> \<open>non-membership\<close>
notation
  not_member  (\<open>'(\<notin>')\<close>) and
  not_member  (\<open>(\<open>notation=\<open>infix \<notin>\<close>\<close>_/ \<notin> _)\<close> [51, 51] 50)

open_bundle member_ASCII_syntax
begin
notation (ASCII)
  member  (\<open>'(:')\<close>) and
  member  (\<open>(\<open>notation=\<open>infix :\<close>\<close>_/ : _)\<close> [51, 51] 50) and
  not_member  (\<open>'(~:')\<close>) and
  not_member  (\<open>(\<open>notation=\<open>infix ~:\<close>\<close>_/ ~: _)\<close> [51, 51] 50)
end


text \<open>Set comprehensions\<close>

syntax
  "_Coll" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a set"    (\<open>(\<open>indent=1 notation=\<open>mixfix set comprehension\<close>\<close>{_./ _})\<close>)
syntax_consts
  "_Coll" \<rightleftharpoons> Collect
translations
  "{x. P}" \<rightleftharpoons> "CONST Collect (\<lambda>x. P)"

syntax (ASCII)
  "_Collect" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> 'a set"  (\<open>(\<open>indent=1 notation=\<open>mixfix set comprehension\<close>\<close>{(_/: _)./ _})\<close>)
syntax
  "_Collect" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> 'a set"  (\<open>(\<open>indent=1 notation=\<open>mixfix set comprehension\<close>\<close>{(_/ \<in> _)./ _})\<close>)
translations
  "{p:A. P}" \<rightharpoonup> "CONST Collect (\<lambda>p. p \<in> A \<and> P)"

ML \<open>
  fun Collect_binder_tr' c [Abs (x, T, t), Const (\<^const_syntax>\<open>Collect\<close>, _) $ Abs (y, _, P)] =
        if x = y then
          let
            val x' = Syntax_Trans.mark_bound_body (x, T);
            val t' = subst_bound (x', t);
            val P' = subst_bound (x', P);
          in Syntax.const c $ Syntax_Trans.mark_bound_abs (x, T) $ P' $ t' end
        else raise Match
    | Collect_binder_tr' _ _ = raise Match
\<close>

lemma CollectI: "P a \<Longrightarrow> a \<in> {x. P x}"
  by sorry

lemma CollectD: "a \<in> {x. P x} \<Longrightarrow> P a"
  by sorry

lemma Collect_cong: "(\<And>x. P x = Q x) \<Longrightarrow> {x. P x} = {x. Q x}"
  by sorry

text \<open>
  Simproc for pulling \<open>x = t\<close> in \<open>{x. \<dots> \<and> x = t \<and> \<dots>}\<close>
  to the front (and similarly for \<open>t = x\<close>):
\<close>

simproc_setup defined_Collect ("{x. P x \<and> Q x}") = \<open>
  K (Quantifier1.rearrange_Collect
    (fn ctxt =>
      resolve_tac ctxt @{thms Collect_cong} 1 THEN
      resolve_tac ctxt @{thms iffI} 1 THEN
      ALLGOALS
        (EVERY' [REPEAT_DETERM o eresolve_tac ctxt @{thms conjE},
          DEPTH_SOLVE_1 o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms conjI})])))
\<close>

lemmas CollectE = CollectD [elim_format]

lemma set_eqI:
  assumes "\<And>x. x \<in> A \<longleftrightarrow> x \<in> B"
  shows "A = B"
  by sorry

lemma set_eq_iff: "A = B \<longleftrightarrow> (\<forall>x. x \<in> A \<longleftrightarrow> x \<in> B)"
  by sorry

lemma Collect_eqI:
  assumes "\<And>x. P x = Q x"
  shows "Collect P = Collect Q"
  by sorry

text \<open>Lifting of predicate class instances\<close>

instantiation set :: (type) boolean_algebra
begin

definition less_eq_set
  where "A \<le> B \<longleftrightarrow> (\<lambda>x. member x A) \<le> (\<lambda>x. member x B)"

definition less_set
  where "A < B \<longleftrightarrow> (\<lambda>x. member x A) < (\<lambda>x. member x B)"

definition inf_set
  where "A \<sqinter> B = Collect ((\<lambda>x. member x A) \<sqinter> (\<lambda>x. member x B))"

definition sup_set
  where "A \<squnion> B = Collect ((\<lambda>x. member x A) \<squnion> (\<lambda>x. member x B))"

definition bot_set
  where "\<bottom> = Collect \<bottom>"

definition top_set
  where "\<top> = Collect \<top>"

definition uminus_set
  where "- A = Collect (- (\<lambda>x. member x A))"

definition minus_set
  where "A - B = Collect ((\<lambda>x. member x A) - (\<lambda>x. member x B))"

instance
  by standard
    (simp_all add: less_eq_set_def less_set_def inf_set_def sup_set_def
      bot_set_def top_set_def uminus_set_def minus_set_def
      less_le_not_le sup_inf_distrib1 diff_eq set_eqI fun_eq_iff
      del: inf_apply sup_apply bot_apply top_apply minus_apply uminus_apply)

end

text \<open>Set enumerations\<close>

abbreviation empty :: "'a set" (\<open>{}\<close>)
  where "{} \<equiv> bot"

definition insert :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where insert_compr: "insert a B = {x. x = a \<or> x \<in> B}"

open_bundle set_enumeration_syntax
begin

syntax
  "_Finset" :: "args \<Rightarrow> 'a set"  (\<open>(\<open>indent=1 notation=\<open>mixfix set enumeration\<close>\<close>{_})\<close>)
syntax_consts
  "_Finset" \<rightleftharpoons> insert
translations
  "{x, xs}" \<rightleftharpoons> "CONST insert x {xs}"
  "{x}" \<rightleftharpoons> "CONST insert x {}"

end


subsection \<open>Subsets and bounded quantifiers\<close>

abbreviation subset :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool"
  where "subset \<equiv> less"

abbreviation subset_eq :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool"
  where "subset_eq \<equiv> less_eq"

notation
  subset  (\<open>'(\<subset>')\<close>) and
  subset  (\<open>(\<open>notation=\<open>infix \<subset>\<close>\<close>_/ \<subset> _)\<close> [51, 51] 50) and
  subset_eq  (\<open>'(\<subseteq>')\<close>) and
  subset_eq  (\<open>(\<open>notation=\<open>infix \<subseteq>\<close>\<close>_/ \<subseteq> _)\<close> [51, 51] 50)

abbreviation (input)
  supset :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "supset \<equiv> greater"

abbreviation (input)
  supset_eq :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "supset_eq \<equiv> greater_eq"

notation
  supset  (\<open>'(\<supset>')\<close>) and
  supset  (\<open>(\<open>notation=\<open>infix \<supset>\<close>\<close>_/ \<supset> _)\<close> [51, 51] 50) and
  supset_eq  (\<open>'(\<supseteq>')\<close>) and
  supset_eq  (\<open>(\<open>notation=\<open>infix \<supseteq>\<close>\<close>_/ \<supseteq> _)\<close> [51, 51] 50)

notation (ASCII output)
  subset  (\<open>'(<')\<close>) and
  subset  (\<open>(\<open>notation=\<open>infix <\<close>\<close>_/ < _)\<close> [51, 51] 50) and
  subset_eq  (\<open>'(<=')\<close>) and
  subset_eq  (\<open>(\<open>notation=\<open>infix <=\<close>\<close>_/ <= _)\<close> [51, 51] 50)

definition Ball :: "'a set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  where "Ball A P \<longleftrightarrow> (\<forall>x. x \<in> A \<longrightarrow> P x)"   \<comment> \<open>bounded universal quantifiers\<close>

definition Bex :: "'a set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  where "Bex A P \<longleftrightarrow> (\<exists>x. x \<in> A \<and> P x)"   \<comment> \<open>bounded existential quantifiers\<close>

syntax (ASCII)
  "_Ball"       :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool"      (\<open>(\<open>indent=3 notation=\<open>binder ALL :\<close>\<close>ALL (_/:_)./ _)\<close> [0, 0, 10] 10)
  "_Bex"        :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool"      (\<open>(\<open>indent=3 notation=\<open>binder EX :\<close>\<close>EX (_/:_)./ _)\<close> [0, 0, 10] 10)
  "_Bex1"       :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool"      (\<open>(\<open>indent=3 notation=\<open>binder EX! :\<close>\<close>EX! (_/:_)./ _)\<close> [0, 0, 10] 10)
  "_Bleast"     :: "id \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> 'a"           (\<open>(\<open>indent=3 notation=\<open>binder LEAST :\<close>\<close>LEAST (_/:_)./ _)\<close> [0, 0, 10] 10)

syntax (input)
  "_Ball"       :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool"      (\<open>(\<open>indent=3 notation=\<open>binder ! :\<close>\<close>! (_/:_)./ _)\<close> [0, 0, 10] 10)
  "_Bex"        :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool"      (\<open>(\<open>indent=3 notation=\<open>binder ? :\<close>\<close>? (_/:_)./ _)\<close> [0, 0, 10] 10)
  "_Bex1"       :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool"      (\<open>(\<open>indent=3 notation=\<open>binder ?! :\<close>\<close>?! (_/:_)./ _)\<close> [0, 0, 10] 10)

syntax
  "_Ball"       :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool"      (\<open>(\<open>indent=3 notation=\<open>binder \<forall>\<close>\<close>\<forall>(_/\<in>_)./ _)\<close> [0, 0, 10] 10)
  "_Bex"        :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool"      (\<open>(\<open>indent=3 notation=\<open>binder \<exists>\<close>\<close>\<exists>(_/\<in>_)./ _)\<close> [0, 0, 10] 10)
  "_Bex1"       :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool"      (\<open>(\<open>indent=3 notation=\<open>binder \<exists>!\<close>\<close>\<exists>!(_/\<in>_)./ _)\<close> [0, 0, 10] 10)
  "_Bleast"     :: "id \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> 'a"           (\<open>(\<open>indent=3 notation=\<open>binder LEAST\<close>\<close>LEAST(_/\<in>_)./ _)\<close> [0, 0, 10] 10)

syntax_consts
  "_Ball" \<rightleftharpoons> Ball and
  "_Bex" \<rightleftharpoons> Bex and
  "_Bex1" \<rightleftharpoons> Ex1 and
  "_Bleast" \<rightleftharpoons> Least

translations
  "\<forall>x\<in>A. P" \<rightleftharpoons> "CONST Ball A (\<lambda>x. P)"
  "\<exists>x\<in>A. P" \<rightleftharpoons> "CONST Bex A (\<lambda>x. P)"
  "\<exists>!x\<in>A. P" \<rightharpoonup> "\<exists>!x. x \<in> A \<and> P"
  "LEAST x:A. P" \<rightharpoonup> "LEAST x. x \<in> A \<and> P"

syntax (ASCII output)
  "_setlessAll" :: "[idt, 'a, bool] \<Rightarrow> bool"  (\<open>(\<open>indent=3 notation=\<open>binder ALL\<close>\<close>ALL _<_./ _)\<close>  [0, 0, 10] 10)
  "_setlessEx"  :: "[idt, 'a, bool] \<Rightarrow> bool"  (\<open>(\<open>indent=3 notation=\<open>binder EX\<close>\<close>EX _<_./ _)\<close>  [0, 0, 10] 10)
  "_setleAll"   :: "[idt, 'a, bool] \<Rightarrow> bool"  (\<open>(\<open>indent=3 notation=\<open>binder ALL\<close>\<close>ALL _<=_./ _)\<close> [0, 0, 10] 10)
  "_setleEx"    :: "[idt, 'a, bool] \<Rightarrow> bool"  (\<open>(\<open>indent=3 notation=\<open>binder EX\<close>\<close>EX _<=_./ _)\<close> [0, 0, 10] 10)
  "_setleEx1"   :: "[idt, 'a, bool] \<Rightarrow> bool"  (\<open>(\<open>indent=3 notation=\<open>binder EX!\<close>\<close>EX! _<=_./ _)\<close> [0, 0, 10] 10)

syntax
  "_setlessAll" :: "[idt, 'a, bool] \<Rightarrow> bool"   (\<open>(\<open>indent=3 notation=\<open>binder \<forall>\<close>\<close>\<forall>_\<subset>_./ _)\<close>  [0, 0, 10] 10)
  "_setlessEx"  :: "[idt, 'a, bool] \<Rightarrow> bool"   (\<open>(\<open>indent=3 notation=\<open>binder \<exists>\<close>\<close>\<exists>_\<subset>_./ _)\<close>  [0, 0, 10] 10)
  "_setleAll"   :: "[idt, 'a, bool] \<Rightarrow> bool"   (\<open>(\<open>indent=3 notation=\<open>binder \<forall>\<close>\<close>\<forall>_\<subseteq>_./ _)\<close> [0, 0, 10] 10)
  "_setleEx"    :: "[idt, 'a, bool] \<Rightarrow> bool"   (\<open>(\<open>indent=3 notation=\<open>binder \<exists>\<close>\<close>\<exists>_\<subseteq>_./ _)\<close> [0, 0, 10] 10)
  "_setleEx1"   :: "[idt, 'a, bool] \<Rightarrow> bool"   (\<open>(\<open>indent=3 notation=\<open>binder \<exists>!\<close>\<close>\<exists>!_\<subseteq>_./ _)\<close> [0, 0, 10] 10)

syntax_consts
  "_setlessAll" "_setleAll" \<rightleftharpoons> All and
  "_setlessEx" "_setleEx" \<rightleftharpoons> Ex and
  "_setleEx1" \<rightleftharpoons> Ex1

translations
  "\<forall>A\<subset>B. P" \<rightharpoonup> "\<forall>A. A \<subset> B \<longrightarrow> P"
  "\<exists>A\<subset>B. P" \<rightharpoonup> "\<exists>A. A \<subset> B \<and> P"
  "\<forall>A\<subseteq>B. P" \<rightharpoonup> "\<forall>A. A \<subseteq> B \<longrightarrow> P"
  "\<exists>A\<subseteq>B. P" \<rightharpoonup> "\<exists>A. A \<subseteq> B \<and> P"
  "\<exists>!A\<subseteq>B. P" \<rightharpoonup> "\<exists>!A. A \<subseteq> B \<and> P"

print_translation \<open>
  let
    val All_binder = Mixfix.binder_name \<^const_syntax>\<open>All\<close>;
    val Ex_binder = Mixfix.binder_name \<^const_syntax>\<open>Ex\<close>;
    val impl = \<^const_syntax>\<open>HOL.implies\<close>;
    val conj = \<^const_syntax>\<open>HOL.conj\<close>;
    val sbset = \<^const_syntax>\<open>subset\<close>;
    val sbset_eq = \<^const_syntax>\<open>subset_eq\<close>;

    val trans =
     [((All_binder, impl, sbset), \<^syntax_const>\<open>_setlessAll\<close>),
      ((All_binder, impl, sbset_eq), \<^syntax_const>\<open>_setleAll\<close>),
      ((Ex_binder, conj, sbset), \<^syntax_const>\<open>_setlessEx\<close>),
      ((Ex_binder, conj, sbset_eq), \<^syntax_const>\<open>_setleEx\<close>)];

    fun mk v (v', T) c n P =
      if v = v' andalso not (Term.exists_subterm (fn Free (x, _) => x = v | _ => false) n)
      then Syntax.const c $ Syntax_Trans.mark_bound_body (v', T) $ n $ P
      else raise Match;

    fun tr' q = (q, fn _ =>
      (fn [Const (\<^syntax_const>\<open>_bound\<close>, _) $ Free (v, \<^Type>\<open>set _\<close>),
          Const (c, _) $
            (Const (d, _) $ (Const (\<^syntax_const>\<open>_bound\<close>, _) $ Free (v', T)) $ n) $ P] =>
          (case AList.lookup (=) trans (q, c, d) of
            NONE => raise Match
          | SOME l => mk v (v', T) l n P)
        | _ => raise Match));
  in
    [tr' All_binder, tr' Ex_binder]
  end
\<close>


text \<open>
  \<^medskip>
  Translate between \<open>{e | x1\<dots>xn. P}\<close> and \<open>{u. \<exists>x1\<dots>xn. u = e \<and> P}\<close>;
  \<open>{y. \<exists>x1\<dots>xn. y = e \<and> P}\<close> is only translated if \<open>[0..n] \<subseteq> bvs e\<close>.
\<close>

syntax
  "_Setcompr" :: "'a \<Rightarrow> idts \<Rightarrow> bool \<Rightarrow> 'a set"
    (\<open>(\<open>indent=1 notation=\<open>mixfix set comprehension\<close>\<close>{_ |/_./ _})\<close>)
syntax_consts
  "_Setcompr" \<rightleftharpoons> Collect

parse_translation \<open>
  let
    val ex_tr = snd (Syntax_Trans.mk_binder_tr ("EX ", \<^const_syntax>\<open>Ex\<close>));

    fun nvars (Const (\<^syntax_const>\<open>_idts\<close>, _) $ _ $ idts) = nvars idts + 1
      | nvars _ = 1;

    fun setcompr_tr ctxt [e, idts, b] =
      let
        val eq = Syntax.const \<^const_syntax>\<open>HOL.eq\<close> $ Bound (nvars idts) $ e;
        val P = Syntax.const \<^const_syntax>\<open>HOL.conj\<close> $ eq $ b;
        val exP = ex_tr ctxt [idts, P];
      in Syntax.const \<^const_syntax>\<open>Collect\<close> $ absdummy dummyT exP end;

  in [(\<^syntax_const>\<open>_Setcompr\<close>, setcompr_tr)] end
\<close>

typed_print_translation \<open>
 [(\<^const_syntax>\<open>Ball\<close>, Syntax_Trans.preserve_binder_abs2_tr' \<^syntax_const>\<open>_Ball\<close>),
  (\<^const_syntax>\<open>Bex\<close>, Syntax_Trans.preserve_binder_abs2_tr' \<^syntax_const>\<open>_Bex\<close>)]
\<close> \<comment> \<open>to avoid eta-contraction of body\<close>

print_translation \<open>
let
  val ex_tr' = snd (Syntax_Trans.mk_binder_tr' (\<^const_syntax>\<open>Ex\<close>, "DUMMY"));

  fun setcompr_tr' ctxt [Abs (abs as (_, _, P))] =
    let
      fun check (Const (\<^const_syntax>\<open>Ex\<close>, _) $ Abs (_, _, P), n) = check (P, n + 1)
        | check (Const (\<^const_syntax>\<open>HOL.conj\<close>, _) $
              (Const (\<^const_syntax>\<open>HOL.eq\<close>, _) $ Bound m $ e) $ P, n) =
            n > 0 andalso m = n andalso not (loose_bvar1 (P, n)) andalso
            subset (=) (0 upto (n - 1), add_loose_bnos (e, 0, []))
        | check _ = false;

        fun tr' (_ $ abs) =
          let val _ $ idts $ (_ $ (_ $ _ $ e) $ Q) = ex_tr' ctxt [abs]
          in Syntax.const \<^syntax_const>\<open>_Setcompr\<close> $ e $ idts $ Q end;
    in
      if check (P, 0) then tr' P
      else
        let
          val (x as _ $ Free(xN, _), t) = Syntax_Trans.atomic_abs_tr' ctxt abs;
          val M = Syntax.const \<^syntax_const>\<open>_Coll\<close> $ x $ t;
        in
          case t of
            Const (\<^const_syntax>\<open>HOL.conj\<close>, _) $
              (Const (\<^const_syntax>\<open>Set.member\<close>, _) $
                (Const (\<^syntax_const>\<open>_bound\<close>, _) $ Free (yN, _)) $ A) $ P =>
            if xN = yN then Syntax.const \<^syntax_const>\<open>_Collect\<close> $ x $ A $ P else M
          | _ => M
        end
    end;
  in [(\<^const_syntax>\<open>Collect\<close>, setcompr_tr')] end
\<close>

simproc_setup defined_Bex ("\<exists>x\<in>A. P x \<and> Q x") = \<open>
  K (Quantifier1.rearrange_Bex (fn ctxt => unfold_tac ctxt @{thms Bex_def}))
\<close>

simproc_setup defined_All ("\<forall>x\<in>A. P x \<longrightarrow> Q x") = \<open>
  K (Quantifier1.rearrange_Ball (fn ctxt => unfold_tac ctxt @{thms Ball_def}))
\<close>

lemma ballI [intro!]: "(\<And>x. x \<in> A \<Longrightarrow> P x) \<Longrightarrow> \<forall>x\<in>A. P x"
  by sorry

lemmas strip = impI allI ballI

lemma bspec [dest?]: "\<forall>x\<in>A. P x \<Longrightarrow> x \<in> A \<Longrightarrow> P x"
  by sorry

text \<open>Gives better instantiation for bound:\<close>
setup \<open>
  map_theory_claset (fn ctxt =>
    ctxt addbefore ("bspec", fn ctxt' => dresolve_tac ctxt' @{thms bspec} THEN' assume_tac ctxt'))
\<close>

ML \<open>
structure Simpdata =
struct
  open Simpdata;
  val mksimps_pairs = [(\<^const_name>\<open>Ball\<close>, @{thms bspec})] @ mksimps_pairs;
end;

open Simpdata;
\<close>

declaration \<open>fn _ => Simplifier.map_simpset (Simplifier.set_mksimps (mksimps mksimps_pairs))\<close>

lemma ballE [elim]: "\<forall>x\<in>A. P x \<Longrightarrow> (P x \<Longrightarrow> Q) \<Longrightarrow> (x \<notin> A \<Longrightarrow> Q) \<Longrightarrow> Q"
  by sorry

lemma bexI [intro]: "P x \<Longrightarrow> x \<in> A \<Longrightarrow> \<exists>x\<in>A. P x"
  \<comment> \<open>Normally the best argument order: \<open>P x\<close> constrains the choice of \<open>x \<in> A\<close>.\<close>
  by sorry

lemma rev_bexI [intro?]: "x \<in> A \<Longrightarrow> P x \<Longrightarrow> \<exists>x\<in>A. P x"
  \<comment> \<open>The best argument order when there is only one \<open>x \<in> A\<close>.\<close>
  by sorry

lemma bexCI: "(\<forall>x\<in>A. \<not> P x \<Longrightarrow> P a) \<Longrightarrow> a \<in> A \<Longrightarrow> \<exists>x\<in>A. P x"
  by sorry

lemma bexE [elim!]: "\<exists>x\<in>A. P x \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> P x \<Longrightarrow> Q) \<Longrightarrow> Q"
  by sorry

lemma ball_triv [simp]: "(\<forall>x\<in>A. P) \<longleftrightarrow> ((\<exists>x. x \<in> A) \<longrightarrow> P)"
  \<comment> \<open>trivial rewrite rule.\<close>
  by sorry

lemma bex_triv [simp]: "(\<exists>x\<in>A. P) \<longleftrightarrow> ((\<exists>x. x \<in> A) \<and> P)"
  \<comment> \<open>Dual form for existentials.\<close>
  by sorry

lemma bex_triv_one_point1 [simp]: "(\<exists>x\<in>A. x = a) \<longleftrightarrow> a \<in> A"
  by sorry

lemma bex_triv_one_point2 [simp]: "(\<exists>x\<in>A. a = x) \<longleftrightarrow> a \<in> A"
  by sorry

lemma bex_one_point1 [simp]: "(\<exists>x\<in>A. x = a \<and> P x) \<longleftrightarrow> a \<in> A \<and> P a"
  by sorry

lemma bex_one_point2 [simp]: "(\<exists>x\<in>A. a = x \<and> P x) \<longleftrightarrow> a \<in> A \<and> P a"
  by sorry

lemma ball_one_point1 [simp]: "(\<forall>x\<in>A. x = a \<longrightarrow> P x) \<longleftrightarrow> (a \<in> A \<longrightarrow> P a)"
  by sorry

lemma ball_one_point2 [simp]: "(\<forall>x\<in>A. a = x \<longrightarrow> P x) \<longleftrightarrow> (a \<in> A \<longrightarrow> P a)"
  by sorry

lemma ball_conj_distrib: "(\<forall>x\<in>A. P x \<and> Q x) \<longleftrightarrow> (\<forall>x\<in>A. P x) \<and> (\<forall>x\<in>A. Q x)"
  by sorry

lemma bex_disj_distrib: "(\<exists>x\<in>A. P x \<or> Q x) \<longleftrightarrow> (\<exists>x\<in>A. P x) \<or> (\<exists>x\<in>A. Q x)"
  by sorry


text \<open>Congruence rules\<close>

lemma ball_cong:
  "\<lbrakk> A = B;  \<And>x. x \<in> B \<Longrightarrow> P x \<longleftrightarrow> Q x \<rbrakk> \<Longrightarrow>
    (\<forall>x\<in>A. P x) \<longleftrightarrow> (\<forall>x\<in>B. Q x)"
  by sorry

lemma ball_cong_simp [cong]:
  "\<lbrakk> A = B;  \<And>x. x \<in> B =simp=> P x \<longleftrightarrow> Q x \<rbrakk> \<Longrightarrow>
    (\<forall>x\<in>A. P x) \<longleftrightarrow> (\<forall>x\<in>B. Q x)"
  by sorry

lemma bex_cong:
  "\<lbrakk> A = B;  \<And>x. x \<in> B \<Longrightarrow> P x \<longleftrightarrow> Q x \<rbrakk> \<Longrightarrow>
    (\<exists>x\<in>A. P x) \<longleftrightarrow> (\<exists>x\<in>B. Q x)"
  by sorry

lemma bex_cong_simp [cong]:
  "\<lbrakk> A = B;  \<And>x. x \<in> B =simp=> P x \<longleftrightarrow> Q x \<rbrakk> \<Longrightarrow>
    (\<exists>x\<in>A. P x) \<longleftrightarrow> (\<exists>x\<in>B. Q x)"
  by sorry

lemma bex1_def: "(\<exists>!x\<in>X. P x) \<longleftrightarrow> (\<exists>x\<in>X. P x) \<and> (\<forall>x\<in>X. \<forall>y\<in>X. P x \<longrightarrow> P y \<longrightarrow> x = y)"
  by sorry


subsection \<open>Basic operations\<close>

subsubsection \<open>Subsets\<close>

lemma subsetI [intro!]: "(\<And>x. x \<in> A \<Longrightarrow> x \<in> B) \<Longrightarrow> A \<subseteq> B"
  by sorry

text \<open>
  \<^medskip>
  Map the type \<open>'a set \<Rightarrow> anything\<close> to just \<open>'a\<close>; for overloading constants
  whose first argument has type \<open>'a set\<close>.
\<close>

lemma subsetD [elim, intro?]: "A \<subseteq> B \<Longrightarrow> c \<in> A \<Longrightarrow> c \<in> B"
  by sorry

lemma rev_subsetD [intro?,no_atp]: "c \<in> A \<Longrightarrow> A \<subseteq> B \<Longrightarrow> c \<in> B"
  \<comment> \<open>The same, with reversed premises for use with @{method erule} -- cf. @{thm rev_mp}.\<close>
  by sorry

lemma subsetCE [elim,no_atp]: "A \<subseteq> B \<Longrightarrow> (c \<notin> A \<Longrightarrow> P) \<Longrightarrow> (c \<in> B \<Longrightarrow> P) \<Longrightarrow> P"
  \<comment> \<open>Classical elimination rule.\<close>
  by sorry

lemma subset_eq: "A \<subseteq> B \<longleftrightarrow> (\<forall>x\<in>A. x \<in> B)"
  by sorry

lemma contra_subsetD [no_atp]: "A \<subseteq> B \<Longrightarrow> c \<notin> B \<Longrightarrow> c \<notin> A"
  by sorry

lemma subset_refl: "A \<subseteq> A"
  by sorry

lemma subset_trans: "A \<subseteq> B \<Longrightarrow> B \<subseteq> C \<Longrightarrow> A \<subseteq> C"
  by sorry

lemma subset_not_subset_eq [code]: "A \<subset> B \<longleftrightarrow> A \<subseteq> B \<and> \<not> B \<subseteq> A"
  by sorry

lemma eq_mem_trans: "a = b \<Longrightarrow> b \<in> A \<Longrightarrow> a \<in> A"
  by sorry

lemmas basic_trans_rules [trans] =
  order_trans_rules rev_subsetD subsetD eq_mem_trans


subsubsection \<open>Equality\<close>

lemma subset_antisym [intro!]: "A \<subseteq> B \<Longrightarrow> B \<subseteq> A \<Longrightarrow> A = B"
  \<comment> \<open>Anti-symmetry of the subset relation.\<close>
  by sorry

text \<open>\<^medskip> Equality rules from ZF set theory -- are they appropriate here?\<close>

lemma equalityD1: "A = B \<Longrightarrow> A \<subseteq> B"
  by sorry

lemma equalityD2: "A = B \<Longrightarrow> B \<subseteq> A"
  by sorry

text \<open>
  \<^medskip>
  Be careful when adding this to the claset as \<open>subset_empty\<close> is in the
  simpset: \<^prop>\<open>A = {}\<close> goes to \<^prop>\<open>{} \<subseteq> A\<close> and \<^prop>\<open>A \<subseteq> {}\<close>
  and then back to \<^prop>\<open>A = {}\<close>!
\<close>

lemma equalityE: "A = B \<Longrightarrow> (A \<subseteq> B \<Longrightarrow> B \<subseteq> A \<Longrightarrow> P) \<Longrightarrow> P"
  by sorry

lemma equalityCE [elim]: "A = B \<Longrightarrow> (c \<in> A \<Longrightarrow> c \<in> B \<Longrightarrow> P) \<Longrightarrow> (c \<notin> A \<Longrightarrow> c \<notin> B \<Longrightarrow> P) \<Longrightarrow> P"
  by sorry

lemma eqset_imp_iff: "A = B \<Longrightarrow> x \<in> A \<longleftrightarrow> x \<in> B"
  by sorry

lemma eqelem_imp_iff: "x = y \<Longrightarrow> x \<in> A \<longleftrightarrow> y \<in> A"
  by sorry


subsubsection \<open>The empty set\<close>

lemma empty_def: "{} = {x. False}"
  by sorry

lemma empty_iff [simp]: "c \<in> {} \<longleftrightarrow> False"
  by sorry

lemma emptyE [elim!]: "a \<in> {} \<Longrightarrow> P"
  by sorry

lemma empty_subsetI [iff]: "{} \<subseteq> A"
  \<comment> \<open>One effect is to delete the ASSUMPTION \<^prop>\<open>{} \<subseteq> A\<close>\<close>
  by sorry

lemma equals0I: "(\<And>y. y \<in> A \<Longrightarrow> False) \<Longrightarrow> A = {}"
  by sorry

lemma equals0D: "A = {} \<Longrightarrow> a \<notin> A"
  \<comment> \<open>Use for reasoning about disjointness: \<open>A \<inter> B = {}\<close>\<close>
  by sorry

lemma ball_empty [simp]: "Ball {} P \<longleftrightarrow> True"
  by sorry

lemma bex_empty [simp]: "Bex {} P \<longleftrightarrow> False"
  by sorry


subsubsection \<open>The universal set -- UNIV\<close>

abbreviation UNIV :: "'a set"
  where "UNIV \<equiv> top"

lemma UNIV_def: "UNIV = {x. True}"
  by sorry

lemma UNIV_I [simp]: "x \<in> UNIV"
  by sorry

declare UNIV_I [intro]  \<comment> \<open>unsafe makes it less likely to cause problems\<close>

lemma UNIV_witness [intro?]: "\<exists>x. x \<in> UNIV"
  by sorry

lemma subset_UNIV: "A \<subseteq> UNIV"
  by sorry

text \<open>
  \<^medskip>
  Eta-contracting these two rules (to remove \<open>P\<close>) causes them
  to be ignored because of their interaction with congruence rules.
\<close>

lemma ball_UNIV [simp]: "Ball UNIV P \<longleftrightarrow> All P"
  by sorry

lemma bex_UNIV [simp]: "Bex UNIV P \<longleftrightarrow> Ex P"
  by sorry

lemma UNIV_eq_I: "(\<And>x. x \<in> A) \<Longrightarrow> UNIV = A"
  by sorry

lemma UNIV_not_empty [iff]: "UNIV \<noteq> {}"
  by sorry

lemma empty_not_UNIV[simp]: "{} \<noteq> UNIV"
  by sorry


subsubsection \<open>The Powerset operator -- Pow\<close>

definition Pow :: "'a set \<Rightarrow> 'a set set"
  where Pow_def: "Pow A = {B. B \<subseteq> A}"

lemma Pow_iff [iff]: "A \<in> Pow B \<longleftrightarrow> A \<subseteq> B"
  by sorry

lemma PowI: "A \<subseteq> B \<Longrightarrow> A \<in> Pow B"
  by sorry

lemma PowD: "A \<in> Pow B \<Longrightarrow> A \<subseteq> B"
  by sorry

lemma Pow_bottom: "{} \<in> Pow B"
  by sorry

lemma Pow_top: "A \<in> Pow A"
  by sorry

lemma Pow_not_empty: "Pow A \<noteq> {}"
  by sorry


subsubsection \<open>Set complement\<close>

lemma Compl_iff [simp]: "c \<in> - A \<longleftrightarrow> c \<notin> A"
  by sorry

lemma ComplI [intro!]: "(c \<in> A \<Longrightarrow> False) \<Longrightarrow> c \<in> - A"
  by sorry

text \<open>
  \<^medskip>
  This form, with negated conclusion, works well with the Classical prover.
  Negated assumptions behave like formulae on the right side of the
  notional turnstile \dots
\<close>

lemma ComplD [dest!]: "c \<in> - A \<Longrightarrow> c \<notin> A"
  by sorry

lemmas ComplE = ComplD [elim_format]

lemma Compl_eq: "- A = {x. \<not> x \<in> A}"
  by sorry


subsubsection \<open>Binary intersection\<close>

abbreviation inter :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set"  (infixl \<open>\<inter>\<close> 70)
  where "(\<inter>) \<equiv> inf"

notation (ASCII)
  inter  (infixl \<open>Int\<close> 70)

lemma Int_def: "A \<inter> B = {x. x \<in> A \<and> x \<in> B}"
  by sorry

lemma Int_iff [simp]: "c \<in> A \<inter> B \<longleftrightarrow> c \<in> A \<and> c \<in> B"
  by sorry

lemma IntI [intro!]: "c \<in> A \<Longrightarrow> c \<in> B \<Longrightarrow> c \<in> A \<inter> B"
  by sorry

lemma IntD1: "c \<in> A \<inter> B \<Longrightarrow> c \<in> A"
  by sorry

lemma IntD2: "c \<in> A \<inter> B \<Longrightarrow> c \<in> B"
  by sorry

lemma IntE [elim!]: "c \<in> A \<inter> B \<Longrightarrow> (c \<in> A \<Longrightarrow> c \<in> B \<Longrightarrow> P) \<Longrightarrow> P"
  by sorry


subsubsection \<open>Binary union\<close>

abbreviation union :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set"  (infixl \<open>\<union>\<close> 65)
  where "union \<equiv> sup"

notation (ASCII)
  union  (infixl \<open>Un\<close> 65)

lemma Un_def: "A \<union> B = {x. x \<in> A \<or> x \<in> B}"
  by sorry

lemma Un_iff [simp]: "c \<in> A \<union> B \<longleftrightarrow> c \<in> A \<or> c \<in> B"
  by sorry

lemma UnI1 [elim?]: "c \<in> A \<Longrightarrow> c \<in> A \<union> B"
  by sorry

lemma UnI2 [elim?]: "c \<in> B \<Longrightarrow> c \<in> A \<union> B"
  by sorry

text \<open>\<^medskip> Classical introduction rule: no commitment to \<open>A\<close> vs. \<open>B\<close>.\<close>
lemma UnCI [intro!]: "(c \<notin> B \<Longrightarrow> c \<in> A) \<Longrightarrow> c \<in> A \<union> B"
  by sorry

lemma UnE [elim!]: "c \<in> A \<union> B \<Longrightarrow> (c \<in> A \<Longrightarrow> P) \<Longrightarrow> (c \<in> B \<Longrightarrow> P) \<Longrightarrow> P"
  by sorry

lemma insert_def: "insert a B = {x. x = a} \<union> B"
  by sorry


subsubsection \<open>Set difference\<close>

text \<open>The minius-sign syntax continues to be accepted\<close>
abbreviation set_difference :: "['a set, 'a set] \<Rightarrow> 'a set" 
  (infixl "\<setminus>" 65) where "A \<setminus> B \<equiv> A-B"

lemma Diff_iff [simp]: "c \<in> A - B \<longleftrightarrow> c \<in> A \<and> c \<notin> B"
  by sorry

lemma DiffI [intro!]: "c \<in> A \<Longrightarrow> c \<notin> B \<Longrightarrow> c \<in> A - B"
  by sorry

lemma DiffD1: "c \<in> A - B \<Longrightarrow> c \<in> A"
  by sorry

lemma DiffD2: "c \<in> A - B \<Longrightarrow> c \<in> B \<Longrightarrow> P"
  by sorry

lemma DiffE [elim!]: "c \<in> A - B \<Longrightarrow> (c \<in> A \<Longrightarrow> c \<notin> B \<Longrightarrow> P) \<Longrightarrow> P"
  by sorry

lemma set_diff_eq: "A - B = {x. x \<in> A \<and> x \<notin> B}"
  by sorry

lemma Compl_eq_Diff_UNIV: "- A = (UNIV - A)"
  by sorry

abbreviation sym_diff :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "sym_diff A B \<equiv> ((A - B) \<union> (B-A))"


subsubsection \<open>Augmenting a set -- \<^const>\<open>insert\<close>\<close>

lemma insert_iff [simp]: "a \<in> insert b A \<longleftrightarrow> a = b \<or> a \<in> A"
  by sorry

lemma insertI1: "a \<in> insert a B"
  by sorry

lemma insertI2: "a \<in> B \<Longrightarrow> a \<in> insert b B"
  by sorry

lemma insertE [elim!]: "a \<in> insert b A \<Longrightarrow> (a = b \<Longrightarrow> P) \<Longrightarrow> (a \<in> A \<Longrightarrow> P) \<Longrightarrow> P"
  by sorry

lemma insertCI [intro!]: "(a \<notin> B \<Longrightarrow> a = b) \<Longrightarrow> a \<in> insert b B"
  \<comment> \<open>Classical introduction rule.\<close>
  by sorry

lemma subset_insert_iff: "A \<subseteq> insert x B \<longleftrightarrow> (if x \<in> A then A - {x} \<subseteq> B else A \<subseteq> B)"
  by sorry

lemma set_insert:
  assumes "x \<in> A"
  obtains B where "A = insert x B" and "x \<notin> B"
  by sorry

lemma insert_ident: "x \<notin> A \<Longrightarrow> x \<notin> B \<Longrightarrow> insert x A = insert x B \<longleftrightarrow> A = B"
  by sorry

lemma insert_eq_iff:
  assumes "a \<notin> A" "b \<notin> B"
  shows "insert a A = insert b B \<longleftrightarrow>
    (if a = b then A = B else \<exists>C. A = insert b C \<and> b \<notin> C \<and> B = insert a C \<and> a \<notin> C)"
    (is "?L \<longleftrightarrow> ?R")
  by sorry

lemma insert_UNIV[simp]: "insert x UNIV = UNIV"
  by sorry


subsubsection \<open>Singletons, using insert\<close>

lemma singletonI [intro!]: "a \<in> {a}"
  \<comment> \<open>Redundant? But unlike \<open>insertCI\<close>, it proves the subgoal immediately!\<close>
  by sorry

lemma singletonD [dest!]: "b \<in> {a} \<Longrightarrow> b = a"
  by sorry

lemmas singletonE = singletonD [elim_format]

lemma singleton_iff: "b \<in> {a} \<longleftrightarrow> b = a"
  by sorry

lemma singleton_inject [dest!]: "{a} = {b} \<Longrightarrow> a = b"
  by sorry

lemma singleton_insert_inj_eq [iff]: "{b} = insert a A \<longleftrightarrow> a = b \<and> A \<subseteq> {b}"
  by sorry

lemma singleton_insert_inj_eq' [iff]: "insert a A = {b} \<longleftrightarrow> a = b \<and> A \<subseteq> {b}"
  by sorry

lemma subset_singletonD: "A \<subseteq> {x} \<Longrightarrow> A = {} \<or> A = {x}"
  by sorry

lemma subset_singleton_iff: "X \<subseteq> {a} \<longleftrightarrow> X = {} \<or> X = {a}"
  by sorry

lemma subset_singleton_iff_Uniq: "(\<exists>a. A \<subseteq> {a}) \<longleftrightarrow> (\<exists>\<^sub>\<le>\<^sub>1x. x \<in> A)"
  by sorry

lemma singleton_conv [simp]: "{x. x = a} = {a}"
  by sorry

lemma singleton_conv2 [simp]: "{x. a = x} = {a}"
  by sorry

lemma Diff_single_insert: "A - {x} \<subseteq> B \<Longrightarrow> A \<subseteq> insert x B"
  by sorry

lemma subset_Diff_insert: "A \<subseteq> B - insert x C \<longleftrightarrow> A \<subseteq> B - C \<and> x \<notin> A"
  by sorry

lemma doubleton_eq_iff: "{a, b} = {c, d} \<longleftrightarrow> a = c \<and> b = d \<or> a = d \<and> b = c"
  by sorry

lemma Un_singleton_iff: "A \<union> B = {x} \<longleftrightarrow> A = {} \<and> B = {x} \<or> A = {x} \<and> B = {} \<or> A = {x} \<and> B = {x}"
  by sorry

lemma singleton_Un_iff: "{x} = A \<union> B \<longleftrightarrow> A = {} \<and> B = {x} \<or> A = {x} \<and> B = {} \<or> A = {x} \<and> B = {x}"
  by sorry


subsubsection \<open>Image of a set under a function\<close>

text \<open>Frequently \<open>b\<close> does not have the syntactic form of \<open>f x\<close>.\<close>

definition image :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set"    (infixr \<open>`\<close> 90)
  where "f ` A = {y. \<exists>x\<in>A. y = f x}"

lemma image_eqI [simp, intro]: "b = f x \<Longrightarrow> x \<in> A \<Longrightarrow> b \<in> f ` A"
  by sorry

lemma imageI: "x \<in> A \<Longrightarrow> f x \<in> f ` A"
  by sorry

lemma rev_image_eqI: "x \<in> A \<Longrightarrow> b = f x \<Longrightarrow> b \<in> f ` A"
  \<comment> \<open>This version's more effective when we already have the required \<open>x\<close>.\<close>
  by sorry

lemma imageE [elim!]:
  assumes "b \<in> (\<lambda>x. f x) ` A"  \<comment> \<open>The eta-expansion gives variable-name preservation.\<close>
  obtains x where "b = f x" and "x \<in> A"
  by sorry

lemma Compr_image_eq: "{x \<in> f ` A. P x} = f ` {x \<in> A. P (f x)}"
  by sorry

lemma image_Un: "f ` (A \<union> B) = f ` A \<union> f ` B"
  by sorry

lemma image_iff: "z \<in> f ` A \<longleftrightarrow> (\<exists>x\<in>A. z = f x)"
  by sorry

lemma image_subsetI: "(\<And>x. x \<in> A \<Longrightarrow> f x \<in> B) \<Longrightarrow> f ` A \<subseteq> B"
  \<comment> \<open>Replaces the three steps \<open>subsetI\<close>, \<open>imageE\<close>,
    \<open>hypsubst\<close>, but breaks too many existing proofs.\<close>
  by sorry

lemma image_subset_iff: "f ` A \<subseteq> B \<longleftrightarrow> (\<forall>x\<in>A. f x \<in> B)"
  \<comment> \<open>This rewrite rule would confuse users if made default.\<close>
  by sorry

lemma subset_imageE:
  assumes "B \<subseteq> f ` A"
  obtains C where "C \<subseteq> A" and "B = f ` C"
  by sorry

lemma subset_image_iff: "B \<subseteq> f ` A \<longleftrightarrow> (\<exists>AA\<subseteq>A. B = f ` AA)"
  by sorry

lemma image_ident [simp]: "(\<lambda>x. x) ` Y = Y"
  by sorry

lemma image_empty [simp]: "f ` {} = {}"
  by sorry

lemma image_insert [simp]: "f ` insert a B = insert (f a) (f ` B)"
  by sorry

lemma image_constant: "x \<in> A \<Longrightarrow> (\<lambda>x. c) ` A = {c}"
  by sorry

lemma image_constant_conv: "(\<lambda>x. c) ` A = (if A = {} then {} else {c})"
  by sorry

lemma image_image: "f ` (g ` A) = (\<lambda>x. f (g x)) ` A"
  by sorry

lemma insert_image [simp]: "x \<in> A \<Longrightarrow> insert (f x) (f ` A) = f ` A"
  by sorry

lemma image_is_empty [iff]: "f ` A = {} \<longleftrightarrow> A = {}"
  by sorry

lemma empty_is_image [iff]: "{} = f ` A \<longleftrightarrow> A = {}"
  by sorry

lemma image_Collect: "f ` {x. P x} = {f x | x. P x}"
  \<comment> \<open>NOT suitable as a default simp rule: the RHS isn't simpler than the LHS,
      with its implicit quantifier and conjunction.  Also image enjoys better
      equational properties than does the RHS.\<close>
  by sorry

lemma if_image_distrib [simp]:
  "(\<lambda>x. if P x then f x else g x) ` S = f ` (S \<inter> {x. P x}) \<union> g ` (S \<inter> {x. \<not> P x})"
  by sorry

lemma image_cong:
  "f ` M = g ` N" if "M = N" "\<And>x. x \<in> N \<Longrightarrow> f x = g x"
  by sorry

lemma image_cong_simp [cong]:
  "f ` M = g ` N" if "M = N" "\<And>x. x \<in> N =simp=> f x = g x"
  by sorry

lemma image_Int_subset: "f ` (A \<inter> B) \<subseteq> f ` A \<inter> f ` B"
  by sorry

lemma image_diff_subset: "f ` A - f ` B \<subseteq> f ` (A - B)"
  by sorry

lemma Setcompr_eq_image: "{f x |x. x \<in> A} = f ` A"
  by sorry

lemma setcompr_eq_image: "{f x |x. P x} = f ` {x. P x}"
  by sorry

lemma ball_imageD: "\<forall>x\<in>f ` A. P x \<Longrightarrow> \<forall>x\<in>A. P (f x)"
  by sorry

lemma bex_imageD: "\<exists>x\<in>f ` A. P x \<Longrightarrow> \<exists>x\<in>A. P (f x)"
  by sorry

lemma image_add_0 [simp]: "(+) (0::'a::comm_monoid_add) ` S = S"
  by sorry

theorem Cantors_theorem: "\<nexists>f. f ` A = Pow A"
  by sorry

text \<open>\<^medskip> Range of a function -- just an abbreviation for image!\<close>

abbreviation range :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b set"  \<comment> \<open>of function\<close>
  where "range f \<equiv> f ` UNIV"

lemma range_eqI: "b = f x \<Longrightarrow> b \<in> range f"
  by sorry

lemma rangeI: "f x \<in> range f"
  by sorry

lemma rangeE [elim?]: "b \<in> range (\<lambda>x. f x) \<Longrightarrow> (\<And>x. b = f x \<Longrightarrow> P) \<Longrightarrow> P"
  by sorry

lemma range_subsetD: "range f \<subseteq> B \<Longrightarrow> f i \<in> B"
  by sorry

lemma full_SetCompr_eq: "{u. \<exists>x. u = f x} = range f"
  by sorry

lemma range_composition: "range (\<lambda>x. f (g x)) = f ` range g"
  by sorry

lemma range_constant [simp]: "range (\<lambda>_. x) = {x}"
  by sorry

lemma range_eq_singletonD: "range f = {a} \<Longrightarrow> f x = a"
  by sorry


subsubsection \<open>Some rules with \<open>if\<close>\<close>

text \<open>Elimination of \<open>{x. \<dots> \<and> x = t \<and> \<dots>}\<close>.\<close>

lemma Collect_conv_if: "{x. x = a \<and> P x} = (if P a then {a} else {})"
  by sorry

lemma Collect_conv_if2: "{x. a = x \<and> P x} = (if P a then {a} else {})"
  by sorry

text \<open>
  Rewrite rules for boolean case-splitting: faster than \<open>if_split [split]\<close>.
\<close>

lemma if_split_eq1: "(if Q then x else y) = b \<longleftrightarrow> (Q \<longrightarrow> x = b) \<and> (\<not> Q \<longrightarrow> y = b)"
  by sorry

lemma if_split_eq2: "a = (if Q then x else y) \<longleftrightarrow> (Q \<longrightarrow> a = x) \<and> (\<not> Q \<longrightarrow> a = y)"
  by sorry

text \<open>
  Split ifs on either side of the membership relation.
  Not for \<open>[simp]\<close> -- can cause goals to blow up!
\<close>

lemma if_split_mem1: "(if Q then x else y) \<in> b \<longleftrightarrow> (Q \<longrightarrow> x \<in> b) \<and> (\<not> Q \<longrightarrow> y \<in> b)"
  by sorry

lemma if_split_mem2: "(a \<in> (if Q then x else y)) \<longleftrightarrow> (Q \<longrightarrow> a \<in> x) \<and> (\<not> Q \<longrightarrow> a \<in> y)"
  by sorry

lemmas split_ifs = if_bool_eq_conj if_split_eq1 if_split_eq2 if_split_mem1 if_split_mem2

(*Would like to add these, but the existing code only searches for the
  outer-level constant, which in this case is just Set.member; we instead need
  to use term-nets to associate patterns with rules.  Also, if a rule fails to
  apply, then the formula should be kept.
  [("uminus", Compl_iff RS iffD1), ("minus", [Diff_iff RS iffD1]),
   ("Int", [IntD1,IntD2]),
   ("Collect", [CollectD]), ("Inter", [InterD]), ("INTER", [INT_D])]
 *)


subsection \<open>Further operations and lemmas\<close>

subsubsection \<open>The ``proper subset'' relation\<close>

lemma psubsetI [intro!]: "A \<subseteq> B \<Longrightarrow> A \<noteq> B \<Longrightarrow> A \<subset> B"
  by sorry

lemma psubsetE [elim!]: "A \<subset> B \<Longrightarrow> (A \<subseteq> B \<Longrightarrow> \<not> B \<subseteq> A \<Longrightarrow> R) \<Longrightarrow> R"
  by sorry

lemma psubset_insert_iff:
  "A \<subset> insert x B \<longleftrightarrow> (if x \<in> B then A \<subset> B else if x \<in> A then A - {x} \<subset> B else A \<subseteq> B)"
  by sorry

lemma psubset_eq: "A \<subset> B \<longleftrightarrow> A \<subseteq> B \<and> A \<noteq> B"
  by sorry

lemma psubset_imp_subset: "A \<subset> B \<Longrightarrow> A \<subseteq> B"
  by sorry

lemma psubset_trans: "A \<subset> B \<Longrightarrow> B \<subset> C \<Longrightarrow> A \<subset> C"
  by sorry

lemma psubsetD: "A \<subset> B \<Longrightarrow> c \<in> A \<Longrightarrow> c \<in> B"
  by sorry

lemma psubset_subset_trans: "A \<subset> B \<Longrightarrow> B \<subseteq> C \<Longrightarrow> A \<subset> C"
  by sorry

lemma subset_psubset_trans: "A \<subseteq> B \<Longrightarrow> B \<subset> C \<Longrightarrow> A \<subset> C"
  by sorry

lemma psubset_imp_ex_mem: "A \<subset> B \<Longrightarrow> \<exists>b. b \<in> B - A"
  by sorry

lemma atomize_ball: "(\<And>x. x \<in> A \<Longrightarrow> P x) \<equiv> Trueprop (\<forall>x\<in>A. P x)"
  by sorry

lemmas [symmetric, rulify] = atomize_ball
  and [symmetric, defn] = atomize_ball

lemma image_Pow_mono: "f ` A \<subseteq> B \<Longrightarrow> image f ` Pow A \<subseteq> Pow B"
  by sorry

lemma image_Pow_surj: "f ` A = B \<Longrightarrow> image f ` Pow A = Pow B"
  by sorry


subsubsection \<open>Derived rules involving subsets.\<close>

text \<open>\<open>insert\<close>.\<close>

lemma subset_insertI: "B \<subseteq> insert a B"
  by sorry

lemma subset_insertI2: "A \<subseteq> B \<Longrightarrow> A \<subseteq> insert b B"
  by sorry

lemma subset_insert: "x \<notin> A \<Longrightarrow> A \<subseteq> insert x B \<longleftrightarrow> A \<subseteq> B"
  by sorry


text \<open>\<^medskip> Finite Union -- the least upper bound of two sets.\<close>

lemma Un_upper1: "A \<subseteq> A \<union> B"
  by sorry

lemma Un_upper2: "B \<subseteq> A \<union> B"
  by sorry

lemma Un_least: "A \<subseteq> C \<Longrightarrow> B \<subseteq> C \<Longrightarrow> A \<union> B \<subseteq> C"
  by sorry


text \<open>\<^medskip> Finite Intersection -- the greatest lower bound of two sets.\<close>

lemma Int_lower1: "A \<inter> B \<subseteq> A"
  by sorry

lemma Int_lower2: "A \<inter> B \<subseteq> B"
  by sorry

lemma Int_greatest: "C \<subseteq> A \<Longrightarrow> C \<subseteq> B \<Longrightarrow> C \<subseteq> A \<inter> B"
  by sorry


text \<open>\<^medskip> Set difference.\<close>

lemma Diff_subset[simp]: "A - B \<subseteq> A"
  by sorry

lemma Diff_subset_conv: "A - B \<subseteq> C \<longleftrightarrow> A \<subseteq> B \<union> C"
  by sorry


subsubsection \<open>Equalities involving union, intersection, inclusion, etc.\<close>

text \<open>\<open>{}\<close>.\<close>

lemma Collect_const [simp]: "{s. P} = (if P then UNIV else {})"
  \<comment> \<open>supersedes \<open>Collect_False_empty\<close>\<close>
  by sorry

lemma subset_empty [simp]: "A \<subseteq> {} \<longleftrightarrow> A = {}"
  by sorry

lemma not_psubset_empty [iff]: "\<not> (A < {})"
  by sorry

lemma Collect_subset [simp]: "{x\<in>A. P x} \<subseteq> A" by auto

lemma Collect_empty_eq [simp]: "Collect P = {} \<longleftrightarrow> (\<forall>x. \<not> P x)"
  by sorry

lemma empty_Collect_eq [simp]: "{} = Collect P \<longleftrightarrow> (\<forall>x. \<not> P x)"
  by sorry

lemma Collect_neg_eq: "{x. \<not> P x} = - {x. P x}"
  by sorry

lemma Collect_disj_eq: "{x. P x \<or> Q x} = {x. P x} \<union> {x. Q x}"
  by sorry

lemma Collect_imp_eq: "{x. P x \<longrightarrow> Q x} = - {x. P x} \<union> {x. Q x}"
  by sorry

lemma Collect_conj_eq: "{x. P x \<and> Q x} = {x. P x} \<inter> {x. Q x}"
  by sorry

lemma Collect_conj_eq2: "{x \<in> A. P x \<and> Q x} = {x \<in> A. P x} \<inter> {x \<in> A. Q x}"
  by sorry

lemma Collect_mono_iff: "Collect P \<subseteq> Collect Q \<longleftrightarrow> (\<forall>x. P x \<longrightarrow> Q x)"
  by sorry


text \<open>\<^medskip> \<open>insert\<close>.\<close>

lemma insert_is_Un: "insert a A = {a} \<union> A"
  \<comment> \<open>NOT SUITABLE FOR REWRITING since \<open>{a} \<equiv> insert a {}\<close>\<close>
  by sorry

lemma insert_not_empty [simp]: "insert a A \<noteq> {}"
  and empty_not_insert [simp]: "{} \<noteq> insert a A"
  by sorry

lemma insert_absorb: "a \<in> A \<Longrightarrow> insert a A = A"
  \<comment> \<open>\<open>[simp]\<close> causes recursive calls when there are nested inserts\<close>
  \<comment> \<open>with \<^emph>\<open>quadratic\<close> running time\<close>
  by sorry

lemma insert_absorb2 [simp]: "insert x (insert x A) = insert x A"
  by sorry

lemma insert_commute: "insert x (insert y A) = insert y (insert x A)"
  by sorry

lemma insert_subset [simp]: "insert x A \<subseteq> B \<longleftrightarrow> x \<in> B \<and> A \<subseteq> B"
  by sorry

lemma mk_disjoint_insert: "a \<in> A \<Longrightarrow> \<exists>B. A = insert a B \<and> a \<notin> B"
  \<comment> \<open>use new \<open>B\<close> rather than \<open>A - {a}\<close> to avoid infinite unfolding\<close>
  by sorry

lemma insert_Collect: "insert a (Collect P) = {u. u \<noteq> a \<longrightarrow> P u}"
  by sorry

lemma insert_inter_insert [simp]: "insert a A \<inter> insert a B = insert a (A \<inter> B)"
  by sorry

lemma insert_disjoint [simp]:
  "insert a A \<inter> B = {} \<longleftrightarrow> a \<notin> B \<and> A \<inter> B = {}"
  "{} = insert a A \<inter> B \<longleftrightarrow> a \<notin> B \<and> {} = A \<inter> B"
  by sorry

lemma disjoint_insert [simp]:
  "B \<inter> insert a A = {} \<longleftrightarrow> a \<notin> B \<and> B \<inter> A = {}"
  "{} = A \<inter> insert b B \<longleftrightarrow> b \<notin> A \<and> {} = A \<inter> B"
  by sorry


text \<open>\<^medskip> \<open>Int\<close>\<close>

lemma Int_absorb: "A \<inter> A = A"
  by sorry

lemma Int_left_absorb: "A \<inter> (A \<inter> B) = A \<inter> B"
  by sorry

lemma Int_commute: "A \<inter> B = B \<inter> A"
  by sorry

lemma Int_left_commute: "A \<inter> (B \<inter> C) = B \<inter> (A \<inter> C)"
  by sorry

lemma Int_assoc: "(A \<inter> B) \<inter> C = A \<inter> (B \<inter> C)"
  by sorry

lemmas Int_ac = Int_assoc Int_left_absorb Int_commute Int_left_commute
  \<comment> \<open>Intersection is an AC-operator\<close>

lemma Int_absorb1: "B \<subseteq> A \<Longrightarrow> A \<inter> B = B"
  by sorry

lemma Int_absorb2: "A \<subseteq> B \<Longrightarrow> A \<inter> B = A"
  by sorry

lemma Int_empty_left: "{} \<inter> B = {}"
  by sorry

lemma Int_empty_right: "A \<inter> {} = {}"
  by sorry

lemma disjoint_eq_subset_Compl: "A \<inter> B = {} \<longleftrightarrow> A \<subseteq> - B"
  by sorry

lemma disjoint_iff: "A \<inter> B = {} \<longleftrightarrow> (\<forall>x. x\<in>A \<longrightarrow> x \<notin> B)"
  by sorry

lemma disjoint_iff_not_equal: "A \<inter> B = {} \<longleftrightarrow> (\<forall>x\<in>A. \<forall>y\<in>B. x \<noteq> y)"
  by sorry

lemma Int_UNIV_left: "UNIV \<inter> B = B"
  by sorry

lemma Int_UNIV_right: "A \<inter> UNIV = A"
  by sorry

lemma Int_Un_distrib: "A \<inter> (B \<union> C) = (A \<inter> B) \<union> (A \<inter> C)"
  by sorry

lemma Int_Un_distrib2: "(B \<union> C) \<inter> A = (B \<inter> A) \<union> (C \<inter> A)"
  by sorry

lemma Int_UNIV: "A \<inter> B = UNIV \<longleftrightarrow> A = UNIV \<and> B = UNIV"
  by sorry

lemma Int_subset_iff: "C \<subseteq> A \<inter> B \<longleftrightarrow> C \<subseteq> A \<and> C \<subseteq> B"
  by sorry

lemma Int_Collect: "x \<in> A \<inter> {x. P x} \<longleftrightarrow> x \<in> A \<and> P x"
  by sorry


text \<open>\<^medskip> \<open>Un\<close>.\<close>

lemma Un_absorb: "A \<union> A = A"
  by sorry

lemma Un_left_absorb: "A \<union> (A \<union> B) = A \<union> B"
  by sorry

lemma Un_commute: "A \<union> B = B \<union> A"
  by sorry

lemma Un_left_commute: "A \<union> (B \<union> C) = B \<union> (A \<union> C)"
  by sorry

lemma Un_assoc: "(A \<union> B) \<union> C = A \<union> (B \<union> C)"
  by sorry

lemmas Un_ac = Un_assoc Un_left_absorb Un_commute Un_left_commute
  \<comment> \<open>Union is an AC-operator\<close>

lemma Un_absorb1: "A \<subseteq> B \<Longrightarrow> A \<union> B = B"
  by sorry

lemma Un_absorb2: "B \<subseteq> A \<Longrightarrow> A \<union> B = A"
  by sorry

lemma Un_empty_left: "{} \<union> B = B"
  by sorry

lemma Un_empty_right: "A \<union> {} = A"
  by sorry

lemma Un_UNIV_left: "UNIV \<union> B = UNIV"
  by sorry

lemma Un_UNIV_right: "A \<union> UNIV = UNIV"
  by sorry

lemma Un_insert_left [simp]: "(insert a B) \<union> C = insert a (B \<union> C)"
  by sorry

lemma Un_insert_right [simp]: "A \<union> (insert a B) = insert a (A \<union> B)"
  by sorry

lemma Int_insert_left: "(insert a B) \<inter> C = (if a \<in> C then insert a (B \<inter> C) else B \<inter> C)"
  by sorry

lemma Int_insert_left_if0 [simp]: "a \<notin> C \<Longrightarrow> (insert a B) \<inter> C = B \<inter> C"
  by sorry

lemma Int_insert_left_if1 [simp]: "a \<in> C \<Longrightarrow> (insert a B) \<inter> C = insert a (B \<inter> C)"
  by sorry

lemma Int_insert_right: "A \<inter> (insert a B) = (if a \<in> A then insert a (A \<inter> B) else A \<inter> B)"
  by sorry

lemma Int_insert_right_if0 [simp]: "a \<notin> A \<Longrightarrow> A \<inter> (insert a B) = A \<inter> B"
  by sorry

lemma Int_insert_right_if1 [simp]: "a \<in> A \<Longrightarrow> A \<inter> (insert a B) = insert a (A \<inter> B)"
  by sorry

lemma Un_Int_distrib: "A \<union> (B \<inter> C) = (A \<union> B) \<inter> (A \<union> C)"
  by sorry

lemma Un_Int_distrib2: "(B \<inter> C) \<union> A = (B \<union> A) \<inter> (C \<union> A)"
  by sorry

lemma Un_Int_crazy: "(A \<inter> B) \<union> (B \<inter> C) \<union> (C \<inter> A) = (A \<union> B) \<inter> (B \<union> C) \<inter> (C \<union> A)"
  by sorry

lemma subset_Un_eq: "A \<subseteq> B \<longleftrightarrow> A \<union> B = B"
  by sorry

lemma Un_empty [iff]: "A \<union> B = {} \<longleftrightarrow> A = {} \<and> B = {}"
  by sorry

lemma Un_subset_iff: "A \<union> B \<subseteq> C \<longleftrightarrow> A \<subseteq> C \<and> B \<subseteq> C"
  by sorry

lemma Un_Diff_Int: "(A - B) \<union> (A \<inter> B) = A"
  by sorry

lemma Diff_Int2: "A \<inter> C - B \<inter> C = A \<inter> C - B"
  by sorry

lemma subset_UnE:
  assumes "C \<subseteq> A \<union> B"
  obtains A' B' where "A' \<subseteq> A" "B' \<subseteq> B" "C = A' \<union> B'"
  by sorry

lemma Un_Int_eq [simp]: "(S \<union> T) \<inter> S = S" "(S \<union> T) \<inter> T = T" "S \<inter> (S \<union> T) = S" "T \<inter> (S \<union> T) = T"
  by sorry

lemma Int_Un_eq [simp]: "(S \<inter> T) \<union> S = S" "(S \<inter> T) \<union> T = T" "S \<union> (S \<inter> T) = S" "T \<union> (S \<inter> T) = T"
  by sorry

text \<open>\<^medskip> Set complement\<close>

lemma Compl_disjoint [simp]: "A \<inter> - A = {}"
  by sorry

lemma Compl_disjoint2 [simp]: "- A \<inter> A = {}"
  by sorry

lemma Compl_partition: "A \<union> - A = UNIV"
  by sorry

lemma Compl_partition2: "- A \<union> A = UNIV"
  by sorry

lemma double_complement: "- (-A) = A" for A :: "'a set"
  by sorry

lemma Compl_Un: "- (A \<union> B) = (- A) \<inter> (- B)"
  by sorry

lemma Compl_Int: "- (A \<inter> B) = (- A) \<union> (- B)"
  by sorry

lemma subset_Compl_self_eq: "A \<subseteq> - A \<longleftrightarrow> A = {}"
  by sorry

lemma Un_Int_assoc_eq: "(A \<inter> B) \<union> C = A \<inter> (B \<union> C) \<longleftrightarrow> C \<subseteq> A"
  \<comment> \<open>Halmos, Naive Set Theory, page 16.\<close>
  by sorry

lemma Compl_UNIV_eq: "- UNIV = {}"
  by sorry

lemma Compl_empty_eq: "- {} = UNIV"
  by sorry

lemma Compl_subset_Compl_iff [iff]: "- A \<subseteq> - B \<longleftrightarrow> B \<subseteq> A"
  by sorry

lemma Compl_eq_Compl_iff [iff]: "- A = - B \<longleftrightarrow> A = B"
  for A B :: "'a set"
  by sorry

lemma Compl_insert: "- insert x A = (- A) - {x}"
  by sorry

text \<open>\<^medskip> Bounded quantifiers.

  The following are not added to the default simpset because
  (a) they duplicate the body and (b) there are no similar rules for \<open>Int\<close>.
\<close>

lemma ball_Un: "(\<forall>x \<in> A \<union> B. P x) \<longleftrightarrow> (\<forall>x\<in>A. P x) \<and> (\<forall>x\<in>B. P x)"
  by sorry

lemma bex_Un: "(\<exists>x \<in> A \<union> B. P x) \<longleftrightarrow> (\<exists>x\<in>A. P x) \<or> (\<exists>x\<in>B. P x)"
  by sorry


text \<open>\<^medskip> Set difference.\<close>

lemma Diff_eq: "A - B = A \<inter> (- B)"
  by sorry

lemma Diff_eq_empty_iff: "A - B = {} \<longleftrightarrow> A \<subseteq> B"
  by sorry

lemma Diff_cancel [simp]: "A - A = {}"
  by sorry

lemma Diff_idemp [simp]: "(A - B) - B = A - B"
  for A B :: "'a set"
  by sorry

lemma Diff_triv: "A \<inter> B = {} \<Longrightarrow> A - B = A"
  by sorry

lemma empty_Diff [simp]: "{} - A = {}"
  by sorry

lemma Diff_empty [simp]: "A - {} = A"
  by sorry

lemma Diff_UNIV [simp]: "A - UNIV = {}"
  by sorry

lemma Diff_insert0 [simp]: "x \<notin> A \<Longrightarrow> A - insert x B = A - B"
  by sorry

lemma Diff_insert: "A - insert a B = A - B - {a}"
  \<comment> \<open>NOT SUITABLE FOR REWRITING since \<open>{a} \<equiv> insert a 0\<close>\<close>
  by sorry

lemma Diff_insert2: "A - insert a B = A - {a} - B"
  \<comment> \<open>NOT SUITABLE FOR REWRITING since \<open>{a} \<equiv> insert a 0\<close>\<close>
  by sorry

lemma insert_Diff_if: "insert x A - B = (if x \<in> B then A - B else insert x (A - B))"
  by sorry

lemma insert_Diff1 [simp]: "x \<in> B \<Longrightarrow> insert x A - B = A - B"
  by sorry

lemma insert_Diff_single[simp]: "insert a (A - {a}) = insert a A"
  by sorry

lemma insert_Diff: "a \<in> A \<Longrightarrow> insert a (A - {a}) = A"
  by sorry

lemma Diff_insert_absorb: "x \<notin> A \<Longrightarrow> (insert x A) - {x} = A"
  by sorry

lemma Diff_disjoint [simp]: "A \<inter> (B - A) = {}"
  by sorry

lemma Diff_partition: "A \<subseteq> B \<Longrightarrow> A \<union> (B - A) = B"
  by sorry

lemma double_diff: "A \<subseteq> B \<Longrightarrow> B \<subseteq> C \<Longrightarrow> B - (C - A) = A"
  by sorry

lemma Un_Diff_cancel [simp]: "A \<union> (B - A) = A \<union> B"
  by sorry

lemma Un_Diff_cancel2 [simp]: "(B - A) \<union> A = B \<union> A"
  by sorry

lemma Diff_Un: "A - (B \<union> C) = (A - B) \<inter> (A - C)"
  by sorry

lemma Diff_Int: "A - (B \<inter> C) = (A - B) \<union> (A - C)"
  by sorry

lemma Diff_Diff_Int: "A - (A - B) = A \<inter> B"
  by sorry

lemma Un_Diff: "(A \<union> B) - C = (A - C) \<union> (B - C)"
  by sorry

lemma Int_Diff: "(A \<inter> B) - C = A \<inter> (B - C)"
  by sorry

lemma Diff_Int_distrib: "C \<inter> (A - B) = (C \<inter> A) - (C \<inter> B)"
  by sorry

lemma Diff_Int_distrib2: "(A - B) \<inter> C = (A \<inter> C) - (B \<inter> C)"
  by sorry

lemma Diff_Compl [simp]: "A - (- B) = A \<inter> B"
  by sorry

lemma Compl_Diff_eq [simp]: "- (A - B) = - A \<union> B"
  by sorry

lemma subset_Compl_singleton [simp]: "A \<subseteq> - {b} \<longleftrightarrow> b \<notin> A"
  by sorry

text \<open>\<^medskip> Quantification over type \<^typ>\<open>bool\<close>.\<close>

lemma bool_induct: "P True \<Longrightarrow> P False \<Longrightarrow> P x"
  by sorry

lemma all_bool_eq: "(\<forall>b. P b) \<longleftrightarrow> P True \<and> P False"
  by sorry

lemma bool_contrapos: "P x \<Longrightarrow> \<not> P False \<Longrightarrow> P True"
  by sorry

lemma ex_bool_eq: "(\<exists>b. P b) \<longleftrightarrow> P True \<or> P False"
  by sorry

lemma UNIV_bool: "UNIV = {False, True}"
  by sorry

text \<open>\<^medskip> \<open>Pow\<close>\<close>

lemma Pow_empty [simp]: "Pow {} = {{}}"
  by sorry

lemma Pow_singleton_iff [simp]: "Pow X = {Y} \<longleftrightarrow> X = {} \<and> Y = {}"
  by sorry

lemma Pow_insert: "Pow (insert a A) = Pow A \<union> (insert a ` Pow A)"
  by sorry

lemma Pow_Compl: "Pow (- A) = {- B | B. A \<in> Pow B}"
  by sorry

lemma Pow_UNIV [simp]: "Pow UNIV = UNIV"
  by sorry

lemma Un_Pow_subset: "Pow A \<union> Pow B \<subseteq> Pow (A \<union> B)"
  by sorry

lemma Pow_Int_eq [simp]: "Pow (A \<inter> B) = Pow A \<inter> Pow B"
  by sorry


text \<open>\<^medskip> Miscellany.\<close>

lemma Int_Diff_disjoint: "A \<inter> B \<inter> (A - B) = {}"
  by sorry

lemma Int_Diff_Un: "A \<inter> B \<union> (A - B) = A"
  by sorry

lemma set_eq_subset: "A = B \<longleftrightarrow> A \<subseteq> B \<and> B \<subseteq> A"
  by sorry

lemma subset_iff: "A \<subseteq> B \<longleftrightarrow> (\<forall>t. t \<in> A \<longrightarrow> t \<in> B)"
  by sorry

lemma subset_iff_psubset_eq: "A \<subseteq> B \<longleftrightarrow> A \<subset> B \<or> A = B"
  by sorry

lemma all_not_in_conv [simp]: "(\<forall>x. x \<notin> A) \<longleftrightarrow> A = {}"
  by sorry

lemma ex_in_conv: "(\<exists>x. x \<in> A) \<longleftrightarrow> A \<noteq> {}"
  by sorry

lemma ball_simps [simp, no_atp]:
  "\<And>A P Q. (\<forall>x\<in>A. P x \<or> Q) \<longleftrightarrow> ((\<forall>x\<in>A. P x) \<or> Q)"
  "\<And>A P Q. (\<forall>x\<in>A. P \<or> Q x) \<longleftrightarrow> (P \<or> (\<forall>x\<in>A. Q x))"
  "\<And>A P Q. (\<forall>x\<in>A. P \<longrightarrow> Q x) \<longleftrightarrow> (P \<longrightarrow> (\<forall>x\<in>A. Q x))"
  "\<And>A P Q. (\<forall>x\<in>A. P x \<longrightarrow> Q) \<longleftrightarrow> ((\<exists>x\<in>A. P x) \<longrightarrow> Q)"
  "\<And>P. (\<forall>x\<in>{}. P x) \<longleftrightarrow> True"
  "\<And>P. (\<forall>x\<in>UNIV. P x) \<longleftrightarrow> (\<forall>x. P x)"
  "\<And>a B P. (\<forall>x\<in>insert a B. P x) \<longleftrightarrow> (P a \<and> (\<forall>x\<in>B. P x))"
  "\<And>P Q. (\<forall>x\<in>Collect Q. P x) \<longleftrightarrow> (\<forall>x. Q x \<longrightarrow> P x)"
  "\<And>A P f. (\<forall>x\<in>f`A. P x) \<longleftrightarrow> (\<forall>x\<in>A. P (f x))"
  "\<And>A P. (\<not> (\<forall>x\<in>A. P x)) \<longleftrightarrow> (\<exists>x\<in>A. \<not> P x)"
  by sorry

lemma bex_simps [simp, no_atp]:
  "\<And>A P Q. (\<exists>x\<in>A. P x \<and> Q) \<longleftrightarrow> ((\<exists>x\<in>A. P x) \<and> Q)"
  "\<And>A P Q. (\<exists>x\<in>A. P \<and> Q x) \<longleftrightarrow> (P \<and> (\<exists>x\<in>A. Q x))"
  "\<And>P. (\<exists>x\<in>{}. P x) \<longleftrightarrow> False"
  "\<And>P. (\<exists>x\<in>UNIV. P x) \<longleftrightarrow> (\<exists>x. P x)"
  "\<And>a B P. (\<exists>x\<in>insert a B. P x) \<longleftrightarrow> (P a \<or> (\<exists>x\<in>B. P x))"
  "\<And>P Q. (\<exists>x\<in>Collect Q. P x) \<longleftrightarrow> (\<exists>x. Q x \<and> P x)"
  "\<And>A P f. (\<exists>x\<in>f`A. P x) \<longleftrightarrow> (\<exists>x\<in>A. P (f x))"
  "\<And>A P. (\<not>(\<exists>x\<in>A. P x)) \<longleftrightarrow> (\<forall>x\<in>A. \<not> P x)"
  by sorry

lemma ex_image_cong_iff [simp, no_atp]:
  "(\<exists>x. x\<in>f`A) \<longleftrightarrow> A \<noteq> {}" "(\<exists>x. x\<in>f`A \<and> P x) \<longleftrightarrow> (\<exists>x\<in>A. P (f x))"
  by sorry

subsubsection \<open>Monotonicity of various operations\<close>

lemma image_mono: "A \<subseteq> B \<Longrightarrow> f ` A \<subseteq> f ` B"
  by sorry

lemma Pow_mono: "A \<subseteq> B \<Longrightarrow> Pow A \<subseteq> Pow B"
  by sorry

lemma insert_mono: "C \<subseteq> D \<Longrightarrow> insert a C \<subseteq> insert a D"
  by sorry

lemma Un_mono: "A \<subseteq> C \<Longrightarrow> B \<subseteq> D \<Longrightarrow> A \<union> B \<subseteq> C \<union> D"
  by sorry

lemma Int_mono: "A \<subseteq> C \<Longrightarrow> B \<subseteq> D \<Longrightarrow> A \<inter> B \<subseteq> C \<inter> D"
  by sorry

lemma Diff_mono: "A \<subseteq> C \<Longrightarrow> D \<subseteq> B \<Longrightarrow> A - B \<subseteq> C - D"
  by sorry

lemma Compl_anti_mono: "A \<subseteq> B \<Longrightarrow> - B \<subseteq> - A"
  by sorry

text \<open>\<^medskip> Monotonicity of implications.\<close>

lemma in_mono: "A \<subseteq> B \<Longrightarrow> x \<in> A \<longrightarrow> x \<in> B"
  by sorry

lemma conj_mono: "P1 \<longrightarrow> Q1 \<Longrightarrow> P2 \<longrightarrow> Q2 \<Longrightarrow> (P1 \<and> P2) \<longrightarrow> (Q1 \<and> Q2)"
  by sorry

lemma disj_mono: "P1 \<longrightarrow> Q1 \<Longrightarrow> P2 \<longrightarrow> Q2 \<Longrightarrow> (P1 \<or> P2) \<longrightarrow> (Q1 \<or> Q2)"
  by sorry

lemma imp_mono: "Q1 \<longrightarrow> P1 \<Longrightarrow> P2 \<longrightarrow> Q2 \<Longrightarrow> (P1 \<longrightarrow> P2) \<longrightarrow> (Q1 \<longrightarrow> Q2)"
  by sorry

lemma imp_refl: "P \<longrightarrow> P" ..

lemma not_mono: "Q \<longrightarrow> P \<Longrightarrow> \<not> P \<longrightarrow> \<not> Q"
  by sorry

lemma ex_mono: "(\<And>x. P x \<longrightarrow> Q x) \<Longrightarrow> (\<exists>x. P x) \<longrightarrow> (\<exists>x. Q x)"
  by sorry

lemma all_mono: "(\<And>x. P x \<longrightarrow> Q x) \<Longrightarrow> (\<forall>x. P x) \<longrightarrow> (\<forall>x. Q x)"
  by sorry

lemma Collect_mono: "(\<And>x. P x \<longrightarrow> Q x) \<Longrightarrow> Collect P \<subseteq> Collect Q"
  by sorry

lemma Int_Collect_mono: "A \<subseteq> B \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> P x \<longrightarrow> Q x) \<Longrightarrow> A \<inter> Collect P \<subseteq> B \<inter> Collect Q"
  by sorry

lemmas basic_monos =
  subset_refl imp_refl disj_mono conj_mono ex_mono Collect_mono in_mono

lemma eq_to_mono: "a = b \<Longrightarrow> c = d \<Longrightarrow> b \<longrightarrow> d \<Longrightarrow> a \<longrightarrow> c"
  by sorry


subsubsection \<open>Inverse image of a function\<close>

definition vimage :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b set \<Rightarrow> 'a set"  (infixr \<open>-`\<close> 90)
  where "f -` B \<equiv> {x. f x \<in> B}"

lemma vimage_eq [simp]: "a \<in> f -` B \<longleftrightarrow> f a \<in> B"
  by sorry

lemma vimage_singleton_eq: "a \<in> f -` {b} \<longleftrightarrow> f a = b"
  by sorry

lemma vimageI [intro]: "f a = b \<Longrightarrow> b \<in> B \<Longrightarrow> a \<in> f -` B"
  by sorry

lemma vimageI2: "f a \<in> A \<Longrightarrow> a \<in> f -` A"
  by sorry

lemma vimageE [elim!]: "a \<in> f -` B \<Longrightarrow> (\<And>x. f a = x \<Longrightarrow> x \<in> B \<Longrightarrow> P) \<Longrightarrow> P"
  by sorry

lemma vimageD: "a \<in> f -` A \<Longrightarrow> f a \<in> A"
  by sorry

lemma vimage_empty [simp]: "f -` {} = {}"
  by sorry

lemma vimage_Compl: "f -` (- A) = - (f -` A)"
  by sorry

lemma vimage_Un [simp]: "f -` (A \<union> B) = (f -` A) \<union> (f -` B)"
  by sorry

lemma vimage_Int [simp]: "f -` (A \<inter> B) = (f -` A) \<inter> (f -` B)"
  by sorry

lemma vimage_Collect_eq [simp]: "f -` Collect P = {y. P (f y)}"
  by sorry

lemma vimage_Collect: "(\<And>x. P (f x) = Q x) \<Longrightarrow> f -` (Collect P) = Collect Q"
  by sorry

lemma vimage_insert: "f -` (insert a B) = (f -` {a}) \<union> (f -` B)"
  \<comment> \<open>NOT suitable for rewriting because of the recurrence of \<open>{a}\<close>.\<close>
  by sorry

lemma vimage_Diff: "f -` (A - B) = (f -` A) - (f -` B)"
  by sorry

lemma vimage_UNIV [simp]: "f -` UNIV = UNIV"
  by sorry

lemma vimage_mono: "A \<subseteq> B \<Longrightarrow> f -` A \<subseteq> f -` B"
  \<comment> \<open>monotonicity\<close>
  by sorry

lemma vimage_image_eq: "f -` (f ` A) = {y. \<exists>x\<in>A. f x = f y}"
  by sorry

lemma image_vimage_subset: "f ` (f -` A) \<subseteq> A"
  by sorry

lemma image_vimage_eq [simp]: "f ` (f -` A) = A \<inter> range f"
  by sorry

lemma image_subset_iff_subset_vimage: "f ` A \<subseteq> B \<longleftrightarrow> A \<subseteq> f -` B"
  by sorry

lemma subset_vimage_iff: "A \<subseteq> f -` B \<longleftrightarrow> (\<forall>x\<in>A. f x \<in> B)"
  by sorry

lemma vimage_const [simp]: "((\<lambda>x. c) -` A) = (if c \<in> A then UNIV else {})"
  by sorry

lemma vimage_if [simp]: "((\<lambda>x. if x \<in> B then c else d) -` A) =
   (if c \<in> A then (if d \<in> A then UNIV else B)
    else if d \<in> A then - B else {})"
  by sorry

lemma vimage_inter_cong: "(\<And> w. w \<in> S \<Longrightarrow> f w = g w) \<Longrightarrow> f -` y \<inter> S = g -` y \<inter> S"
  by sorry

lemma vimage_ident [simp]: "(\<lambda>x. x) -` Y = Y"
  by sorry


subsubsection \<open>Singleton sets\<close>

definition is_singleton :: "'a set \<Rightarrow> bool"
  where "is_singleton A \<longleftrightarrow> (\<exists>x. A = {x})"

lemma is_singletonI [simp, intro!]: "is_singleton {x}"
  by sorry

lemma is_singletonI': "A \<noteq> {} \<Longrightarrow> (\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x = y) \<Longrightarrow> is_singleton A"
  by sorry

lemma is_singletonE: "is_singleton A \<Longrightarrow> (\<And>x. A = {x} \<Longrightarrow> P) \<Longrightarrow> P"
  by sorry

lemma is_singleton_iff_ex1:
  \<open>is_singleton A \<longleftrightarrow> (\<exists>!x. x \<in> A)\<close>
  by sorry


subsubsection \<open>Getting the contents of a singleton set\<close>

definition the_elem :: "'a set \<Rightarrow> 'a"
  where "the_elem X = (THE x. X = {x})"

lemma the_elem_eq [simp]: "the_elem {x} = x"
  by sorry

lemma is_singleton_the_elem: "is_singleton A \<longleftrightarrow> A = {the_elem A}"
  by sorry

lemma the_elem_image_unique:
  assumes "A \<noteq> {}"
    and *: "\<And>y. y \<in> A \<Longrightarrow> f y = a"
  shows "the_elem (f ` A) = a"
  by sorry


subsubsection \<open>Monad operation\<close>

definition bind :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> 'b set"
  where "bind A f = {x. \<exists>B \<in> f`A. x \<in> B}"

hide_const (open) bind

lemma bind_bind: "Set.bind (Set.bind A B) C = Set.bind A (\<lambda>x. Set.bind (B x) C)"
  for A :: "'a set"
  by sorry

lemma empty_bind [simp]: "Set.bind {} f = {}"
  by sorry

lemma nonempty_bind_const: "A \<noteq> {} \<Longrightarrow> Set.bind A (\<lambda>_. B) = B"
  by sorry

lemma bind_const: "Set.bind A (\<lambda>_. B) = (if A = {} then {} else B)"
  by sorry

lemma bind_singleton_conv_image: "Set.bind A (\<lambda>x. {f x}) = f ` A"
  by sorry


subsubsection \<open>Operations for execution\<close>

text \<open>
  Use those operations only for generating executable / efficient code.
  Otherwise use the RHSs directly.
\<close>

context
begin

qualified definition is_empty :: "'a set \<Rightarrow> bool" \<comment> \<open>only for code generation\<close>
  where is_empty_iff [code_abbrev, simp]: "is_empty A \<longleftrightarrow> A = {}"

qualified definition remove :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a set" \<comment> \<open>only for code generation\<close>
  where remove_eq [code_abbrev, simp]: "remove x A = A - {x}"

qualified definition filter :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a set" \<comment> \<open>only for code generation\<close>
  where filter_eq [code_abbrev, simp]: "filter P A = {a \<in> A. P a}"

qualified definition can_select :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" \<comment> \<open>only for code generation\<close>
  where can_select_iff [code_abbrev, simp]: "can_select P A = (\<exists>!x\<in>A. P x)"

qualified lemma can_select_iff_is_singleton:
  \<open>Set.can_select P A \<longleftrightarrow> is_singleton (Set.filter P A)\<close>
  by (simp add: is_singleton_iff_ex1)

end

instantiation set :: (equal) equal
begin

definition "HOL.equal A B \<longleftrightarrow> A \<subseteq> B \<and> B \<subseteq> A"

instance
  by standard (auto simp add: equal_set_def)

end


text \<open>Misc\<close>

definition pairwise :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool"
  where "pairwise R S \<longleftrightarrow> (\<forall>x \<in> S. \<forall>y \<in> S. x \<noteq> y \<longrightarrow> R x y)"

lemma pairwise_alt: "pairwise R S \<longleftrightarrow> (\<forall>x\<in>S. \<forall>y\<in>S-{x}. R x y)"
  by sorry

lemma pairwise_trivial [simp]: "pairwise (\<lambda>i j. j \<noteq> i) I"
  by sorry

lemma pairwiseI [intro?]:
  "pairwise R S" if "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> x \<noteq> y \<Longrightarrow> R x y"
  by sorry

lemma pairwiseD:
  "R x y" and "R y x"
  if "pairwise R S" "x \<in> S" and "y \<in> S" and "x \<noteq> y"
  by sorry

lemma pairwise_empty [simp]: "pairwise P {}"
  by sorry

lemma pairwise_singleton [simp]: "pairwise P {A}"
  by sorry

lemma pairwise_insert:
  "pairwise r (insert x s) \<longleftrightarrow> (\<forall>y. y \<in> s \<and> y \<noteq> x \<longrightarrow> r x y \<and> r y x) \<and> pairwise r s"
  by sorry

lemma pairwise_subset: "pairwise P S \<Longrightarrow> T \<subseteq> S \<Longrightarrow> pairwise P T"
  by sorry

lemma pairwise_mono: "\<lbrakk>pairwise P A; \<And>x y. P x y \<Longrightarrow> Q x y; B \<subseteq> A\<rbrakk> \<Longrightarrow> pairwise Q B"
  by sorry

lemma pairwise_imageI:
  "pairwise P (f ` A)"
  if "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<noteq> y \<Longrightarrow> f x \<noteq> f y \<Longrightarrow> P (f x) (f y)"
  by sorry

lemma pairwise_image: "pairwise r (f ` s) \<longleftrightarrow> pairwise (\<lambda>x y. (f x \<noteq> f y) \<longrightarrow> r (f x) (f y)) s"
  by sorry

definition disjnt :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool"
  where "disjnt A B \<longleftrightarrow> A \<inter> B = {}"

lemma disjnt_self_iff_empty [simp]: "disjnt S S \<longleftrightarrow> S = {}"
  by sorry

lemma disjnt_commute: "disjnt A B = disjnt B A"
  by sorry

lemma disjnt_iff: "disjnt A B \<longleftrightarrow> (\<forall>x. \<not> (x \<in> A \<and> x \<in> B))"
  by sorry

lemma disjnt_sym: "disjnt A B \<Longrightarrow> disjnt B A"
  by sorry

lemma disjnt_empty1 [simp]: "disjnt {} A" and disjnt_empty2 [simp]: "disjnt A {}"
  by sorry

lemma disjnt_insert1 [simp]: "disjnt (insert a X) Y \<longleftrightarrow> a \<notin> Y \<and> disjnt X Y"
  by sorry

lemma disjnt_insert2 [simp]: "disjnt Y (insert a X) \<longleftrightarrow> a \<notin> Y \<and> disjnt Y X"
  by sorry

lemma disjnt_subset1 : "\<lbrakk>disjnt X Y; Z \<subseteq> X\<rbrakk> \<Longrightarrow> disjnt Z Y"
  by sorry

lemma disjnt_subset2 : "\<lbrakk>disjnt X Y; Z \<subseteq> Y\<rbrakk> \<Longrightarrow> disjnt X Z"
  by sorry

lemma disjnt_Un1 [simp]: "disjnt (A \<union> B) C \<longleftrightarrow> disjnt A C \<and> disjnt B C"
  by sorry

lemma disjnt_Un2 [simp]: "disjnt C (A \<union> B) \<longleftrightarrow> disjnt C A \<and> disjnt C B"
  by sorry

lemma disjnt_Diff1: "disjnt (X-Y) (U-V)" and disjnt_Diff2: "disjnt (U-V) (X-Y)" if "X \<subseteq> V"
  by sorry

lemma disjoint_image_subset: "\<lbrakk>pairwise disjnt \<A>; \<And>X. X \<in> \<A> \<Longrightarrow> f X \<subseteq> X\<rbrakk> \<Longrightarrow> pairwise disjnt (f `\<A>)"
  by sorry

lemma pairwise_disjnt_iff: "pairwise disjnt \<A> \<longleftrightarrow> (\<forall>x. \<exists>\<^sub>\<le>\<^sub>1 X. X \<in> \<A> \<and> x \<in> X)"
  by sorry

lemma disjnt_insert: \<^marker>\<open>contributor \<open>Lars Hupel\<close>\<close>
  \<open>disjnt (insert x M) N\<close> if \<open>x \<notin> N\<close> \<open>disjnt M N\<close>
  by sorry

lemma Int_emptyI: "(\<And>x. x \<in> A \<Longrightarrow> x \<in> B \<Longrightarrow> False) \<Longrightarrow> A \<inter> B = {}"
  by sorry

lemma in_image_insert_iff:
  assumes "\<And>C. C \<in> B \<Longrightarrow> x \<notin> C"
  shows "A \<in> insert x ` B \<longleftrightarrow> x \<in> A \<and> A - {x} \<in> B" (is "?P \<longleftrightarrow> ?Q")
  by sorry

hide_const (open) member not_member

lemmas equalityI = subset_antisym
lemmas set_mp = subsetD
lemmas set_rev_mp = rev_subsetD

end
