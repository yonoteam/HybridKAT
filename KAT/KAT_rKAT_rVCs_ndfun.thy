(*  Title:       Verification and refinement of hybrid systems in the state transformer  KAT
    Author:      Jonathan Julián Huerta y Munive, 2019
    Maintainer:  Jonathan Julián Huerta y Munive <jjhuertaymunive1@sheffield.ac.uk>
*)

section \<open> Verification and refinement of HS in the state transformer KAT \<close>

text \<open> We use our state transformers model to obtain verification and refinement components for 
hybrid programs. We devise three methods for reasoning with evolution commands and their continuous 
dynamics: providing flows, solutions or invariants. \<close>

theory KAT_rKAT_rVCs_ndfun
  imports 
    KAT_rKAT_Models
    "Hybrid_Systems_VCs.HS_ODEs"
begin recall_syntax


subsection \<open> ODEs Invariant Extensions \<close>

type_synonym 'a pred = "'a \<Rightarrow> bool"

\<comment> \<open>We start by deleting some conflicting notation.\<close>

no_notation Archimedean_Field.ceiling ("\<lceil>_\<rceil>")
        and Archimedean_Field.floor_ceiling_class.floor ("\<lfloor>_\<rfloor>")
        and tau ("\<tau>")
        and Relation.relcomp (infixl ";" 75)
        and proto_near_quantale_class.bres (infixr "\<rightarrow>" 60)
        and tt ("\<lparr>_\<rparr>_\<lparr>_\<rparr>")

lemma diff_invariant_nleq_rule:
  fixes \<mu>1::"'a::banach \<Rightarrow> real"
  shows "diff_invariant (\<lambda>s. \<not> \<mu>1 s \<le> \<mu>2 s) f T S t\<^sub>0 G \<longleftrightarrow> diff_invariant (\<lambda>s. \<mu>1 s > \<mu>2 s) f T S t\<^sub>0 G"
  unfolding diff_invariant_eq
  by safe (clarsimp, erule_tac x=s in allE, simp, erule_tac x=X in ballE, force, force)+

lemma diff_invariant_neq_rule1 [diff_invariant_rules]:
  fixes \<mu>1::"'a::banach \<Rightarrow> real"
  assumes "diff_invariant (\<lambda>s. \<mu>1 s < \<mu>2 s) f T S t\<^sub>0 G"
    and "diff_invariant (\<lambda>s. \<mu>1 s > \<mu>2 s) f T S t\<^sub>0 G"
  shows "diff_invariant (\<lambda>s. \<mu>1 s \<noteq> \<mu>2 s) f T S t\<^sub>0 G"
proof(unfold diff_invariant_eq, clarsimp)
  fix s::'a and X::"real \<Rightarrow> 'a" and t::real
  assume "\<mu>1 s \<noteq> \<mu>2 s" and Xhyp: "X \<in> Sols (\<lambda>t. f) T S t\<^sub>0 s" 
     and thyp: "t \<in> T" and Ghyp: "\<forall>\<tau>. \<tau> \<in> T \<and> \<tau> \<le> t \<longrightarrow> G (X \<tau>)"
  hence "\<mu>1 s < \<mu>2 s \<or> \<mu>1 s > \<mu>2 s"
    by linarith
  moreover have "\<mu>1 s < \<mu>2 s \<Longrightarrow> \<mu>1 (X t) < \<mu>2 (X t)"
    using assms(1) Xhyp thyp Ghyp unfolding diff_invariant_eq by auto
  moreover have "\<mu>1 s > \<mu>2 s \<Longrightarrow> \<mu>1 (X t) > \<mu>2 (X t)"
    using assms(2) Xhyp thyp Ghyp unfolding diff_invariant_eq by auto
  ultimately show "\<mu>1 (X t) = \<mu>2 (X t) \<Longrightarrow> False"
    by auto
qed

lemma IVT_two_functions:
  fixes f :: "('a::{linear_continuum_topology, real_vector}) \<Rightarrow> 
  ('b::{linorder_topology,real_normed_vector,ordered_ab_group_add})"
  assumes conts: "continuous_on {a..b} f" "continuous_on {a..b} g"
      and ahyp: "f a < g a" and bhyp: "g b < f b " and "a \<le> b"
    shows "\<exists>x\<in>{a..b}. f x = g x"
proof-
  let "?h x" = "f x - g x"
  have "?h a \<le> 0" and "?h b \<ge> 0"
    using ahyp bhyp by simp_all
  also have "continuous_on {a..b} ?h"
    using conts continuous_on_diff by blast 
  ultimately obtain x where "a \<le> x" "x \<le> b" and "?h x = 0"
    using IVT'[of "?h"] \<open>a \<le> b\<close> by blast
  thus ?thesis
    using \<open>a \<le> b\<close> by auto
qed

lemma IVT_two_functions_real_ivl:
  fixes f :: "real \<Rightarrow> real"
  assumes conts: "continuous_on {a--b} f" "continuous_on {a--b} g"
      and ahyp: "f a < g a" and bhyp: "g b < f b "
    shows "\<exists>x\<in>{a--b}. f x = g x"
proof(cases "a \<le> b")
  case True
  then show ?thesis 
    using IVT_two_functions assms 
    unfolding closed_segment_eq_real_ivl by auto
next
  case False
  hence "a \<ge> b"
    by auto
  hence "continuous_on {b..a} f" "continuous_on {b..a} g"
    using conts False unfolding closed_segment_eq_real_ivl by auto
  hence "\<exists>x\<in>{b..a}. g x = f x"
    using IVT_two_functions[of b a g f] assms(3,4) False by auto
  then show ?thesis  
    using \<open>a \<ge> b\<close> unfolding closed_segment_eq_real_ivl by auto force
qed

lemma diff_invariant_neq_rule2 [diff_invariant_rules]:
  fixes \<mu>1::"'a::banach \<Rightarrow> real"
  assumes Thyp: "is_interval T" "t\<^sub>0 \<in> T" "\<forall>t\<in>T. t\<^sub>0 \<le> t"
      and conts: "\<forall>X. (D X = (\<lambda>\<tau>. f (X \<tau>)) on T) \<longrightarrow> continuous_on (\<P> X T) \<mu>1 \<and> continuous_on (\<P> X T) \<mu>2"
      and dIhyp:"diff_invariant (\<lambda>s. \<mu>1 s \<noteq> \<mu>2 s) f T S t\<^sub>0 G"
    shows "diff_invariant (\<lambda>s. \<mu>1 s < \<mu>2 s) f T S t\<^sub>0 G"
proof(unfold diff_invariant_eq, clarsimp)
  fix s::'a and X::"real \<Rightarrow> 'a" and t::real
  assume ineq0: "\<mu>1 s < \<mu>2 s" and Xhyp: "X \<in> Sols (\<lambda>t. f) T S t\<^sub>0 s"
    and Ghyp: "\<forall>\<tau>. \<tau> \<in> T \<and> \<tau> \<le> t \<longrightarrow> G (X \<tau>)" and thyp: "t\<in>T"
  hence ineq1: "\<mu>1 (X t\<^sub>0) < \<mu>2 (X t\<^sub>0)"
    by (auto simp: ivp_solsD)
  have "t\<^sub>0 \<le> t" and "\<mu>2 (X t) \<noteq> \<mu>1 (X t)"
    using \<open>t \<in> T\<close> Thyp dIhyp thyp Xhyp Ghyp ineq0 unfolding diff_invariant_eq by force+
  moreover
  {assume ineq2:"\<mu>1 (X t) > \<mu>2 (X t)"
    note continuous_on_compose[OF vderiv_on_continuous_on[OF ivp_solsD(1)[OF Xhyp]]]
    hence "continuous_on T (\<mu>1 \<circ> X)" and "continuous_on T (\<mu>2 \<circ> X)"
      using ivp_solsD(1)[OF Xhyp] conts by auto
    also have "{t\<^sub>0--t} \<subseteq> T"
      using Thyp thyp by (simp add: closed_segment_subset_interval)
    ultimately have "continuous_on {t\<^sub>0--t} (\<lambda>\<tau>. \<mu>1 (X \<tau>))" and "continuous_on {t\<^sub>0--t} (\<lambda>\<tau>. \<mu>2 (X \<tau>))"
      using continuous_on_subset by auto
    then obtain \<tau> where "\<tau> \<in> {t\<^sub>0--t}" "\<mu>2 (X \<tau>) = \<mu>1 (X \<tau>)"
      using IVT_two_functions_real_ivl[OF _ _ ineq1 ineq2] by force
    hence "\<forall>r\<in>down T \<tau>. G (X r)" and "\<tau> \<in> T"
      using Ghyp \<open>\<tau> \<in> {t\<^sub>0--t}\<close> \<open>t\<^sub>0 \<le> t\<close> \<open>{t\<^sub>0--t} \<subseteq> T\<close> by (auto simp: closed_segment_eq_real_ivl)
    hence "\<mu>2 (X \<tau>) \<noteq> \<mu>1 (X \<tau>)"
      using dIhyp Xhyp \<open>\<mu>1 s < \<mu>2 s\<close> unfolding diff_invariant_eq by force
    hence "False"
      using \<open>\<mu>2 (X \<tau>) = \<mu>1 (X \<tau>)\<close> by blast}
  ultimately show "\<mu>1 (X t) < \<mu>2 (X t)"
    by fastforce
qed

lemma diff_invariant_neq_rule3 [diff_invariant_rules]:
  fixes \<mu>1::"'a::banach \<Rightarrow> real"
  assumes Thyp: "is_interval T" "t\<^sub>0 \<in> T" "\<forall>t\<in>T. t\<^sub>0 \<le> t"
      and conts: "\<forall>X. (D X = (\<lambda>\<tau>. f (X \<tau>)) on T) \<longrightarrow> continuous_on (\<P> X T) \<mu>1 \<and> continuous_on (\<P> X T) \<mu>2"
      and dIhyp:"diff_invariant (\<lambda>s. \<mu>1 s \<noteq> \<mu>2 s) f T S t\<^sub>0 G"
    shows "diff_invariant (\<lambda>s. \<mu>1 s > \<mu>2 s) f T S t\<^sub>0 G"
proof-
  have "(\<lambda>s. \<mu>1 s \<noteq> \<mu>2 s) = (\<lambda>s. \<mu>2 s \<noteq> \<mu>1 s)"
    by auto
  hence obs: "\<forall>X. (D X = (\<lambda>\<tau>. f (X \<tau>)) on T) \<longrightarrow> continuous_on (\<P> X T) \<mu>2 \<and> continuous_on (\<P> X T) \<mu>1"
    "diff_invariant (\<lambda>s. \<mu>2 s \<noteq> \<mu>1 s) f T S t\<^sub>0 G"
    using dIhyp conts by auto
  show ?thesis
    using diff_invariant_neq_rule2[OF Thyp obs] .
qed


subsection \<open> Store and Hoare triples \<close>

\<comment> \<open>Canonical lifting from predicates to state transformers and its simplification rules\<close>

definition p2ndf :: "'a upred \<Rightarrow> 'a nd_fun" ("(1\<lceil>_\<rceil>)")
  where "\<lceil>Q\<rceil> \<equiv> (\<lambda> x::'a. {s::'a. s = x \<and> \<lbrakk>Q\<rbrakk>\<^sub>e s})\<^sup>\<bullet>"

lemma p2ndf_simps[simp]: 
  "\<lceil>P\<rceil> \<le> \<lceil>Q\<rceil> = `P \<Rightarrow> Q`"
  "(\<lceil>P\<rceil> = \<lceil>Q\<rceil>) = `P \<Leftrightarrow> Q`"
  "(\<lceil>P\<rceil> \<cdot> \<lceil>Q\<rceil>) = \<lceil>P \<and> Q\<rceil>"
  "(\<lceil>P\<rceil> + \<lceil>Q\<rceil>) = \<lceil>P \<or> Q\<rceil>"
  "t \<lceil>P\<rceil> = \<lceil>P\<rceil>"
  "n \<lceil>P\<rceil> = \<lceil>\<not> P\<rceil>"
  unfolding p2ndf_def one_nd_fun_def less_eq_nd_fun_def times_nd_fun_def plus_nd_fun_def 
  by (auto simp add: nd_fun_eq_iff kcomp_def le_fun_def n_op_nd_fun_def conj_upred_def 
      inf_uexpr.rep_eq disj_upred_def sup_uexpr.rep_eq not_upred_def uminus_uexpr_def 
      impl.rep_eq uexpr_appl.rep_eq lit.rep_eq taut.rep_eq iff_upred.rep_eq)

\<comment> \<open> Meaning of the state-transformer Hoare triple \<close>

lemma ndfun_kat_H: "H \<lceil>P\<rceil> X \<lceil>Q\<rceil> \<longleftrightarrow> (\<forall>s s'. \<lbrakk>P\<rbrakk>\<^sub>e s \<longrightarrow> s' \<in> (X\<^sub>\<bullet>) s \<longrightarrow> \<lbrakk>Q\<rbrakk>\<^sub>e s')"
  unfolding Hoare_def p2ndf_def less_eq_nd_fun_def times_nd_fun_def kcomp_def 
  by (auto simp add: le_fun_def n_op_nd_fun_def)

abbreviation HTriple ("\<^bold>{_\<^bold>} _ \<^bold>{_\<^bold>}") where "\<^bold>{P\<^bold>}X\<^bold>{Q\<^bold>} \<equiv> H \<lceil>P\<rceil> X \<lceil>Q\<rceil>"

utp_lift_notation HTriple (1)

\<comment> \<open> Hoare triple for skip and a simp-rule \<close>

abbreviation "skip \<equiv> (1::'a nd_fun)"

lemma H_skip: "\<^bold>{P\<^bold>}skip\<^bold>{P\<^bold>}"
  using H_skip by blast

lemma sH_skip[simp]: "\<^bold>{P\<^bold>}skip\<^bold>{Q\<^bold>} \<longleftrightarrow> `P \<Rightarrow> Q`"
  unfolding ndfun_kat_H by (simp add: one_nd_fun_def impl.rep_eq taut.rep_eq)

\<comment> \<open> Hoare logic consequence rule \<close>

lemma H_conseq: 
  assumes "\<^bold>{p\<^sub>2\<^bold>}S\<^bold>{q\<^sub>2\<^bold>}" "`p\<^sub>1 \<Rightarrow> p\<^sub>2`" "`q\<^sub>2 \<Rightarrow> q\<^sub>1`" 
  shows "\<^bold>{p\<^sub>1\<^bold>}S\<^bold>{q\<^sub>1\<^bold>}"
  using assms
  unfolding ndfun_kat_H by (rel_auto)

\<comment> \<open> We introduce assignments and compute derive their rule of Hoare logic. \<close>

definition assigns :: "'s usubst \<Rightarrow> 's nd_fun" ("\<^bold>\<langle>_\<^bold>\<rangle>") where
[upred_defs]: "assigns \<sigma> = (\<lambda> s. {\<lbrakk>\<sigma>\<rbrakk>\<^sub>e s})\<^sup>\<bullet>"

(*
definition assign :: "'b \<Rightarrow> ('a^'b \<Rightarrow> 'a) \<Rightarrow> ('a^'b) nd_fun" ("(2_ ::= _)" [70, 65] 61) 
  where "(x ::= e) = (\<lambda>s. {vec_upd s x (e s)})\<^sup>\<bullet>"
*)

abbreviation assign ("(2_ ::= _)" [70, 65] 61) 
  where "assign x e \<equiv> assigns [&x \<mapsto>\<^sub>s e]"

utp_lift_notation assign (0)

lemma H_assigns: "P = (\<sigma> \<dagger> Q) \<Longrightarrow> \<^bold>{P\<^bold>} \<^bold>\<langle>\<sigma>\<^bold>\<rangle> \<^bold>{Q\<^bold>}"
  unfolding ndfun_kat_H by (simp add: assigns_def, pred_auto)

lemma H_assign: "P = Q\<lbrakk>e/&x\<rbrakk> \<Longrightarrow> \<^bold>{P\<^bold>} x ::= e \<^bold>{Q\<^bold>}"
  unfolding ndfun_kat_H by (simp add: assigns_def, pred_auto)

(* lemma H_assign: "(\<lambda>s. Q (\<chi> j. ((($) s)(x := (e s))) j)) \<Longrightarrow> Hoare \<lceil>P\<rceil> (x ::= e) \<lceil>Q\<rceil>" *)

lemma sH_assign[simp]: "\<^bold>{P\<^bold>} x ::= e \<^bold>{Q\<^bold>} = (\<forall>s. \<lbrakk>P\<rbrakk>\<^sub>e s \<longrightarrow> \<lbrakk>Q\<lbrakk>e/&x\<rbrakk>\<rbrakk>\<^sub>e s)"
  unfolding ndfun_kat_H by (pred_auto)

lemma sH_assigns[simp]: "\<^bold>{P\<^bold>} \<^bold>\<langle>\<sigma>\<^bold>\<rangle> \<^bold>{Q\<^bold>} = (\<forall>s. \<lbrakk>P\<rbrakk>\<^sub>e s \<longrightarrow> \<lbrakk>\<sigma> \<dagger> Q\<rbrakk>\<^sub>e s)"
  unfolding ndfun_kat_H by (pred_auto)

lemma sH_assign_alt: "\<^bold>{P\<^bold>}x ::= e\<^bold>{Q\<^bold>} \<longleftrightarrow> `P \<Rightarrow> Q\<lbrakk>e/x\<rbrakk>`"
  unfolding ndfun_kat_H by (pred_auto)

lemma H_assign_floyd_hoare:
  assumes "vwb_lens x"
  shows "\<^bold>{p\<^bold>} x ::= e \<^bold>{\<exists> v . p\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk> \<and> &x = e\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>\<^bold>}"
  using assms by (simp, rel_auto', metis vwb_lens_wb wb_lens.get_put)

(*
lemma sH_assign[simp]: "Hoare \<lceil>P\<rceil> (x ::= e) \<lceil>Q\<rceil> \<longleftrightarrow> (\<forall>s. P s \<longrightarrow> Q (\<chi> j. ((($) s)(x := (e s))) j))"
*)

\<comment> \<open> Next, the Hoare rule of the composition \<close>

abbreviation seq_comp :: "'a nd_fun \<Rightarrow> 'a nd_fun \<Rightarrow> 'a nd_fun" (infixr ";" 75)
  where "f ; g \<equiv> f \<cdot> g"

lemma H_seq: "\<^bold>{P\<^bold>} X \<^bold>{R\<^bold>} \<Longrightarrow> \<^bold>{R\<^bold>} Y \<^bold>{Q\<^bold>} \<Longrightarrow> \<^bold>{P\<^bold>} X ; Y \<^bold>{Q\<^bold>}"
  by (auto intro: H_seq)

lemma sH_seq: "\<^bold>{P\<^bold>} X ; Y \<^bold>{Q\<^bold>} =  \<^bold>{P\<^bold>} X \<^bold>{\<forall>s'. s' \<in> Y\<^sub>\<circ> \<Rightarrow> Q\<lbrakk>s'/&\<^bold>v\<rbrakk>\<^bold>}"
  unfolding ndfun_kat_H by (auto simp: times_nd_fun_def kcomp_def, pred_auto+)

lemma H_seq_inv_1: "\<^bold>{P\<^bold>} X \<^bold>{P\<^bold>} \<Longrightarrow> \<^bold>{P\<^bold>} Y \<^bold>{Q\<^bold>} \<Longrightarrow> \<^bold>{P\<^bold>} X ; Y \<^bold>{Q\<^bold>}"
  by (simp add: H_seq)

lemma H_seq_inv_2: "\<^bold>{P\<^bold>} X \<^bold>{Q\<^bold>} \<Longrightarrow> \<^bold>{Q\<^bold>} Y \<^bold>{Q\<^bold>} \<Longrightarrow> \<^bold>{P\<^bold>} X ; Y \<^bold>{Q\<^bold>}"
  by (simp add: H_seq)

text \<open> Assignment laws \<close>

\<comment> \<open> Assignment forward law \<close>

lemma H_assign_init:
  assumes "vwb_lens x" "\<And> x\<^sub>0. \<^bold>{&x = e\<lbrakk>\<guillemotleft>x\<^sub>0\<guillemotright>/&x\<rbrakk> \<and> p\<lbrakk>\<guillemotleft>x\<^sub>0\<guillemotright>/&x\<rbrakk>\<^bold>}S\<^bold>{q\<^bold>}"
  shows "\<^bold>{p\<^bold>}(x ::= e) ; S\<^bold>{q\<^bold>}"
proof -
  from assms(2) have "\<^bold>{\<exists> v. p\<lbrakk>v/x\<rbrakk> \<and> &x = e\<lbrakk>v/x\<rbrakk>\<^bold>} S \<^bold>{q\<^bold>}"
    unfolding ndfun_kat_H by (rel_auto')
  thus ?thesis
    by (rule_tac H_seq, rule_tac H_assign_floyd_hoare, simp_all add: assms)
qed

lemma assign_self: "vwb_lens x \<Longrightarrow> (x ::= &x) = skip"
  by (rel_simp' simp: one_nd_fun.abs_eq)

lemma assigns_comp: "\<^bold>\<langle>\<sigma>\<^bold>\<rangle> ; \<^bold>\<langle>\<rho>\<^bold>\<rangle> = \<^bold>\<langle>\<rho> \<circ>\<^sub>s \<sigma>\<^bold>\<rangle>"
  by (simp add: assigns_def nd_fun_eq_iff subst_comp.rep_eq, transfer, simp add: kcomp_def)

lemma assign_twice: "vwb_lens x \<Longrightarrow> (x ::= e) ; (x ::= f) = x ::= f\<lbrakk>e/&x\<rbrakk>"
  by (simp add: assigns_comp usubst)

lemma assign_commute: "\<lbrakk> x \<bowtie> y; x \<sharp> f; y \<sharp> e \<rbrakk> \<Longrightarrow> (x ::= e) ; (y ::= f) = (y ::= f) ; (x ::= e)"
  by (simp add: assigns_comp usubst usubst_upd_comm)

\<comment> \<open> Rewriting the Hoare rule for the conditional statement \<close>

abbreviation cond_sugar :: "'a upred \<Rightarrow> 'a nd_fun \<Rightarrow> 'a nd_fun \<Rightarrow> 'a nd_fun" ("IF _ THEN _ ELSE _" [64,64] 63) 
  where "IF B THEN X ELSE Y \<equiv> ifthenelse \<lceil>B\<rceil> X Y"

utp_lift_notation cond_sugar (1 2)

lemma H_cond: "\<^bold>{P \<and> B\<^bold>} X \<^bold>{Q\<^bold>} \<Longrightarrow> \<^bold>{P \<and> \<not> B\<^bold>} Y \<^bold>{Q\<^bold>} \<Longrightarrow> \<^bold>{P\<^bold>} IF B THEN X ELSE Y \<^bold>{Q\<^bold>}"
  by (rule H_cond, simp_all)

lemma sH_cond[simp]: "\<^bold>{P\<^bold>} IF B THEN X ELSE Y \<^bold>{Q\<^bold>} = (\<^bold>{P \<and> B\<^bold>} X \<^bold>{Q\<^bold>} \<and> \<^bold>{P \<and> \<not> B\<^bold>} Y \<^bold>{Q\<^bold>})"
  by (auto simp: H_cond_iff ndfun_kat_H)

lemma assigns_test: "\<^bold>\<langle>\<sigma>\<^bold>\<rangle> ; \<lceil>p\<rceil> = \<lceil>\<sigma> \<dagger> p\<rceil> ; \<^bold>\<langle>\<sigma>\<^bold>\<rangle>"
  apply (simp add: assigns_def n_op_nd_fun_def nd_fun_eq_iff subst_comp.rep_eq p2ndf_def)
  apply (transfer)
  apply (auto simp add:kcomp_def)
  done

lemma assigns_cond:
  "\<^bold>\<langle>\<sigma>\<^bold>\<rangle> ; (IF B THEN P ELSE Q) = IF \<sigma> \<dagger> B THEN \<^bold>\<langle>\<sigma>\<^bold>\<rangle> ; P ELSE \<^bold>\<langle>\<sigma>\<^bold>\<rangle> ; Q"
  by (simp add: ifthenelse_def KAT_rKAT_Models.nd_fun_distl assigns_test Groups.mult_ac[THEN sym] usubst)

lemma cond_assigns: "(IF B THEN \<^bold>\<langle>\<sigma>\<^bold>\<rangle> ELSE \<^bold>\<langle>\<rho>\<^bold>\<rangle>) = \<^bold>\<langle>\<sigma> \<triangleleft> B \<triangleright> \<rho>\<^bold>\<rangle>"
  apply (simp add: ifthenelse_def assigns_def p2ndf_def n_op_nd_fun_def plus_nd_fun_def Abs_nd_fun_inject)
  apply (transfer)
  apply (auto simp add: kcomp_def sup_fun_def comp_def fun_eq_iff uIf_def)
  done

lemmas assign_simps = assigns_cond assigns_test assigns_comp

\<comment> \<open> Rewriting the Hoare rule for the while loop \<close>

abbreviation while_inv_sugar :: "'a upred \<Rightarrow> 'a upred \<Rightarrow> 'a nd_fun \<Rightarrow> 'a nd_fun" ("WHILE _ INV _ DO _" [64,64,64] 63) 
  where "WHILE B INV I DO X \<equiv> while_inv \<lceil>B\<rceil> \<lceil>I\<rceil> X"

utp_lift_notation while_inv_sugar (2)

(*
lemma sH_while_inv: "\<forall>s. P s \<longrightarrow> I s \<Longrightarrow> \<forall>s. I s \<and> \<not> B s \<longrightarrow> Q s \<Longrightarrow> Hoare \<lceil>\<lambda>s. I s \<and> B s\<rceil> X \<lceil>I\<rceil> 
  \<Longrightarrow> Hoare \<lceil>P\<rceil> (WHILE B INV I DO X) \<lceil>Q\<rceil>"
*)


lemma sH_while_inv: "`P \<Rightarrow> I` \<Longrightarrow> `I \<and> \<not> B \<Rightarrow> Q` \<Longrightarrow>  \<^bold>{I \<and> B\<^bold>} X \<^bold>{I\<^bold>}
  \<Longrightarrow>  \<^bold>{P\<^bold>} WHILE B INV I DO X \<^bold>{Q\<^bold>}"
  by (rule H_while_inv, simp_all add: ndfun_kat_H impl.rep_eq taut.rep_eq)
  
\<comment> \<open> Finally, we add a Hoare triple rule for finite iterations. \<close>

abbreviation loopi_sugar :: "'a nd_fun \<Rightarrow> 'a upred \<Rightarrow> 'a nd_fun" ("LOOP _ INV _ " [64,64] 63)
  where "LOOP X INV I \<equiv> loopi X \<lceil>I\<rceil>"

utp_lift_notation loopi_sugar (0)

lemma H_loop: "\<^bold>{P\<^bold>} X \<^bold>{P\<^bold>} \<Longrightarrow> \<^bold>{P\<^bold>} LOOP X INV I  \<^bold>{P\<^bold>}"
  by (auto intro: H_loop)

lemma H_loopI: "\<^bold>{I\<^bold>} X \<^bold>{I\<^bold>} \<Longrightarrow> \<lceil>P\<rceil> \<le> \<lceil>I\<rceil> \<Longrightarrow> \<lceil>I\<rceil> \<le> \<lceil>Q\<rceil> \<Longrightarrow> \<^bold>{P\<^bold>} LOOP X INV I  \<^bold>{Q\<^bold>}"
  using H_loop_inv[of "\<lceil>P\<rceil>" "\<lceil>I\<rceil>" X "\<lceil>Q\<rceil>"] by auto

subsection\<open> Verification of hybrid programs \<close>

\<comment> \<open>Verification by providing evolution\<close>

definition g_evol :: "(('a::ord) \<Rightarrow> 'b usubst) \<Rightarrow> 'b upred \<Rightarrow> 'a set \<Rightarrow> 'b nd_fun" ("EVOL")
  where "EVOL \<phi> G T = (\<lambda>s. g_orbit (\<lambda>t. \<lbrakk>\<phi> t\<rbrakk>\<^sub>e s) \<lbrakk>G\<rbrakk>\<^sub>e T)\<^sup>\<bullet>"

utp_lift_notation g_evol (0 2)

lemma H_g_evol: 
  fixes \<phi> :: "('a::preorder) \<Rightarrow> 'b usubst"
  assumes "P = (\<^bold>\<forall> t\<in>\<guillemotleft>T\<guillemotright> \<bullet> (\<^bold>\<forall>\<tau>\<in>\<guillemotleft>down T t\<guillemotright> \<bullet> G\<lbrakk>\<phi> \<tau>/&\<^bold>v\<rbrakk>) \<Rightarrow> Q\<lbrakk>\<phi> t/&\<^bold>v\<rbrakk>)"
  shows "\<^bold>{P\<^bold>} EVOL \<phi> G T \<^bold>{Q\<^bold>}"
  unfolding ndfun_kat_H g_evol_def g_orbit_eq by (simp add: assms, pred_auto)

lemma H_g_evol_alt: 
  fixes \<phi> :: "('a::preorder) \<Rightarrow> 'b usubst"
  assumes "P = (\<^bold>\<forall> t\<in>\<guillemotleft>T\<guillemotright> \<bullet> (\<^bold>\<forall>\<tau>\<in>\<guillemotleft>down T t\<guillemotright> \<bullet> \<phi> \<tau> \<dagger> G) \<Rightarrow> Q\<lbrakk>\<phi> t/&\<^bold>v\<rbrakk>)"
  shows "\<^bold>{P\<^bold>} EVOL \<phi> G T \<^bold>{Q\<^bold>}"
  using assms by (rule_tac H_g_evol, pred_auto)

lemma sH_g_evol[simp]:  
  fixes \<phi> :: "('a::preorder) \<Rightarrow> 'b usubst"
  shows "\<^bold>{P\<^bold>} EVOL \<phi> G T \<^bold>{Q\<^bold>} = `P \<Rightarrow> (\<^bold>\<forall> t\<in>\<guillemotleft>T\<guillemotright> \<bullet> (\<^bold>\<forall>\<tau>\<in>\<guillemotleft>down T t\<guillemotright> \<bullet> G\<lbrakk>\<phi> \<tau>/&\<^bold>v\<rbrakk>) \<Rightarrow> Q\<lbrakk>\<phi> t/&\<^bold>v\<rbrakk>)`"
  unfolding ndfun_kat_H g_evol_def g_orbit_eq by (pred_auto)

lemma sH_g_evol_alt[simp]:  
  fixes \<phi> :: "('a::preorder) \<Rightarrow> 'b usubst"
  shows "\<^bold>{P\<^bold>} EVOL \<phi> G T \<^bold>{Q\<^bold>} = `P \<Rightarrow> (\<^bold>\<forall> t\<in>\<guillemotleft>T\<guillemotright> \<bullet> (\<^bold>\<forall>\<tau>\<in>\<guillemotleft>down T t\<guillemotright> \<bullet> \<phi> \<tau> \<dagger> G) \<Rightarrow> \<phi> t \<dagger> Q)`"
  unfolding ndfun_kat_H g_evol_def g_orbit_eq by (pred_auto)

\<comment> \<open>Verification by providing solutions\<close>

definition ivp_sols' :: "(('a::real_normed_vector) \<Rightarrow> 'a) \<Rightarrow> real set \<Rightarrow> 'a set \<Rightarrow> 
  real \<Rightarrow> ((real \<Rightarrow> 'a) set, 'a) uexpr" where
[upred_defs]: "ivp_sols' \<sigma> T S t\<^sub>0 = mk\<^sub>e (ivp_sols (\<lambda>t. \<sigma>) T S t\<^sub>0)"

definition g_ode ::"(('a::banach) \<Rightarrow> 'a) \<Rightarrow> 'a upred \<Rightarrow> real set \<Rightarrow> 'a set \<Rightarrow> 
  real \<Rightarrow> 'a nd_fun" ("(1x\<acute>= _ & _ on _ _ @ _)") 
  where "(x\<acute>= f & G on T S @ t\<^sub>0) \<equiv> (\<lambda> s. g_orbital f \<lbrakk>G\<rbrakk>\<^sub>e T S t\<^sub>0 s)\<^sup>\<bullet>"

utp_lift_notation g_ode (0 2 3 4)

lemma H_g_orbital: 
  "P = (\<^bold>\<forall> X\<in>(\<guillemotleft>ivp_sols (\<lambda> t. f) T S t\<^sub>0\<guillemotright> |> &\<^bold>v) \<bullet> (\<^bold>\<forall>t\<in>\<guillemotleft>T\<guillemotright> \<bullet> (\<^bold>\<forall> \<tau> \<in> \<guillemotleft>down T t\<guillemotright> \<bullet> G\<lbrakk>\<guillemotleft>X \<tau>\<guillemotright>/&\<^bold>v\<rbrakk>) \<Rightarrow> Q\<lbrakk>\<guillemotleft>X t\<guillemotright>/&\<^bold>v\<rbrakk>)) \<Longrightarrow> 
  \<^bold>{P\<^bold>} x\<acute>= f & G on T S @ t\<^sub>0 \<^bold>{Q\<^bold>}"
  unfolding ndfun_kat_H g_ode_def g_orbital_eq by pred_simp

(*
lemma H_g_orbital: 
  "P = (\<lambda>s. (\<forall>X\<in>ivp_sols (\<lambda>t. f) T S t\<^sub>0 s. \<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (X \<tau>)) \<longrightarrow> Q (X t))) \<Longrightarrow> 
  Hoare \<lceil>P\<rceil> (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
  unfolding ndfun_kat_H g_ode_def g_orbital_eq by clarsimp
*)

lemma sH_g_orbital: "\<^bold>{P\<^bold>} x\<acute>= f & G on T S @ t\<^sub>0 \<^bold>{Q\<^bold>} = 
  `P \<Rightarrow> (\<^bold>\<forall> X\<in>ivp_sols' f T S t\<^sub>0 \<bullet> (\<^bold>\<forall>t\<in>\<guillemotleft>T\<guillemotright> \<bullet> (\<^bold>\<forall> \<tau> \<in> \<guillemotleft>down T t\<guillemotright> \<bullet> G\<lbrakk>\<guillemotleft>X \<tau>\<guillemotright>/&\<^bold>v\<rbrakk>) \<Rightarrow> Q\<lbrakk>\<guillemotleft>X t\<guillemotright>/&\<^bold>v\<rbrakk>))`"
  unfolding g_orbital_eq g_ode_def ndfun_kat_H by (pred_auto)

locale ue_local_flow = local_flow "\<lbrakk>\<sigma>\<rbrakk>\<^sub>e" T S "\<lambda> t. \<lbrakk>\<rho> t\<rbrakk>\<^sub>e" for \<sigma> \<rho> T S

context local_flow
begin

lemma sH_g_ode: "Hoare \<lceil>P\<rceil> (x\<acute>= f & G on T S @ 0) \<lceil>Q\<rceil> = 
  (\<forall>s\<in>S. \<lbrakk>P\<rbrakk>\<^sub>e s \<longrightarrow> (\<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. \<lbrakk>G\<rbrakk>\<^sub>e (\<phi> \<tau> s)) \<longrightarrow> \<lbrakk>Q\<rbrakk>\<^sub>e (\<phi> t s)))"
proof(unfold sH_g_orbital, rel_simp, safe)
  fix s t
  assume hyps: "s \<in> S" "\<lbrakk>P\<rbrakk>\<^sub>e s" "t\<in>T" "\<forall>\<tau>. \<tau> \<in> T \<and> \<tau> \<le> t \<longrightarrow> \<lbrakk>G\<rbrakk>\<^sub>e (\<phi> \<tau> s)"
    and main: "\<forall>s. \<lbrakk>P\<rbrakk>\<^sub>e s \<longrightarrow> (\<forall>X. X\<in>Sols (\<lambda>t. f) T S 0 s \<longrightarrow> (\<forall>t. t\<in>T \<longrightarrow> (\<forall>\<tau>. \<tau> \<in> T \<and> \<tau> \<le> t \<longrightarrow> \<lbrakk>G\<rbrakk>\<^sub>e (X \<tau>)) \<longrightarrow> \<lbrakk>Q\<rbrakk>\<^sub>e (X t)))"
  hence "(\<lambda>t. \<phi> t s) \<in> Sols (\<lambda>t. f) T S 0 s"
    using in_ivp_sols by blast
  thus "\<lbrakk>Q\<rbrakk>\<^sub>e (\<phi> t s)"
    using main hyps by fastforce
next
  fix s X t
  assume hyps: "\<lbrakk>P\<rbrakk>\<^sub>e s" "X \<in> Sols (\<lambda>t. f) T S 0 s" "t \<in> T"  "\<forall>\<tau>. \<tau> \<in> T \<and> \<tau> \<le> t \<longrightarrow> \<lbrakk>G\<rbrakk>\<^sub>e (X \<tau>)"
    and main: "\<forall>s\<in>S. \<lbrakk>P\<rbrakk>\<^sub>e s \<longrightarrow> (\<forall>t\<in>T. (\<forall>\<tau>. \<tau> \<in> T \<and> \<tau> \<le> t \<longrightarrow> \<lbrakk>G\<rbrakk>\<^sub>e (\<phi> \<tau> s)) \<longrightarrow> \<lbrakk>Q\<rbrakk>\<^sub>e (\<phi> t s))"
  hence obs: "s \<in> S"
    using ivp_sols_def[of "\<lambda>t. f"] init_time by auto
  hence "\<forall>\<tau>\<in>down T t. X \<tau> = \<phi> \<tau> s"
    using eq_solution hyps by blast
  thus "\<lbrakk>Q\<rbrakk>\<^sub>e (X t)"
    using hyps main obs by auto
qed

lemma H_g_ode:
  assumes "P = (U(&\<^bold>v \<in> \<guillemotleft>S\<guillemotright>) \<Rightarrow> (\<^bold>\<forall>t\<in>\<guillemotleft>T\<guillemotright> \<bullet> (\<^bold>\<forall> \<tau> \<in> \<guillemotleft>down T t\<guillemotright> \<bullet> G\<lbrakk>\<guillemotleft>\<phi> \<tau>\<guillemotright> |> &\<^bold>v/&\<^bold>v\<rbrakk>) \<Rightarrow> Q\<lbrakk>\<guillemotleft>\<phi> t\<guillemotright> |> &\<^bold>v/&\<^bold>v\<rbrakk>))" 
  shows "Hoare \<lceil>P\<rceil> (x\<acute>= f & G on T S @ 0) \<lceil>Q\<rceil>"
  using assms unfolding sH_g_ode by pred_simp

lemma sH_g_ode_ivl: "\<tau> \<ge> 0 \<Longrightarrow> \<tau> \<in> T \<Longrightarrow> Hoare \<lceil>P\<rceil> (x\<acute>= f & G on {0..\<tau>} S @ 0) \<lceil>Q\<rceil> = 
  (\<forall>s\<in>S. \<lbrakk>P\<rbrakk>\<^sub>e s \<longrightarrow> (\<forall>t\<in>{0..\<tau>}. (\<forall>\<tau>\<in>{0..t}. \<lbrakk>G\<rbrakk>\<^sub>e (\<phi> \<tau> s)) \<longrightarrow> \<lbrakk>Q\<rbrakk>\<^sub>e (\<phi> t s)))"
proof(unfold sH_g_orbital, rel_simp, safe)
  fix s t
  assume hyps: "0 \<le> \<tau>" "\<tau> \<in> T" "s \<in> S" "\<lbrakk>P\<rbrakk>\<^sub>e s" "t \<in> {0..\<tau>}" "\<forall>\<tau>\<in>{0..t}. \<lbrakk>G\<rbrakk>\<^sub>e (\<phi> \<tau> s)"
    and main: "\<forall>s. \<lbrakk>P\<rbrakk>\<^sub>e s \<longrightarrow> (\<forall>X. X\<in>Sols (\<lambda>t. f) {0..\<tau>} S 0 s \<longrightarrow> (\<forall>t. 0 \<le> t \<and> t \<le> \<tau> \<longrightarrow>
  (\<forall>\<tau>'. 0 \<le> \<tau>' \<and> \<tau>' \<le> \<tau> \<and> \<tau>' \<le> t \<longrightarrow> \<lbrakk>G\<rbrakk>\<^sub>e (X \<tau>')) \<longrightarrow> \<lbrakk>Q\<rbrakk>\<^sub>e (X t)))"
  hence "(\<lambda>t. \<phi> t s) \<in> Sols (\<lambda>t. f) {0..\<tau>} S 0 s"
    using in_ivp_sols_ivl closed_segment_eq_real_ivl[of 0 \<tau>] by force
  thus "\<lbrakk>Q\<rbrakk>\<^sub>e (\<phi> t s)"
    using main hyps by fastforce
next
  fix s X t
  assume hyps: "0 \<le> \<tau>" "\<tau> \<in> T" "\<lbrakk>P\<rbrakk>\<^sub>e s" "X \<in> Sols (\<lambda>t. f) {0..\<tau>} S 0 s" "0 \<le> t" "t \<le> \<tau>"  
    "\<forall>\<tau>'. 0 \<le> \<tau>' \<and> \<tau>' \<le> \<tau> \<and> \<tau>' \<le> t \<longrightarrow> \<lbrakk>G\<rbrakk>\<^sub>e (X \<tau>')"
    and main: "\<forall>s\<in>S. \<lbrakk>P\<rbrakk>\<^sub>e s \<longrightarrow> (\<forall>t\<in>{0..\<tau>}. (\<forall>\<tau>\<in>{0..t}. \<lbrakk>G\<rbrakk>\<^sub>e (\<phi> \<tau> s)) \<longrightarrow> \<lbrakk>Q\<rbrakk>\<^sub>e (\<phi> t s))"
  hence "s \<in> S"
    using ivp_sols_def[of "\<lambda>t. f"] init_time by auto
  have obs1: "\<forall>\<tau>\<in>down {0..\<tau>} t. D X = (\<lambda>t. f (X t)) on {0--\<tau>}"
    apply(clarsimp, rule has_vderiv_on_subset)
    using ivp_solsD(1)[OF hyps(4)] by (auto simp: closed_segment_eq_real_ivl)
  have obs2: "X 0 = s" "\<forall>\<tau>\<in>down {0..\<tau>} t. X \<in> {0--\<tau>} \<rightarrow> S"
    using ivp_solsD(2,3)[OF hyps(4)] by (auto simp: closed_segment_eq_real_ivl)
  have "\<forall>\<tau>\<in>down {0..\<tau>} t. \<tau> \<in> T"
  using subintervalI[OF init_time \<open>\<tau> \<in> T\<close>] by (auto simp: closed_segment_eq_real_ivl)
  hence "\<forall>\<tau>\<in>down {0..\<tau>} t. X \<tau> = \<phi> \<tau> s"
    using obs1 obs2 apply(clarsimp)
    by (rule eq_solution_ivl) (auto simp: closed_segment_eq_real_ivl)
  thus "\<lbrakk>Q\<rbrakk>\<^sub>e (X t)"
    using hyps main \<open>s \<in> S\<close> by auto
qed

lemma H_g_ode_ivl: "\<tau> \<ge> 0 \<Longrightarrow> \<tau> \<in> T \<Longrightarrow>  
  (\<forall>s\<in>S. \<lbrakk>P\<rbrakk>\<^sub>e s \<longrightarrow> (\<forall>t\<in>{0..\<tau>}. (\<forall>\<tau>\<in>{0..t}. \<lbrakk>G\<rbrakk>\<^sub>e (\<phi> \<tau> s)) \<longrightarrow> \<lbrakk>Q\<rbrakk>\<^sub>e (\<phi> t s))) \<Longrightarrow> 
  Hoare \<lceil>P\<rceil> (x\<acute>= f & G on {0..\<tau>} S @ 0) \<lceil>Q\<rceil>"
  unfolding sH_g_ode_ivl by simp

lemma H_g_ode_ivl2:
  assumes "P = (U(&\<^bold>v \<in> \<guillemotleft>S\<guillemotright>) \<Rightarrow> (\<^bold>\<forall>t\<in>\<guillemotleft>{0..\<tau>}\<guillemotright> \<bullet> (\<^bold>\<forall> \<tau> \<in> \<guillemotleft>{0..t}\<guillemotright> \<bullet> G\<lbrakk>\<guillemotleft>\<phi> \<tau>\<guillemotright> |> &\<^bold>v/&\<^bold>v\<rbrakk>) \<Rightarrow> Q\<lbrakk>\<guillemotleft>\<phi> t\<guillemotright> |> &\<^bold>v/&\<^bold>v\<rbrakk>))" 
     and "\<tau> \<ge> 0" and "\<tau> \<in> T"
  shows "Hoare \<lceil>P\<rceil> (x\<acute>= f & G on {0..\<tau>} S @ 0) \<lceil>Q\<rceil>"
  unfolding sH_g_ode_ivl[OF assms(2,3)] using assms by pred_simp

lemma sH_orbit: "Hoare \<lceil>P\<rceil> (\<gamma>\<^sup>\<phi>\<^sup>\<bullet>) \<lceil>Q\<rceil> = (\<forall>s \<in> S. \<lbrakk>P\<rbrakk>\<^sub>e s \<longrightarrow> (\<forall> t \<in> T. \<lbrakk>Q\<rbrakk>\<^sub>e (\<phi> t s)))"
  using sH_g_ode[of P "true_upred" Q] unfolding orbit_def g_ode_def by pred_simp

end

\<comment> \<open> Verification with differential invariants \<close>

definition g_ode_inv :: "(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a upred \<Rightarrow> real set \<Rightarrow> 'a set \<Rightarrow> 
  real \<Rightarrow> 'a upred \<Rightarrow> 'a nd_fun" ("(1x\<acute>=_ & _ on _ _ @ _ DINV _ )") 
  where "(x\<acute>= f & G on T S @ t\<^sub>0 DINV I) = (x\<acute>= f & G on T S @ t\<^sub>0)"

utp_lift_notation g_ode_inv (0 2 3 4)

lemma sH_g_orbital_guard: 
  assumes "R = (G \<and> Q)"
  shows "Hoare \<lceil>P\<rceil> (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil> = Hoare \<lceil>P\<rceil> (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>R\<rceil>" 
  unfolding g_orbital_eq ndfun_kat_H ivp_sols_def g_ode_def assms by (pred_auto)

lemma sH_g_orbital_inv:
  assumes "\<lceil>P\<rceil> \<le> \<lceil>I\<rceil>" and "Hoare \<lceil>I\<rceil> (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>I\<rceil>" and "\<lceil>I\<rceil> \<le> \<lceil>Q\<rceil>"
  shows "Hoare \<lceil>P\<rceil> (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
  using assms(1) apply(rule_tac p'="\<lceil>I\<rceil>" in H_consl, simp)
  using assms(3) apply(rule_tac q'="\<lceil>I\<rceil>" in H_consr, simp)
  using assms(2) by simp

lemma sH_diff_inv[simp]: "Hoare \<lceil>I\<rceil> (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>I\<rceil> = diff_invariant \<lbrakk>I\<rbrakk>\<^sub>e f T S t\<^sub>0 \<lbrakk>G\<rbrakk>\<^sub>e"
  unfolding diff_invariant_eq ndfun_kat_H g_orbital_eq g_ode_def by auto

lemma H_g_ode_inv: "Hoare \<lceil>I\<rceil> (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>I\<rceil> \<Longrightarrow> \<lceil>P\<rceil> \<le> \<lceil>I\<rceil> \<Longrightarrow> 
  \<lceil>I \<and> G\<rceil> \<le> \<lceil>Q\<rceil> \<Longrightarrow> Hoare \<lceil>P\<rceil> (x\<acute>= f & G on T S @ t\<^sub>0 DINV I) \<lceil>Q\<rceil>"
  unfolding g_ode_inv_def apply(rule_tac q'="\<lceil>I \<and> G\<rceil>" in H_consr, simp)
  apply(subst sH_g_orbital_guard[of _ "G" "I", symmetric], pred_auto)
  by (rule_tac I="I" in sH_g_orbital_inv, simp_all)


subsection \<open> Refinement Components \<close>

abbreviation RProgr ("\<^bold>[_,_\<^bold>]") where "\<^bold>[P,Q\<^bold>] \<equiv> Ref \<lceil>P\<rceil> \<lceil>Q\<rceil>"

utp_lift_notation RProgr 

\<comment> \<open> Skip \<close>

lemma R_skip: "`P \<Rightarrow> Q` \<Longrightarrow> 1 \<le> \<^bold>[P,Q\<^bold>]"
  by (auto simp: spec_def ndfun_kat_H one_nd_fun_def, pred_auto)

\<comment> \<open> Composition \<close>

lemma R_seq: "\<^bold>[P,R\<^bold>] ; \<^bold>[R,Q\<^bold>] \<le> \<^bold>[P,Q\<^bold>]"
  using R_seq by blast

lemma R_seq_law: "X \<le> \<^bold>[P,R\<^bold>] \<Longrightarrow> Y \<le> \<^bold>[R,Q\<^bold>] \<Longrightarrow> X; Y \<le> \<^bold>[P,Q\<^bold>]"
  unfolding spec_def by (rule H_seq)

lemmas R_seq_mono = mult_isol_var

\<comment> \<open> Assignment \<close>

lemma R_assign: "(x ::= e) \<le> \<^bold>[P\<lbrakk>e/&x\<rbrakk>,P\<^bold>]"
  unfolding spec_def by (rule H_assign, clarsimp simp: fun_eq_iff fun_upd_def)

lemma R_assign_law: "`P \<Rightarrow> Q\<lbrakk>e/&x\<rbrakk>` \<Longrightarrow> (x ::= e) \<le> \<^bold>[P,Q\<^bold>]"
  unfolding sH_assign[symmetric] spec_def by (metis pr_var_def sH_assign_alt) 

lemma R_assignl: "P = R\<lbrakk>e/&x\<rbrakk> \<Longrightarrow> (x ::= e) ; \<^bold>[R,Q\<^bold>] \<le> \<^bold>[P,Q\<^bold>]"
  apply(rule_tac R=R in R_seq_law)
  by (rule_tac R_assign_law, simp_all)

lemma R_assignr: "R = Q\<lbrakk>e/&x\<rbrakk> \<Longrightarrow> \<^bold>[P,R\<^bold>]; (x ::= e) \<le> \<^bold>[P,Q\<^bold>]"
  apply(rule_tac R=R in R_seq_law, simp)
  by (rule_tac R_assign_law, simp)

lemma "(x ::= e) ; \<^bold>[Q,Q\<^bold>] \<le> \<^bold>[Q\<lbrakk>e/&x\<rbrakk>,Q\<^bold>]"
  by (rule R_assignl) simp

lemma "\<^bold>[Q,Q\<lbrakk>e/&x\<rbrakk>\<^bold>] ; (x ::= e) \<le> \<^bold>[Q,Q\<^bold>]"
  by (rule R_assignr) simp

\<comment> \<open> Conditional \<close>

lemma R_cond: "K1 = U(B \<and> P) \<Longrightarrow> K2 = U(\<not> B \<and> P) \<Longrightarrow> (IF B THEN \<^bold>[K1,Q\<^bold>] ELSE \<^bold>[K2,Q\<^bold>]) \<le> \<^bold>[P,Q\<^bold>]"
  using R_cond[of "\<lceil>B\<rceil>" "\<lceil>P\<rceil>" "\<lceil>Q\<rceil>"] by simp

lemma R_cond_mono: "X \<le> X' \<Longrightarrow> Y \<le> Y' \<Longrightarrow> (IF B THEN X ELSE Y) \<le> IF B THEN X' ELSE Y'"
  unfolding ifthenelse_def times_nd_fun_def plus_nd_fun_def n_op_nd_fun_def
  by (auto simp: kcomp_def less_eq_nd_fun_def p2ndf_def le_fun_def)

lemma R_cond_law: "X \<le> \<^bold>[B \<and> P,Q\<^bold>] \<Longrightarrow> Y \<le> \<^bold>[\<not> B \<and> P,Q\<^bold>] \<Longrightarrow> (IF B THEN X ELSE Y) \<le> \<^bold>[P,Q\<^bold>]"
  by (rule order_trans; (rule R_cond_mono)?, (rule R_cond)?) auto

\<comment> \<open> While loop \<close>

lemma R_while: "K=U(P \<and> \<not> Q) \<Longrightarrow> WHILE Q INV I DO \<^bold>[P \<and> Q,P\<^bold>] \<le> \<^bold>[P,K\<^bold>]"
  unfolding while_inv_def using R_while[of "\<lceil>Q\<rceil>" "\<lceil>P\<rceil>"] by simp

lemma R_while_mono: "X \<le> X' \<Longrightarrow> (WHILE B INV I DO X) \<le> WHILE B INV I DO X'"
  by (simp add: while_inv_def while_def mult_isol mult_isor star_iso)

lemma R_while_law: "X \<le> \<^bold>[P \<and> B,P\<^bold>] \<Longrightarrow> Q = U(P \<and> \<not> B) \<Longrightarrow> (WHILE B INV I DO X) \<le> \<^bold>[P, Q\<^bold>]"
  by (rule order_trans; (rule R_while_mono)?, (rule R_while)?)

\<comment> \<open> Finite loop \<close>

lemma R_loop: "\<lceil>P\<rceil> \<le> \<lceil>I\<rceil> \<Longrightarrow> \<lceil>I\<rceil> \<le> \<lceil>Q\<rceil> \<Longrightarrow> LOOP \<^bold>[I,I\<^bold>] INV I \<le>  \<^bold>[P,Q\<^bold>]"
  unfolding spec_def by (rule H_loopI, rule R1, simp_all)

lemma R_loop_mono: "X \<le> X' \<Longrightarrow> LOOP X INV I \<le> LOOP X' INV I"
  unfolding loopi_def by (simp add: star_iso)

lemma R_loop_law: "X \<le> \<^bold>[I,I\<^bold>] \<Longrightarrow> \<lceil>P\<rceil> \<le> \<lceil>I\<rceil> \<Longrightarrow> \<lceil>I\<rceil> \<le> \<lceil>Q\<rceil> \<Longrightarrow> LOOP X INV I \<le> \<^bold>[P,Q\<^bold>]"
  unfolding spec_def using H_loopI by blast

\<comment> \<open> Evolution command (flow) \<close>

lemma R_g_evol: 
  fixes \<phi> :: "('a::preorder) \<Rightarrow> 'b usubst"
  shows "(EVOL \<phi> G T) \<le> Ref \<lceil>\<^bold>\<forall>t\<in>\<guillemotleft>T\<guillemotright> \<bullet> (\<^bold>\<forall>\<tau>\<in>\<guillemotleft>down T t\<guillemotright> \<bullet> \<phi> \<tau> \<dagger> G) \<Rightarrow> \<phi> t \<dagger> P\<rceil> \<lceil>P\<rceil>"
  unfolding spec_def by (rule H_g_evol, rel_simp)

lemma R_g_evol_law: 
  fixes \<phi> :: "('a::preorder) \<Rightarrow> 'b usubst"
  shows "`P \<Rightarrow> (\<^bold>\<forall>t\<in>\<guillemotleft>T\<guillemotright> \<bullet> (\<^bold>\<forall>\<tau>\<in>\<guillemotleft>down T t\<guillemotright> \<bullet> \<phi> \<tau> \<dagger> G) \<Rightarrow> \<phi> t \<dagger> Q)` \<Longrightarrow> (EVOL \<phi> G T) \<le> \<^bold>[P,Q\<^bold>]"
  unfolding sH_g_evol_alt[symmetric] spec_def by (auto)

lemma R_g_evoll: 
  fixes \<phi> :: "('a::preorder) \<Rightarrow> 'b usubst"
  shows "P = (\<^bold>\<forall>t\<in>\<guillemotleft>T\<guillemotright> \<bullet> (\<^bold>\<forall>\<tau>\<in>\<guillemotleft>down T t\<guillemotright> \<bullet> \<phi> \<tau> \<dagger> G) \<Rightarrow> \<phi> t \<dagger> R) \<Longrightarrow> 
  (EVOL \<phi> G T) ; \<^bold>[R,Q\<^bold>] \<le> \<^bold>[P,Q\<^bold>]"
  apply(rule_tac R=R in R_seq_law)
  by (rule_tac R_g_evol_law, simp_all)

lemma R_g_evolr: 
  fixes \<phi> :: "('a::preorder) \<Rightarrow> 'b usubst"
  shows "R = (\<^bold>\<forall>t\<in>\<guillemotleft>T\<guillemotright> \<bullet> (\<^bold>\<forall>\<tau>\<in>\<guillemotleft>down T t\<guillemotright> \<bullet> \<phi> \<tau> \<dagger> G) \<Rightarrow> \<phi> t \<dagger> Q) \<Longrightarrow> 
  \<^bold>[P,R\<^bold>]; (EVOL \<phi> G T) \<le> \<^bold>[P,Q\<^bold>]"
  apply(rule_tac R=R in R_seq_law, simp)
  by (rule_tac R_g_evol_law, simp)

lemma 
  fixes \<phi> :: "('a::preorder) \<Rightarrow> 'b usubst"
  shows "EVOL \<phi> G T ; \<^bold>[Q,Q\<^bold>] \<le> Ref \<lceil>\<^bold>\<forall>t\<in>\<guillemotleft>T\<guillemotright> \<bullet> (\<^bold>\<forall>\<tau>\<in>\<guillemotleft>down T t\<guillemotright> \<bullet> \<phi> \<tau> \<dagger> G) \<Rightarrow> \<phi> t \<dagger> Q\<rceil> \<lceil>Q\<rceil>"
  by (rule R_g_evoll) simp

lemma 
  fixes \<phi> :: "('a::preorder) \<Rightarrow> 'b usubst"
  shows "Ref \<lceil>Q\<rceil> \<lceil>\<^bold>\<forall>t\<in>\<guillemotleft>T\<guillemotright> \<bullet> (\<^bold>\<forall>\<tau>\<in>\<guillemotleft>down T t\<guillemotright> \<bullet> \<phi> \<tau> \<dagger> G) \<Rightarrow> \<phi> t \<dagger> Q\<rceil> ; EVOL \<phi> G T \<le> \<^bold>[Q,Q\<^bold>]"
  by (rule R_g_evolr) simp

\<comment> \<open> Evolution command (ode) \<close>

context local_flow
begin

lemma R_g_ode: "(x\<acute>= f & G on T S @ 0) \<le> Ref \<lceil>U(&\<^bold>v\<in>\<guillemotleft>S\<guillemotright> \<Rightarrow> (\<forall>t\<in>\<guillemotleft>T\<guillemotright>. (\<forall>\<tau>\<in>\<guillemotleft>down T t\<guillemotright>. G\<lbrakk>\<guillemotleft>\<phi> \<tau>\<guillemotright> |> &\<^bold>v/&\<^bold>v\<rbrakk>) \<Rightarrow> P\<lbrakk>\<guillemotleft>\<phi> t\<guillemotright> |> &\<^bold>v/&\<^bold>v\<rbrakk>))\<rceil> \<lceil>P\<rceil>"
  unfolding spec_def by (rule H_g_ode, rel_auto)

lemma R_g_ode_law: "(\<forall>s\<in>S. \<lbrakk>P\<rbrakk>\<^sub>e s \<longrightarrow> (\<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. \<lbrakk>G\<rbrakk>\<^sub>e (\<phi> \<tau> s)) \<longrightarrow> \<lbrakk>Q\<rbrakk>\<^sub>e (\<phi> t s))) \<Longrightarrow> 
  (x\<acute>= f & G on T S @ 0) \<le> \<^bold>[P,Q\<^bold>]"
  unfolding sH_g_ode[symmetric] by (rule R2)

lemma R_g_odel: "P = U(\<forall>t\<in>\<guillemotleft>T\<guillemotright>. (\<forall>\<tau>\<in>\<guillemotleft>down T t\<guillemotright>. G\<lbrakk>\<guillemotleft>\<phi> \<tau>\<guillemotright> |> &\<^bold>v/&\<^bold>v\<rbrakk>) \<longrightarrow> R\<lbrakk>\<guillemotleft>\<phi> t\<guillemotright> |> &\<^bold>v/&\<^bold>v\<rbrakk>) \<Longrightarrow> 
  (x\<acute>= f & G on T S @ 0) ; Ref \<lceil>R\<rceil> \<lceil>Q\<rceil> \<le> \<^bold>[P,Q\<^bold>]"
  apply(rule_tac R=R in R_seq_law)
   apply (rule_tac R_g_ode_law, simp_all, rel_auto)
  done

lemma R_g_oder: "R = U(\<forall>t\<in>\<guillemotleft>T\<guillemotright>. (\<forall>\<tau>\<in>\<guillemotleft>down T t\<guillemotright>. G\<lbrakk>\<guillemotleft>\<phi> \<tau>\<guillemotright> |> &\<^bold>v/&\<^bold>v\<rbrakk>) \<longrightarrow> Q\<lbrakk>\<guillemotleft>\<phi> t\<guillemotright> |> &\<^bold>v/&\<^bold>v\<rbrakk>) \<Longrightarrow> 
  \<^bold>[P,R\<^bold>]; (x\<acute>= f & G on T S @ 0) \<le> \<^bold>[P,Q\<^bold>]"
  apply(rule_tac R=R in R_seq_law, simp)
  by (rule_tac R_g_ode_law, rel_simp)

lemma "(x\<acute>= f & G on T S @ 0) ; \<^bold>[Q,Q\<^bold>] \<le> Ref \<lceil>U(\<forall>t\<in>\<guillemotleft>T\<guillemotright>. (\<forall>\<tau>\<in>\<guillemotleft>down T t\<guillemotright>. G\<lbrakk>\<guillemotleft>\<phi> \<tau>\<guillemotright> |> &\<^bold>v/&\<^bold>v\<rbrakk>) \<longrightarrow> Q\<lbrakk>\<guillemotleft>\<phi> t\<guillemotright> |> &\<^bold>v/&\<^bold>v\<rbrakk>)\<rceil> \<lceil>Q\<rceil>"
  by (rule R_g_odel) simp

lemma "Ref \<lceil>Q\<rceil> \<lceil>U(\<forall>t\<in>\<guillemotleft>T\<guillemotright>. (\<forall>\<tau>\<in>\<guillemotleft>down T t\<guillemotright>. G\<lbrakk>\<guillemotleft>\<phi> \<tau>\<guillemotright> |> &\<^bold>v/&\<^bold>v\<rbrakk>) \<Rightarrow> Q\<lbrakk>\<guillemotleft>\<phi> t\<guillemotright> |> &\<^bold>v/&\<^bold>v\<rbrakk>)\<rceil>; (x\<acute>= f & G on T S @ 0) \<le> \<^bold>[Q,Q\<^bold>]"
  by (rule R_g_oder) rel_simp

lemma R_g_ode_ivl: 
  "\<tau> \<ge> 0 \<Longrightarrow> \<tau> \<in> T \<Longrightarrow> (\<forall>s\<in>S. \<lbrakk>P\<rbrakk>\<^sub>e s \<longrightarrow> (\<forall>t\<in>{0..\<tau>}. (\<forall>\<tau>\<in>{0..t}. \<lbrakk>G\<rbrakk>\<^sub>e (\<phi> \<tau> s)) \<longrightarrow> \<lbrakk>Q\<rbrakk>\<^sub>e (\<phi> t s))) \<Longrightarrow> 
  (x\<acute>= f & G on {0..\<tau>} S @ 0) \<le> \<^bold>[P,Q\<^bold>]"
  unfolding sH_g_ode_ivl[symmetric] by (rule R2)

end

\<comment> \<open> Evolution command (invariants) \<close>

lemma R_g_ode_inv: "diff_invariant \<lbrakk>I\<rbrakk>\<^sub>e f T S t\<^sub>0 \<lbrakk>G\<rbrakk>\<^sub>e \<Longrightarrow> \<lceil>P\<rceil> \<le> \<lceil>I\<rceil> \<Longrightarrow> \<lceil>I \<and> G\<rceil> \<le> \<lceil>Q\<rceil> \<Longrightarrow> 
  (x\<acute>=f & G on T S @ t\<^sub>0 DINV I) \<le> \<^bold>[P,Q\<^bold>]"
  unfolding spec_def by (auto simp: H_g_ode_inv)


subsection \<open> Derivation of the rules of dL \<close>

text \<open> We derive a generalised version of some domain specific rules of differential dynamic logic (dL).\<close>

lemma diff_solve_axiom: 
  fixes c::"'a::{heine_borel, banach}"
  assumes "0 \<in> T" and "is_interval T" "open T"
    and "\<forall>s. \<lbrakk>P\<rbrakk>\<^sub>e s \<longrightarrow> (\<forall>t\<in>T. (\<P> (\<lambda> t. s + t *\<^sub>R c) (down T t) \<subseteq> {s. \<lbrakk>G\<rbrakk>\<^sub>e s}) \<longrightarrow> \<lbrakk>Q\<rbrakk>\<^sub>e (s + t *\<^sub>R c))"
  shows "Hoare \<lceil>P\<rceil> (x\<acute>=(\<lambda>s. c) & G on T UNIV @ 0) \<lceil>Q\<rceil>"
  apply(subst local_flow.sH_g_ode[where f="\<lambda>s. c" and \<phi>="(\<lambda> t x. x + t *\<^sub>R c)"])
  using line_is_local_flow assms by auto

lemma diff_solve_rule:
  assumes "local_flow f T UNIV \<phi>"
    and "\<forall>s. \<lbrakk>P\<rbrakk>\<^sub>e s \<longrightarrow> (\<forall> t\<in>T. (\<P> (\<lambda>t. \<phi> t s) (down T t) \<subseteq> {s. \<lbrakk>G\<rbrakk>\<^sub>e s}) \<longrightarrow> \<lbrakk>Q\<rbrakk>\<^sub>e (\<phi> t s))"
  shows "Hoare \<lceil>P\<rceil> (x\<acute>= f & G on T UNIV @ 0) \<lceil>Q\<rceil>"
  using assms by(subst local_flow.sH_g_ode, auto)

lemma diff_weak_rule: 
  assumes "\<lceil>G\<rceil> \<le> \<lceil>Q\<rceil>"
  shows "Hoare \<lceil>P\<rceil> (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
  using assms unfolding ndfun_kat_H g_ode_def g_orbital_eq ivp_sols_def by (simp, rel_auto)

lemma diff_cut_rule:
  assumes Thyp: "is_interval T" "t\<^sub>0 \<in> T"
    and wp_C:"Hoare \<lceil>P\<rceil> (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>C\<rceil>"
    and wp_Q:"Hoare \<lceil>P\<rceil> (x\<acute>= f & (G \<and> C) on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
  shows "Hoare \<lceil>P\<rceil> (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
proof(subst ndfun_kat_H, simp add: g_orbital_eq p2ndf_def g_ode_def, clarsimp)
  fix t::real and X::"real \<Rightarrow> 'a" and s assume "\<lbrakk>P\<rbrakk>\<^sub>e s" and "t \<in> T"
    and x_ivp:"X \<in> ivp_sols (\<lambda>t. f) T S t\<^sub>0 s" 
    and guard_x:"\<forall>x. x \<in> T \<and> x \<le> t \<longrightarrow> \<lbrakk>G\<rbrakk>\<^sub>e (X x)"
  have "\<forall>t\<in>(down T t). X t \<in> g_orbital f \<lbrakk>G\<rbrakk>\<^sub>e T S t\<^sub>0 s"
    using g_orbitalI[OF x_ivp] guard_x by auto
  hence "\<forall>t\<in>(down T t). \<lbrakk>C\<rbrakk>\<^sub>e (X t)" 
    using wp_C \<open>\<lbrakk>P\<rbrakk>\<^sub>e s\<close> by (subst (asm) ndfun_kat_H, auto simp: g_ode_def)
  hence "X t \<in> g_orbital f \<lbrakk>G \<and> C\<rbrakk>\<^sub>e T S t\<^sub>0 s"
    using guard_x \<open>t \<in> T\<close> by (auto intro!: g_orbitalI x_ivp, rel_simp)
  thus "\<lbrakk>Q\<rbrakk>\<^sub>e (X t)"
    using \<open>\<lbrakk>P\<rbrakk>\<^sub>e s\<close> wp_Q by (subst (asm) ndfun_kat_H) (auto simp: g_ode_def)
qed

abbreviation g_global_ode ::"(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a upred \<Rightarrow> 'a nd_fun" ("(1x\<acute>=_ & _)") 
  where "(x\<acute>= f & G) \<equiv> (x\<acute>= f & G on UNIV UNIV @ 0)"

utp_lift_notation g_global_ode (0)

abbreviation g_global_ode_inv :: "(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a upred \<Rightarrow> 'a upred \<Rightarrow> 'a nd_fun" 
  ("(1x\<acute>=_ & _ DINV _)") where "(x\<acute>= f & G DINV I) \<equiv> (x\<acute>= f & G on UNIV UNIV @ 0 DINV I)"

utp_lift_notation g_global_ode_inv (0)

end