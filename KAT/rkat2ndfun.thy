(*  Title:       Refinement components for Hybrid Systems with relational KAT 
    Author:      Jonathan Julián Huerta y Munive, 2019
    Maintainer:  Jonathan Julián Huerta y Munive <jjhuertaymunive1@sheffield.ac.uk>
*)

section \<open> Refinement components for HS with relational KAT \<close>

text \<open> We use our relational model to obtain a refinement component for hybrid programs. 
We provide three methods for refining continuous dynamics of hybrid systems in this 
setting: using flows, solutions, and differential invariants. \<close>

theory rkat2ndfun
  imports kat2ndfun

begin

subsection \<open> Refinement Components \<close>

lemma R_skip: "(\<forall>s. P s \<longrightarrow> Q s) \<Longrightarrow> 1 \<le> Ref \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  by (auto simp: spec_def ndfun_kat_H one_nd_fun_def)

lemma R_comp: "(Ref \<lceil>P\<rceil> \<lceil>R\<rceil>) ; (Ref \<lceil>R\<rceil> \<lceil>Q\<rceil>) \<le> Ref \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  using R_seq by blast

lemma R_comp_rule: "X \<le> Ref \<lceil>P\<rceil> \<lceil>R\<rceil> \<Longrightarrow> Y \<le> Ref \<lceil>R\<rceil> \<lceil>Q\<rceil> \<Longrightarrow> X; Y \<le> Ref \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  unfolding spec_def by (rule H_comp)

lemmas R_comp_mono = mult_isol_var

lemma R_assign: "(x ::= e) \<le> Ref \<lceil>\<lambda>s. P (\<chi> j. ((($) s)(x := e s)) j)\<rceil> \<lceil>P\<rceil>"
  unfolding spec_def by (rule H_assign, clarsimp simp: fun_eq_iff fun_upd_def)

lemma R_assign_rule: "(\<forall>s. P s \<longrightarrow> Q (\<chi> j. ((($) s)(x := (e s))) j)) \<Longrightarrow> (x ::= e) \<le> Ref \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  unfolding sH_assign[symmetric] spec_def .

lemma R_assignl: "P = (\<lambda>s. R (\<chi> j. ((($) s)(x := e s)) j)) \<Longrightarrow> (x ::= e) ; Ref \<lceil>R\<rceil> \<lceil>Q\<rceil> \<le> Ref \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  apply(rule_tac R=R in R_comp_rule)
  by (rule_tac R_assign_rule, simp_all)

lemma R_assignr: "R = (\<lambda>s. Q (\<chi> j. ((($) s)(x := e s)) j)) \<Longrightarrow> Ref \<lceil>P\<rceil> \<lceil>R\<rceil>; (x ::= e) \<le> Ref \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  apply(rule_tac R=R in R_comp_rule, simp)
  by (rule_tac R_assign_rule, simp)

lemma R_cond: "(IF B THEN Ref \<lceil>\<lambda>s. B s \<and> P s\<rceil> \<lceil>Q\<rceil> ELSE Ref \<lceil>\<lambda>s. \<not> B s \<and> P s\<rceil> \<lceil>Q\<rceil>) \<le> Ref \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  using R_cond[of "\<lceil>B\<rceil>" "\<lceil>P\<rceil>" "\<lceil>Q\<rceil>"] by simp

lemma R_cond_mono: "X \<le> X' \<Longrightarrow> Y \<le> Y' \<Longrightarrow> (IF P THEN X ELSE Y) \<le> IF P THEN X' ELSE Y'"
  unfolding ifthenelse_def times_nd_fun_def plus_nd_fun_def n_op_nd_fun_def
  by (auto simp: kcomp_def less_eq_nd_fun_def p2ndf_def le_fun_def)

lemma R_while: "WHILE Q INV I DO (Ref \<lceil>\<lambda>s. P s \<and> Q s\<rceil> \<lceil>P\<rceil>) \<le> Ref \<lceil>P\<rceil> \<lceil>\<lambda>s. P s \<and> \<not> Q s\<rceil>"
  unfolding while_inv_def using R_while[of "\<lceil>Q\<rceil>" "\<lceil>P\<rceil>"] by simp

lemma R_while_mono: "X \<le> X' \<Longrightarrow> (WHILE P INV I DO X) \<le> WHILE P INV I DO X'"
  by (simp add: while_inv_def while_def mult_isol mult_isor star_iso)

lemma R_loop: "X \<le> Ref \<lceil>I\<rceil> \<lceil>I\<rceil> \<Longrightarrow> \<lceil>P\<rceil> \<le> \<lceil>I\<rceil> \<Longrightarrow> \<lceil>I\<rceil> \<le> \<lceil>Q\<rceil> \<Longrightarrow> LOOP X INV I \<le> Ref \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  unfolding spec_def using H_loopI by blast

lemma R_loop_mono: "X \<le> X' \<Longrightarrow> LOOP X INV I \<le> LOOP X' INV I"
  unfolding loopi_def by (simp add: star_iso)

lemma R_g_evol: 
  fixes \<phi> :: "('a::preorder) \<Rightarrow> 'b \<Rightarrow> 'b"
  shows"(\<forall>s. P s \<longrightarrow> (\<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s))) \<Longrightarrow> 
  (EVOL \<phi> G T) \<le> Ref \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  unfolding sH_g_evol[symmetric] spec_def .

lemma (in local_flow) R_g_ode: "(\<forall>s\<in>S. P s \<longrightarrow> (\<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s))) \<Longrightarrow> 
  (x\<acute>= f & G on T S @ 0) \<le> Ref \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  unfolding sH_g_ode[symmetric] by (rule R2)

(* MISSING LEFT AND RIGHT RULES FOR EVOLUTION COMMANDS *)

lemma (in local_flow) R_g_ode_ivl: 
  "\<tau> \<ge> 0 \<Longrightarrow> \<tau> \<in> T \<Longrightarrow> (\<forall>s\<in>S. P s \<longrightarrow> (\<forall>t\<in>{0..\<tau>}. (\<forall>\<tau>\<in>{0..t}. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s))) \<Longrightarrow> 
  (x\<acute>= f & G on {0..\<tau>} S @ 0) \<le> Ref \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  unfolding sH_g_ode_ivl[symmetric] by (rule R2)

lemma R_g_ode_inv: "diff_invariant I f T S t\<^sub>0 G \<Longrightarrow> \<lceil>P\<rceil> \<le> \<lceil>I\<rceil> \<Longrightarrow> \<lceil>\<lambda>s. I s \<and> G s\<rceil> \<le> \<lceil>Q\<rceil> \<Longrightarrow> 
  (x\<acute>=f & G on T S @ t\<^sub>0 DINV I) \<le> Ref \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  unfolding spec_def by (auto simp: H_g_ode_inv)


subsection \<open> Examples \<close>


subsubsection \<open> Thermostat \<close>

abbreviation temp_vec_field :: "real \<Rightarrow> real \<Rightarrow> real^4 \<Rightarrow> real^4" ("f")
  where "f a L s \<equiv> (\<chi> i. if i = 2 then 1 else (if i = 1 then - a * (s$1 - L) else 0))"

abbreviation temp_flow :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real^4 \<Rightarrow> real^4" ("\<phi>")
  where "\<phi> a L \<tau> s \<equiv> (\<chi> i. if i = 1 then - exp(-a * \<tau>) * (L - s$1) + L else 
  (if i = 2 then \<tau> + s$2 else s$i))"

lemma norm_diff_temp_dyn: "0 < a \<Longrightarrow> \<parallel>f a L s\<^sub>1 - f a L s\<^sub>2\<parallel> = \<bar>a\<bar> * \<bar>s\<^sub>1$1 - s\<^sub>2$1\<bar>"
proof(simp add: norm_vec_def L2_set_def, unfold UNIV_4, simp)
  assume a1: "0 < a"
  have f2: "\<And>r ra. \<bar>(r::real) + - ra\<bar> = \<bar>ra + - r\<bar>"
    by (metis abs_minus_commute minus_real_def)
  have "\<And>r ra rb. (r::real) * ra + - (r * rb) = r * (ra + - rb)"
    by (metis minus_real_def right_diff_distrib)
  hence "\<bar>a * (s\<^sub>1$1 + - L) + - (a * (s\<^sub>2$1 + - L))\<bar> = a * \<bar>s\<^sub>1$1 + - s\<^sub>2$1\<bar>"
    using a1 by (simp add: abs_mult)
  thus "\<bar>a * (s\<^sub>2$1 - L) - a * (s\<^sub>1$1 - L)\<bar> = a * \<bar>s\<^sub>1$1 - s\<^sub>2$1\<bar>"
    using f2 minus_real_def by presburger
qed

lemma local_lipschitz_temp_dyn:
  assumes "0 < (a::real)"
  shows "local_lipschitz UNIV UNIV (\<lambda>t::real. f a L)"
  apply(unfold local_lipschitz_def lipschitz_on_def dist_norm)
  apply(clarsimp, rule_tac x=1 in exI, clarsimp, rule_tac x=a in exI)
  using assms apply(simp_all add: norm_diff_temp_dyn)
  apply(simp add: norm_vec_def L2_set_def, unfold UNIV_4, clarsimp)
  unfolding real_sqrt_abs[symmetric] by (rule real_le_lsqrt) auto

lemma local_flow_temp: "a > 0 \<Longrightarrow> local_flow (f a L) UNIV UNIV (\<phi> a L)"
  by (unfold_locales, auto intro!: poly_derivatives local_lipschitz_temp_dyn 
      simp: forall_4 vec_eq_iff)

lemma temp_dyn_down_real_arith:
  assumes "a > 0" and Thyps: "0 < Tmin" "Tmin \<le> T" "T \<le> Tmax"
    and thyps: "0 \<le> (\<tau>::real)" "\<forall>\<tau>\<in>{0..\<tau>}. \<tau> \<le> - (ln (Tmin / T) / a) "
  shows "Tmin \<le> exp (-a * \<tau>) * T" and "exp (-a * \<tau>) * T \<le> Tmax"
proof-
  have "0 \<le> \<tau> \<and> \<tau> \<le> - (ln (Tmin / T) / a)"
    using thyps by auto
  hence "ln (Tmin / T) \<le> - a * \<tau> \<and> - a * \<tau> \<le> 0"
    using assms(1) divide_le_cancel by fastforce
  also have "Tmin / T > 0"
    using Thyps by auto
  ultimately have obs: "Tmin / T \<le> exp (-a * \<tau>)" "exp (-a * \<tau>) \<le> 1"
    using exp_ln exp_le_one_iff by (metis exp_less_cancel_iff not_less, simp)
  thus "Tmin \<le> exp (-a * \<tau>) * T"
    using Thyps by (simp add: pos_divide_le_eq)
  show "exp (-a * \<tau>) * T \<le> Tmax"
    using Thyps mult_left_le_one_le[OF _ exp_ge_zero obs(2), of T] 
      less_eq_real_def order_trans_rules(23) by blast
qed

lemma temp_dyn_up_real_arith:
  assumes "a > 0" and Thyps: "Tmin \<le> T" "T \<le> Tmax" "Tmax < (L::real)"
    and thyps: "0 \<le> \<tau>" "\<forall>\<tau>\<in>{0..\<tau>}. \<tau> \<le> - (ln ((L - Tmax) / (L - T)) / a) "
  shows "L - Tmax \<le> exp (-(a * \<tau>)) * (L - T)" 
    and "L - exp (-(a * \<tau>)) * (L - T) \<le> Tmax" 
    and "Tmin \<le> L - exp (-(a * \<tau>)) * (L - T)"
proof-
  have "0 \<le> \<tau> \<and> \<tau> \<le> - (ln ((L - Tmax) / (L - T)) / a)"
    using thyps by auto
  hence "ln ((L - Tmax) / (L - T)) \<le> - a * \<tau> \<and> - a * \<tau> \<le> 0"
    using assms(1) divide_le_cancel by fastforce
  also have "(L - Tmax) / (L - T) > 0"
    using Thyps by auto
  ultimately have "(L - Tmax) / (L - T) \<le> exp (-a * \<tau>) \<and> exp (-a * \<tau>) \<le> 1"
    using exp_ln exp_le_one_iff by (metis exp_less_cancel_iff not_less)
  moreover have "L - T > 0"
    using Thyps by auto
  ultimately have obs: "(L - Tmax) \<le> exp (-a * \<tau>) * (L - T) \<and> exp (-a * \<tau>) * (L - T) \<le> (L - T)"
    by (simp add: pos_divide_le_eq)
  thus "(L - Tmax) \<le> exp (-(a * \<tau>)) * (L - T)"
    by auto
  thus "L - exp (-(a * \<tau>)) * (L - T) \<le> Tmax"
    by auto
  show "Tmin \<le> L - exp (-(a * \<tau>)) * (L - T)"
    using Thyps and obs by auto
qed

lemma R_therm_dyn_down: 
  assumes "a > 0" and "0 \<le> \<tau>" and "0 < Tmin" and "Tmax < L"
  shows "Ref 
    \<lceil>\<lambda>s. s$4 = 0 \<and> Tmin \<le> s$1 \<and> s$1 \<le> Tmax \<and> s$2 = 0 \<and> s$3 = s$1 \<and> (s$4 = 0 \<or> s$4 = 1)\<rceil>
    \<lceil>\<lambda>s. Tmin \<le> s$1 \<and> s$1 \<le> Tmax \<and> (s$4 = 0 \<or> s$4 = 1)\<rceil> \<ge> 
  (x\<acute>=(f a 0) & (\<lambda>s. s$2 \<le> - (ln (Tmin/s$3))/a) on {0..\<tau>} UNIV @ 0)"
  apply(rule local_flow.R_g_ode_ivl[OF local_flow_temp])
  using assms temp_dyn_down_real_arith[OF assms(1,3), of _ Tmax] by auto

lemma R_therm_dyn_up: 
  assumes "a > 0" and "0 \<le> \<tau>" and "0 < Tmin" and "Tmax < L"
  shows "Ref 
    \<lceil>\<lambda>s. s$4 \<noteq> 0 \<and> Tmin \<le> s$1 \<and> s$1 \<le> Tmax \<and> s$2 = 0 \<and> s$3 = s$1 \<and> (s$4 = 0 \<or> s$4 = 1)\<rceil>
    \<lceil>\<lambda>s. Tmin \<le> s$1 \<and> s$1 \<le> Tmax \<and> (s$4 = 0 \<or> s$4 = 1)\<rceil> \<ge> 
  (x\<acute>=f a L & \<lambda>s. s$2 \<le> - ln ((L - Tmax) / (L - s$3)) / a on {0..\<tau>} UNIV @ 0)"
  apply(rule local_flow.R_g_ode_ivl[OF local_flow_temp])
  using assms temp_dyn_up_real_arith[OF assms(1) _ _ assms(4), of Tmin] by auto

lemma R_therm_dyn:
  assumes "a > 0" and "0 \<le> \<tau>" and "0 < Tmin" and "Tmax < L"
  shows "Ref 
    \<lceil>\<lambda>s. Tmin \<le> s$1 \<and> s$1 \<le> Tmax \<and> s$2 = 0 \<and> s$3 = s$1 \<and> (s$4 = 0 \<or> s$4 = 1)\<rceil>
    \<lceil>\<lambda>s. Tmin \<le> s$1 \<and> s$1 \<le> Tmax \<and> (s$4 = 0 \<or> s$4 = 1)\<rceil> \<ge> 
  (IF (\<lambda>s. s$4 = 0) THEN (x\<acute>=(f a 0) & (\<lambda>s. s$2 \<le> - (ln (Tmin/s$3))/a) on {0..\<tau>} UNIV @ 0) 
  ELSE (x\<acute>=(f a L) & (\<lambda>s. s$2 \<le> - (ln ((L-Tmax)/(L-s$3)))/a) on {0..\<tau>} UNIV @ 0))"
  apply(rule order_trans)
   apply(rule R_cond_mono)
  apply(rule R_therm_dyn_down[OF assms])
  apply(rule R_therm_dyn_up[OF assms])
  by (rule R_cond)

lemma R_therm_assign1:
  "Ref 
    \<lceil>\<lambda>s::real^4. Tmin \<le> s$1 \<and> s$1 \<le> Tmax \<and> (s$4 = 0 \<or> s$4 = 1)\<rceil> 
    \<lceil>\<lambda>s. Tmin \<le> s$1 \<and> s$1 \<le> Tmax \<and> (s$4 = 0 \<or> s$4 = 1) \<and> s$2 = 0\<rceil> \<ge> (2 ::= (\<lambda>s. 0))"
  by (auto simp: R_assign_rule)

lemma R_therm_assign2:
  "Ref 
    \<lceil>\<lambda>s::real^4. Tmin \<le> s$1 \<and> s$1 \<le> Tmax \<and> (s$4 = 0 \<or> s$4 = 1) \<and> s$2 = 0\<rceil>
    \<lceil>\<lambda>s. Tmin \<le> s$1 \<and> s$1 \<le> Tmax \<and> (s$4 = 0 \<or> s$4 = 1) \<and> s$2 = 0 \<and> s$3 = s$1\<rceil> \<ge> (3 ::= (\<lambda>s. s$1))"
  by (auto simp: R_assign_rule)

lemma R_therm_ctrl:
  "Ref 
    \<lceil>\<lambda>s::real^4. Tmin \<le> s$1 \<and> s$1 \<le> Tmax \<and> (s$4 = 0 \<or> s$4 = 1)\<rceil> 
    \<lceil>\<lambda>s. Tmin \<le> s$1 \<and> s$1 \<le> Tmax \<and> s$2 = 0 \<and> s$3 = s$1 \<and> (s$4 = 0 \<or> s$4 = 1)\<rceil> \<ge>
  (2 ::= (\<lambda>s. 0));(3 ::= (\<lambda>s. s$1));
  (IF (\<lambda>s. s$4 = 0 \<and> s$3 \<le> Tmin + 1) THEN (4 ::= (\<lambda>s.1)) ELSE 
  (IF (\<lambda>s. s$4 = 1 \<and> s$3 \<ge> Tmax - 1) THEN (4 ::= (\<lambda>s.0)) ELSE skip))"
  apply(rule R_comp_rule)+
    apply(rule R_therm_assign1)
   apply(rule R_therm_assign2)
  apply(rule order_trans)
   apply(rule R_cond_mono)
    apply(rule R_assign_rule) defer
    apply(rule R_cond_mono)
     apply(rule R_assign_rule) defer
     apply(rule R_skip) defer
     apply(rule order_trans)
      apply(rule R_cond_mono)
       apply force
  by (rule R_cond)+ auto

lemma R_therm_loop: "Ref \<lceil>\<lambda>s. Tmin \<le> s$1 \<and> s$1 \<le> Tmax \<and> s$4 = 0\<rceil> \<lceil>\<lambda>s. Tmin \<le> s$1 \<and> s$1 \<le> Tmax\<rceil> \<ge> 
  (LOOP 
    Ref 
      \<lceil>\<lambda>s. Tmin \<le> s$1 \<and> s$1 \<le> Tmax \<and> (s$4 = 0 \<or> s$4 = 1)\<rceil> 
      \<lceil>\<lambda>s. Tmin \<le> s$1 \<and> s$1 \<le> Tmax \<and> s$2 = 0 \<and> s$3 = s$1 \<and> (s$4 = 0 \<or> s$4 = 1)\<rceil>;
    Ref 
      \<lceil>\<lambda>s. Tmin \<le> s$1 \<and> s$1 \<le> Tmax \<and> s$2 = 0 \<and> s$3 = s$1 \<and> (s$4 = 0 \<or> s$4 = 1)\<rceil>
      \<lceil>\<lambda>s. Tmin \<le> s$1 \<and> s$1 \<le> Tmax \<and> (s$4 = 0 \<or> s$4 = 1)\<rceil>
  INV (\<lambda>s. Tmin \<le>s$1 \<and> s$1 \<le> Tmax \<and> (s$4 = 0 \<or> s$4 = 1)))"
  by (intro R_loop R_comp, simp_all)

lemma R_thermostat: 
  assumes "a > 0" and "0 \<le> \<tau>" and "0 < Tmin" and "Tmax < L"
  shows "Ref \<lceil>\<lambda>s. Tmin \<le> s$1 \<and> s$1 \<le> Tmax \<and> s$4 = 0\<rceil> \<lceil>\<lambda>s. Tmin \<le> s$1 \<and> s$1 \<le> Tmax\<rceil> \<ge> 
  (LOOP 
    \<comment> \<open>control\<close>
    ((2 ::= (\<lambda>s. 0));(3 ::= (\<lambda>s. s$1));
    (IF (\<lambda>s. s$4 = 0 \<and> s$3 \<le> Tmin + 1) THEN (4 ::= (\<lambda>s.1)) ELSE 
    (IF (\<lambda>s. s$4 = 1 \<and> s$3 \<ge> Tmax - 1) THEN (4 ::= (\<lambda>s.0)) ELSE skip));
    \<comment> \<open>dynamics\<close>
    (IF (\<lambda>s. s$4 = 0) THEN (x\<acute>=(f a 0) & (\<lambda>s. s$2 \<le> - (ln (Tmin/s$3))/a) on {0..\<tau>} UNIV @ 0) 
    ELSE (x\<acute>=(f a L) & (\<lambda>s. s$2 \<le> - (ln ((L-Tmax)/(L-s$3)))/a) on {0..\<tau>} UNIV @ 0)) )
  INV (\<lambda>s. Tmin \<le>s$1 \<and> s$1 \<le> Tmax \<and> (s$4 = 0 \<or> s$4 = 1)))"
  apply(rule order_trans[OF _ R_therm_loop])
   apply(rule R_loop_mono)
    apply(rule R_comp_mono)
     apply(rule R_therm_ctrl)
  by (rule R_therm_dyn[OF assms])

no_notation temp_vec_field ("f")
        and temp_flow ("\<phi>")


subsubsection \<open> Water tank \<close>  \<comment> \<open>Variation of Hespanha and \cite{Alur et. all, 1995}\<close>

abbreviation water_vec_field :: "real \<Rightarrow> real \<Rightarrow> real^4 \<Rightarrow> real^4" ("f")
  where "f c\<^sub>i c\<^sub>o s \<equiv> (\<chi> i. if i = 2 then 1 else (if i = 1 then c\<^sub>i - c\<^sub>o else 0))"

abbreviation water_flow :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real^4 \<Rightarrow> real^4" ("\<phi>")
  where "\<phi> c\<^sub>i c\<^sub>o \<tau> s \<equiv> (\<chi> i. if i = 1 then (c\<^sub>i - c\<^sub>o) * \<tau> + s$1 else 
  (if i = 2 then \<tau> + s$2 else s$i))"

lemma water_tank_diff_inv:
  "0 \<le> \<tau> \<Longrightarrow> diff_invariant (\<lambda>s. s$1 = (c\<^sub>i - (c\<^sub>o::real)) \<cdot> s$2 + s$4 \<and> 0 \<le> s$2 \<and> 
    Hmin \<le> s$4 \<and> s$4 \<le> Hmax \<and> (s$3 =0 \<or> s$3 = 1)) (f c\<^sub>i c\<^sub>o) {0..\<tau>} UNIV 0 G"
  apply(intro diff_invariant_conj_rule)
      apply(force intro!: poly_derivatives diff_invariant_rules)
     apply(rule_tac \<nu>'="\<lambda>t. 0" and \<mu>'="\<lambda>t. 1" in diff_invariant_leq_rule, simp_all)
    apply(rule_tac \<nu>'="\<lambda>t. 0" and \<mu>'="\<lambda>t. 0" in diff_invariant_leq_rule, simp_all)
    apply(force intro!: poly_derivatives)+
  by (auto intro!: poly_derivatives diff_invariant_rules)

lemma water_tank_inv_arith1:
  assumes "0 \<le> (\<tau>::real)" and "c\<^sub>o < c\<^sub>i" and b: "Hmin \<le> y\<^sub>0" and g: "\<tau> \<le> (Hmax - y\<^sub>0) / (c\<^sub>i - c\<^sub>o)"
  shows "Hmin \<le> (c\<^sub>i - c\<^sub>o) \<cdot> \<tau> + y\<^sub>0" and "(c\<^sub>i - c\<^sub>o) \<cdot> \<tau> + y\<^sub>0 \<le> Hmax"
proof-
  have "(c\<^sub>i - c\<^sub>o) \<cdot> \<tau> \<le> (Hmax - y\<^sub>0)"
    using g assms(2,3) by (metis diff_gt_0_iff_gt mult.commute pos_le_divide_eq) 
  thus "(c\<^sub>i - c\<^sub>o) \<cdot> \<tau> + y\<^sub>0 \<le> Hmax"
    by auto
  show "Hmin \<le> (c\<^sub>i - c\<^sub>o) \<cdot> \<tau> + y\<^sub>0"
    using b assms(1,2) by (metis add.commute add_increasing2 diff_ge_0_iff_ge 
        less_eq_real_def mult_nonneg_nonneg) 
qed

lemma water_tank_inv_arith2:
  assumes "0 \<le> (\<tau>::real)" and "0 < c\<^sub>o" and b: "y\<^sub>0 \<le> Hmax" and g: "\<tau> \<le> (y\<^sub>0 - Hmin) / c\<^sub>o"
  shows "Hmin \<le> y\<^sub>0 - c\<^sub>o \<cdot> \<tau>" and "y\<^sub>0 - c\<^sub>o \<cdot> \<tau> \<le> Hmax"
proof-
  have "\<tau> \<cdot> c\<^sub>o \<le> y\<^sub>0 - Hmin"
    using g \<open>0 < c\<^sub>o\<close> by (metis pos_le_divide_eq) 
  thus "Hmin \<le> y\<^sub>0 - c\<^sub>o \<cdot> \<tau>"
    by (auto simp: mult.commute)
  show "y\<^sub>0 - c\<^sub>o \<cdot> \<tau> \<le> Hmax" 
    using b assms(1,2) by (smt linordered_field_class.sign_simps(39) mult_less_cancel_right) 
qed



lemma water_tank_inv:
  assumes "0 \<le> \<tau>" and "0 < c\<^sub>o" and "c\<^sub>o < c\<^sub>i"
  shows "Ref \<lceil>\<lambda>s. Hmin < s$1 \<and> s$1 < Hmax \<and> s$3 = 1\<rceil> \<lceil>\<lambda>s. Hmin \<le> s$1 \<and> s$1 \<le> Hmax\<rceil> \<ge>
  (LOOP 
    \<comment> \<open>control\<close>
    ((2 ::=(\<lambda>s.0));(4 ::=(\<lambda>s. s$1));
    (IF (\<lambda>s. s$3 = 0 \<and> s$4 \<le> Hmin + 1) THEN (3 ::= (\<lambda>s.1)) ELSE 
    (IF (\<lambda>s. s$3 = 1 \<and> s$4 \<ge> Hmax - 1) THEN (3 ::= (\<lambda>s.0)) ELSE skip));
    \<comment> \<open>dynamics\<close>
    (IF (\<lambda>s. s$3 = 0) THEN 
      (x\<acute>=(f c\<^sub>i c\<^sub>o) & (\<lambda>s. s$2 \<le> (Hmax - s$4)/(c\<^sub>i - c\<^sub>o)) on {0..\<tau>} UNIV @ 0
       DINV (\<lambda>s. s$1 = ((c\<^sub>i - c\<^sub>o)) * s$2 + s$4 \<and> s$2 \<ge> 0 \<and> Hmin \<le> s$4 \<and> s$4 \<le> Hmax \<and> (s$3 =0 \<or> s$3 = 1))) 
     ELSE 
      (x\<acute>=(f 0 c\<^sub>o) & (\<lambda>s. s$2 \<le> (s$4 - Hmin)/c\<^sub>o) on {0..\<tau>} UNIV @ 0
       DINV (\<lambda>s. s$1 = (- c\<^sub>o) * s$2 + s$4 \<and> s$2 \<ge> 0 \<and> Hmin \<le> s$4 \<and> s$4 \<le> Hmax \<and> (s$3 =0 \<or> s$3 = 1)))) )
  INV (\<lambda>s. Hmin \<le> s$1 \<and> s$1 \<le> Hmax \<and> (s$3 =0 \<or> s$3 = 1)))" (is "LOOP (?ctrl;?dyn) INV ?I \<le> ?ref")
proof-
  have "(IF (\<lambda>s. s$3 = 1 \<and> s$4 \<ge> Hmax - 1) THEN (3 ::= (\<lambda>s.0)) ELSE skip) \<le> 
  IF (\<lambda>s. s$3 = 1 \<and> s$4 \<ge> Hmax - 1) THEN (3 ::= (\<lambda>s.0)) ELSE skip"
    sorry
  have "(IF (\<lambda>s. s$3 = 0 \<and> s$4 \<le> Hmin + 1) THEN (3 ::= (\<lambda>s.1)) ELSE 
      (IF (\<lambda>s. s$3 = 1 \<and> s$4 \<ge> Hmax - 1) THEN (3 ::= (\<lambda>s.0)) ELSE skip)) \<le>
   Ref \<lceil>\<lambda>s. (Hmin \<le> s$1 \<and> s$1 \<le> Hmax \<and> (s$3 = 0 \<or> s$3 = 1)) \<and> s$2 = 0 \<and> s$4 = s$1\<rceil>
        \<lceil>\<lambda>s. (Hmin \<le> s$1 \<and> s$1 \<le> Hmax \<and> (s$3 = 0 \<or> s$3 = 1)) \<and> s$2 = 0 \<and> s$4 = s$1\<rceil>"
    apply(rule order_trans, rule R_cond_mono, rule R_assign)
    apply(rule order_trans, rule R_cond_mono, rule R_assign, rule R_skip) defer
    apply(rule R_cond)
  have ctrl: "?ctrl \<le> Ref \<lceil>?I\<rceil> \<lceil>\<lambda>s. ?I s \<and> s$2 = 0 \<and> s$4 = s$1\<rceil>"
    apply(rule_tac R="\<lambda>s. ?I s \<and> s$2 = 0 \<and> s$4 = s$1" in R_comp_rule)
     apply(rule_tac R="\<lambda>s. ?I s \<and> s$2 = 0" in R_comp_rule)
      apply(rule R_assign_rule, force)+
    apply(rule R_cond)
    apply(intro R_assign_)
    apply(force intro!: R_comp_mono R_assign_rule)
    apply(auto intro!: R_comp R_cond_mono)
  have pre_inv: "\<lceil>\<lambda>s. Hmin < s$1 \<and> s$1 < Hmax \<and> s$3 = 1\<rceil> \<le> \<lceil>?I\<rceil>"
    by simp
  moreover have inv_pos: "\<lceil>?I\<rceil> \<le> \<lceil>\<lambda>s. Hmin \<le> s$1 \<and> s$1 \<le> Hmax\<rceil>"
    by simp
  moreover have inv_inv: "Ref \<lceil>?I\<rceil> \<lceil>?I\<rceil> \<ge> Ref \<lceil>?I\<rceil> \<lceil>P\<rceil>; (Ref \<lceil>P\<rceil> \<lceil>?I\<rceil>)"
    sorry
  have "?ctrl;?dyn \<le> 
  (Ref \<lceil>\<lambda>s::real^4. Hmin \<le> s$1 \<and> s$1 \<le> Hmax \<and> (s$3 =0 \<or> s$3 = 1)\<rceil> \<lceil>P\<rceil>;
    \<comment> \<open>dynamics\<close>
    (Ref \<lceil>P\<rceil> \<lceil>\<lambda>s. Hmin \<le> s$1 \<and> s$1 \<le> Hmax \<and> (s$3 =0 \<or> s$3 = 1)\<rceil> ) )"
    apply(rule R_comp_mono)
    sorry
  apply(rule H_loopI)
    apply(rule_tac R="\<lambda>s. Hmin \<le> s$1 \<and> s$1 \<le> Hmax \<and> s$2=0 \<and> s$4 = s$1 \<and> (s$3 =0 \<or> s$3 = 1)" in H_comp)
     apply(rule_tac R="\<lambda>s. Hmin \<le> s$1 \<and> s$1 \<le> Hmax \<and> s$2=0 \<and> s$4 = s$1 \<and> (s$3 =0 \<or> s$3 = 1)" in H_comp)
      apply(rule_tac R="\<lambda>s. Hmin \<le> s$1 \<and> s$1 \<le> Hmax \<and> s$2=0 \<and> (s$3 =0 \<or> s$3 = 1)" in H_comp, simp, simp)
     apply(rule H_cond, simp)
     apply(rule H_cond, simp, simp)
    apply(rule H_cond)
     apply(rule H_g_ode_inv)
  using assms water_tank_inv_arith1 apply(force simp: water_tank_diff_inv, simp, clarsimp)
    apply(rule H_g_ode_inv)
  using assms water_tank_diff_inv[of _ 0 c\<^sub>o Hmin] water_tank_inv_arith2 by auto

no_notation water_vec_field ("f")
        and water_flow ("\<phi>")
end