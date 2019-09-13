(*  Title:       Refinement components for Hybrid Systems with relational KAT 
    Author:      Jonathan Julián Huerta y Munive, 2019
    Maintainer:  Jonathan Julián Huerta y Munive <jjhuertaymunive1@sheffield.ac.uk>
*)

section \<open> Refinement components for HS with relational KAT \<close>

text \<open> We prepare refinement laws in the class of Kleene algebra with tests (KAT). 
We use its relational model to derive a refinement component for hybrid programs. 
We provide three methods for refining continuous dynamics of hybrid systems in this 
setting: using flows, solutions, and differential invariants. \<close>

theory rkat2rel
  imports kat2rel

begin


subsection \<open> refinement KAT preparation \<close> 

class rkat = kat +
  fixes Ref :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes spec_def:  "x \<le> Ref p q \<longleftrightarrow> H p x q"

begin (* by Victor Gomes, Georg Struth *)

lemma R1: "H p (Ref p q) q"
  using spec_def by blast

lemma R2: "H p x q \<Longrightarrow> x \<le> Ref p q"
  by (simp add: spec_def)

lemma R_cons: "t p \<le> t p' \<Longrightarrow> t q' \<le> t q \<Longrightarrow> Ref p' q' \<le> Ref p q"
proof -
  assume h1: "t p \<le> t p'" and h2: "t q' \<le> t q"
  have "H p' (Ref p' q') q'"
    by (simp add: R1)
  hence "H p (Ref p' q') q"
    using h1 h2 H_consl H_consr by blast
  thus ?thesis
    by (rule R2)
qed

\<comment> \<open> Abort and skip programs \<close>

lemma R_skip: "1 \<le> Ref p p"
proof -
  have "H p 1 p"
    by (simp add: H_skip)
  thus ?thesis
    by (rule R2)
qed

lemma R_zero_one: "x \<le> Ref 0 1"
proof -
  have "H 0 x 1"
    by (simp add: Hoare_def)
  thus ?thesis
    by (rule R2)
qed

lemma R_one_zero: "Ref 1 0 = 0"
proof -
  have "H 1 (Ref 1 0) 0"
    by (simp add: R1)
  thus ?thesis
    by (simp add: Hoare_def join.le_bot)
qed

\<comment> \<open> Sequential composition \<close>

lemma R_seq: "(Ref p r) \<cdot> (Ref r q) \<le> Ref p q"
proof -
  have "H p (Ref p r) r" and "H r (Ref r q) q"
    by (simp add: R1)+
  hence "H p ((Ref p r) \<cdot> (Ref r q)) q"
    by (rule H_seq)
  thus ?thesis
    by (rule R2)
qed

\<comment> \<open> Conditional statement \<close>

lemma R_cond: "if v then (Ref (t v \<cdot> t p) q) else (Ref (n v \<cdot> t p) q) fi \<le> Ref p q"
proof - 
  have "H (t v \<cdot> t p) (Ref (t v \<cdot> t p) q) q" and "H (n v \<cdot> t p) (Ref (n v \<cdot> t p) q) q"
    by (simp add: R1)+
  hence "H p (if v then (Ref (t v \<cdot> t p) q) else (Ref (n v \<cdot> t p) q) fi) q"
    by (simp add: H_cond n_mult_comm)
 thus ?thesis
    by (rule R2)
qed

\<comment> \<open> While loop \<close>

lemma R_while: "while q do (Ref (t p \<cdot> t q) p) od \<le> Ref p (t p \<cdot> n q)"
proof -
  have "H (t p \<cdot> t q) (Ref (t p \<cdot> t q) p)  p" 
    by (simp_all add: R1)
  hence "H p (while q do (Ref (t p \<cdot> t q) p) od) (t p \<cdot> n q)"
    by (simp add: H_while)
  thus ?thesis
    by (rule R2)
qed

\<comment> \<open> Finite iteration \<close>

lemma R_star: "(Ref i i)\<^sup>\<star> \<le> Ref i i"
proof -
  have "H i (Ref i i) i"
    using R1 by blast
  hence "H i ((Ref i i)\<^sup>\<star>) i"
    using H_star by blast
  thus "Ref i i\<^sup>\<star> \<le> Ref i i"
    by (rule R2)
qed

lemma R_loop: "loop (Ref p p) inv i \<le> Ref p p"
  unfolding loopi_def by (rule R_star)

\<comment> \<open> Invariants \<close>

lemma R_inv: "t p \<le> t i \<Longrightarrow> t i \<le> t q \<Longrightarrow> Ref i i \<le> Ref p q"
  using R_cons by force

end

subsection \<open> Refinement Components \<close>

definition rel_R :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where 
  "rel_R P Q = \<Union>{X. rel_kat.Hoare P X Q}"

interpretation rel_rkat: rkat "(\<union>)" "(;)" Id "{}" "(\<subseteq>)" "(\<subset>)" rtrancl "(\<lambda>X. Id \<inter> - X)" rel_R
  by (standard, auto simp: rel_R_def rel_kat.Hoare_def)

lemma RdL_is_rRKAT: "(\<forall>x. {(x,x)}; R1 \<subseteq> {(x,x)}; R2) = (R1 \<subseteq> R2)" (* Refinement in dL is that of rKAT *)
  by auto

lemma R_skip: "(\<forall>s. P s \<longrightarrow> Q s) \<Longrightarrow> Id \<le> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  by (simp add: rel_rkat.R2 rel_kat_H)

lemma R_assign: "(\<forall>s. P s \<longrightarrow> Q (\<chi> j. ((($) s)(x := (e s))) j)) \<Longrightarrow> (x ::= e) \<le> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  unfolding sH_assign[symmetric] by (rule rel_rkat.R2)

(* MISSING LEFT AND RIGHT RULES FOR ASSIGNMENTS *)

lemma R_comp: "(rel_R \<lceil>P\<rceil> \<lceil>R\<rceil>) ; (rel_R \<lceil>R\<rceil> \<lceil>Q\<rceil>) \<le> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  using rel_rkat.R_seq by blast

lemma R_comp_rule: "X \<le> rel_R \<lceil>P\<rceil> \<lceil>R\<rceil> \<Longrightarrow> Y \<le> rel_R \<lceil>R\<rceil> \<lceil>Q\<rceil> \<Longrightarrow> X; Y \<le> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  unfolding rel_rkat.spec_def by (rule H_comp)

lemmas R_comp_mono = relcomp_mono

lemma R_cond: "(IF B THEN rel_R \<lceil>\<lambda>s. B s \<and> P s\<rceil> \<lceil>Q\<rceil> ELSE rel_R \<lceil>\<lambda>s. \<not> B s \<and> P s\<rceil> \<lceil>Q\<rceil>) \<le> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  using rel_rkat.R_cond[of "\<lceil>B\<rceil>" "\<lceil>P\<rceil>" "\<lceil>Q\<rceil>"] by simp

lemma R_cond_mono: "X \<subseteq> X' \<Longrightarrow> Y \<subseteq> Y' \<Longrightarrow> (IF P THEN X ELSE Y) \<le> IF P THEN X' ELSE Y'"
  by (auto simp: rel_kat.ifthenelse_def)

lemma R_while: "WHILE Q INV I DO (rel_R \<lceil>\<lambda>s. P s \<and> Q s\<rceil> \<lceil>P\<rceil>) \<subseteq> rel_R \<lceil>P\<rceil> \<lceil>\<lambda>s. P s \<and> \<not> Q s\<rceil>"
  unfolding rel_kat.while_inv_def using rel_rkat.R_while[of "\<lceil>Q\<rceil>" "\<lceil>P\<rceil>"] by simp

lemma R_while_mono: "X \<subseteq> X' \<Longrightarrow> (WHILE P INV I DO X) \<subseteq> WHILE P INV I DO X'"
  by (simp add: rel_kat.while_inv_def rel_kat.while_def rel_dioid.mult_isol 
      rel_dioid.mult_isor rel_kleene_algebra.star_iso)

lemma R_loop: "X \<le> rel_R \<lceil>I\<rceil> \<lceil>I\<rceil> \<Longrightarrow> \<lceil>P\<rceil> \<le> \<lceil>I\<rceil> \<Longrightarrow> \<lceil>I\<rceil> \<le> \<lceil>Q\<rceil> \<Longrightarrow> LOOP X INV I \<le> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  unfolding rel_rkat.spec_def using H_loopI by blast

lemma R_loop_mono: "X \<subseteq> X' \<Longrightarrow> LOOP X INV I \<subseteq> LOOP X' INV I"
  unfolding rel_kat.loopi_def by (simp add: rel_kleene_algebra.star_iso)

lemma R_g_evol: 
  fixes \<phi> :: "('a::preorder) \<Rightarrow> 'b \<Rightarrow> 'b"
  shows"(\<forall>s. P s \<longrightarrow> (\<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s))) \<Longrightarrow> 
  (EVOL \<phi> G T) \<le> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  unfolding sH_g_evol[symmetric] rel_rkat.spec_def .

lemma (in local_flow) R_g_ode: "(\<forall>s\<in>S. P s \<longrightarrow> (\<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s))) \<Longrightarrow> 
  (x\<acute>= f & G on T S @ 0) \<le> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  unfolding sH_g_ode[symmetric] by (rule rel_rkat.R2)

(* MISSING LEFT AND RIGHT RULES FOR EVOLUTION COMMANDS *)

lemma (in local_flow) R_g_ode_ivl: 
  "\<tau> \<ge> 0 \<Longrightarrow> \<tau> \<in> T \<Longrightarrow> (\<forall>s\<in>S. P s \<longrightarrow> (\<forall>t\<in>{0..\<tau>}. (\<forall>\<tau>\<in>{0..t}. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s))) \<Longrightarrow> 
  (x\<acute>= f & G on {0..\<tau>} S @ 0) \<le> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  unfolding sH_g_ode_ivl[symmetric] by (rule rel_rkat.R2)

lemma R_g_ode_inv: "diff_invariant I f T S t\<^sub>0 G \<Longrightarrow> \<lceil>P\<rceil> \<le> \<lceil>I\<rceil> \<Longrightarrow> \<lceil>\<lambda>s. I s \<and> G s\<rceil> \<le> \<lceil>Q\<rceil> \<Longrightarrow> 
  (x\<acute>=f & G on T S @ t\<^sub>0 DINV I) \<le> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  unfolding rel_rkat.spec_def by (auto simp: H_g_ode_inv)

subsection \<open> Example \<close>

lemma four_eq_zero: "(4::4) = 0"
  by simp

lemma UNIV_4: "(UNIV::4 set) = {0, 1, 2, 3}"
  apply safe using exhaust_4 four_eq_zero by auto

abbreviation temp_vec_field :: "real \<Rightarrow> real \<Rightarrow> real^4 \<Rightarrow> real^4" ("f")
  where "f a L s \<equiv> (\<chi> i. if i = 1 then 1 else (if i = 0 then - a * (s$0 - L) else 0))"

abbreviation temp_flow :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real^4 \<Rightarrow> real^4" ("\<phi>")
  where "\<phi> a L \<tau> s \<equiv> (\<chi> i. if i = 0 then - exp(-a * \<tau>) * (L - s$0) + L else 
  (if i = 1 then \<tau> + s$1 else (if i = 2 then s$2 else s$3)))"

lemma norm_diff_temp_dyn: "0 < a \<Longrightarrow> \<parallel>f a L s\<^sub>1 - f a L s\<^sub>2\<parallel> = \<bar>a\<bar> * \<bar>s\<^sub>1$0 - s\<^sub>2$0\<bar>"
proof(simp add: norm_vec_def L2_set_def, unfold UNIV_4, simp)
  assume a1: "0 < a"
  have f2: "\<And>r ra. \<bar>(r::real) + - ra\<bar> = \<bar>ra + - r\<bar>"
    by (metis abs_minus_commute minus_real_def)
  have "\<And>r ra rb. (r::real) * ra + - (r * rb) = r * (ra + - rb)"
    by (metis minus_real_def right_diff_distrib)
  hence "\<bar>a * (s\<^sub>1$0 + - L) + - (a * (s\<^sub>2$0 + - L))\<bar> = a * \<bar>s\<^sub>1$0 + - s\<^sub>2$0\<bar>"
    using a1 by (simp add: abs_mult)
  thus "\<bar>a * (s\<^sub>2$0 - L) - a * (s\<^sub>1$0 - L)\<bar> = a * \<bar>s\<^sub>1$0 - s\<^sub>2$0\<bar>"
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
      simp: forall_4 vec_eq_iff four_eq_zero)

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
  shows "rel_R 
    \<lceil>\<lambda>s. s$3 = 0 \<and> Tmin \<le> s$0 \<and> s$0 \<le> Tmax \<and> s$1 = 0 \<and> s$2 = s$0 \<and> (s$3 = 0 \<or> s$3 = 1)\<rceil>
    \<lceil>\<lambda>s. Tmin \<le> s$0 \<and> s$0 \<le> Tmax \<and> (s$3 = 0 \<or> s$3 = 1)\<rceil> \<ge> 
  (x\<acute>=(f a 0) & (\<lambda>s. s$1 \<le> - (ln (Tmin/s$2))/a) on {0..\<tau>} UNIV @ 0)"
  apply(rule local_flow.R_g_ode_ivl[OF local_flow_temp])
  using assms temp_dyn_down_real_arith[OF assms(1,3), of _ Tmax] by auto

lemma R_therm_dyn_up: 
  assumes "a > 0" and "0 \<le> \<tau>" and "0 < Tmin" and "Tmax < L"
  shows "rel_R 
    \<lceil>\<lambda>s. s$3 \<noteq> 0 \<and> Tmin \<le> s$0 \<and> s$0 \<le> Tmax \<and> s$1 = 0 \<and> s$2 = s$0 \<and> (s$3 = 0 \<or> s$3 = 1)\<rceil>
    \<lceil>\<lambda>s. Tmin \<le> s$0 \<and> s$0 \<le> Tmax \<and> (s$3 = 0 \<or> s$3 = 1)\<rceil> \<ge> 
  (x\<acute>=f a L & \<lambda>s. s$1 \<le> - ln ((L - Tmax) / (L - s$2)) / a on {0..\<tau>} UNIV @ 0)"
  apply(rule local_flow.R_g_ode_ivl[OF local_flow_temp])
  using assms temp_dyn_up_real_arith[OF assms(1) _ _ assms(4), of Tmin] by auto

lemma R_therm_dyn:
  assumes "a > 0" and "0 \<le> \<tau>" and "0 < Tmin" and "Tmax < L"
  shows "rel_R 
    \<lceil>\<lambda>s. Tmin \<le> s$0 \<and> s$0 \<le> Tmax \<and> s$1 = 0 \<and> s$2 = s$0 \<and> (s$3 = 0 \<or> s$3 = 1)\<rceil>
    \<lceil>\<lambda>s. Tmin \<le> s$0 \<and> s$0 \<le> Tmax \<and> (s$3 = 0 \<or> s$3 = 1)\<rceil> \<ge> 
  (IF (\<lambda>s. s$3 = 0) THEN (x\<acute>=(f a 0) & (\<lambda>s. s$1 \<le> - (ln (Tmin/s$2))/a) on {0..\<tau>} UNIV @ 0) 
  ELSE (x\<acute>=(f a L) & (\<lambda>s. s$1 \<le> - (ln ((L-Tmax)/(L-s$2)))/a) on {0..\<tau>} UNIV @ 0))"
  apply(rule order_trans)
   apply(rule R_cond_mono)
  apply(rule R_therm_dyn_down[OF assms])
  apply(rule R_therm_dyn_up[OF assms])
  by (rule R_cond)

lemma R_therm_assign1:
  "rel_R 
    \<lceil>\<lambda>s::real^4. Tmin \<le> s$0 \<and> s$0 \<le> Tmax \<and> (s$3 = 0 \<or> s$3 = 1)\<rceil> 
    \<lceil>\<lambda>s. Tmin \<le> s$0 \<and> s$0 \<le> Tmax \<and> (s$3 = 0 \<or> s$3 = 1) \<and> s$1 = 0\<rceil> \<ge> (1 ::= (\<lambda>s. 0))"
  by (auto simp: R_assign)

lemma R_therm_assign2:
  "rel_R 
    \<lceil>\<lambda>s::real^4. Tmin \<le> s $ 0 \<and> s $ 0 \<le> Tmax \<and> (s $ 3 = 0 \<or> s $ 3 = 1) \<and> s $ 1 = 0\<rceil>
    \<lceil>\<lambda>s. Tmin \<le> s$0 \<and> s$0 \<le> Tmax \<and> (s$3 = 0 \<or> s$3 = 1) \<and> s$1 = 0 \<and> s$2 = s$0\<rceil> \<ge> (2 ::= (\<lambda>s. s$0))"
  by (auto simp: R_assign)

lemma R_therm_ctrl:
  "rel_R 
    \<lceil>\<lambda>s::real^4. Tmin \<le> s$0 \<and> s$0 \<le> Tmax \<and> (s$3 = 0 \<or> s$3 = 1)\<rceil> 
    \<lceil>\<lambda>s. Tmin \<le> s$0 \<and> s$0 \<le> Tmax \<and> s$1 = 0 \<and> s$2 = s$0 \<and> (s$3 = 0 \<or> s$3 = 1)\<rceil> \<ge>
  (1 ::= (\<lambda>s. 0));(2 ::= (\<lambda>s. s$0));
  (IF (\<lambda>s. s$3 = 0 \<and> s$2 \<le> Tmin + 1) THEN (3 ::= (\<lambda>s.1)) ELSE 
  (IF (\<lambda>s. s$3 = 1 \<and> s$2 \<ge> Tmax - 1) THEN (3 ::= (\<lambda>s.0)) ELSE skip))"
  apply(rule R_comp_rule)+
    apply(rule R_therm_assign1)
   apply(rule R_therm_assign2)
  apply(rule order_trans)
   apply(rule R_cond_mono)
    apply(rule R_assign) defer
    apply(rule R_cond_mono)
     apply(rule R_assign) defer
     apply(rule R_skip) defer
     apply(rule order_trans)
      apply(rule R_cond_mono)
       apply force
  by (rule R_cond)+ auto

lemma R_therm_loop: "rel_R \<lceil>\<lambda>s. Tmin \<le> s$0 \<and> s$0 \<le> Tmax \<and> s$3 = 0\<rceil> \<lceil>\<lambda>s. Tmin \<le> s$0 \<and> s$0 \<le> Tmax\<rceil> \<ge> 
  (LOOP 
    rel_R 
      \<lceil>\<lambda>s. Tmin \<le> s$0 \<and> s$0 \<le> Tmax \<and> (s$3 = 0 \<or> s$3 = 1)\<rceil> 
      \<lceil>\<lambda>s. Tmin \<le> s$0 \<and> s$0 \<le> Tmax \<and> s$1 = 0 \<and> s$2 = s$0 \<and> (s$3 = 0 \<or> s$3 = 1)\<rceil>;
    rel_R 
      \<lceil>\<lambda>s. Tmin \<le> s$0 \<and> s$0 \<le> Tmax \<and> s$1 = 0 \<and> s$2 = s$0 \<and> (s$3 = 0 \<or> s$3 = 1)\<rceil>
      \<lceil>\<lambda>s. Tmin \<le> s$0 \<and> s$0 \<le> Tmax \<and> (s$3 = 0 \<or> s$3 = 1)\<rceil>
  INV (\<lambda>s. Tmin \<le>s$0 \<and> s$0 \<le> Tmax \<and> (s$3 = 0 \<or> s$3 = 1)))"
  by (intro R_loop R_comp, simp_all)

lemma R_thermostat: 
  assumes "a > 0" and "0 \<le> \<tau>" and "0 < Tmin" and "Tmax < L"
  shows "rel_R \<lceil>\<lambda>s. Tmin \<le> s$0 \<and> s$0 \<le> Tmax \<and> s$3 = 0\<rceil> \<lceil>\<lambda>s. Tmin \<le> s$0 \<and> s$0 \<le> Tmax\<rceil> \<ge> 
  (LOOP 
    \<comment> \<open>control\<close>
    ((1 ::= (\<lambda>s. 0));(2 ::= (\<lambda>s. s$0));
    (IF (\<lambda>s. s$3 = 0 \<and> s$2 \<le> Tmin + 1) THEN (3 ::= (\<lambda>s.1)) ELSE 
    (IF (\<lambda>s. s$3 = 1 \<and> s$2 \<ge> Tmax - 1) THEN (3 ::= (\<lambda>s.0)) ELSE skip));
    \<comment> \<open>dynamics\<close>
    (IF (\<lambda>s. s$3 = 0) THEN (x\<acute>=(f a 0) & (\<lambda>s. s$1 \<le> - (ln (Tmin/s$2))/a) on {0..\<tau>} UNIV @ 0) 
    ELSE (x\<acute>=(f a L) & (\<lambda>s. s$1 \<le> - (ln ((L-Tmax)/(L-s$2)))/a) on {0..\<tau>} UNIV @ 0)) )
  INV (\<lambda>s. Tmin \<le>s$0 \<and> s$0 \<le> Tmax \<and> (s$3 = 0 \<or> s$3 = 1)))"
  apply(rule order_trans[OF _ R_therm_loop])
   apply(rule R_loop_mono)
    apply(rule R_comp_mono)
     apply(rule R_therm_ctrl)
  by (rule R_therm_dyn[OF assms])

end