(*  Title:       Examples of hybrid systems verifications
    Author:      Jonathan Julián Huerta y Munive, 2019
    Maintainer:  Jonathan Julián Huerta y Munive <jjhuertaymunive1@sheffield.ac.uk>
*)

subsection \<open> Examples \<close>

text \<open> We prove partial correctness specifications of some hybrid systems with our 
refinement and verification components.\<close>

theory KAT_rKAT_Examples_rel
  imports KAT_rKAT_rVCs_rel

begin


subsubsection \<open>Pendulum\<close>

text \<open> The ODEs @{text "x' t = y t"} and {text "y' t = - x t"} describe the circular motion of 
a mass attached to a string looked from above. We use @{text "s$1"} to represent the x-coordinate
and @{text "s$2"} for the y-coordinate. We prove that this motion remains circular. \<close>

abbreviation fpend :: "real^2 \<Rightarrow> real^2" ("f")
  where "f s \<equiv> (\<chi> i. if i=1 then s$2 else -s$1)"

abbreviation pend_flow :: "real \<Rightarrow> real^2 \<Rightarrow> real^2" ("\<phi>")
  where "\<phi> \<tau> s \<equiv> (\<chi> i. if i = 1 then s$1 \<cdot> cos \<tau> + s$2 \<cdot> sin \<tau> 
  else - s$1 \<cdot> sin \<tau> + s$2 \<cdot> cos \<tau>)"

\<comment> \<open>Verified with annotated dynamics \<close>

lemma pendulum_dyn: "rel_kat.Hoare \<lceil>\<lambda>s. r\<^sup>2 = (s$1)\<^sup>2 + (s$2)\<^sup>2\<rceil> (EVOL \<phi> G T) \<lceil>\<lambda>s. r\<^sup>2 = (s$1)\<^sup>2 + (s$2)\<^sup>2\<rceil>"
  by simp

\<comment> \<open>Verified with differential invariants \<close>

lemma pendulum_inv: "rel_kat.Hoare
  \<lceil>\<lambda>s. r\<^sup>2 = (s$1)\<^sup>2 + (s$2)\<^sup>2\<rceil> (x\<acute>=f & G) \<lceil>\<lambda>s. r\<^sup>2 = (s$1)\<^sup>2 + (s$2)\<^sup>2\<rceil>"
  by (auto intro!: diff_invariant_rules poly_derivatives)

\<comment> \<open>Verified with the flow \<close>

lemma local_flow_pend: "local_flow f UNIV UNIV \<phi>"
  apply(unfold_locales, simp_all add: local_lipschitz_def lipschitz_on_def vec_eq_iff, clarsimp)
  apply(rule_tac x="1" in exI, clarsimp, rule_tac x=1 in exI)
    apply(simp add: dist_norm norm_vec_def L2_set_def power2_commute UNIV_2)
  by (auto simp: forall_2 intro!: poly_derivatives)

lemma pendulum_flow: "rel_kat.Hoare
  \<lceil>\<lambda>s. r\<^sup>2 = (s$1)\<^sup>2 + (s$2)\<^sup>2\<rceil> (x\<acute>=f & G) \<lceil>\<lambda>s. r\<^sup>2 = (s$1)\<^sup>2 + (s$2)\<^sup>2\<rceil>"
  by (simp only: local_flow.sH_g_ode[OF local_flow_pend], simp)

no_notation fpend ("f")
        and pend_flow ("\<phi>")


subsubsection \<open> Bouncing Ball \<close>

text \<open> A ball is dropped from rest at an initial height @{text "h"}. The motion is described with 
the free-fall equations @{text "x' t = v t"} and @{text "v' t = g"} where @{text "g"} is the 
constant acceleration due to gravity. The bounce is modelled with a variable assigntment that 
flips the velocity, thus it is a completely elastic collision with the ground. We use @{text "s$1"} 
to ball's height and @{text "s$2"} for its velocity. We prove that the ball remains above ground
and below its initial resting position. \<close>

abbreviation fball :: "real \<Rightarrow> real^2 \<Rightarrow> real^2" ("f") 
  where "f g s \<equiv> (\<chi> i. if i=1 then s$2 else g)"

abbreviation ball_flow :: "real \<Rightarrow> real \<Rightarrow> real^2 \<Rightarrow> real^2" ("\<phi>") 
  where "\<phi> g \<tau> s \<equiv> (\<chi> i. if i=1 then g \<cdot> \<tau> ^ 2/2 + s$2 \<cdot> \<tau> + s$1 else g \<cdot> \<tau> + s$2)"

\<comment> \<open>Verified with differential invariants \<close>

named_theorems bb_real_arith "real arithmetic properties for the bouncing ball."

lemma [bb_real_arith]: 
  assumes "0 > g" and inv: "2 \<cdot> g \<cdot> x - 2 \<cdot> g \<cdot> h = v \<cdot> v"
  shows "(x::real) \<le> h"
proof-
  have "v \<cdot> v = 2 \<cdot> g \<cdot> x - 2 \<cdot> g \<cdot> h \<and> 0 > g" 
    using inv and \<open>0 > g\<close> by auto
  hence obs:"v \<cdot> v = 2 \<cdot> g \<cdot> (x - h) \<and> 0 > g \<and> v \<cdot> v \<ge> 0" 
    using left_diff_distrib mult.commute by (metis zero_le_square) 
  hence "(v \<cdot> v)/(2 \<cdot> g) = (x - h)" 
    by auto 
  also from obs have "(v \<cdot> v)/(2 \<cdot> g) \<le> 0"
    using divide_nonneg_neg by fastforce 
  ultimately have "h - x \<ge> 0" 
    by linarith
  thus ?thesis by auto
qed

lemma fball_invariant: 
  fixes g h :: real
  defines dinv: "I \<equiv> (\<lambda>s. 2 \<cdot> g \<cdot> s$1 - 2 \<cdot> g \<cdot> h - (s$2 \<cdot> s$2) = 0)"
  shows "diff_invariant I (f g) UNIV UNIV 0 G"
  unfolding dinv apply(rule diff_invariant_rules, simp, simp, clarify)
  by(auto intro!: poly_derivatives)

lemma bouncing_ball_inv: "g < 0 \<Longrightarrow> h \<ge> 0 \<Longrightarrow> rel_kat.Hoare
  \<lceil>\<lambda>s. s$1 = h \<and> s$2 = 0\<rceil>
  (LOOP 
      ((x\<acute>= f g & (\<lambda> s. s$1 \<ge> 0) DINV (\<lambda>s. 2 \<cdot> g \<cdot> s$1 - 2 \<cdot> g \<cdot> h - s$2 \<cdot> s$2 = 0));
       (IF (\<lambda> s. s$1 = 0) THEN (2 ::= (\<lambda>s. - s$2)) ELSE skip)) 
    INV (\<lambda>s. 0 \<le> s$1 \<and> 2 \<cdot> g \<cdot> s$1 = 2 \<cdot> g \<cdot> h + s$2 \<cdot> s$2)
  ) \<lceil>\<lambda>s. 0 \<le> s$1 \<and> s$1 \<le> h\<rceil>"
  apply(rule H_loopI)
    apply(rule H_seq[where R="\<lambda>s. 0 \<le> s$1 \<and> 2 \<cdot> g \<cdot> s$1 = 2 \<cdot> g \<cdot> h + s$2 \<cdot> s$2"])
     apply(rule H_g_ode_inv)
  by (auto simp: bb_real_arith intro!: poly_derivatives diff_invariant_rules)

\<comment> \<open>Verified with annotated dynamics \<close>

lemma [bb_real_arith]:
  assumes invar: "2 \<cdot> g \<cdot> x = 2 \<cdot> g \<cdot> h + v \<cdot> v"
    and pos: "g \<cdot> \<tau>\<^sup>2 / 2 + v \<cdot> \<tau> + (x::real) = 0"
  shows "2 \<cdot> g \<cdot> h + (- (g \<cdot> \<tau>) - v) \<cdot> (- (g \<cdot> \<tau>) - v) = 0"
    and "2 \<cdot> g \<cdot> h + (g \<cdot> \<tau> \<cdot> (g \<cdot> \<tau> + v) + v \<cdot> (g \<cdot> \<tau> + v)) = 0"
proof-
  from pos have "g \<cdot> \<tau>\<^sup>2  + 2 \<cdot> v \<cdot> \<tau> + 2 \<cdot> x = 0" by auto
  then have "g\<^sup>2  \<cdot> \<tau>\<^sup>2  + 2 \<cdot> g \<cdot> v \<cdot> \<tau> + 2 \<cdot> g \<cdot> x = 0"
    by (metis (mono_tags, hide_lams) Groups.mult_ac(1,3) mult_zero_right
        monoid_mult_class.power2_eq_square semiring_class.distrib_left)
  hence "g\<^sup>2 \<cdot> \<tau>\<^sup>2 + 2 \<cdot> g \<cdot> v \<cdot> \<tau> + v\<^sup>2 + 2 \<cdot> g \<cdot> h = 0"
    using invar by (simp add: monoid_mult_class.power2_eq_square) 
  hence obs: "(g \<cdot> \<tau> + v)\<^sup>2 + 2 \<cdot> g \<cdot> h = 0"
    apply(subst power2_sum) by (metis (no_types, hide_lams) Groups.add_ac(2, 3) 
        Groups.mult_ac(2, 3) monoid_mult_class.power2_eq_square nat_distrib(2))
  thus "2 \<cdot> g \<cdot> h + (g \<cdot> \<tau> \<cdot> (g \<cdot> \<tau> + v) + v \<cdot> (g \<cdot> \<tau> + v)) = 0"
    by (simp add: monoid_mult_class.power2_eq_square)
  have  "2 \<cdot> g \<cdot> h + (- ((g \<cdot> \<tau>) + v))\<^sup>2 = 0"
    using obs by (metis Groups.add_ac(2) power2_minus)
  thus "2 \<cdot> g \<cdot> h + (- (g \<cdot> \<tau>) - v) \<cdot> (- (g \<cdot> \<tau>) - v) = 0"
    by (simp add: monoid_mult_class.power2_eq_square)
qed

lemma [bb_real_arith]:
  assumes invar: "2 \<cdot> g \<cdot> x = 2 \<cdot> g \<cdot> h + v \<cdot> v"
  shows "2 \<cdot> g \<cdot> (g \<cdot> \<tau>\<^sup>2 / 2 + v \<cdot> \<tau> + (x::real)) = 
  2 \<cdot> g \<cdot> h + (g \<cdot> \<tau> \<cdot> (g \<cdot> \<tau> + v) + v \<cdot> (g \<cdot> \<tau> + v))" (is "?lhs = ?rhs")
proof-
  have "?lhs = g\<^sup>2 \<cdot> \<tau>\<^sup>2 + 2 \<cdot> g \<cdot> v \<cdot> \<tau> + 2 \<cdot> g \<cdot> x" 
      apply(subst Rat.sign_simps(18))+ 
      by(auto simp: semiring_normalization_rules(29))
    also have "... = g\<^sup>2 \<cdot> \<tau>\<^sup>2 + 2 \<cdot> g \<cdot> v \<cdot> \<tau> + 2 \<cdot> g \<cdot> h + v \<cdot> v" (is "... = ?middle")
      by(subst invar, simp)
    finally have "?lhs = ?middle".
  moreover 
  {have "?rhs = g \<cdot> g \<cdot> (\<tau> \<cdot> \<tau>) + 2 \<cdot> g \<cdot> v \<cdot> \<tau> + 2 \<cdot> g \<cdot> h + v \<cdot> v"
    by (simp add: Groups.mult_ac(2,3) semiring_class.distrib_left)
  also have "... = ?middle"
    by (simp add: semiring_normalization_rules(29))
  finally have "?rhs = ?middle".}
  ultimately show ?thesis by auto
qed

lemma bouncing_ball_dyn: "g < 0 \<Longrightarrow> h \<ge> 0 \<Longrightarrow> rel_kat.Hoare
  \<lceil>\<lambda>s. s$1 = h \<and> s$2 = 0\<rceil>
  (LOOP 
      ((EVOL (\<phi> g) (\<lambda> s. s$1 \<ge> 0) T);
       (IF (\<lambda> s. s$1 = 0) THEN (2 ::= (\<lambda>s. - s$2)) ELSE skip)) 
    INV (\<lambda>s. 0 \<le> s$1 \<and> 2 \<cdot> g \<cdot> s$1 = 2 \<cdot> g \<cdot> h + s$2 \<cdot> s$2)
  ) \<lceil>\<lambda>s. 0 \<le> s$1 \<and> s$1 \<le> h\<rceil>"
  apply(rule H_loopI, rule H_seq[where R="\<lambda>s. 0 \<le> s$1 \<and> 2 \<cdot> g \<cdot> s$1 = 2 \<cdot> g \<cdot> h + s$2 \<cdot> s$2"])
  by (auto simp: bb_real_arith)

\<comment> \<open>Verified with the flow \<close>

lemma local_flow_ball: "local_flow (f g) UNIV UNIV (\<phi> g)"
  apply(unfold_locales, simp_all add: local_lipschitz_def lipschitz_on_def vec_eq_iff, clarsimp)
  apply(rule_tac x="1/2" in exI, clarsimp, rule_tac x=1 in exI)
    apply(simp add: dist_norm norm_vec_def L2_set_def UNIV_2)
  by (auto simp: forall_2 intro!: poly_derivatives)

lemma bouncing_ball_flow: "g < 0 \<Longrightarrow> h \<ge> 0 \<Longrightarrow> rel_kat.Hoare
  \<lceil>\<lambda>s. s$1 = h \<and> s$2 = 0\<rceil>
  (LOOP 
      ((x\<acute>= f g & (\<lambda> s. s$1 \<ge> 0));
       (IF (\<lambda> s. s$1 = 0) THEN (2 ::= (\<lambda>s. - s$2)) ELSE skip)) 
    INV (\<lambda>s. 0 \<le> s$1 \<and> 2 \<cdot> g \<cdot> s$1 = 2 \<cdot> g \<cdot> h + s$2 \<cdot> s$2)
  ) \<lceil>\<lambda>s. 0 \<le> s$1 \<and> s$1 \<le> h\<rceil>"
  apply(rule H_loopI)
    apply(rule H_seq[where R="\<lambda>s. 0 \<le> s$1 \<and> 2 \<cdot> g \<cdot> s$1 = 2 \<cdot> g \<cdot> h + s$2 \<cdot> s$2"])
     apply(subst local_flow.sH_g_ode[OF local_flow_ball])
     apply(force simp: bb_real_arith)
  by (rule H_cond) (auto simp: bb_real_arith)

\<comment> \<open>Refined with annotated dynamics \<close>

lemma R_bb_assign: "g < (0::real) \<Longrightarrow> 0 \<le> h \<Longrightarrow> 
  2 ::= (\<lambda>s. - s$2) \<le> rel_R 
    \<lceil>\<lambda>s. s$1 = 0 \<and> 0 \<le> s$1 \<and> 2 \<cdot> g \<cdot> s$1 = 2 \<cdot> g \<cdot> h + s$2 \<cdot> s$2\<rceil> 
    \<lceil>\<lambda>s. 0 \<le> s$1 \<and> 2 \<cdot> g \<cdot> s$1 = 2 \<cdot> g \<cdot> h + s$2 \<cdot> s$2\<rceil>"
  by (rule R_assign_rule, auto)

lemma R_bouncing_ball_dyn:
  assumes "g < 0" and "h \<ge> 0"
  shows "rel_R \<lceil>\<lambda>s. s$1 = h \<and> s$2 = 0\<rceil> \<lceil>\<lambda>s. 0 \<le> s$1 \<and> s$1 \<le> h\<rceil> \<ge> 
  (LOOP 
      ((EVOL (\<phi> g) (\<lambda> s. s$1 \<ge> 0) T);
       (IF (\<lambda> s. s$1 = 0) THEN (2 ::= (\<lambda>s. - s$2)) ELSE skip)) 
    INV (\<lambda>s. 0 \<le> s$1 \<and> 2 \<cdot> g \<cdot> s$1 = 2 \<cdot> g \<cdot> h + s$2 \<cdot> s$2))"
  apply(rule order_trans)
   apply(rule R_loop_mono) defer
   apply(rule R_loop)
     apply(rule R_seq)
  using assms apply(simp_all, force simp: bb_real_arith)
  apply(rule R_seq_mono) defer
  apply(rule order_trans)
    apply(rule R_cond_mono) defer defer
     apply(rule R_cond) defer
  using R_bb_assign apply force
   apply(rule R_skip, clarsimp)
  by (rule R_g_evol_rule, force simp: bb_real_arith)

no_notation fball ("f")
        and ball_flow ("\<phi>")


subsubsection \<open> Thermostat \<close>

text \<open> A thermostat has a chronometer, a thermometer and a switch to turn on and off a heater. 
At most every @{text "t"} minutes, it sets its chronometer to @{term "0::real"}, it registers 
the room temperature, and it turns the heater on (or off) based on this reading. The temperature 
follows the ODE @{text "T' = - a * (T - U)"} where @{text "U"} is @{text "L \<ge> 0"} when the heater 
is on, and @{text "U = 0"} when it is off. We use @{term "1::4"} to denote the room's temperature, 
@{term "2::4"} is time as measured by the thermostat's chronometer, and @{term "3::4"} is a variable
to save temperature measurements. Finally, @{term "4::5"} states whether the heater is on 
(@{text "s$4 = 1"}) or off (@{text "s$4 = 0"}). We prove that the thermostat keeps the room's 
temperature between @{text "Tmin"} and @{text "Tmax"}. \<close>

abbreviation therm_vec_field :: "real \<Rightarrow> real \<Rightarrow> real^4 \<Rightarrow> real^4" ("f")
  where "f a L s \<equiv> (\<chi> i. if i = 2 then 1 else (if i = 1 then - a * (s$1 - L) else 0))"

abbreviation therm_guard :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real^4 \<Rightarrow> bool" ("G")
  where "G Tmin Tmax a L s \<equiv> (s$2 \<le> - (ln ((L-(if L=0 then Tmin else Tmax))/(L-s$3)))/a)"

abbreviation therm_loop_inv :: "real \<Rightarrow> real \<Rightarrow> real^4 \<Rightarrow> bool" ("I")
  where "I Tmin Tmax s \<equiv> Tmin \<le> s$1 \<and> s$1 \<le> Tmax \<and> (s$4 = 0 \<or> s$4 = 1)"

abbreviation therm_flow :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real^4 \<Rightarrow> real^4" ("\<phi>")
  where "\<phi> a L \<tau> s \<equiv> (\<chi> i. if i = 1 then - exp(-a * \<tau>) * (L - s$1) + L else 
  (if i = 2 then \<tau> + s$2 else s$i))"

\<comment> \<open>Verified with the flow \<close>

lemma norm_diff_therm_dyn: "0 < a \<Longrightarrow> \<parallel>f a L s\<^sub>1 - f a L s\<^sub>2\<parallel> = \<bar>a\<bar> * \<bar>s\<^sub>1$1 - s\<^sub>2$1\<bar>"
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

lemma local_lipschitz_therm_dyn:
  assumes "0 < (a::real)"
  shows "local_lipschitz UNIV UNIV (\<lambda>t::real. f a L)"
  apply(unfold local_lipschitz_def lipschitz_on_def dist_norm)
  apply(clarsimp, rule_tac x=1 in exI, clarsimp, rule_tac x=a in exI)
  using assms apply(simp_all add: norm_diff_therm_dyn)
  apply(simp add: norm_vec_def L2_set_def, unfold UNIV_4, clarsimp)
  unfolding real_sqrt_abs[symmetric] by (rule real_le_lsqrt) auto

lemma local_flow_therm: "a > 0 \<Longrightarrow> local_flow (f a L) UNIV UNIV (\<phi> a L)"
  by (unfold_locales, auto intro!: poly_derivatives local_lipschitz_therm_dyn 
      simp: forall_4 vec_eq_iff)

lemma therm_dyn_down_real_arith:
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

lemma therm_dyn_up_real_arith:
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

lemmas H_g_ode_therm = local_flow.sH_g_ode_ivl[OF local_flow_therm _ UNIV_I]

lemma thermostat_flow: 
  assumes "0 < a" and "0 \<le> \<tau>" and "0 < Tmin" and "Tmax < L"
  shows "rel_kat.Hoare \<lceil>I Tmin Tmax\<rceil>
  (LOOP (
    \<comment> \<open>control\<close>
    (2 ::= (\<lambda>s. 0));
    (3 ::= (\<lambda>s. s$1));
    (IF (\<lambda>s. s$4 = 0 \<and> s$3 \<le> Tmin + 1) THEN 
      (4 ::= (\<lambda>s.1)) 
     ELSE IF (\<lambda>s. s$4 = 1 \<and> s$3 \<ge> Tmax - 1) THEN 
      (4 ::= (\<lambda>s.0)) 
     ELSE skip);
    \<comment> \<open>dynamics\<close>
    (IF (\<lambda>s. s$4 = 0) THEN 
      (x\<acute>= f a 0 & G Tmin Tmax a 0 on {0..\<tau>} UNIV @ 0) 
    ELSE 
      (x\<acute>= f a L & G Tmin Tmax a L on {0..\<tau>} UNIV @ 0))
  ) INV I Tmin Tmax)
  \<lceil>I Tmin Tmax\<rceil>"
  apply(rule H_loopI)
    apply(rule_tac R="\<lambda>s. I Tmin Tmax s \<and> s$2=0 \<and> s$3 = s$1" in H_seq)
     apply(rule_tac R="\<lambda>s. I Tmin Tmax s\<and> s$2=0 \<and> s$3 = s$1" in H_seq)
      apply(rule_tac R="\<lambda>s. I Tmin Tmax s \<and> s$2=0" in H_seq, simp, simp)
      apply(rule H_cond, simp_all add: H_g_ode_therm[OF assms(1,2)])+
  using therm_dyn_up_real_arith[OF assms(1) _ _ assms(4), of Tmin]
    and therm_dyn_down_real_arith[OF assms(1,3), of _ Tmax] by auto

\<comment> \<open>Refined with the flow \<close>

lemma R_therm_dyn_down: 
  assumes "a > 0" and "0 \<le> \<tau>" and "0 < Tmin" and "Tmax < L"
  shows "rel_R \<lceil>\<lambda>s. s$4 = 0 \<and> I Tmin Tmax s \<and> s$2 = 0 \<and> s$3 = s$1\<rceil> \<lceil>I Tmin Tmax\<rceil> \<ge> 
    (x\<acute>= f a 0 & G Tmin Tmax a 0 on {0..\<tau>} UNIV @ 0)"
  apply(rule local_flow.R_g_ode_ivl[OF local_flow_therm])
  using assms therm_dyn_down_real_arith[OF assms(1,3), of _ Tmax] by auto

lemma R_therm_dyn_up: 
  assumes "a > 0" and "0 \<le> \<tau>" and "0 < Tmin" and "Tmax < L"
  shows "rel_R \<lceil>\<lambda>s. s$4 \<noteq> 0 \<and> I Tmin Tmax s \<and> s$2 = 0 \<and> s$3 = s$1\<rceil> \<lceil>I Tmin Tmax\<rceil> \<ge> 
    (x\<acute>= f a L & G Tmin Tmax a L on {0..\<tau>} UNIV @ 0)"
  apply(rule local_flow.R_g_ode_ivl[OF local_flow_therm])
  using assms therm_dyn_up_real_arith[OF assms(1) _ _ assms(4), of Tmin] by auto

lemma R_therm_dyn:
  assumes "a > 0" and "0 \<le> \<tau>" and "0 < Tmin" and "Tmax < L"
  shows "rel_R \<lceil>\<lambda>s. I Tmin Tmax s \<and> s$2 = 0 \<and> s$3 = s$1\<rceil> \<lceil>I Tmin Tmax\<rceil> \<ge> 
  (IF (\<lambda>s. s$4 = 0) THEN 
    (x\<acute>= f a 0 & G Tmin Tmax a 0 on {0..\<tau>} UNIV @ 0) 
  ELSE 
    (x\<acute>= f a L & G Tmin Tmax a L on {0..\<tau>} UNIV @ 0))"
  apply(rule order_trans, rule R_cond_mono)
  using R_therm_dyn_down[OF assms] R_therm_dyn_up[OF assms] by (auto intro!: R_cond)

lemma R_therm_assign1: "rel_R \<lceil>I Tmin Tmax\<rceil> \<lceil>\<lambda>s. I Tmin Tmax s \<and> s$2 = 0\<rceil> \<ge> (2 ::= (\<lambda>s. 0))"
  by (auto simp: R_assign_rule)

lemma R_therm_assign2: 
  "rel_R \<lceil>\<lambda>s. I Tmin Tmax s \<and> s$2 = 0\<rceil> \<lceil>\<lambda>s. I Tmin Tmax s \<and> s$2 = 0 \<and> s$3 = s$1\<rceil> \<ge> (3 ::= (\<lambda>s. s$1))"
  by (auto simp: R_assign_rule)

lemma R_therm_ctrl:
  "rel_R \<lceil>I Tmin Tmax\<rceil> \<lceil>\<lambda>s. I Tmin Tmax s \<and> s$2 = 0 \<and> s$3 = s$1\<rceil> \<ge>
  (2 ::= (\<lambda>s. 0));
  (3 ::= (\<lambda>s. s$1));
  (IF (\<lambda>s. s$4 = 0 \<and> s$3 \<le> Tmin + 1) THEN 
    (4 ::= (\<lambda>s.1)) 
   ELSE IF (\<lambda>s. s$4 = 1 \<and> s$3 \<ge> Tmax - 1) THEN 
    (4 ::= (\<lambda>s.0)) 
   ELSE skip)"
  apply(rule R_seq_rule)+
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

lemma R_therm_loop: "rel_R \<lceil>I Tmin Tmax\<rceil> \<lceil>I Tmin Tmax\<rceil> \<ge> 
  (LOOP 
    rel_R \<lceil>I Tmin Tmax\<rceil> \<lceil>\<lambda>s. I Tmin Tmax s \<and> s$2 = 0 \<and> s$3 = s$1\<rceil>;
    rel_R \<lceil>\<lambda>s. I Tmin Tmax s \<and> s$2 = 0 \<and> s$3 = s$1\<rceil> \<lceil>I Tmin Tmax\<rceil>
  INV I Tmin Tmax)"
  by (intro R_loop R_seq, simp_all)

lemma R_thermostat_flow: 
  assumes "a > 0" and "0 \<le> \<tau>" and "0 < Tmin" and "Tmax < L"
  shows "rel_R \<lceil>I Tmin Tmax\<rceil> \<lceil>I Tmin Tmax\<rceil> \<ge> 
  (LOOP (
    \<comment> \<open>control\<close>
    (2 ::= (\<lambda>s. 0));(3 ::= (\<lambda>s. s$1));
    (IF (\<lambda>s. s$4 = 0 \<and> s$3 \<le> Tmin + 1) THEN 
      (4 ::= (\<lambda>s.1)) 
     ELSE IF (\<lambda>s. s$4 = 1 \<and> s$3 \<ge> Tmax - 1) THEN 
      (4 ::= (\<lambda>s.0)) 
     ELSE skip);
    \<comment> \<open>dynamics\<close>
    (IF (\<lambda>s. s$4 = 0) THEN 
      (x\<acute>= f a 0 & G Tmin Tmax a 0 on {0..\<tau>} UNIV @ 0) 
    ELSE 
      (x\<acute>= f a L & G Tmin Tmax a L on {0..\<tau>} UNIV @ 0))
  ) INV I Tmin Tmax)"
  by (intro order_trans[OF _ R_therm_loop] R_loop_mono 
      R_seq_mono R_therm_ctrl R_therm_dyn[OF assms])

no_notation therm_vec_field ("f")
        and therm_flow ("\<phi>")
        and therm_guard ("G")
        and therm_loop_inv ("I")


subsubsection \<open> Water tank \<close>  \<comment> \<open>Variation of Hespanha and \cite{AlurCHHHNOSY95}\<close>

abbreviation tank_vec_field :: "real \<Rightarrow> real^4 \<Rightarrow> real^4" ("f")
  where "f k s \<equiv> (\<chi> i. if i = 2 then 1 else (if i = 1 then k else 0))"

abbreviation tank_flow :: "real \<Rightarrow> real \<Rightarrow> real^4 \<Rightarrow> real^4" ("\<phi>")
  where "\<phi> k \<tau> s \<equiv> (\<chi> i. if i = 1 then k * \<tau> + s$1 else 
  (if i = 2 then \<tau> + s$2 else s$i))"

abbreviation tank_guard :: "real \<Rightarrow> real \<Rightarrow> real^4 \<Rightarrow> bool" ("G")
  where "G Hm k s \<equiv> s$2 \<le> (Hm - s$3)/k"

abbreviation tank_loop_inv :: "real \<Rightarrow> real \<Rightarrow> real^4 \<Rightarrow> bool" ("I")
  where "I Hmin Hmax s \<equiv> Hmin \<le> s$1 \<and> s$1 \<le> Hmax \<and> (s$4 = 0 \<or> s$4 = 1)"

abbreviation tank_diff_inv :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real^4 \<Rightarrow> bool" ("dI")
  where "dI Hmin Hmax k s \<equiv> s$1 = k \<cdot> s$2 + s$3 \<and> 0 \<le> s$2 \<and> 
    Hmin \<le> s$3 \<and> s$3 \<le> Hmax \<and> (s$4 =0 \<or> s$4 = 1)"

\<comment> \<open>Verified with the flow \<close>

lemma local_flow_tank: "local_flow (f k) UNIV UNIV (\<phi> k)"
  apply (unfold_locales, unfold local_lipschitz_def lipschitz_on_def, simp_all, clarsimp)
  apply(rule_tac x="1/2" in exI, clarsimp, rule_tac x=1 in exI)
  apply(simp add: dist_norm norm_vec_def L2_set_def, unfold UNIV_4)
  by (auto intro!: poly_derivatives simp: vec_eq_iff)

lemma tank_arith:
  assumes "0 \<le> (\<tau>::real)" and "0 < c\<^sub>o" and "c\<^sub>o < c\<^sub>i"
  shows "\<forall>\<tau>\<in>{0..\<tau>}. \<tau> \<le> - ((Hmin - y) / c\<^sub>o) \<Longrightarrow>  Hmin \<le> y - c\<^sub>o * \<tau>"
    and "\<forall>\<tau>\<in>{0..\<tau>}. \<tau> \<le> (Hmax - y) / (c\<^sub>i - c\<^sub>o) \<Longrightarrow>  (c\<^sub>i - c\<^sub>o) * \<tau> + y \<le> Hmax"
    and "Hmin \<le> y \<Longrightarrow> Hmin \<le> (c\<^sub>i - c\<^sub>o) \<cdot> \<tau> + y"
    and "y \<le> Hmax \<Longrightarrow> y - c\<^sub>o \<cdot> \<tau> \<le> Hmax"
  apply(simp_all add: field_simps le_divide_eq assms)
  using assms apply (meson add_mono less_eq_real_def mult_left_mono)
  using assms by (meson add_increasing2 less_eq_real_def mult_nonneg_nonneg) 

lemmas H_g_ode_tank = local_flow.sH_g_ode_ivl[OF local_flow_tank _ UNIV_I]

lemma tank_flow:
  assumes "0 \<le> \<tau>" and "0 < c\<^sub>o" and "c\<^sub>o < c\<^sub>i"
  shows "rel_kat.Hoare \<lceil>I Hmin Hmax\<rceil>
  (LOOP 
    \<comment> \<open>control\<close>
    ((2 ::=(\<lambda>s.0));(3 ::=(\<lambda>s. s$1));
    (IF (\<lambda>s. s$4 = 0 \<and> s$3 \<le> Hmin + 1) THEN (4 ::= (\<lambda>s.1)) ELSE 
    (IF (\<lambda>s. s$4 = 1 \<and> s$3 \<ge> Hmax - 1) THEN (4 ::= (\<lambda>s.0)) ELSE skip));
    \<comment> \<open>dynamics\<close>
    (IF (\<lambda>s. s$4 = 0) THEN (x\<acute>= f (c\<^sub>i-c\<^sub>o) & G Hmax (c\<^sub>i-c\<^sub>o) on {0..\<tau>} UNIV @ 0) 
     ELSE (x\<acute>= f (-c\<^sub>o) & G Hmin (-c\<^sub>o) on {0..\<tau>} UNIV @ 0)) )
  INV I Hmin Hmax) \<lceil>I Hmin Hmax\<rceil>"
  apply(rule H_loopI)
    apply(rule_tac R="\<lambda>s. I Hmin Hmax s \<and> s$2=0 \<and> s$3 = s$1" in H_seq)
     apply(rule_tac R="\<lambda>s. I Hmin Hmax s \<and> s$2=0 \<and> s$3 = s$1" in H_seq)
      apply(rule_tac R="\<lambda>s. I Hmin Hmax s \<and> s$2=0" in H_seq, simp, simp)
     apply(rule H_cond, simp_all add: H_g_ode_tank[OF assms(1)])
  using assms tank_arith[OF _ assms(2,3)] by auto

\<comment> \<open>Verified with differential invariants \<close>

lemma tank_diff_inv:
  "0 \<le> \<tau> \<Longrightarrow> diff_invariant (dI Hmin Hmax k) (f k) {0..\<tau>} UNIV 0 Guard"
  apply(intro diff_invariant_conj_rule)
      apply(force intro!: poly_derivatives diff_invariant_rules)
     apply(rule_tac \<nu>'="\<lambda>t. 0" and \<mu>'="\<lambda>t. 1" in diff_invariant_leq_rule, simp_all)
    apply(rule_tac \<nu>'="\<lambda>t. 0" and \<mu>'="\<lambda>t. 0" in diff_invariant_leq_rule, simp_all)
    apply(force intro!: poly_derivatives)+
  by (auto intro!: poly_derivatives diff_invariant_rules)

lemma tank_inv_arith1:
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

lemma tank_inv_arith2:
  assumes "0 \<le> (\<tau>::real)" and "0 < c\<^sub>o" and b: "y\<^sub>0 \<le> Hmax" and g: "\<tau> \<le> - ((Hmin - y\<^sub>0) / c\<^sub>o)"
  shows "Hmin \<le> y\<^sub>0 - c\<^sub>o \<cdot> \<tau>" and "y\<^sub>0 - c\<^sub>o \<cdot> \<tau> \<le> Hmax"
proof-
  have "\<tau> \<cdot> c\<^sub>o \<le> y\<^sub>0 - Hmin"
    using g \<open>0 < c\<^sub>o\<close> pos_le_minus_divide_eq by fastforce 
  thus "Hmin \<le> y\<^sub>0 - c\<^sub>o \<cdot> \<tau>"
    by (auto simp: mult.commute)
  show "y\<^sub>0 - c\<^sub>o \<cdot> \<tau> \<le> Hmax" 
    using b assms(1,2) by (smt linordered_field_class.sign_simps(39) mult_less_cancel_right) 
qed

lemma tank_inv:
  assumes "0 \<le> \<tau>" and "0 < c\<^sub>o" and "c\<^sub>o < c\<^sub>i"
  shows "rel_kat.Hoare \<lceil>I Hmin Hmax\<rceil>
  (LOOP 
    \<comment> \<open>control\<close>
    ((2 ::=(\<lambda>s.0));(3 ::=(\<lambda>s. s$1));
    (IF (\<lambda>s. s$4 = 0 \<and> s$3 \<le> Hmin + 1) THEN (4 ::= (\<lambda>s.1)) ELSE 
    (IF (\<lambda>s. s$4 = 1 \<and> s$3 \<ge> Hmax - 1) THEN (4 ::= (\<lambda>s.0)) ELSE skip));
    \<comment> \<open>dynamics\<close>
    (IF (\<lambda>s. s$4 = 0) THEN 
      (x\<acute>= f (c\<^sub>i-c\<^sub>o) & G Hmax (c\<^sub>i-c\<^sub>o) on {0..\<tau>} UNIV @ 0 DINV (dI Hmin Hmax (c\<^sub>i-c\<^sub>o))) 
     ELSE 
      (x\<acute>= f (-c\<^sub>o) & G Hmin (-c\<^sub>o) on {0..\<tau>} UNIV @ 0 DINV (dI Hmin Hmax (-c\<^sub>o)))) )
  INV I Hmin Hmax) \<lceil>I Hmin Hmax\<rceil>"
  apply(rule H_loopI)
    apply(rule_tac R="\<lambda>s. I Hmin Hmax s \<and> s$2=0 \<and> s$3 = s$1" in H_seq)
     apply(rule_tac R="\<lambda>s. I Hmin Hmax s \<and> s$2=0 \<and> s$3 = s$1" in H_seq)
      apply(rule_tac R="\<lambda>s. I Hmin Hmax s \<and> s$2=0" in H_seq, simp, simp)
     apply(rule H_cond, simp)
     apply(rule H_cond, simp, simp)
    apply(rule H_cond)
     apply(rule H_g_ode_inv)
  using assms tank_inv_arith1 apply(force simp: tank_diff_inv, simp, clarsimp)
    apply(rule H_g_ode_inv)
  using assms tank_diff_inv[of _ "-c\<^sub>o" Hmin Hmax] tank_inv_arith2 by auto

\<comment> \<open>Refined with differential invariants \<close>

lemma R_tank_inv:
  assumes "0 \<le> \<tau>" and "0 < c\<^sub>o" and "c\<^sub>o < c\<^sub>i"
  shows "rel_R \<lceil>I Hmin Hmax\<rceil> \<lceil>I Hmin Hmax\<rceil> \<ge>
  (LOOP 
    \<comment> \<open>control\<close>
    ((2 ::=(\<lambda>s.0));(3 ::=(\<lambda>s. s$1));
    (IF (\<lambda>s. s$4 = 0 \<and> s$3 \<le> Hmin + 1) THEN (4 ::= (\<lambda>s.1)) ELSE 
    (IF (\<lambda>s. s$4 = 1 \<and> s$3 \<ge> Hmax - 1) THEN (4 ::= (\<lambda>s.0)) ELSE skip));
    \<comment> \<open>dynamics\<close>
    (IF (\<lambda>s. s$4 = 0) THEN 
      (x\<acute>= f (c\<^sub>i-c\<^sub>o) & G Hmax (c\<^sub>i-c\<^sub>o) on {0..\<tau>} UNIV @ 0 DINV (dI Hmin Hmax (c\<^sub>i-c\<^sub>o))) 
     ELSE 
      (x\<acute>= f (-c\<^sub>o) & G Hmin (-c\<^sub>o) on {0..\<tau>} UNIV @ 0 DINV (dI Hmin Hmax (-c\<^sub>o)))) )
  INV I Hmin Hmax)" (is "LOOP (?ctrl;?dyn) INV _ \<le> ?ref")
proof-
  \<comment> \<open>First we refine the control. \<close>
  let ?Icntrl = "\<lambda>s. I Hmin Hmax s \<and> s$2 = 0 \<and> s$3 = s$1"
  and ?cond = "\<lambda>s. s$4 = 0 \<and> s$3 \<le> Hmin + 1"
  have ifbranch1: "4 ::= (\<lambda>s.1) \<le> rel_R \<lceil>\<lambda>s. ?cond s \<and> ?Icntrl s\<rceil> \<lceil>?Icntrl\<rceil>" (is "_ \<le> ?branch1")
    by (rule R_assign_rule, simp)
  have ifbranch2: "(IF (\<lambda>s. s$4 = 1 \<and> s$3 \<ge> Hmax - 1) THEN (4 ::= (\<lambda>s.0)) ELSE skip) \<le> 
    rel_R \<lceil>\<lambda>s. \<not> ?cond s \<and> ?Icntrl s\<rceil> \<lceil>?Icntrl\<rceil>" (is "_ \<le> ?branch2")
    apply(rule order_trans, rule R_cond_mono) defer defer
    by (rule R_cond) (auto intro!: R_assign_rule R_skip)
  have ifthenelse: "(IF ?cond THEN ?branch1 ELSE ?branch2) \<le> rel_R \<lceil>?Icntrl\<rceil> \<lceil>?Icntrl\<rceil>" (is "?ifthenelse \<le> _") 
    by (rule R_cond)
  have "(IF ?cond THEN (4 ::= (\<lambda>s.1)) ELSE (IF (\<lambda>s. s$4 = 1 \<and> s$3 \<ge> Hmax - 1) THEN (4 ::= (\<lambda>s.0)) ELSE skip)) \<le>
   rel_R \<lceil>?Icntrl\<rceil> \<lceil>?Icntrl\<rceil>"
    apply(rule_tac y="?ifthenelse" in order_trans, rule R_cond_mono)
    using ifbranch1 ifbranch2 ifthenelse by auto
  hence ctrl: "?ctrl \<le> rel_R \<lceil>I Hmin Hmax\<rceil> \<lceil>?Icntrl\<rceil>"
    apply(rule_tac R="?Icntrl" in R_seq_rule)
     apply(rule_tac R="\<lambda>s. I Hmin Hmax s \<and> s$2 = 0" in R_seq_rule)
    by (auto intro!: R_assign_rule)
  \<comment> \<open>Then we refine the dynamics. \<close>
  have dynup: "(x\<acute>=f (c\<^sub>i-c\<^sub>o) & G Hmax (c\<^sub>i-c\<^sub>o) on {0..\<tau>} UNIV @ 0 DINV (dI Hmin Hmax (c\<^sub>i-c\<^sub>o))) \<le> 
    rel_R \<lceil>\<lambda>s. s$4 = 0 \<and> ?Icntrl s\<rceil> \<lceil>I Hmin Hmax\<rceil>"
    apply(rule R_g_ode_inv[OF tank_diff_inv[OF assms(1)]])
    using assms by (auto simp: tank_inv_arith1)
  have dyndown: "(x\<acute>=f (-c\<^sub>o) & G Hmin (-c\<^sub>o) on {0..\<tau>} UNIV @ 0 DINV (dI Hmin Hmax (-c\<^sub>o))) \<le> 
    rel_R \<lceil>\<lambda>s. s$4 \<noteq> 0 \<and> ?Icntrl s\<rceil> \<lceil>I Hmin Hmax\<rceil>"
    apply(rule R_g_ode_inv)
    using tank_diff_inv[OF assms(1), of "-c\<^sub>o"] assms
    by (auto simp: tank_inv_arith2)
  have dyn: "?dyn \<le> rel_R \<lceil>?Icntrl\<rceil> \<lceil>I Hmin Hmax\<rceil>"
    apply(rule order_trans, rule R_cond_mono)
    using dynup dyndown by (auto intro!: R_cond)
  \<comment> \<open>Finally we put everything together. \<close>
  have pre_inv: "\<lceil>I Hmin Hmax\<rceil> \<le> \<lceil>I Hmin Hmax\<rceil>"
    by simp
  have inv_pos: "\<lceil>I Hmin Hmax\<rceil> \<le> \<lceil>\<lambda>s. Hmin \<le> s$1 \<and> s$1 \<le> Hmax\<rceil>"
    by simp
  have inv_inv: "rel_R \<lceil>I Hmin Hmax\<rceil> \<lceil>?Icntrl\<rceil>; (rel_R \<lceil>?Icntrl\<rceil> \<lceil>I Hmin Hmax\<rceil>) \<le> rel_R \<lceil>I Hmin Hmax\<rceil> \<lceil>I Hmin Hmax\<rceil>"
    by (rule R_seq)
  have loopref: "LOOP rel_R \<lceil>I Hmin Hmax\<rceil> \<lceil>?Icntrl\<rceil>; (rel_R \<lceil>?Icntrl\<rceil> \<lceil>I Hmin Hmax\<rceil>) INV I Hmin Hmax \<le> ?ref"
    apply(rule R_loop)
    using pre_inv inv_inv inv_pos by auto
  have obs: "?ctrl;?dyn \<le> rel_R \<lceil>I Hmin Hmax\<rceil> \<lceil>?Icntrl\<rceil>; (rel_R \<lceil>?Icntrl\<rceil> \<lceil>I Hmin Hmax\<rceil>)"
    apply(rule R_seq_mono)
    using ctrl dyn by auto
  show "LOOP (?ctrl;?dyn) INV I Hmin Hmax \<le> ?ref"
    by (rule order_trans[OF _ loopref], rule R_loop_mono[OF obs])
qed

no_notation tank_vec_field ("f")
        and tank_flow ("\<phi>")
        and tank_guard ("G")
        and tank_loop_inv ("I")
        and tank_diff_inv ("dI")

end