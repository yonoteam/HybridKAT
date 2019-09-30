(*  Title:       Examples of hybrid systems verifications
    Author:      Jonathan Julián Huerta y Munive, 2019
    Maintainer:  Jonathan Julián Huerta y Munive <jjhuertaymunive1@sheffield.ac.uk>
*)

subsection \<open> Examples \<close>

text \<open> We prove partial correctness specifications of some hybrid systems with our 
refinement and verification components.\<close>

theory KAT_rKAT_Examples_ndfun
  imports KAT_rKAT_rVCs_ndfun

begin

utp_lit_vars

definition vec_lens :: "'i \<Rightarrow> ('a \<Longrightarrow> 'a^'i)" where
[lens_defs]: "vec_lens k = \<lparr> lens_get = (\<lambda> s. vec_nth s k)
                           , lens_put = (\<lambda> s v. (\<chi> j. ((($) s)(k := v)) j)) \<rparr>"

lemma vec_vwb_lens [simp]: "vwb_lens (vec_lens k)"
  apply (unfold_locales)
  apply (simp_all add: vec_lens_def fun_eq_iff)
  using vec_lambda_unique apply fastforce
  done

lemma vec_lens_indep [simp]: "(i \<noteq> j) \<Longrightarrow> (vec_lens i \<bowtie> vec_lens j)"
  by (simp add: lens_indep_vwb_iff, auto simp add: lens_defs)

subsubsection \<open>Pendulum\<close>

abbreviation x :: "real \<Longrightarrow> real^2" where "x \<equiv> vec_lens 1"
abbreviation y :: "real \<Longrightarrow> real^2" where "y \<equiv> vec_lens 2"

text \<open> The ODEs @{text "x' t = y t"} and {text "y' t = - x t"} describe the circular motion of 
a mass attached to a string looked from above. We prove that this motion remains circular. \<close>

abbreviation fpend :: "(real^2) usubst" ("f") 
  where "fpend \<equiv> [x \<mapsto>\<^sub>s y, y \<mapsto>\<^sub>s -x]"

abbreviation pend_flow :: "real \<Rightarrow> (real^2) usubst" ("\<phi>") 
  where "pend_flow \<tau> \<equiv> [x \<mapsto>\<^sub>s x \<cdot> cos \<tau> + y \<cdot> sin \<tau>, y \<mapsto>\<^sub>s - x \<cdot> sin \<tau> + y \<cdot> cos \<tau>]"

\<comment> \<open>Verified with annotated dynamics \<close>

lemma pendulum_dyn: "\<^bold>{r\<^sup>2 = x\<^sup>2 + y\<^sup>2\<^bold>}(EVOL \<phi> G T)\<^bold>{r\<^sup>2 = x\<^sup>2 + y\<^sup>2\<^bold>}"
  by (simp, rel_auto)

\<comment> \<open>Verified with invariants \<close>

lemma pendulum_inv: "\<^bold>{r\<^sup>2 = x\<^sup>2 + y\<^sup>2\<^bold>} (x\<acute>= \<lbrakk>f\<rbrakk>\<^sub>e & G) \<^bold>{r\<^sup>2 = x\<^sup>2 + y\<^sup>2\<^bold>}"
  by (simp, pred_simp, auto intro!: diff_invariant_rules poly_derivatives)
  
\<comment> \<open>Verified by providing solutions \<close>

lemma local_flow_pend: "local_flow \<lbrakk>f\<rbrakk>\<^sub>e UNIV UNIV (\<lambda> t. \<lbrakk>\<phi> t\<rbrakk>\<^sub>e)"
  apply(unfold_locales, simp_all add: local_lipschitz_def lipschitz_on_def vec_eq_iff, clarsimp)
  apply(rule_tac x="1" in exI, clarsimp, rule_tac x=1 in exI, pred_simp)
    apply(simp add: dist_norm norm_vec_def L2_set_def power2_commute UNIV_2)
  by (simp add: forall_2, pred_simp, force intro!: poly_derivatives, pred_simp)

lemma pendulum_flow: "\<^bold>{r\<^sup>2 = x\<^sup>2 + y\<^sup>2\<^bold>} (x\<acute>= \<lbrakk>f\<rbrakk>\<^sub>e & G) \<^bold>{r\<^sup>2 = x\<^sup>2 + y\<^sup>2\<^bold>}"
  by (simp only: local_flow.sH_g_ode[OF local_flow_pend], pred_simp)

no_notation fpend ("f")
        and pend_flow ("\<phi>")


subsubsection \<open> Bouncing Ball \<close>

text \<open> A ball is dropped from rest at an initial height @{text "h"}. The motion is described with 
the free-fall equations @{text "x' t = v t"} and @{text "v' t = g"} where @{text "g"} is the 
constant acceleration due to gravity. The bounce is modelled with a variable assigntment that 
flips the velocity, thus it is a completely elastic collision with the ground. We prove that the 
ball remains above ground and below its initial resting position. \<close>

abbreviation v :: "real \<Longrightarrow> real^2" 
  where "v \<equiv> vec_lens 2"

abbreviation fball :: "real \<Rightarrow> (real, 2) vec \<Rightarrow> (real, 2) vec" ("f") 
  where "fball g \<equiv> \<lbrakk>[x \<mapsto>\<^sub>s v, v \<mapsto>\<^sub>s g]\<rbrakk>\<^sub>e"

abbreviation ball_flow :: "real \<Rightarrow> real \<Rightarrow> (real^2) usubst" ("\<phi>") 
  where "ball_flow g \<tau> \<equiv> [x \<mapsto>\<^sub>s g \<cdot> \<tau> ^ 2/2 + v \<cdot> \<tau> + x,  v \<mapsto>\<^sub>s g \<cdot> \<tau> + v]"

\<comment> \<open>Verified with invariants \<close>

named_theorems bb_real_arith "real arithmetic properties for the bouncing ball."

lemma [bb_real_arith]: 
  fixes x v :: real
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
  defines dinv: "I \<equiv> U(2 \<cdot> \<guillemotleft>g\<guillemotright> \<cdot> x - 2 \<cdot> \<guillemotleft>g\<guillemotright> \<cdot> \<guillemotleft>h\<guillemotright> - (v \<cdot> v) = 0)"
  shows "diff_invariant \<lbrakk>I\<rbrakk>\<^sub>e (f g) UNIV UNIV 0 \<lbrakk>G\<rbrakk>\<^sub>e"
  unfolding dinv apply(pred_simp, rule diff_invariant_rules, simp, simp, clarify)
  by(auto intro!: poly_derivatives)

abbreviation "bb_dinv g h \<equiv> 
  (LOOP
    ((x\<acute>= f g & (x \<ge> 0) DINV (2 \<cdot> g \<cdot> x - 2 \<cdot> g \<cdot> h - v \<cdot> v = 0));
    (IF (v = 0) THEN (v ::= -v) ELSE skip)) 
  INV (0 \<le> x \<and> 2 \<cdot> g \<cdot> x = 2 \<cdot> g \<cdot> h + v \<cdot> v))"

lemma bouncing_ball_inv: "g < 0 \<Longrightarrow> h \<ge> 0 \<Longrightarrow> \<^bold>{x = h \<and> v = 0\<^bold>} bb_dinv g h \<^bold>{0 \<le> x \<and> x \<le> h\<^bold>}"
  apply(rule H_loopI, rule H_seq[where R="U(0 \<le> x \<and> 2 \<cdot> g \<cdot> x = 2 \<cdot> g \<cdot> h + v \<cdot> v)"])
     apply(rule H_g_ode_inv, pred_simp, force intro!: poly_derivatives diff_invariant_rules)
  by (simp_all, rel_auto' simp: bb_real_arith)

\<comment> \<open>Verified with annotated dynamics \<close>

lemma [bb_real_arith]:
  fixes x v :: real
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
  fixes x v :: real
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

abbreviation "bb_evol g h T \<equiv> 
  (LOOP (
    (EVOL (\<phi> g) (x \<ge> 0) T);
    (IF (v = 0) THEN (v ::= -v) ELSE skip)) 
  INV (0 \<le> x \<and> 2 \<cdot> g \<cdot> x = 2 \<cdot> g \<cdot> h + v \<cdot> v))"

lemma bouncing_ball_dyn: 
  assumes "g < 0" and "h \<ge> 0"
  shows "
  \<^bold>{x = h \<and> v = 0\<^bold>} 
    bb_evol g h T 
  \<^bold>{0 \<le> x \<and> x \<le> h\<^bold>}"
  apply(rule H_loopI, rule H_seq[where R="U(0 \<le> x \<and> 2 \<cdot> g \<cdot> x = 2 \<cdot> g \<cdot> h + v \<cdot> v)"])
  using assms by (simp_all, rel_auto' simp: bb_real_arith)

\<comment> \<open>Verified by providing solutions \<close>

lemma local_flow_ball: "local_flow (f g) UNIV UNIV (\<lambda> t. \<lbrakk>\<phi> g t\<rbrakk>\<^sub>e)"
  apply(unfold_locales, simp_all add: local_lipschitz_def lipschitz_on_def vec_eq_iff, clarsimp)
  apply(rule_tac x="1/2" in exI, clarsimp, rule_tac x=1 in exI, pred_simp)
    apply(simp add: dist_norm norm_vec_def L2_set_def UNIV_2)
  by (simp add: forall_2, pred_simp, force intro!: poly_derivatives, pred_simp)

abbreviation "bb_sol g h \<equiv>
  (LOOP (
    (x\<acute>= f g & (x \<ge> 0));
    (IF (v = 0) THEN (v ::= -v) ELSE skip))
  INV (0 \<le> x \<and> 2 \<cdot> g \<cdot> x = 2 \<cdot> g \<cdot> h + v \<cdot> v))"

lemma bouncing_ball_flow: 
  assumes "g < 0" and "h \<ge> 0"
  shows "
  \<^bold>{x = h \<and> v = 0\<^bold>} 
    bb_sol g h 
  \<^bold>{0 \<le> x \<and> x \<le> h\<^bold>}"
  apply(rule H_loopI, rule H_seq[where R="U(0 \<le> x \<and> 2 \<cdot> g \<cdot> x = 2 \<cdot> g \<cdot> h + v \<cdot> v)"])
     apply(subst local_flow.sH_g_ode[OF local_flow_ball])
  using assms by (simp_all, rel_auto' simp: bb_real_arith)

\<comment> \<open>Refined with annotated dynamics \<close>

lemma R_bb_assign: "g < (0::real) \<Longrightarrow> 0 \<le> h \<Longrightarrow> 
  (v ::= - v) \<le> \<^bold>[v = 0 \<and> 0 \<le> x \<and> 2 \<cdot> g \<cdot> x = 2 \<cdot> g \<cdot> h + v \<cdot> v, 0 \<le> x \<and> 2 \<cdot> g \<cdot> x = 2 \<cdot> g \<cdot> h + v \<cdot> v\<^bold>]"
  by (rule R_assign_rule, pred_simp)

lemma R_bouncing_ball_dyn:
  assumes "g < 0" and "h \<ge> 0"
  shows "\<^bold>[x = h \<and> v = 0, 0 \<le> x \<and> x \<le> h\<^bold>] \<ge> bb_evol g h T"
  apply(rule order_trans)
   apply(rule R_loop_mono) defer
   apply(rule R_loop)
     apply(rule R_seq)
  using assms apply(simp, pred_simp)
  using assms apply(simp, pred_simp, force simp: bb_real_arith)
  apply(rule R_seq_mono) defer
  apply(rule order_trans)
    apply(rule R_cond_mono) defer defer
     apply(rule R_cond) defer defer defer
  apply(rule R_bb_assign, simp_all add: assms)
   apply(rule R_skip, pred_simp)
  by (rule R_g_evol_rule, rel_auto' simp: bb_real_arith)

no_notation fball ("f")
        and ball_flow ("\<phi>")


subsubsection \<open> Thermostat \<close>

text \<open> A thermostat has a chronometer, a thermometer and a switch to turn on and off a heater. 
At most every @{text "\<tau>"} minutes, it sets its chronometer to @{term "0::real"}, it registers 
the room temperature, and it turns the heater on (or off) based on this reading. The temperature 
follows the ODE @{text "T' = - a * (T - c)"} where @{text "c = L \<ge> 0"} when the heater 
is on, and @{text "c = 0"} when it is off. We prove that the thermostat keeps the room's 
temperature between @{text "T\<^sub>m"} and @{text "T\<^sub>M"}. \<close>

abbreviation T :: "real \<Longrightarrow> real^4" where "T \<equiv> vec_lens 1"
abbreviation t :: "real \<Longrightarrow> real^4" where "t \<equiv> vec_lens 2"
abbreviation T\<^sub>0 :: "real \<Longrightarrow> real^4" where "T\<^sub>0 \<equiv> vec_lens 3"
abbreviation \<Theta> :: "real \<Longrightarrow> real^4" where "\<Theta> \<equiv> vec_lens 4"

abbreviation ftherm :: "real \<Rightarrow> real \<Rightarrow> (real, 4) vec \<Rightarrow> (real, 4) vec" ("f")
  where "f a c \<equiv> \<lbrakk>[T \<mapsto>\<^sub>s - a * (T - c), t \<mapsto>\<^sub>s 1, T\<^sub>0 \<mapsto>\<^sub>s 0, \<Theta> \<mapsto>\<^sub>s 0]\<rbrakk>\<^sub>e"

abbreviation therm_guard :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real^4) upred" ("G")
  where "G T\<^sub>m T\<^sub>M a L \<equiv> U(t \<le> - (ln ((L-(if L=0 then T\<^sub>m else T\<^sub>M))/(L-T\<^sub>0)))/a)"

no_utp_lift "therm_guard" (0 1 2 3)

abbreviation therm_loop_inv :: "real \<Rightarrow> real \<Rightarrow> (real^4) upred" ("I")
  where "I T\<^sub>m T\<^sub>M \<equiv> U(T\<^sub>m \<le> T \<and> T \<le> T\<^sub>M \<and> (\<Theta> = 0 \<or> \<Theta> = 1))"

no_utp_lift "therm_loop_inv" (0 1)

abbreviation therm_flow :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real^4) usubst" ("\<phi>") 
  where "\<phi> a c \<tau> \<equiv> [T \<mapsto>\<^sub>s - exp(-a * \<tau>) * (c - T) + c, t \<mapsto>\<^sub>s \<tau> + t, T\<^sub>0 \<mapsto>\<^sub>s T\<^sub>0, \<Theta> \<mapsto>\<^sub>s \<Theta>]"

abbreviation therm_ctrl :: "real \<Rightarrow> real \<Rightarrow> (real^4) nd_fun" ("ctrl")
  where "ctrl T\<^sub>m T\<^sub>M \<equiv> 
  (t ::= 0); (T\<^sub>0 ::= T);
  (IF (\<Theta> = 0 \<and> T\<^sub>0 \<le> T\<^sub>m + 1) THEN (\<Theta> ::= 1) ELSE 
   IF (\<Theta> = 1 \<and> T\<^sub>0 \<ge> T\<^sub>M - 1) THEN (\<Theta> ::= 0) ELSE skip)"

abbreviation therm_dyn :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real^4) nd_fun" ("dyn")
  where "dyn T\<^sub>m T\<^sub>M a L \<tau> \<equiv> 
  (IF (\<Theta> = 0) THEN (x\<acute>= f a 0 & G T\<^sub>m T\<^sub>M a 0 on {0..\<tau>} UNIV @ 0) 
   ELSE (x\<acute>= f a L & G T\<^sub>m T\<^sub>M a L on {0..\<tau>} UNIV @ 0))"

abbreviation "therm T\<^sub>m T\<^sub>M a L \<tau> \<equiv> LOOP (ctrl T\<^sub>m T\<^sub>M ; dyn T\<^sub>m T\<^sub>M a L \<tau>) INV (I T\<^sub>m T\<^sub>M)"

\<comment> \<open>Verified by providing solutions \<close>

lemma norm_diff_therm_dyn: "0 < (a::real) \<Longrightarrow> (a \<cdot> (s\<^sub>2$1 - L) - a \<cdot> (s\<^sub>1$1 - L))\<^sup>2
       \<le> (a \<cdot> sqrt ((s\<^sub>1$1 - s\<^sub>2$1)\<^sup>2 + ((s\<^sub>1$2 - s\<^sub>2$2)\<^sup>2 + ((s\<^sub>1$3 - s\<^sub>2$3)\<^sup>2 + (s\<^sub>1$4 - s\<^sub>2$4)\<^sup>2))))\<^sup>2"
proof(simp add: field_simps)
  assume a1: "0 < a"
  have "(a \<cdot> s\<^sub>2$1 - a \<cdot> s\<^sub>1$1)\<^sup>2 = a\<^sup>2 \<cdot> (s\<^sub>2$1 - s\<^sub>1$1)\<^sup>2"
    by (metis (mono_tags, hide_lams) Rings.ring_distribs(4) mult.left_commute 
        semiring_normalization_rules(18) semiring_normalization_rules(29))
  moreover have "(s\<^sub>2$1 - s\<^sub>1$1)\<^sup>2 \<le> (s\<^sub>1$1 - s\<^sub>2$1)\<^sup>2 + ((s\<^sub>1$2 - s\<^sub>2$2)\<^sup>2 + ((s\<^sub>1$3 - s\<^sub>2$3)\<^sup>2 + (s\<^sub>1$4 - s\<^sub>2$4)\<^sup>2))"
    using zero_le_power2 by (simp add: power2_commute) 
  thus "(a \<cdot> s\<^sub>2 $ 1 - a \<cdot> s\<^sub>1 $ 1)\<^sup>2 \<le> a\<^sup>2 \<cdot> (s\<^sub>1 $ 1 - s\<^sub>2 $ 1)\<^sup>2 + 
  (a\<^sup>2 \<cdot> (s\<^sub>1 $ 2 - s\<^sub>2 $ 2)\<^sup>2 + (a\<^sup>2 \<cdot> (s\<^sub>1 $ 3 - s\<^sub>2 $ 3)\<^sup>2 + a\<^sup>2 \<cdot> (s\<^sub>1 $ 4 - s\<^sub>2 $ 4)\<^sup>2))"
    using a1 by (simp add: Groups.algebra_simps(18)[symmetric] calculation)
qed

lemma local_lipschitz_therm_dyn:
  assumes "0 < (a::real)"
  shows "local_lipschitz UNIV UNIV (\<lambda>t::real. f a L)"
  apply(unfold local_lipschitz_def lipschitz_on_def dist_norm)
  apply(clarsimp, rule_tac x=1 in exI, clarsimp, rule_tac x=a in exI, pred_simp)
  using assms apply(simp add: norm_vec_def L2_set_def, unfold UNIV_4, pred_simp)
  unfolding real_sqrt_abs[symmetric] apply (rule real_le_lsqrt)
  by (simp_all add: norm_diff_therm_dyn)

lemma local_flow_therm: "a > 0 \<Longrightarrow> local_flow (f a L) UNIV UNIV (\<lambda> t. \<lbrakk>\<phi> a L t\<rbrakk>\<^sub>e)"
  apply (unfold_locales, simp_all)
  using local_lipschitz_therm_dyn apply(pred_simp)
   apply(simp add: forall_4, pred_simp, force intro!: poly_derivatives)
  by (pred_simp, force simp: vec_eq_iff)

lemma therm_dyn_down_real_arith:
  fixes T::real
  assumes "a > 0" and Thyps: "0 < T\<^sub>m" "T\<^sub>m \<le> T" "T \<le> T\<^sub>M"
    and thyps: "0 \<le> (\<tau>::real)" "\<forall>\<tau>\<in>{0..\<tau>}. \<tau> \<le> - (ln (T\<^sub>m / T) / a) "
  shows "T\<^sub>m \<le> exp (-a * \<tau>) * T" and "exp (-a * \<tau>) * T \<le> T\<^sub>M"
proof-
  have "0 \<le> \<tau> \<and> \<tau> \<le> - (ln (T\<^sub>m / T) / a)"
    using thyps by auto
  hence "ln (T\<^sub>m / T) \<le> - a * \<tau> \<and> - a * \<tau> \<le> 0"
    using assms(1) divide_le_cancel by fastforce
  also have "T\<^sub>m / T > 0"
    using Thyps by auto
  ultimately have obs: "T\<^sub>m / T \<le> exp (-a * \<tau>)" "exp (-a * \<tau>) \<le> 1"
    using exp_ln exp_le_one_iff by (metis exp_less_cancel_iff not_less, simp)
  thus "T\<^sub>m \<le> exp (-a * \<tau>) * T"
    using Thyps by (simp add: pos_divide_le_eq)
  show "exp (-a * \<tau>) * T \<le> T\<^sub>M"
    using Thyps mult_left_le_one_le[OF _ exp_ge_zero obs(2), of T] 
      less_eq_real_def order_trans_rules(23) by blast
qed

lemma therm_dyn_up_real_arith:
  fixes T::real
  assumes "a > 0" and Thyps: "T\<^sub>m \<le> T" "T \<le> T\<^sub>M" "T\<^sub>M < (L::real)"
    and thyps: "0 \<le> \<tau>" "\<forall>\<tau>\<in>{0..\<tau>}. \<tau> \<le> - (ln ((L - T\<^sub>M) / (L - T)) / a) "
  shows "L - T\<^sub>M \<le> exp (-(a * \<tau>)) * (L - T)" 
    and "L - exp (-(a * \<tau>)) * (L - T) \<le> T\<^sub>M" 
    and "T\<^sub>m \<le> L - exp (-(a * \<tau>)) * (L - T)"
proof-
  have "0 \<le> \<tau> \<and> \<tau> \<le> - (ln ((L - T\<^sub>M) / (L - T)) / a)"
    using thyps by auto
  hence "ln ((L - T\<^sub>M) / (L - T)) \<le> - a * \<tau> \<and> - a * \<tau> \<le> 0"
    using assms(1) divide_le_cancel by fastforce
  also have "(L - T\<^sub>M) / (L - T) > 0"
    using Thyps by auto
  ultimately have "(L - T\<^sub>M) / (L - T) \<le> exp (-a * \<tau>) \<and> exp (-a * \<tau>) \<le> 1"
    using exp_ln exp_le_one_iff by (metis exp_less_cancel_iff not_less)
  moreover have "L - T > 0"
    using Thyps by auto
  ultimately have obs: "(L - T\<^sub>M) \<le> exp (-a * \<tau>) * (L - T) \<and> exp (-a * \<tau>) * (L - T) \<le> (L - T)"
    by (simp add: pos_divide_le_eq)
  thus "(L - T\<^sub>M) \<le> exp (-(a * \<tau>)) * (L - T)"
    by auto
  thus "L - exp (-(a * \<tau>)) * (L - T) \<le> T\<^sub>M"
    by auto
  show "T\<^sub>m \<le> L - exp (-(a * \<tau>)) * (L - T)"
    using Thyps and obs by auto
qed

lemmas H_g_ode_therm = local_flow.sH_g_ode_ivl[OF local_flow_therm _ UNIV_I]

lemma thermostat_flow: 
  assumes "0 < a" and "0 \<le> \<tau>" and "0 < T\<^sub>m" and "T\<^sub>M < L"
  shows "
  \<^bold>{I T\<^sub>m T\<^sub>M\<^bold>}
    therm T\<^sub>m T\<^sub>M a L \<tau>
  \<^bold>{I T\<^sub>m T\<^sub>M\<^bold>}"
  apply(rule H_loopI)
    apply(rule_tac R="U(I T\<^sub>m T\<^sub>M \<and> t=0 \<and> T\<^sub>0 = T)" in H_seq)
     apply(rule_tac R="U(I T\<^sub>m T\<^sub>M \<and> t=0 \<and> T\<^sub>0 = T)" in H_seq)
      apply(rule_tac R="U(I T\<^sub>m T\<^sub>M \<and> t=0)" in H_seq)
       apply(simp_all only: H_g_ode_therm[OF assms(1,2)] sH_cond, simp_all)
  using therm_dyn_up_real_arith[OF assms(1) _ _ assms(4), of T\<^sub>m]
    and therm_dyn_down_real_arith[OF assms(1,3), of _ T\<^sub>M] by rel_auto'

\<comment> \<open>Refined by providing solutions \<close>

lemma R_therm_dyn_down: 
  assumes "a > 0" and "0 \<le> \<tau>" and "0 < T\<^sub>m" and "T\<^sub>M < L"
  shows "\<^bold>[\<Theta> = 0 \<and> I T\<^sub>m T\<^sub>M \<and> t = 0 \<and> T\<^sub>0 = T, I T\<^sub>m T\<^sub>M\<^bold>] \<ge> (x\<acute>= f a 0 & G T\<^sub>m T\<^sub>M a 0 on {0..\<tau>} UNIV @ 0)"
  apply(rule local_flow.R_g_ode_ivl[OF local_flow_therm])
  using assms apply(simp_all, pred_simp)
  using therm_dyn_down_real_arith[OF assms(1,3), of _ T\<^sub>M] by auto

lemma R_therm_dyn_up: 
  assumes "a > 0" and "0 \<le> \<tau>" and "0 < T\<^sub>m" and "T\<^sub>M < L"
  shows "\<^bold>[\<not> \<Theta> = 0 \<and> I T\<^sub>m T\<^sub>M \<and> t = 0 \<and> T\<^sub>0 = T, I T\<^sub>m T\<^sub>M\<^bold>] \<ge> (x\<acute>= f a L & G T\<^sub>m T\<^sub>M a L on {0..\<tau>} UNIV @ 0)"
  apply(rule local_flow.R_g_ode_ivl[OF local_flow_therm])
  using assms apply(simp_all, pred_simp)
  using therm_dyn_up_real_arith[OF assms(1) _ _ assms(4), of T\<^sub>m] by auto

lemma R_therm_dyn:
  assumes "a > 0" and "0 \<le> \<tau>" and "0 < T\<^sub>m" and "T\<^sub>M < L"
  shows "\<^bold>[I T\<^sub>m T\<^sub>M \<and> t = 0 \<and> T\<^sub>0 = T, I T\<^sub>m T\<^sub>M\<^bold>] \<ge> dyn T\<^sub>m T\<^sub>M a L \<tau>"
  apply(rule order_trans, rule R_cond_mono)
  using R_therm_dyn_down[OF assms] R_therm_dyn_up[OF assms] by (auto intro!: R_cond)

lemma R_therm_assign1: "\<^bold>[I T\<^sub>m T\<^sub>M, I T\<^sub>m T\<^sub>M \<and> t = 0\<^bold>] \<ge> (t ::= 0)"
  by (rule R_assign_rule, pred_simp)

lemma R_therm_assign2: "\<^bold>[I T\<^sub>m T\<^sub>M \<and> t = 0, I T\<^sub>m T\<^sub>M \<and> t = 0 \<and> T\<^sub>0 = T\<^bold>] \<ge> (T\<^sub>0 ::= T)"
  by (rule R_assign_rule, pred_simp)

lemma R_therm_ctrl: "\<^bold>[I T\<^sub>m T\<^sub>M, I T\<^sub>m T\<^sub>M \<and> t = 0 \<and> T\<^sub>0 = T\<^bold>] \<ge> ctrl T\<^sub>m T\<^sub>M"
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
      apply (rule R_cond) defer defer
       apply (rule R_cond) defer defer
  by (simp_all, rel_auto')

lemma R_therm_loop: "\<^bold>[I T\<^sub>m T\<^sub>M, I T\<^sub>m T\<^sub>M\<^bold>] \<ge> 
  (LOOP 
    \<^bold>[I T\<^sub>m T\<^sub>M, I T\<^sub>m T\<^sub>M \<and> t = 0 \<and> T\<^sub>0 = T\<^bold>];
    \<^bold>[I T\<^sub>m T\<^sub>M \<and> t = 0 \<and> T\<^sub>0 = T, I T\<^sub>m T\<^sub>M\<^bold>]
  INV I T\<^sub>m T\<^sub>M)"
  by (intro R_loop R_seq, simp_all)

lemma R_thermostat_flow: 
  assumes "a > 0" and "0 \<le> \<tau>" and "0 < T\<^sub>m" and "T\<^sub>M < L"
  shows "\<^bold>[I T\<^sub>m T\<^sub>M, I T\<^sub>m T\<^sub>M\<^bold>] \<ge> therm T\<^sub>m T\<^sub>M a L \<tau>"
  by (intro order_trans[OF _ R_therm_loop] R_loop_mono 
      R_seq_mono R_therm_ctrl R_therm_dyn[OF assms])

no_notation ftherm ("f")
        and therm_flow ("\<phi>")
        and therm_guard ("G")
        and therm_loop_inv ("I")
        and therm_ctrl ("ctrl")
        and therm_dyn ("dyn")


subsubsection \<open> Water tank \<close>  \<comment> \<open>Variation of Hespanha and \cite{AlurCHHHNOSY95}\<close>

abbreviation h :: "real \<Longrightarrow> real^4" where "h \<equiv> vec_lens 1"
abbreviation h\<^sub>0 :: "real \<Longrightarrow> real^4" where "h\<^sub>0 \<equiv> vec_lens 3"
abbreviation Pump :: "real \<Longrightarrow> real^4" where "Pump \<equiv> vec_lens 4"

abbreviation ftank :: "real \<Rightarrow> (real, 4) vec \<Rightarrow> (real, 4) vec" ("f")
  where "f k \<equiv> \<lbrakk>[h \<mapsto>\<^sub>s k, t \<mapsto>\<^sub>s 1, h\<^sub>0 \<mapsto>\<^sub>s 0, Pump \<mapsto>\<^sub>s 0]\<rbrakk>\<^sub>e"

abbreviation tank_flow :: "real \<Rightarrow> real \<Rightarrow> (real^4) usubst" ("\<phi>") 
  where "\<phi> k \<tau> \<equiv> [h \<mapsto>\<^sub>s k * \<tau> + h, t \<mapsto>\<^sub>s \<tau> + t, h\<^sub>0 \<mapsto>\<^sub>s h\<^sub>0, Pump \<mapsto>\<^sub>s Pump]"

abbreviation tank_guard :: "real \<Rightarrow> real \<Rightarrow> (real^4) upred" ("G")
  where "G Hm k \<equiv> U(t \<le> (Hm - h\<^sub>0)/k)"

no_utp_lift "tank_guard" (0 1)

abbreviation tank_loop_inv :: "real \<Rightarrow> real \<Rightarrow> (real^4) upred" ("I")
  where "I h\<^sub>m h\<^sub>M \<equiv> U(h\<^sub>m \<le> T \<and> T \<le> h\<^sub>M \<and> (Pump = 0 \<or> Pump = 1))"

no_utp_lift "tank_loop_inv" (0 1)

abbreviation tank_diff_inv :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real^4) upred" ("dI")
  where "dI h\<^sub>m h\<^sub>M k \<equiv> U(h = k \<cdot> t + h\<^sub>0 \<and> 0 \<le> t \<and> 
    h\<^sub>m \<le> h\<^sub>0 \<and> h\<^sub>0 \<le> h\<^sub>M \<and> (Pump = 0 \<or> Pump = 1))"

no_utp_lift "tank_diff_inv" (0 1 2)

\<comment> \<open>Verified by providing solutions \<close>

lemma local_flow_tank: "local_flow (f k) UNIV UNIV (\<lambda> t. \<lbrakk>\<phi> k t\<rbrakk>\<^sub>e)"
  apply(unfold_locales, unfold local_lipschitz_def lipschitz_on_def, simp_all, clarsimp)
  apply(rule_tac x="1/2" in exI, clarsimp, rule_tac x=1 in exI)
    apply(simp add: dist_norm norm_vec_def L2_set_def, unfold UNIV_4, pred_simp)
   apply(simp add: forall_4, pred_simp, force intro!: poly_derivatives)
  by (pred_simp, simp add: vec_eq_iff)

lemma tank_arith:
  fixes y::real
  assumes "0 \<le> (\<tau>::real)" and "0 < c\<^sub>o" and "c\<^sub>o < c\<^sub>i"
  shows "\<forall>\<tau>\<in>{0..\<tau>}. \<tau> \<le> - ((h\<^sub>m - y) / c\<^sub>o) \<Longrightarrow>  h\<^sub>m \<le> y - c\<^sub>o * \<tau>"
    and "\<forall>\<tau>\<in>{0..\<tau>}. \<tau> \<le> (h\<^sub>M - y) / (c\<^sub>i - c\<^sub>o) \<Longrightarrow>  (c\<^sub>i - c\<^sub>o) * \<tau> + y \<le> h\<^sub>M"
    and "h\<^sub>m \<le> y \<Longrightarrow> h\<^sub>m \<le> (c\<^sub>i - c\<^sub>o) \<cdot> \<tau> + y"
    and "y \<le> h\<^sub>M \<Longrightarrow> y - c\<^sub>o \<cdot> \<tau> \<le> h\<^sub>M"
  apply(simp_all add: field_simps le_divide_eq assms)
  using assms apply (meson add_mono less_eq_real_def mult_left_mono)
  using assms by (meson add_increasing2 less_eq_real_def mult_nonneg_nonneg) 

abbreviation tank_ctrl :: "real \<Rightarrow> real \<Rightarrow> (real^4) nd_fun" ("ctrl")
  where "ctrl h\<^sub>m h\<^sub>M \<equiv> (t ::=0);(h\<^sub>0 ::= h);
  (IF (Pump = 0 \<and> h\<^sub>0 \<le> h\<^sub>m + 1) THEN (Pump ::= 1) ELSE
  (IF (Pump = 1 \<and> h\<^sub>0 \<ge> h\<^sub>M - 1) THEN (Pump ::= 0) ELSE skip))"

abbreviation tank_dyn_sol :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real^4) nd_fun" ("dyn")
  where "dyn c\<^sub>i c\<^sub>o h\<^sub>m h\<^sub>M \<tau> \<equiv> (IF (Pump = 0) THEN 
    (x\<acute>= f (c\<^sub>i-c\<^sub>o) & G h\<^sub>M (c\<^sub>i-c\<^sub>o) on {0..\<tau>} UNIV @ 0)
  ELSE (x\<acute>= f (-c\<^sub>o) & G h\<^sub>m (-c\<^sub>o) on {0..\<tau>} UNIV @ 0))"

abbreviation "tank_sol c\<^sub>i c\<^sub>o h\<^sub>m h\<^sub>M \<tau> \<equiv> LOOP (ctrl h\<^sub>m h\<^sub>M ; dyn c\<^sub>i c\<^sub>o h\<^sub>m h\<^sub>M \<tau>) INV (I h\<^sub>m h\<^sub>M)"

lemmas H_g_ode_tank = local_flow.sH_g_ode_ivl[OF local_flow_tank _ UNIV_I]

lemma tank_flow:
  assumes "0 \<le> \<tau>" and "0 < c\<^sub>o" and "c\<^sub>o < c\<^sub>i"
  shows "
  \<^bold>{I h\<^sub>m h\<^sub>M\<^bold>}
    tank_sol c\<^sub>i c\<^sub>o h\<^sub>m h\<^sub>M \<tau>
  \<^bold>{I h\<^sub>m h\<^sub>M\<^bold>}"
  apply(rule H_loopI)
    apply(rule_tac R="U(I h\<^sub>m h\<^sub>M \<and> t = 0 \<and> h\<^sub>0 = h)" in H_seq)
     apply(rule_tac R="U(I h\<^sub>m h\<^sub>M \<and> t = 0 \<and> h\<^sub>0 = h)" in H_seq)
      apply(rule_tac R="U(I h\<^sub>m h\<^sub>M \<and> t = 0)" in H_seq)
       apply(simp_all only: H_g_ode_tank[OF assms(1)] sH_cond, simp_all)
  using assms tank_arith[OF _ assms(2,3)] by rel_auto'

no_notation tank_dyn_sol ("dyn")

\<comment> \<open>Verified with invariants \<close>

lemma tank_diff_inv:
  "0 \<le> \<tau> \<Longrightarrow> diff_invariant  \<lbrakk>dI h\<^sub>m h\<^sub>M k\<rbrakk>\<^sub>e (f k) {0..\<tau>} UNIV 0 Guard"
  apply(pred_simp, intro diff_invariant_conj_rule)
      apply(force intro!: poly_derivatives diff_invariant_rules)
     apply(rule_tac \<nu>'="\<lambda>t. 0" and \<mu>'="\<lambda>t. 1" in diff_invariant_leq_rule, simp_all add: forall_4)
    apply(rule_tac \<nu>'="\<lambda>t. 0" and \<mu>'="\<lambda>t. 0" in diff_invariant_leq_rule, simp_all)
  by (auto intro!: poly_derivatives diff_invariant_rules)

lemma tank_inv_arith1:
  assumes "0 \<le> (\<tau>::real)" and "c\<^sub>o < c\<^sub>i" and b: "h\<^sub>m \<le> y\<^sub>0" and g: "\<tau> \<le> (h\<^sub>M - y\<^sub>0) / (c\<^sub>i - c\<^sub>o)"
  shows "h\<^sub>m \<le> (c\<^sub>i - c\<^sub>o) \<cdot> \<tau> + y\<^sub>0" and "(c\<^sub>i - c\<^sub>o) \<cdot> \<tau> + y\<^sub>0 \<le> h\<^sub>M"
proof-
  have "(c\<^sub>i - c\<^sub>o) \<cdot> \<tau> \<le> (h\<^sub>M - y\<^sub>0)"
    using g assms(2,3) by (metis diff_gt_0_iff_gt mult.commute pos_le_divide_eq) 
  thus "(c\<^sub>i - c\<^sub>o) \<cdot> \<tau> + y\<^sub>0 \<le> h\<^sub>M"
    by auto
  show "h\<^sub>m \<le> (c\<^sub>i - c\<^sub>o) \<cdot> \<tau> + y\<^sub>0"
    using b assms(1,2) by (metis add.commute add_increasing2 diff_ge_0_iff_ge 
        less_eq_real_def mult_nonneg_nonneg) 
qed

lemma tank_inv_arith2:
  assumes "0 \<le> (\<tau>::real)" and "0 < c\<^sub>o" and b: "y\<^sub>0 \<le> h\<^sub>M" and g: "\<tau> \<le> - ((h\<^sub>m - y\<^sub>0) / c\<^sub>o)"
  shows "h\<^sub>m \<le> y\<^sub>0 - c\<^sub>o \<cdot> \<tau>" and "y\<^sub>0 - c\<^sub>o \<cdot> \<tau> \<le> h\<^sub>M"
proof-
  have "\<tau> \<cdot> c\<^sub>o \<le> y\<^sub>0 - h\<^sub>m"
    using g \<open>0 < c\<^sub>o\<close> pos_le_minus_divide_eq by fastforce 
  thus "h\<^sub>m \<le> y\<^sub>0 - c\<^sub>o \<cdot> \<tau>"
    by (auto simp: mult.commute)
  show "y\<^sub>0 - c\<^sub>o \<cdot> \<tau> \<le> h\<^sub>M" 
    using b assms(1,2) by (smt linordered_field_class.sign_simps(39) mult_less_cancel_right) 
qed

abbreviation tank_dyn_dinv :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real^4) nd_fun" ("dyn")
  where "dyn c\<^sub>i c\<^sub>o h\<^sub>m h\<^sub>M \<tau> \<equiv> (IF (Pump = 0) THEN 
    (x\<acute>= f (c\<^sub>i-c\<^sub>o) & G h\<^sub>M (c\<^sub>i-c\<^sub>o) on {0..\<tau>} UNIV @ 0 DINV (dI h\<^sub>m h\<^sub>M (c\<^sub>i-c\<^sub>o)))
  ELSE (x\<acute>= f (-c\<^sub>o) & G h\<^sub>m (-c\<^sub>o) on {0..\<tau>} UNIV @ 0 DINV (dI h\<^sub>m h\<^sub>M (-c\<^sub>o))))"

abbreviation "tank_dinv c\<^sub>i c\<^sub>o h\<^sub>m h\<^sub>M \<tau> \<equiv> LOOP (ctrl h\<^sub>m h\<^sub>M ; dyn c\<^sub>i c\<^sub>o h\<^sub>m h\<^sub>M \<tau>) INV (I h\<^sub>m h\<^sub>M)"

lemma tank_inv:
  assumes "0 \<le> \<tau>" and "0 < c\<^sub>o" and "c\<^sub>o < c\<^sub>i"
  shows "
  \<^bold>{I h\<^sub>m h\<^sub>M\<^bold>}
    tank_dinv c\<^sub>i c\<^sub>o h\<^sub>m h\<^sub>M \<tau> 
  \<^bold>{I h\<^sub>m h\<^sub>M\<^bold>}"
  apply(rule H_loopI)
    apply(rule_tac R="U(I h\<^sub>m h\<^sub>M \<and> t = 0 \<and> h\<^sub>0 = h)" in H_seq)
     apply(rule_tac R="U(I h\<^sub>m h\<^sub>M \<and> t = 0 \<and> h\<^sub>0 = h)" in H_seq)
      apply(rule_tac R="U(I h\<^sub>m h\<^sub>M \<and> t = 0)" in H_seq)
       apply(simp, pred_simp, simp, pred_simp)
     apply(rule H_cond, simp, pred_simp)+
  apply(simp, pred_simp)
  apply(rule H_cond, rule H_g_ode_inv, simp, pred_simp)
  using tank_diff_inv[OF assms(1)] apply(pred_simp)
      apply(simp, pred_simp, simp, pred_simp)
  using assms tank_inv_arith1 apply force
    apply(rule H_g_ode_inv, simp, pred_simp)
  using assms tank_diff_inv[of _ "-c\<^sub>o" h\<^sub>m h\<^sub>M] apply(pred_simp)
      apply(simp, pred_simp, simp, pred_simp)
  using assms tank_inv_arith2 by force (simp, pred_simp)

\<comment> \<open>Refined with invariants \<close>

lemma R_tank_inv:
  assumes "0 \<le> \<tau>" and "0 < c\<^sub>o" and "c\<^sub>o < c\<^sub>i"
  shows "\<^bold>[I h\<^sub>m h\<^sub>M, I h\<^sub>m h\<^sub>M\<^bold>] \<ge> tank_dinv c\<^sub>i c\<^sub>o h\<^sub>m h\<^sub>M \<tau>"
proof-
  \<comment> \<open>First we refine the control. \<close>
  have ifbranch1: 
    "Pump ::= 1 \<le> \<^bold>[Pump = 0 \<and> h\<^sub>0 \<le> h\<^sub>m + 1 \<and> I h\<^sub>m h\<^sub>M \<and> t = 0 \<and> h\<^sub>0 = h, I h\<^sub>m h\<^sub>M \<and> t = 0 \<and> h\<^sub>0 = h\<^bold>]" 
    (is "_ \<le> ?branch1") by (rule R_assign_rule, pred_simp)
  have ifbranch2: 
    "(IF (Pump = 1 \<and> h\<^sub>0 \<ge> h\<^sub>M - 1) THEN (Pump ::= 0) ELSE skip) \<le> 
    \<^bold>[\<not> (Pump = 0 \<and> h\<^sub>0 \<le> h\<^sub>m + 1) \<and> I h\<^sub>m h\<^sub>M \<and> t = 0 \<and> h\<^sub>0 = h, I h\<^sub>m h\<^sub>M \<and> t = 0 \<and> h\<^sub>0 = h\<^bold>]" 
    (is "_ \<le> ?branch2") apply(rule order_trans, rule R_cond_mono) defer defer
    by (rule R_cond, auto intro!: R_assign_rule R_skip, rel_auto')
  have ifthenelse: 
    "(IF (Pump = 0 \<and> h\<^sub>0 \<le> h\<^sub>m + 1) THEN ?branch1 ELSE ?branch2) \<le> 
    \<^bold>[I h\<^sub>m h\<^sub>M \<and> t = 0 \<and> h\<^sub>0 = h, I h\<^sub>m h\<^sub>M \<and> t = 0 \<and> h\<^sub>0 = h\<^bold>]" 
    (is "?ifthenelse \<le> _") by (rule R_cond, rel_auto')
  have 
    "(IF (Pump = 0 \<and> h\<^sub>0 \<le> h\<^sub>m + 1) THEN (Pump ::= 1) ELSE 
     (IF (Pump = 1 \<and> h\<^sub>0 \<ge> h\<^sub>M - 1) THEN (Pump ::= 0) ELSE skip)) \<le>
     \<^bold>[I h\<^sub>m h\<^sub>M \<and> t = 0 \<and> h\<^sub>0 = h, I h\<^sub>m h\<^sub>M \<and> t = 0 \<and> h\<^sub>0 = h\<^bold>]"
    apply(rule_tac y="?ifthenelse" in order_trans, rule R_cond_mono)
    using ifbranch1 ifbranch2 ifthenelse by auto
  hence ctrl: "ctrl h\<^sub>m h\<^sub>M \<le> \<^bold>[I h\<^sub>m h\<^sub>M, I h\<^sub>m h\<^sub>M \<and> t = 0 \<and> h\<^sub>0 = h\<^bold>]" (is "_ \<le> ?ctrl_ref")
    apply(rule_tac R="U(I h\<^sub>m h\<^sub>M \<and> t = 0 \<and> h\<^sub>0 = h)" in R_seq_rule)
     apply(rule_tac R="U(I h\<^sub>m h\<^sub>M \<and> t = 0)" in R_seq_rule)
    by (auto intro!: R_assign_rule, rel_auto')
  \<comment> \<open>Then we refine the dynamics. \<close>
  have dynup: 
    "(x\<acute>= f (c\<^sub>i-c\<^sub>o) & G h\<^sub>M (c\<^sub>i-c\<^sub>o) on {0..\<tau>} UNIV @ 0 DINV (dI h\<^sub>m h\<^sub>M (c\<^sub>i-c\<^sub>o))) \<le> 
    \<^bold>[Pump = 0 \<and> I h\<^sub>m h\<^sub>M \<and> t = 0 \<and> h\<^sub>0 = h, I h\<^sub>m h\<^sub>M\<^bold>]"
    apply(rule R_g_ode_inv[OF tank_diff_inv[OF assms(1)]])
    using assms apply(simp_all, pred_simp, pred_simp)
    by (auto simp: tank_inv_arith1)
  have dyndown: 
    "(x\<acute>= f (-c\<^sub>o) & G h\<^sub>m (-c\<^sub>o) on {0..\<tau>} UNIV @ 0 DINV (dI h\<^sub>m h\<^sub>M (-c\<^sub>o))) \<le> 
    \<^bold>[\<not> Pump = 0 \<and> I h\<^sub>m h\<^sub>M \<and> t = 0 \<and> h\<^sub>0 = h, I h\<^sub>m h\<^sub>M\<^bold>]"
    apply(rule R_g_ode_inv, simp)
    using tank_diff_inv[OF assms(1), of "-c\<^sub>o"] apply(pred_simp)
    using assms by (simp_all, rel_auto' simp: tank_inv_arith2)
  have dyn: "dyn c\<^sub>i c\<^sub>o h\<^sub>m h\<^sub>M \<tau> \<le> \<^bold>[I h\<^sub>m h\<^sub>M \<and> t = 0 \<and> h\<^sub>0 = h, I h\<^sub>m h\<^sub>M\<^bold>]" (is "_ \<le> ?dyn_ref")
    apply(rule order_trans, rule R_cond_mono)
    using dynup dyndown apply(force, force)
    by (rule R_cond, rel_auto')
  \<comment> \<open>Finally we put everything together. \<close>
  have pre_pos: "\<lceil>I h\<^sub>m h\<^sub>M\<rceil> \<le> \<lceil>I h\<^sub>m h\<^sub>M\<rceil>"
    by simp
  have inv_inv: "?ctrl_ref; ?dyn_ref \<le> \<^bold>[I h\<^sub>m h\<^sub>M, I h\<^sub>m h\<^sub>M\<^bold>]"
    by (rule R_seq)
  have loopref: "LOOP ?ctrl_ref; ?dyn_ref INV I h\<^sub>m h\<^sub>M \<le> \<^bold>[I h\<^sub>m h\<^sub>M, I h\<^sub>m h\<^sub>M\<^bold>]"
    apply(rule R_loop)
    using pre_pos inv_inv by auto
  have obs: "(ctrl h\<^sub>m h\<^sub>M;dyn c\<^sub>i c\<^sub>o h\<^sub>m h\<^sub>M \<tau>) \<le> ?ctrl_ref; ?dyn_ref"
    apply(rule R_seq_mono)
    using ctrl dyn by auto
  show "tank_dinv c\<^sub>i c\<^sub>o h\<^sub>m h\<^sub>M \<tau> \<le> \<^bold>[I h\<^sub>m h\<^sub>M, I h\<^sub>m h\<^sub>M\<^bold>]"
    by (rule order_trans[OF _ loopref], rule R_loop_mono[OF obs])
qed

no_notation ftank ("f")
        and tank_flow ("\<phi>")
        and tank_guard ("G")
        and tank_loop_inv ("I")
        and tank_diff_inv ("dI")
        and tank_ctrl ("ctrl")
        and tank_dyn_dinv ("dyn")

end