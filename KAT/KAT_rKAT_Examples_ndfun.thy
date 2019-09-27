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
a mass attached to a string looked from above. We use @{text "s$1"} to represent the x-coordinate
and @{text "s$2"} for the y-coordinate. We prove that this motion remains circular. \<close>

(*
abbreviation fpend :: "real^2 \<Rightarrow> real^2" ("f")
  where "f s \<equiv> (\<chi> i. if i=1 then s$2 else -s$1)"
*)

abbreviation fpend :: "(real^2) usubst" ("f") where
"fpend \<equiv> [x \<mapsto>\<^sub>s y, y \<mapsto>\<^sub>s -x]"

abbreviation pend_flow :: "real \<Rightarrow> (real^2) usubst" ("\<phi>") where
"pend_flow \<tau> \<equiv> [x \<mapsto>\<^sub>s x \<cdot> cos \<tau> + y \<cdot> sin \<tau>
                ,y \<mapsto>\<^sub>s - x \<cdot> sin \<tau> + y \<cdot> cos \<tau>]"

(*
abbreviation pend_flow :: "real \<Rightarrow> real^2 \<Rightarrow> real^2" ("\<phi>")
  where "\<phi> \<tau> s \<equiv> (\<chi> i. if i = 1 then s$1 \<cdot> cos \<tau> + s$2 \<cdot> sin \<tau> 
  else - s$1 \<cdot> sin \<tau> + s$2 \<cdot> cos \<tau>)"
*)

\<comment> \<open>Verified with annotated dynamics \<close>

lemma pendulum_dyn: "\<^bold>{r\<^sup>2 = x\<^sup>2 + y\<^sup>2\<^bold>}(EVOL \<phi> G T)\<^bold>{r\<^sup>2 = x\<^sup>2 + y\<^sup>2\<^bold>}"
  by (simp, rel_auto)

\<comment> \<open>Verified with differential invariants \<close>

lemma pendulum_inv: "\<^bold>{r\<^sup>2 = x\<^sup>2 + y\<^sup>2\<^bold>} (x\<acute>= \<lbrakk>f\<rbrakk>\<^sub>e & G) \<^bold>{r\<^sup>2 = x\<^sup>2 + y\<^sup>2\<^bold>}"
  by (simp, pred_simp, auto intro!: diff_invariant_rules poly_derivatives)
  
\<comment> \<open>Verified with the flow \<close>

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
flips the velocity, thus it is a completely elastic collision with the ground. We use @{text "s$1"} 
to ball's height and @{text "s$2"} for its velocity. We prove that the ball remains above ground
and below its initial resting position. \<close>

abbreviation v :: "real \<Longrightarrow> real^2" where "v \<equiv> vec_lens 2"

abbreviation fball :: "real \<Rightarrow> (real^2) usubst" ("f") 
  where "fball g \<equiv> [x \<mapsto>\<^sub>s v, v \<mapsto>\<^sub>s g]"

(* abbreviation fball :: "real \<Rightarrow> real^2 \<Rightarrow> real^2" ("f") 
  where "f g s \<equiv> (\<chi> i. if i=1 then s$2 else g)" *)

abbreviation ball_flow :: "real \<Rightarrow> real \<Rightarrow> (real^2) usubst" ("\<phi>") where
"ball_flow g \<tau> \<equiv> [  x \<mapsto>\<^sub>s g \<cdot> \<tau> ^ 2/2 + v \<cdot> \<tau> + x
                 ,  v \<mapsto>\<^sub>s g \<cdot> \<tau> + v]"

(*abbreviation ball_flow :: "real \<Rightarrow> real \<Rightarrow> real^2 \<Rightarrow> real^2" ("\<phi>") 
  where "\<phi> g \<tau> s \<equiv> (\<chi> i. if i=1 then g \<cdot> \<tau> ^ 2/2 + s$2 \<cdot> \<tau> + s$1 else g \<cdot> \<tau> + s$2)"*)

\<comment> \<open>Verified with differential invariants \<close>

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
  shows "diff_invariant \<lbrakk>I\<rbrakk>\<^sub>e \<lbrakk>f g\<rbrakk>\<^sub>e UNIV UNIV 0 \<lbrakk>G\<rbrakk>\<^sub>e"
  unfolding dinv apply(pred_simp, rule diff_invariant_rules, simp, simp, clarify)
  by(auto intro!: poly_derivatives)

lemma bouncing_ball_inv: "g < 0 \<Longrightarrow> h \<ge> 0 \<Longrightarrow> 
  \<^bold>{x = h \<and> v = 0\<^bold>} 
  (LOOP 
      ((x\<acute>= \<lbrakk>f g\<rbrakk>\<^sub>e & U(x \<ge> 0) DINV U(2 \<cdot> g \<cdot> x - 2 \<cdot> g \<cdot> h - v \<cdot> v = 0));
       (IF U(v = 0) THEN (v ::= -v) ELSE skip)) 
    INV U(0 \<le> x \<and> 2 \<cdot> g \<cdot> x = 2 \<cdot> g \<cdot> h + v \<cdot> v)
  ) \<^bold>{0 \<le> x \<and> x \<le> h\<^bold>}"
  apply(rule H_loopI)
    apply(rule H_seq[where R="U(0 \<le> x \<and> 2 \<cdot> g \<cdot> x = 2 \<cdot> g \<cdot> h + v \<cdot> v)"])
     apply(rule H_g_ode_inv)
       apply (pred_simp, force intro!: poly_derivatives diff_invariant_rules)
      apply(simp, pred_simp)+ 
  by (auto simp: bb_real_arith)

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

lemma bouncing_ball_dyn: "g < 0 \<Longrightarrow> h \<ge> 0 \<Longrightarrow>
  \<^bold>{x = h \<and> v = 0\<^bold>} 
  (LOOP 
      ((EVOL (\<phi> g) U(x \<ge> 0) T);
       (IF U(v = 0) THEN (v ::= -v) ELSE skip)) 
    INV U(0 \<le> x \<and> 2 \<cdot> g \<cdot> x = 2 \<cdot> g \<cdot> h + v \<cdot> v)
  ) \<^bold>{0 \<le> x \<and> x \<le> h\<^bold>}"
  apply(rule H_loopI, rule H_seq[where R="U(0 \<le> x \<and> 2 \<cdot> g \<cdot> x = 2 \<cdot> g \<cdot> h + v \<cdot> v)"])
     apply(simp, pred_simp, force simp: bb_real_arith)
    apply(simp, pred_simp)+
  by (force simp: bb_real_arith)


\<comment> \<open>Verified with the flow \<close>

lemma local_flow_ball: "local_flow \<lbrakk>f g\<rbrakk>\<^sub>e UNIV UNIV (\<lambda> t. \<lbrakk>\<phi> g t\<rbrakk>\<^sub>e)"
  apply(unfold_locales, simp_all add: local_lipschitz_def lipschitz_on_def vec_eq_iff, clarsimp)
  apply(rule_tac x="1/2" in exI, clarsimp, rule_tac x=1 in exI, pred_simp)
    apply(simp add: dist_norm norm_vec_def L2_set_def UNIV_2)
  by (simp add: forall_2, pred_simp, force intro!: poly_derivatives, pred_simp)

lemma bouncing_ball_flow: "g < 0 \<Longrightarrow> h \<ge> 0 \<Longrightarrow>
  \<^bold>{x = h \<and> v = 0\<^bold>} 
  (LOOP 
      ((x\<acute>= \<lbrakk>f g\<rbrakk>\<^sub>e & U(x \<ge> 0));
       (IF U(v = 0) THEN (v ::= -v) ELSE skip)) 
    INV U(0 \<le> x \<and> 2 \<cdot> g \<cdot> x = 2 \<cdot> g \<cdot> h + v \<cdot> v)
  ) \<^bold>{0 \<le> x \<and> x \<le> h\<^bold>}"
  apply(rule H_loopI, rule H_seq[where R="U(0 \<le> x \<and> 2 \<cdot> g \<cdot> x = 2 \<cdot> g \<cdot> h + v \<cdot> v)"])
     apply(subst local_flow.sH_g_ode[OF local_flow_ball], pred_simp)
     apply(force simp: bb_real_arith)
    apply(rule H_cond, simp)
     apply(pred_simp, simp)+
  by (pred_simp, force simp: bb_real_arith)

\<comment> \<open>Refined with annotated dynamics \<close>

lemma R_bb_assign: "g < (0::real) \<Longrightarrow> 0 \<le> h \<Longrightarrow> 
  (v ::=  - v) \<le> Ref 
    \<lceil>U(v = 0 \<and> 0 \<le> x \<and> 2 \<cdot> g \<cdot> x = 2 \<cdot> g \<cdot> h + v \<cdot> v)\<rceil> 
    \<lceil>U(0 \<le> x \<and> 2 \<cdot> g \<cdot> x = 2 \<cdot> g \<cdot> h + v \<cdot> v)\<rceil>"
  by (rule R_assign_rule, pred_simp)

lemma R_bouncing_ball_dyn:
  assumes "g < 0" and "h \<ge> 0"
  shows "Ref \<lceil>U(x = h \<and> v = 0)\<rceil> \<lceil>U(0 \<le> x \<and> x \<le> h)\<rceil> \<ge> 
  (LOOP 
      ((EVOL (\<phi> g) U(x \<ge> 0) T);
       (IF U(v = 0) THEN (v ::= -v) ELSE skip)) 
    INV U(0 \<le> x \<and> 2 \<cdot> g \<cdot> x = 2 \<cdot> g \<cdot> h + v \<cdot> v))"
  apply(rule order_trans)
   apply(rule R_loop_mono) defer
   apply(rule R_loop)
     apply(rule R_seq)
  using assms apply(simp, pred_simp)
  using assms apply(simp, pred_simp, force simp: bb_real_arith)
  apply(rule R_seq_mono) defer
  apply(rule order_trans)
    apply(rule R_cond_mono) defer defer
     apply(rule R_cond) defer
  apply(rule R_bb_assign, simp_all add: assms)
   apply(rule R_skip, pred_simp)
  by (rule R_g_evol_rule, pred_simp, force simp: bb_real_arith)

no_notation fball ("f")
        and ball_flow ("\<phi>")


subsubsection \<open> Thermostat \<close>

text \<open> A thermostat has a chronometer, a thermometer and a switch to turn on and off a heater. 
At most every @{text "\<tau>"} minutes, it sets its chronometer to @{term "0::real"}, it registers 
the room temperature, and it turns the heater on (or off) based on this reading. The temperature 
follows the ODE @{text "T' = - a * (T - U)"} where @{text "U = L \<ge> 0"} when the heater 
is on, and @{text "U = 0"} when it is off. We use @{term "1::4"} to denote the room's temperature, 
@{term "2::4"} is time as measured by the thermostat's chronometer, and @{term "3::4"} is a variable
to save temperature measurements. Finally, @{term "4::4"} states whether the heater is on 
(@{text "s$4 = 1"}) or off (@{text "s$4 = 0"}). We prove that the thermostat keeps the room's 
temperature between @{text "Tmin"} and @{text "Tmax"}. \<close>

abbreviation T :: "real \<Longrightarrow> real^4" where "T \<equiv> vec_lens 1"
abbreviation t :: "real \<Longrightarrow> real^4" where "t \<equiv> vec_lens 2"
abbreviation T\<^sub>0 :: "real \<Longrightarrow> real^4" where "T\<^sub>0 \<equiv> vec_lens 3"
abbreviation \<Theta> :: "real \<Longrightarrow> real^4" where "\<Theta> \<equiv> vec_lens 4"

abbreviation ftherm :: "real \<Rightarrow> real \<Rightarrow> (real^4) usubst" ("f")
  where "f a L \<equiv> [T \<mapsto>\<^sub>s - a * (T - L), t \<mapsto>\<^sub>s 1, T\<^sub>0 \<mapsto>\<^sub>s 0, \<Theta> \<mapsto>\<^sub>s 0]"

(* abbreviation therm_vec_field :: "real \<Rightarrow> real \<Rightarrow> real^4 \<Rightarrow> real^4" ("f")
  where "f a L s \<equiv> (\<chi> i. if i = 2 then 1 else (if i = 1 then - a * (s$1 - L) else 0))" *)

abbreviation therm_guard :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real^4) upred" ("G")
  where "G Tmin Tmax a L \<equiv> U(t \<le> - (ln ((L-(if L=0 then Tmin else Tmax))/(L-T\<^sub>0)))/a)"

(*abbreviation therm_guard :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real^4 \<Rightarrow> bool" ("G")
  where "G Tmin Tmax a L s \<equiv> (s$2 \<le> - (ln ((L-(if L=0 then Tmin else Tmax))/(L-s$3)))/a)" *)

abbreviation therm_loop_inv :: "real \<Rightarrow> real \<Rightarrow> (real^4) upred" ("I")
  where "I Tmin Tmax \<equiv> U(Tmin \<le> T \<and> T \<le> Tmax \<and> (\<Theta> = 0 \<or> \<Theta> = 1))"

no_utp_lift "therm_loop_inv" (0 1)

(* abbreviation therm_loop_inv :: "real \<Rightarrow> real \<Rightarrow> real^4 \<Rightarrow> bool" ("I")
  where "I Tmin Tmax s \<equiv> Tmin \<le> s$1 \<and> s$1 \<le> Tmax \<and> (s$4 = 0 \<or> s$4 = 1)" *)

abbreviation therm_flow :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real^4) usubst" ("\<phi>") 
  where "therm_flow a L \<tau> \<equiv> [T \<mapsto>\<^sub>s - exp(-a * \<tau>) * (L - T) + L, t \<mapsto>\<^sub>s \<tau> + t, T\<^sub>0 \<mapsto>\<^sub>s T\<^sub>0, \<Theta> \<mapsto>\<^sub>s \<Theta>]"

(*abbreviation therm_flow :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real^4 \<Rightarrow> real^4" ("\<phi>")
  where "\<phi> a L \<tau> s \<equiv> (\<chi> i. if i = 1 then - exp(-a * \<tau>) * (L - s$1) + L else 
  (if i = 2 then \<tau> + s$2 else s$i))"*)

\<comment> \<open>Verified with the flow \<close>

lemma norm_diff_therm_dyn: "0 < (a::real) \<Longrightarrow> (a \<cdot> (s\<^sub>2$1 - L) - a \<cdot> (s\<^sub>1$1 - L))\<^sup>2
       \<le> (a \<cdot> sqrt ((s\<^sub>1$1 - s\<^sub>2$1)\<^sup>2 + ((s\<^sub>1$2 - s\<^sub>2$2)\<^sup>2 + ((s\<^sub>1$3 - s\<^sub>2$3)\<^sup>2 + (s\<^sub>1$4 - s\<^sub>2$4)\<^sup>2))))\<^sup>2"
proof(simp add: field_simps)
  assume a1: "0 < a"
  have "(a \<cdot> s\<^sub>2$1 - a \<cdot> s\<^sub>1$1)\<^sup>2 = a\<^sup>2 \<cdot> (s\<^sub>2$1 - s\<^sub>1$1)\<^sup>2"
    by (metis (mono_tags, hide_lams) Rings.ring_distribs(4) mult.left_commute 
        semiring_normalization_rules(18) semiring_normalization_rules(29))
  moreover have "(s\<^sub>2$1 - s\<^sub>1$1)\<^sup>2 \<le> (s\<^sub>1$1 - s\<^sub>2$1)\<^sup>2 + ((s\<^sub>1$2 - s\<^sub>2$2)\<^sup>2 + ((s\<^sub>1$3 - s\<^sub>2$3)\<^sup>2 + (s\<^sub>1$4 - s\<^sub>2$4)\<^sup>2))"
    using zero_le_power2 by (simp add: power2_commute) 
  thus "(a \<cdot> s\<^sub>2 $ 1 - a \<cdot> s\<^sub>1 $ 1)\<^sup>2
    \<le> a\<^sup>2 \<cdot> (s\<^sub>1 $ 1 - s\<^sub>2 $ 1)\<^sup>2 + (a\<^sup>2 \<cdot> (s\<^sub>1 $ 2 - s\<^sub>2 $ 2)\<^sup>2 + (a\<^sup>2 \<cdot> (s\<^sub>1 $ 3 - s\<^sub>2 $ 3)\<^sup>2 + a\<^sup>2 \<cdot> (s\<^sub>1 $ 4 - s\<^sub>2 $ 4)\<^sup>2))"
    using a1 by (simp add: Groups.algebra_simps(18)[symmetric] calculation)
qed

lemma local_lipschitz_therm_dyn:
  assumes "0 < (a::real)"
  shows "local_lipschitz UNIV UNIV (\<lambda>t::real. \<lbrakk>f a L\<rbrakk>\<^sub>e)"
  apply(unfold local_lipschitz_def lipschitz_on_def dist_norm)
  apply(clarsimp, rule_tac x=1 in exI, clarsimp, rule_tac x=a in exI, pred_simp)
  using assms apply(simp add: norm_vec_def L2_set_def, unfold UNIV_4, pred_simp)
  unfolding real_sqrt_abs[symmetric] apply (rule real_le_lsqrt)
  by (simp_all add: norm_diff_therm_dyn)

lemma local_flow_therm: "a > 0 \<Longrightarrow> local_flow \<lbrakk>f a L\<rbrakk>\<^sub>e UNIV UNIV (\<lambda> t. \<lbrakk>\<phi> a L t\<rbrakk>\<^sub>e)"
  apply (unfold_locales, simp_all)
  using local_lipschitz_therm_dyn apply(pred_simp)
   apply(simp add: forall_4, pred_simp, force intro!: poly_derivatives)
  by (pred_simp, force simp: vec_eq_iff)

lemma therm_dyn_down_real_arith:
  fixes T::real
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
  fixes T::real
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
  shows "\<^bold>{I Tmin Tmax\<^bold>}
  (LOOP (
    \<comment> \<open>control\<close>
    (t ::= 0);
    (T\<^sub>0 ::= T);
    (IF U(\<Theta> = 0 \<and> T\<^sub>0 \<le> Tmin + 1) THEN 
      (\<Theta> ::= 1) 
     ELSE IF U(\<Theta> = 1 \<and> T\<^sub>0 \<ge> Tmax - 1) THEN 
      (\<Theta> ::= 0) 
     ELSE skip);
    \<comment> \<open>dynamics\<close>
    (IF U(\<Theta> = 0) THEN 
      (x\<acute>= \<lbrakk>f a 0\<rbrakk>\<^sub>e & G Tmin Tmax a 0 on {0..\<tau>} UNIV @ 0) 
    ELSE 
      (x\<acute>= \<lbrakk>f a L\<rbrakk>\<^sub>e & G Tmin Tmax a L on {0..\<tau>} UNIV @ 0))
  ) INV I Tmin Tmax)
  \<^bold>{I Tmin Tmax\<^bold>}"
  apply(rule H_loopI)
    apply(rule_tac R="U(I Tmin Tmax \<and> t=0 \<and> T\<^sub>0 = T)" in H_seq)
     apply(rule_tac R="U(I Tmin Tmax \<and> t=0 \<and> T\<^sub>0 = T)" in H_seq)
      apply(rule_tac R="U(I Tmin Tmax \<and> t=0)" in H_seq)
  apply(simp, pred_simp, simp, pred_simp)
     apply(rule H_cond, simp add: H_g_ode_therm[OF assms(1,2)], pred_simp)+
     apply(simp, pred_simp)
    apply(rule H_cond, simp_all only: H_g_ode_therm[OF assms(1,2)], pred_simp)
  using therm_dyn_down_real_arith[OF assms(1,3), of _ Tmax] apply force
  apply pred_simp
  using therm_dyn_up_real_arith[OF assms(1) _ _ assms(4), of Tmin]
    and therm_dyn_down_real_arith[OF assms(1,3), of _ Tmax] by auto

\<comment> \<open>Refined with the flow \<close>

lemma R_therm_dyn_down: 
  assumes "a > 0" and "0 \<le> \<tau>" and "0 < Tmin" and "Tmax < L"
  shows "Ref \<lceil>U(\<Theta> = 0 \<and> I Tmin Tmax \<and> t = 0 \<and> T\<^sub>0 = T)\<rceil> \<lceil>I Tmin Tmax\<rceil> \<ge> 
    (x\<acute>= \<lbrakk>f a 0\<rbrakk>\<^sub>e & G Tmin Tmax a 0 on {0..\<tau>} UNIV @ 0)"
  apply(rule local_flow.R_g_ode_ivl[OF local_flow_therm])
  using assms apply(simp_all, pred_simp)
  using therm_dyn_down_real_arith[OF assms(1,3), of _ Tmax] by auto

lemma R_therm_dyn_up: 
  assumes "a > 0" and "0 \<le> \<tau>" and "0 < Tmin" and "Tmax < L"
  shows "Ref \<lceil>U(\<not> \<Theta> = 0 \<and> I Tmin Tmax \<and> t = 0 \<and> T\<^sub>0 = T)\<rceil> \<lceil>I Tmin Tmax\<rceil> \<ge> 
    (x\<acute>= \<lbrakk>f a L\<rbrakk>\<^sub>e & G Tmin Tmax a L on {0..\<tau>} UNIV @ 0)"
  apply(rule local_flow.R_g_ode_ivl[OF local_flow_therm])
  using assms apply(simp_all, pred_simp)
  using therm_dyn_up_real_arith[OF assms(1) _ _ assms(4), of Tmin] by auto

lemma R_therm_dyn:
  assumes "a > 0" and "0 \<le> \<tau>" and "0 < Tmin" and "Tmax < L"
  shows "Ref \<lceil>U(I Tmin Tmax \<and> t = 0 \<and> T\<^sub>0 = T)\<rceil> \<lceil>I Tmin Tmax\<rceil> \<ge> 
  (IF U(\<Theta> = 0) THEN 
    (x\<acute>= \<lbrakk>f a 0\<rbrakk>\<^sub>e & G Tmin Tmax a 0 on {0..\<tau>} UNIV @ 0) 
  ELSE 
    (x\<acute>= \<lbrakk>f a L\<rbrakk>\<^sub>e & G Tmin Tmax a L on {0..\<tau>} UNIV @ 0))"
  apply(rule order_trans, rule R_cond_mono)
  using R_therm_dyn_down[OF assms] R_therm_dyn_up[OF assms] by (auto intro!: R_cond)

lemma R_therm_assign1: "Ref \<lceil>I Tmin Tmax\<rceil> \<lceil>U(I Tmin Tmax \<and> t = 0)\<rceil> \<ge> (t ::= 0)"
  by (rule R_assign_rule, pred_simp)

lemma R_therm_assign2: 
  "Ref \<lceil>U(I Tmin Tmax \<and> t = 0)\<rceil> \<lceil>U(I Tmin Tmax \<and> t = 0 \<and> T\<^sub>0 = T)\<rceil> \<ge> (T\<^sub>0 ::= T)"
  by (rule R_assign_rule, pred_simp)

lemma R_therm_ctrl:
  "Ref \<lceil>I Tmin Tmax\<rceil> \<lceil>U(I Tmin Tmax \<and> t = 0 \<and> T\<^sub>0 = T)\<rceil> \<ge>
  (t ::= 0);
  (T\<^sub>0 ::= T);
  (IF U(\<Theta> = 0 \<and> T\<^sub>0 \<le> Tmin + 1) THEN 
      (\<Theta> ::= 1) 
     ELSE IF U(\<Theta> = 1 \<and> T\<^sub>0 \<ge> Tmax - 1) THEN 
      (\<Theta> ::= 0) 
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
  by (rule R_cond)+ (pred_simp)+

lemma R_therm_loop: "Ref \<lceil>I Tmin Tmax\<rceil> \<lceil>I Tmin Tmax\<rceil> \<ge> 
  (LOOP 
    Ref \<lceil>I Tmin Tmax\<rceil> \<lceil>U(I Tmin Tmax \<and> t = 0 \<and> T\<^sub>0 = T)\<rceil>;
    Ref \<lceil>U(I Tmin Tmax \<and> t = 0 \<and> T\<^sub>0 = T)\<rceil> \<lceil>I Tmin Tmax\<rceil>
  INV I Tmin Tmax)"
  by (intro R_loop R_seq, simp_all)

lemma R_thermostat_flow: 
  assumes "a > 0" and "0 \<le> \<tau>" and "0 < Tmin" and "Tmax < L"
  shows "Ref \<lceil>I Tmin Tmax\<rceil> \<lceil>I Tmin Tmax\<rceil> \<ge> 
  (LOOP (
    \<comment> \<open>control\<close>
    (t ::= 0);
    (T\<^sub>0 ::= T);
    (IF U(\<Theta> = 0 \<and> T\<^sub>0 \<le> Tmin + 1) THEN 
      (\<Theta> ::= 1) 
     ELSE IF U(\<Theta> = 1 \<and> T\<^sub>0 \<ge> Tmax - 1) THEN 
      (\<Theta> ::= 0) 
     ELSE skip);
    \<comment> \<open>dynamics\<close>
    (IF U(\<Theta> = 0) THEN 
      (x\<acute>= \<lbrakk>f a 0\<rbrakk>\<^sub>e & G Tmin Tmax a 0 on {0..\<tau>} UNIV @ 0) 
    ELSE 
      (x\<acute>= \<lbrakk>f a L\<rbrakk>\<^sub>e & G Tmin Tmax a L on {0..\<tau>} UNIV @ 0))
  ) INV I Tmin Tmax)"
  by (intro order_trans[OF _ R_therm_loop] R_loop_mono 
      R_seq_mono R_therm_ctrl R_therm_dyn[OF assms])

no_notation ftherm ("f")
        and therm_flow ("\<phi>")
        and therm_guard ("G")
        and therm_loop_inv ("I")

subsubsection \<open> Water tank \<close>  \<comment> \<open>Variation of Hespanha and \cite{AlurCHHHNOSY95}\<close>


abbreviation h :: "real \<Longrightarrow> real^4" where "h \<equiv> vec_lens 1"
abbreviation h\<^sub>0 :: "real \<Longrightarrow> real^4" where "h\<^sub>0 \<equiv> vec_lens 3"
abbreviation Pump :: "real \<Longrightarrow> real^4" where "Pump \<equiv> vec_lens 4"

abbreviation ftank :: "real \<Rightarrow> (real^4) usubst" ("f")
  where "f k \<equiv> [h \<mapsto>\<^sub>s k, t \<mapsto>\<^sub>s 1, h\<^sub>0 \<mapsto>\<^sub>s 0, Pump \<mapsto>\<^sub>s 0]"

(*abbreviation ftherm :: "real \<Rightarrow> real \<Rightarrow> (real^4) usubst" ("f")
  where "f a L \<equiv> [T \<mapsto>\<^sub>s - a * (T - L), t \<mapsto>\<^sub>s 1, T\<^sub>0 \<mapsto>\<^sub>s 0, \<Theta> \<mapsto>\<^sub>s 0]"*)

abbreviation tank_flow :: "real \<Rightarrow> real \<Rightarrow> (real^4) usubst" ("\<phi>") 
  where "\<phi> k \<tau> \<equiv> [h \<mapsto>\<^sub>s k * \<tau> + h, t \<mapsto>\<^sub>s \<tau> + t, h\<^sub>0 \<mapsto>\<^sub>s h\<^sub>0, Pump \<mapsto>\<^sub>s Pump]"

(*abbreviation tank_flow :: "real \<Rightarrow> real \<Rightarrow> real^4 \<Rightarrow> real^4" ("\<phi>")
  where "\<phi> k \<tau> s \<equiv> (\<chi> i. if i = 1 then k * \<tau> + s$1 else 
  (if i = 2 then \<tau> + s$2 else s$i))"*)

abbreviation tank_guard :: "real \<Rightarrow> real \<Rightarrow> (real^4) upred" ("G")
  where "G Hm k \<equiv> U(t \<le> (Hm - h\<^sub>0)/k)"

(*abbreviation tank_guard :: "real \<Rightarrow> real \<Rightarrow> real^4 \<Rightarrow> bool" ("G")
  where "G Hm k s \<equiv> s$2 \<le> (Hm - s$3)/k"*)

abbreviation tank_loop_inv :: "real \<Rightarrow> real \<Rightarrow> (real^4) upred" ("I")
  where "I hmin hmax \<equiv> U(hmin \<le> T \<and> T \<le> hmax \<and> (Pump = 0 \<or> Pump = 1))"

no_utp_lift "tank_loop_inv" (0 1)

(*abbreviation tank_loop_inv :: "real \<Rightarrow> real \<Rightarrow> real^4 \<Rightarrow> bool" ("I")
  where "I hmin hmax s \<equiv> hmin \<le> s$1 \<and> s$1 \<le> hmax \<and> (s$4 = 0 \<or> s$4 = 1)"*)

abbreviation tank_diff_inv :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real^4) upred" ("dI")
  where "dI hmin hmax k \<equiv> U(h = k \<cdot> t + h\<^sub>0 \<and> 0 \<le> t \<and> 
    hmin \<le> h\<^sub>0 \<and> h\<^sub>0 \<le> hmax \<and> (Pump = 0 \<or> Pump = 1))"

no_utp_lift "tank_loop_inv" (0 1 2)

(*abbreviation tank_diff_inv :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real^4 \<Rightarrow> bool" ("dI")
  where "dI hmin hmax k s \<equiv> s$1 = k \<cdot> s$2 + s$3 \<and> 0 \<le> s$2 \<and> 
    hmin \<le> s$3 \<and> s$3 \<le> hmax \<and> (s$4 = 0 \<or> s$4 = 1)"*)

\<comment> \<open>Verified with the flow \<close>

lemma local_flow_tank: "local_flow \<lbrakk>f k\<rbrakk>\<^sub>e UNIV UNIV (\<lambda> t. \<lbrakk>\<phi> k t\<rbrakk>\<^sub>e)"
  apply(unfold_locales, unfold local_lipschitz_def lipschitz_on_def, simp_all, clarsimp)
  apply(rule_tac x="1/2" in exI, clarsimp, rule_tac x=1 in exI)
    apply(simp add: dist_norm norm_vec_def L2_set_def, unfold UNIV_4, pred_simp)
   apply(simp add: forall_4, pred_simp, force intro!: poly_derivatives)
  by (pred_simp, simp add: vec_eq_iff)

lemma tank_arith:
  fixes y::real
  assumes "0 \<le> (\<tau>::real)" and "0 < c\<^sub>o" and "c\<^sub>o < c\<^sub>i"
  shows "\<forall>\<tau>\<in>{0..\<tau>}. \<tau> \<le> - ((hmin - y) / c\<^sub>o) \<Longrightarrow>  hmin \<le> y - c\<^sub>o * \<tau>"
    and "\<forall>\<tau>\<in>{0..\<tau>}. \<tau> \<le> (hmax - y) / (c\<^sub>i - c\<^sub>o) \<Longrightarrow>  (c\<^sub>i - c\<^sub>o) * \<tau> + y \<le> hmax"
    and "hmin \<le> y \<Longrightarrow> hmin \<le> (c\<^sub>i - c\<^sub>o) \<cdot> \<tau> + y"
    and "y \<le> hmax \<Longrightarrow> y - c\<^sub>o \<cdot> \<tau> \<le> hmax"
  apply(simp_all add: field_simps le_divide_eq assms)
  using assms apply (meson add_mono less_eq_real_def mult_left_mono)
  using assms by (meson add_increasing2 less_eq_real_def mult_nonneg_nonneg) 

lemmas H_g_ode_tank = local_flow.sH_g_ode_ivl[OF local_flow_tank _ UNIV_I]

lemma tank_flow:
  assumes "0 \<le> \<tau>" and "0 < c\<^sub>o" and "c\<^sub>o < c\<^sub>i"
  shows "\<^bold>{I hmin hmax\<^bold>}
  (LOOP 
    \<comment> \<open>control\<close>
    ((t ::=0);(h\<^sub>0 ::= h);
    (IF U(Pump = 0 \<and> h\<^sub>0 \<le> hmin + 1) THEN (Pump ::= 1) ELSE 
    (IF U(Pump = 1 \<and> h\<^sub>0 \<ge> hmax - 1) THEN (Pump ::= 0) ELSE skip));
    \<comment> \<open>dynamics\<close>
    (IF U(Pump = 0) THEN (x\<acute>= \<lbrakk>f (c\<^sub>i-c\<^sub>o)\<rbrakk>\<^sub>e & G hmax (c\<^sub>i-c\<^sub>o) on {0..\<tau>} UNIV @ 0) 
     ELSE (x\<acute>= \<lbrakk>f (-c\<^sub>o)\<rbrakk>\<^sub>e & G hmin (-c\<^sub>o) on {0..\<tau>} UNIV @ 0)) )
  INV I hmin hmax) \<^bold>{I hmin hmax\<^bold>}"
  apply(rule H_loopI)
    apply(rule_tac R="U(I hmin hmax \<and> t = 0 \<and> h\<^sub>0 = h)" in H_seq)
     apply(rule_tac R="U(I hmin hmax \<and> t = 0 \<and> h\<^sub>0 = h)" in H_seq)
      apply(rule_tac R="U(I hmin hmax \<and> t = 0)" in H_seq)
  apply(simp, pred_simp, simp, pred_simp)
     apply(rule H_cond, simp, pred_simp)+
   apply(simp, pred_simp)
    apply(rule H_cond)
  apply(simp_all only: H_g_ode_tank[OF assms(1)], pred_simp)
  using assms tank_arith[OF _ assms(2,3)] apply force
  apply(pred_simp)
  using assms tank_arith[OF _ assms(2,3)] by auto

\<comment> \<open>Verified with differential invariants \<close>

lemma tank_diff_inv:
  "0 \<le> \<tau> \<Longrightarrow> diff_invariant  \<lbrakk>dI hmin hmax k\<rbrakk>\<^sub>e \<lbrakk>f k\<rbrakk>\<^sub>e {0..\<tau>} UNIV 0 Guard"
  apply(pred_simp, intro diff_invariant_conj_rule)
      apply(force intro!: poly_derivatives diff_invariant_rules)
     apply(rule_tac \<nu>'="\<lambda>t. 0" and \<mu>'="\<lambda>t. 1" in diff_invariant_leq_rule, simp_all add: forall_4)
    apply(rule_tac \<nu>'="\<lambda>t. 0" and \<mu>'="\<lambda>t. 0" in diff_invariant_leq_rule, simp_all)
    apply(force intro!: poly_derivatives)+
  by (auto intro!: poly_derivatives diff_invariant_rules)

lemma tank_inv_arith1:
  assumes "0 \<le> (\<tau>::real)" and "c\<^sub>o < c\<^sub>i" and b: "hmin \<le> y\<^sub>0" and g: "\<tau> \<le> (hmax - y\<^sub>0) / (c\<^sub>i - c\<^sub>o)"
  shows "hmin \<le> (c\<^sub>i - c\<^sub>o) \<cdot> \<tau> + y\<^sub>0" and "(c\<^sub>i - c\<^sub>o) \<cdot> \<tau> + y\<^sub>0 \<le> hmax"
proof-
  have "(c\<^sub>i - c\<^sub>o) \<cdot> \<tau> \<le> (hmax - y\<^sub>0)"
    using g assms(2,3) by (metis diff_gt_0_iff_gt mult.commute pos_le_divide_eq) 
  thus "(c\<^sub>i - c\<^sub>o) \<cdot> \<tau> + y\<^sub>0 \<le> hmax"
    by auto
  show "hmin \<le> (c\<^sub>i - c\<^sub>o) \<cdot> \<tau> + y\<^sub>0"
    using b assms(1,2) by (metis add.commute add_increasing2 diff_ge_0_iff_ge 
        less_eq_real_def mult_nonneg_nonneg) 
qed

lemma tank_inv_arith2:
  assumes "0 \<le> (\<tau>::real)" and "0 < c\<^sub>o" and b: "y\<^sub>0 \<le> hmax" and g: "\<tau> \<le> - ((hmin - y\<^sub>0) / c\<^sub>o)"
  shows "hmin \<le> y\<^sub>0 - c\<^sub>o \<cdot> \<tau>" and "y\<^sub>0 - c\<^sub>o \<cdot> \<tau> \<le> hmax"
proof-
  have "\<tau> \<cdot> c\<^sub>o \<le> y\<^sub>0 - hmin"
    using g \<open>0 < c\<^sub>o\<close> pos_le_minus_divide_eq by fastforce 
  thus "hmin \<le> y\<^sub>0 - c\<^sub>o \<cdot> \<tau>"
    by (auto simp: mult.commute)
  show "y\<^sub>0 - c\<^sub>o \<cdot> \<tau> \<le> hmax" 
    using b assms(1,2) by (smt linordered_field_class.sign_simps(39) mult_less_cancel_right) 
qed

lemma tank_inv:
  assumes "0 \<le> \<tau>" and "0 < c\<^sub>o" and "c\<^sub>o < c\<^sub>i"
  shows "\<^bold>{I hmin hmax\<^bold>}
  (LOOP 
    \<comment> \<open>control\<close>
    ((t ::=0);(h\<^sub>0 ::= h);
    (IF U(Pump = 0 \<and> h\<^sub>0 \<le> hmin + 1) THEN (Pump ::= 1) ELSE 
    (IF U(Pump = 1 \<and> h\<^sub>0 \<ge> hmax - 1) THEN (Pump ::= 0) ELSE skip));
    \<comment> \<open>dynamics\<close>
    (IF U(Pump = 0) THEN 
      (x\<acute>= \<lbrakk>f (c\<^sub>i-c\<^sub>o)\<rbrakk>\<^sub>e & G hmax (c\<^sub>i-c\<^sub>o) on {0..\<tau>} UNIV @ 0 DINV (dI hmin hmax (c\<^sub>i-c\<^sub>o))) 
     ELSE 
      (x\<acute>= \<lbrakk>f (-c\<^sub>o)\<rbrakk>\<^sub>e & G hmin (-c\<^sub>o) on {0..\<tau>} UNIV @ 0 DINV (dI hmin hmax (-c\<^sub>o)))) )
  INV I hmin hmax) \<^bold>{I hmin hmax\<^bold>}"
  apply(rule H_loopI)
    apply(rule_tac R="U(I hmin hmax \<and> t = 0 \<and> h\<^sub>0 = h)" in H_seq)
     apply(rule_tac R="U(I hmin hmax \<and> t = 0 \<and> h\<^sub>0 = h)" in H_seq)
      apply(rule_tac R="U(I hmin hmax \<and> t = 0)" in H_seq)
       apply(simp, pred_simp, simp, pred_simp)
     apply(rule H_cond, simp, pred_simp)+
  apply(simp, pred_simp)
    apply(rule H_cond, rule H_g_ode_inv, simp, pred_simp)
  using tank_diff_inv[OF assms(1)] apply(pred_simp)
      apply(simp, pred_simp, simp, pred_simp)
  using assms tank_inv_arith1 apply force
    apply(rule H_g_ode_inv, simp, pred_simp)
  using assms tank_diff_inv[of _ "-c\<^sub>o" hmin hmax] apply(pred_simp)
      apply(simp, pred_simp, simp, pred_simp)
  using assms tank_inv_arith2 by force (simp, pred_simp)

\<comment> \<open>Refined with differential invariants \<close>

lemma R_tank_inv:
  assumes "0 \<le> \<tau>" and "0 < c\<^sub>o" and "c\<^sub>o < c\<^sub>i"
  shows "Ref \<lceil>I hmin hmax\<rceil> \<lceil>I hmin hmax\<rceil> \<ge>
  (LOOP 
    \<comment> \<open>control\<close>
    ((t ::=0);(h\<^sub>0 ::= h);
    (IF U(Pump = 0 \<and> h\<^sub>0 \<le> hmin + 1) THEN (Pump ::= 1) ELSE 
    (IF U(Pump = 1 \<and> h\<^sub>0 \<ge> hmax - 1) THEN (Pump ::= 0) ELSE skip));
    \<comment> \<open>dynamics\<close>
    (IF U(Pump = 0) THEN 
      (x\<acute>= \<lbrakk>f (c\<^sub>i-c\<^sub>o)\<rbrakk>\<^sub>e & G hmax (c\<^sub>i-c\<^sub>o) on {0..\<tau>} UNIV @ 0 DINV (dI hmin hmax (c\<^sub>i-c\<^sub>o))) 
     ELSE 
      (x\<acute>= \<lbrakk>f (-c\<^sub>o)\<rbrakk>\<^sub>e & G hmin (-c\<^sub>o) on {0..\<tau>} UNIV @ 0 DINV (dI hmin hmax (-c\<^sub>o)))) )
  INV I hmin hmax)" (is "LOOP (?ctrl;?dyn) INV _ \<le> ?ref")
proof-
  \<comment> \<open>First we refine the control. \<close>
  let ?Icntrl = "U(I hmin hmax \<and> t = 0 \<and> h\<^sub>0 = h)"
  and ?cond = "U(Pump = 0 \<and> h\<^sub>0 \<le> hmin + 1)"
  have ifbranch1: "Pump ::= 1 \<le> Ref \<lceil>?cond \<and> ?Icntrl\<rceil> \<lceil>?Icntrl\<rceil>" (is "_ \<le> ?branch1")
    by (rule R_assign_rule, pred_simp)
  have ifbranch2: "(IF U(Pump = 1 \<and> h\<^sub>0 \<ge> hmax - 1) THEN (Pump ::= 0) ELSE skip) \<le> 
    Ref \<lceil>\<not> ?cond \<and> ?Icntrl\<rceil> \<lceil>?Icntrl\<rceil>" (is "_ \<le> ?branch2")
    apply(rule order_trans, rule R_cond_mono) defer defer
      apply (rule R_cond)
    by (auto intro!: R_assign_rule R_skip, pred_simp, pred_simp, auto)
  have ifthenelse: "(IF ?cond THEN ?branch1 ELSE ?branch2) \<le> Ref \<lceil>?Icntrl\<rceil> \<lceil>?Icntrl\<rceil>" (is "?ifthenelse \<le> _") 
    by (rule R_cond)
  have "(IF ?cond THEN (Pump ::= 1) ELSE (IF U(Pump = 1 \<and> h\<^sub>0 \<ge> hmax - 1) THEN (Pump ::= 0) ELSE skip)) \<le>
   Ref \<lceil>?Icntrl\<rceil> \<lceil>?Icntrl\<rceil>"
    apply(rule_tac y="?ifthenelse" in order_trans, rule R_cond_mono)
    using ifbranch1 ifbranch2 ifthenelse by auto
  hence ctrl: "?ctrl \<le> Ref \<lceil>I hmin hmax\<rceil> \<lceil>?Icntrl\<rceil>"
    apply(rule_tac R="?Icntrl" in R_seq_rule)
     apply(rule_tac R="U(I hmin hmax \<and> t = 0)" in R_seq_rule)
    apply(rule R_assign_rule, pred_simp)+
    by simp
  \<comment> \<open>Then we refine the dynamics. \<close>
  have dynup: "(x\<acute>=\<lbrakk>f (c\<^sub>i-c\<^sub>o)\<rbrakk>\<^sub>e & G hmax (c\<^sub>i-c\<^sub>o) on {0..\<tau>} UNIV @ 0 DINV (dI hmin hmax (c\<^sub>i-c\<^sub>o))) \<le> 
    Ref \<lceil>U(Pump = 0 \<and> I hmin hmax \<and> t = 0 \<and> h\<^sub>0 = h)\<rceil> \<lceil>I hmin hmax\<rceil>"
    apply(rule R_g_ode_inv[OF tank_diff_inv[OF assms(1)]])
    using assms apply(simp_all, pred_simp, pred_simp)
    by (auto simp: tank_inv_arith1)
  have dyndown: "(x\<acute>=\<lbrakk>f (-c\<^sub>o)\<rbrakk>\<^sub>e & G hmin (-c\<^sub>o) on {0..\<tau>} UNIV @ 0 DINV (dI hmin hmax (-c\<^sub>o))) \<le> 
    Ref \<lceil>U(\<not> Pump = 0 \<and> I hmin hmax \<and> t = 0 \<and> h\<^sub>0 = h)\<rceil> \<lceil>I hmin hmax\<rceil>"
    apply(rule R_g_ode_inv, simp)
    using tank_diff_inv[OF assms(1), of "-c\<^sub>o"] apply(pred_simp)
    using assms apply(simp_all, pred_simp, pred_simp)
    by (auto simp: tank_inv_arith2)
  have dyn: "?dyn \<le> Ref \<lceil>?Icntrl\<rceil> \<lceil>I hmin hmax\<rceil>"
    apply(rule order_trans, rule R_cond_mono)
    using dynup dyndown apply(force, force)
    by (rule R_cond)
  \<comment> \<open>Finally we put everything together. \<close>
  have pre_pos: "\<lceil>I hmin hmax\<rceil> \<le> \<lceil>I hmin hmax\<rceil>"
    by simp
  have inv_inv: "Ref \<lceil>I hmin hmax\<rceil> \<lceil>?Icntrl\<rceil>; (Ref \<lceil>?Icntrl\<rceil> \<lceil>I hmin hmax\<rceil>) \<le> Ref \<lceil>I hmin hmax\<rceil> \<lceil>I hmin hmax\<rceil>"
    by (rule R_seq)
  have loopref: "LOOP Ref \<lceil>I hmin hmax\<rceil> \<lceil>?Icntrl\<rceil>; (Ref \<lceil>?Icntrl\<rceil> \<lceil>I hmin hmax\<rceil>) INV I hmin hmax \<le> ?ref"
    apply(rule R_loop)
    using pre_pos inv_inv by auto
  have obs: "?ctrl;?dyn \<le> Ref \<lceil>I hmin hmax\<rceil> \<lceil>?Icntrl\<rceil>; (Ref \<lceil>?Icntrl\<rceil> \<lceil>I hmin hmax\<rceil>)"
    apply(rule R_seq_mono)
    using ctrl dyn by auto
  show "LOOP (?ctrl;?dyn) INV I hmin hmax \<le> ?ref"
    by (rule order_trans[OF _ loopref], rule R_loop_mono[OF obs])
qed

no_notation ftank ("f")
        and tank_flow ("\<phi>")
        and tank_guard ("G")
        and tank_loop_inv ("I")
        and tank_diff_inv ("dI")

end