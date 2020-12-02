(*  Title:       Examples of hybrid systems verifications
    Author:      Jonathan Julián Huerta y Munive, 2019
    Maintainer:  Jonathan Julián Huerta y Munive <jjhuertaymunive1@sheffield.ac.uk>
*)

subsection \<open> Examples \<close>

text \<open> We prove partial correctness specifications of some hybrid systems with our 
refinement and verification components.\<close>

theory KAT_rKAT_exuclid_Examples_ndfun
  imports KAT_rKAT_rVCs_ndfun "UTP-dL.utp_hyprog_deriv"
begin recall_syntax

declare [[coercion Rep_uexpr]]

\<comment> \<open>Frechet derivatives \<close>

no_notation dual ("\<partial>")
        and n_op ("n _" [90] 91)
        and vec_nth (infixl "$" 90)

notation vec_nth (infixl "\<exclamdown>" 90)

abbreviation "\<e> k \<equiv> axis k (1::real)"

lemma frechet_derivative_id:
  fixes t::"'a :: {inverse,banach,real_normed_algebra_1}"
  shows "\<partial> (\<lambda>t::'a. t) (at t) = (\<lambda>t. t)"
  using frechet_derivative_at[OF has_derivative_id] unfolding id_def ..

lemma has_derivative_exp: "D exp \<mapsto> (\<lambda>t. t \<cdot> exp x) at x within T" for x::real
  by (auto intro!: derivative_intros)

lemma has_derivative_exp_compose: 
  fixes f::"real \<Rightarrow> real"
  assumes "D f \<mapsto> f' at y within T"
  shows "D (\<lambda>t. exp (f t)) \<mapsto> (\<lambda>x. f' x \<cdot> exp (f y)) at y within T"
  using has_derivative_compose[OF assms has_derivative_exp] by simp

lemma frechet_derivative_works1: "f differentiable (at t) \<Longrightarrow> (D f \<mapsto> (\<partial> f (at t)) (at t))" for t::real
  by (simp add: frechet_derivative_works)

lemmas frechet_derivative_exp = 
  frechet_derivative_works1[THEN frechet_derivative_at[OF has_derivative_exp_compose, symmetric]]

lemma differentiable_exp[simp]: "exp differentiable (at x)" for x::"'a::{banach,real_normed_field}"
  unfolding differentiable_def using DERIV_exp[of x] unfolding has_field_derivative_def by blast

lemma differentiable_sin[simp]: "sin differentiable (at x)" for x::"'a::{banach,real_normed_field}"
  unfolding differentiable_def using DERIV_sin[of x] unfolding has_field_derivative_def by blast

lemma differentiable_cos[simp]: "cos differentiable (at x)" for x::"'a::{banach,real_normed_field}"
  unfolding differentiable_def using DERIV_cos[of x] unfolding has_field_derivative_def by blast

lemma differentiable_exp_compose[derivative_intros]: 
  fixes f::"'a::real_normed_vector \<Rightarrow> 'b::{banach,real_normed_field}"
  shows "f differentiable (at x) \<Longrightarrow> (\<lambda>t. exp (f t)) differentiable (at x)"
  by (rule differentiable_compose[of exp], simp_all)

named_theorems frechet_simps "simplification rules for Frechet derivatives"

declare frechet_derivative_plus   [frechet_simps]
        frechet_derivative_minus  [frechet_simps]
        frechet_derivative_uminus [frechet_simps]
        frechet_derivative_mult   [frechet_simps]
        frechet_derivative_power  [frechet_simps]
        frechet_derivative_exp    [frechet_simps]
        frechet_derivative_sin    [frechet_simps]
        frechet_derivative_id     [frechet_simps]
        frechet_derivative_const  [frechet_simps]

method frechet_derivate
  = (subst frechet_simps; (frechet_derivate)?)

lemma "D (\<lambda>t. a * t\<^sup>2 + v * t + x) = (\<lambda>t. 2 * a * t + v) on T"
  by(auto intro!: poly_derivatives)

lemma "\<partial> (\<lambda>t. a \<cdot> t\<^sup>2 + v \<cdot> t + x) (at t) = (\<lambda>x. x \<cdot> (2 \<cdot> a \<cdot> t + v))" for t::real
  by (simp add: frechet_simps field_simps)

lemma "D (\<lambda>t. a5 * t^5 - a2 * exp (t^2) + a1 * sin t + a0) = 
  (\<lambda>t. 5 * a5 * t^4 - 2 * a2 * t * exp (t^2) + a1 * cos t) on T"
  by (auto intro!: poly_derivatives)

lemma "\<partial> (\<lambda>t. a5 \<cdot> t ^ 5 - a2 \<cdot> exp (t\<^sup>2) + a1 \<cdot> sin t + a0) (at t) =
  (\<lambda>x. x \<cdot> (5 \<cdot> a5 \<cdot> t ^ 4 - 2 \<cdot> a2 \<cdot> t \<cdot> exp (t\<^sup>2) + a1 \<cdot> cos t))" for t::real
  by (frechet_derivate, auto simp: field_simps intro!: derivative_intros)

utp_lit_vars

\<comment> \<open>A tactic for verification of hybrid programs \<close>

named_theorems hoare_intros

declare H_assign_init [hoare_intros]
    and H_cond [hoare_intros]
    and local_flow.H_g_ode_ivl [hoare_intros]
    and H_g_ode_inv [hoare_intros]

method body_hoare 
  = (rule hoare_intros,(simp)?; body_hoare?)

method hyb_hoare for P::"'a upred" 
  = (rule H_loopI, rule H_seq[where R=P]; body_hoare?)

\<comment> \<open>A tactic for refinement of hybrid programs \<close>

named_theorems refine_intros "selected refinement lemmas"

declare R_loop_law [refine_intros]
    and R_loop_mono [refine_intros]
    and R_cond_law [refine_intros]
    and R_cond_mono [refine_intros]
    and R_while_law [refine_intros]
    and R_assignl [refine_intros]
    and R_seq_law [refine_intros]
    and R_seq_mono [refine_intros]
    and R_g_evol_law [refine_intros]
    and R_skip [refine_intros]
    and R_g_ode_inv [refine_intros]

method refinement
  = (rule refine_intros; (refinement)?)

declare eucl_of_list_def [simp]
    and axis_def [simp]

\<comment> \<open>Preliminary lemmas for type 2 \<close>

lemma two_eq_zero[simp]: "(2::2) = 0" 
  by simp

declare forall_2 [simp]

instance integer :: order_lean
  by intro_classes auto

lemma enum_2[simp]: "(enum_class.enum::2 list) = [0::2, 1]"
  by code_simp+

lemma basis_list2[simp]: "Basis_list = [\<e> (0::2), \<e> 1]"
  by (auto simp: Basis_list_vec_def Basis_list_real_def)

lemma list_of_eucl2[simp]: "list_of_eucl (s::real^2) = map ((\<bullet>) s) [\<e> (0::2), \<e> 1]"
  unfolding list_of_eucl_def by simp

lemma inner_axis2[simp]: "x \<bullet> (\<chi> j::2. if j = i then (k::real) else 0) = (x\<exclamdown>i) \<cdot> k"
  unfolding inner_vec_def UNIV_2 inner_real_def using exhaust_2 by force

\<comment> \<open>Preliminary lemmas for type 2 \<close>

declare forall_4 [simp]

lemma four_eq_zero[simp]: "(4::4) = 0" 
  by simp

lemma enum_4[simp]: "(enum_class.enum::4 list) = [0::4, 1, 2, 3]"
  by code_simp+

lemma basis_list4[simp]: "Basis_list = [\<e> (0::4), \<e> 1, \<e> 2, \<e> 3]"
  by (auto simp: Basis_list_vec_def Basis_list_real_def)

lemma list_of_eucl4[simp]: "list_of_eucl (s::real^4) = map ((\<bullet>) s) [\<e> (0::4), \<e> 1, \<e> 2, \<e> 3]"
  unfolding list_of_eucl_def by simp

lemma inner_axis4[simp]: "x \<bullet> (\<chi> j::4. if j = i then (k::real) else 0) = (x\<exclamdown>i) \<cdot> k"
  unfolding inner_vec_def UNIV_4 inner_real_def using exhaust_4 by force

subsubsection \<open>Pendulum\<close>

abbreviation x :: "real \<Longrightarrow> real^2" where "x \<equiv> \<Pi>[0]"
abbreviation y :: "real \<Longrightarrow> real^2" where "y \<equiv> \<Pi>[Suc 0]"

text \<open> The ODEs @{text "x' t = y t"} and {text "y' t = - x t"} describe the circular motion of 
a mass attached to a string looked from above. We prove that this motion remains circular. \<close>

abbreviation fpend :: "(real^2) usubst" ("f") 
  where "fpend \<equiv> [x \<mapsto>\<^sub>s y, y \<mapsto>\<^sub>s -x]"

abbreviation pend_flow :: "real \<Rightarrow> (real^2) usubst" ("\<phi>") 
  where "pend_flow \<tau> \<equiv> [x \<mapsto>\<^sub>s x \<cdot> cos \<tau> + y \<cdot> sin \<tau>, y \<mapsto>\<^sub>s - x \<cdot> sin \<tau> + y \<cdot> cos \<tau>]"

\<comment> \<open>Verified with annotated dynamics \<close>

lemma pendulum_dyn: "\<^bold>{r\<^sup>2 = x\<^sup>2 + y\<^sup>2\<^bold>}(EVOL \<phi> G T)\<^bold>{r\<^sup>2 = x\<^sup>2 + y\<^sup>2\<^bold>}"
  apply (simp, rel_auto) oops

\<comment> \<open>Verified with invariants \<close>

lemma pendulum_inv: "\<^bold>{r\<^sup>2 = x\<^sup>2 + y\<^sup>2\<^bold>} (x\<acute>= f & G) \<^bold>{r\<^sup>2 = x\<^sup>2 + y\<^sup>2\<^bold>}"
  by (pred_simp, auto simp: eucl_nth_def intro!: poly_derivatives diff_invariant_rules)

\<comment> \<open>Verified by providing solutions \<close>

lemma local_flow_pend: "local_flow f UNIV UNIV \<phi>"
  apply(unfold_locales, simp_all add: local_lipschitz_def lipschitz_on_def vec_eq_iff, clarsimp)
    apply(rule_tac x="1" in exI, clarsimp, rule_tac x=1 in exI, pred_simp)
    apply(simp add: eucl_nth_def dist_norm norm_vec_def L2_set_def power2_commute UNIV_2, pred_simp)
  by (auto simp: eucl_nth_def intro!: poly_derivatives, rel_auto' simp: eucl_nth_def)

lemma pendulum_flow: "\<^bold>{r\<^sup>2 = x\<^sup>2 + y\<^sup>2\<^bold>} (x\<acute>= f & G) \<^bold>{r\<^sup>2 = x\<^sup>2 + y\<^sup>2\<^bold>}"
  by (simp only: local_flow.sH_g_ode[OF local_flow_pend], rel_auto' simp: eucl_nth_def)

no_notation fpend ("f")
        and pend_flow ("\<phi>")


subsubsection \<open> Bouncing Ball \<close>

text \<open> A ball is dropped from rest at an initial height @{text "h"}. The motion is described with 
the free-fall equations @{text "x' t = v t"} and @{text "v' t = g"} where @{text "g"} is the 
constant acceleration due to gravity. The bounce is modelled with a variable assigntment that 
flips the velocity, thus it is a completely elastic collision with the ground. We prove that the 
ball remains above ground and below its initial resting position. \<close>

abbreviation v :: "real \<Longrightarrow> real^2" 
  where "v \<equiv> \<Pi>[Suc 0]"

abbreviation fball :: "real \<Rightarrow> (real, 2) vec \<Rightarrow> (real, 2) vec" ("f") 
  where "f g \<equiv> [x \<mapsto>\<^sub>s v, v \<mapsto>\<^sub>s g]"

abbreviation ball_flow :: "real \<Rightarrow> real \<Rightarrow> (real^2) usubst" ("\<phi>") 
  where "\<phi> g \<tau> \<equiv> [x \<mapsto>\<^sub>s g \<cdot> \<tau> ^ 2/2 + v \<cdot> \<tau> + x,  v \<mapsto>\<^sub>s g \<cdot> \<tau> + v]"

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
  defines dinv: "I \<equiv> \<^U>(2 \<cdot> \<guillemotleft>g\<guillemotright> \<cdot> x - 2 \<cdot> \<guillemotleft>g\<guillemotright> \<cdot> \<guillemotleft>h\<guillemotright> - (v \<cdot> v) = 0)"
  shows "diff_invariant I (f g) UNIV UNIV 0 G"
  unfolding dinv apply(pred_simp, rule diff_invariant_rules, simp, simp, clarify)
  by (auto simp: eucl_nth_def intro!: poly_derivatives)

abbreviation "bb_dinv g h \<equiv> 
  (LOOP
    ((x\<acute>= f g & (x \<ge> 0) DINV (2 \<cdot> g \<cdot> x - 2 \<cdot> g \<cdot> h - v \<cdot> v = 0));
    (IF (v = 0) THEN (v ::= -v) ELSE skip)) 
  INV (0 \<le> x \<and> 2 \<cdot> g \<cdot> x = 2 \<cdot> g \<cdot> h + v \<cdot> v))"

lemma bouncing_ball_inv: "g < 0 \<Longrightarrow> h \<ge> 0 \<Longrightarrow> \<^bold>{x = h \<and> v = 0\<^bold>} bb_dinv g h \<^bold>{0 \<le> x \<and> x \<le> h\<^bold>}"
  apply(hyb_hoare "\<^U>(0 \<le> x \<and> 2 \<cdot> g \<cdot> x = 2 \<cdot> g \<cdot> h + v \<cdot> v)")
  using fball_invariant apply (simp_all)
  by (rel_auto' simp: bb_real_arith)


\<comment> \<open>Verified with annotated dynamics \<close>

lemma [bb_real_arith]:
  fixes x v :: real
  assumes invar: "2 \<cdot> g \<cdot> x = 2 \<cdot> g \<cdot> h + v \<cdot> v"
    and pos: "g \<cdot> \<tau>\<^sup>2 / 2 + v \<cdot> \<tau> + (x::real) = 0"
  shows "2 \<cdot> g \<cdot> h + (- (g \<cdot> \<tau>) - v) \<cdot> (- (g \<cdot> \<tau>) - v) = 0"
    and "2 \<cdot> g \<cdot> h + (g \<cdot> \<tau> \<cdot> (g \<cdot> \<tau> + v) + v \<cdot> (g \<cdot> \<tau> + v)) = 0"
  using assms
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
  shows "\<^bold>{x = h \<and> v = 0\<^bold>} bb_evol g h T \<^bold>{0 \<le> x \<and> x \<le> h\<^bold>}"
  apply(hyb_hoare "\<^U>(0 \<le> x \<and> 2 \<cdot> g \<cdot> x = 2 \<cdot> g \<cdot> h + v \<cdot> v)")
  using assms by (rel_auto' simp: bb_real_arith)

\<comment> \<open>Verified by providing solutions \<close>

lemma local_flow_ball: "local_flow (f g) UNIV UNIV (\<phi> g)"
  apply(unfold_locales, simp_all add: local_lipschitz_def lipschitz_on_def vec_eq_iff, clarsimp)
  apply(rule_tac x="1/2" in exI, clarsimp, rule_tac x=1 in exI, pred_simp)
    apply(simp add: dist_norm norm_vec_def L2_set_def UNIV_2)
  by (rel_auto' simp: eucl_nth_def, auto intro!: poly_derivatives)

abbreviation "bb_sol g h \<equiv>
  (LOOP (
    (x\<acute>= f g & (x \<ge> 0));
    (IF (v = 0) THEN (v ::= -v) ELSE skip))
  INV (0 \<le> x \<and> 2 \<cdot> g \<cdot> x = 2 \<cdot> g \<cdot> h + v \<cdot> v))"

lemma bouncing_ball_flow: 
  assumes "g < 0" and "h \<ge> 0"
  shows "\<^bold>{x = h \<and> v = 0\<^bold>} bb_sol g h \<^bold>{0 \<le> x \<and> x \<le> h\<^bold>}"
  apply(hyb_hoare "\<^U>(0 \<le> x \<and> 2 \<cdot> g \<cdot> x = 2 \<cdot> g \<cdot> h + v \<cdot> v)")
      apply(subst local_flow.sH_g_ode[OF local_flow_ball])
  using assms by (rel_auto' simp: bb_real_arith)

\<comment> \<open>Refined with annotated dynamics \<close>

lemma R_bb_assign: "g < (0::real) \<Longrightarrow> 0 \<le> h \<Longrightarrow> 
  \<^bold>[v = 0 \<and> 0 \<le> x \<and> 2 \<cdot> g \<cdot> x = 2 \<cdot> g \<cdot> h + v \<cdot> v, 0 \<le> x \<and> 2 \<cdot> g \<cdot> x = 2 \<cdot> g \<cdot> h + v \<cdot> v\<^bold>] \<ge> (v ::= - v)"
  by (rule R_assign_law, pred_simp)

lemma R_bouncing_ball_dyn:
  assumes "g < 0" and "h \<ge> 0"
  shows "\<^bold>[x = h \<and> v = 0, 0 \<le> x \<and> x \<le> h\<^bold>] \<ge> bb_evol g h T"
  apply(refinement; (rule R_bb_assign[OF assms])?)
  using assms by (rel_auto' simp: bb_real_arith)

no_notation fball ("f")
        and ball_flow ("\<phi>")


subsubsection \<open> Thermostat \<close>

text \<open> A thermostat has a chronometer, a thermometer and a switch to turn on and off a heater. 
At most every @{text "\<tau>"} minutes, it sets its chronometer to @{term "0::real"}, it registers 
the room temperature, and it turns the heater on (or off) based on this reading. The temperature 
follows the ODE @{text "T' = - a * (T - c)"} where @{text "c = L \<ge> 0"} when the heater 
is on, and @{text "c = 0"} when it is off. We prove that the thermostat keeps the room's 
temperature between @{text "T\<^sub>l"} and @{text "T\<^sub>h"}. \<close>

hide_const t

abbreviation T :: "real \<Longrightarrow> real^4" where "T \<equiv> \<Pi>[0]"
abbreviation t :: "real \<Longrightarrow> real^4" where "t \<equiv> \<Pi>[1]"
abbreviation T\<^sub>0 :: "real \<Longrightarrow> real^4" where "T\<^sub>0 \<equiv> \<Pi>[2]"
abbreviation \<theta> :: "real \<Longrightarrow> real^4" where "\<theta> \<equiv> \<Pi>[3]"

abbreviation ftherm :: "real \<Rightarrow> real \<Rightarrow> (real, 4) vec \<Rightarrow> (real, 4) vec" ("f")
  where "f a c \<equiv> [T \<mapsto>\<^sub>s - (a * (T - c)), T\<^sub>0 \<mapsto>\<^sub>s 0, \<theta> \<mapsto>\<^sub>s 0, t \<mapsto>\<^sub>s 1]"

abbreviation therm_guard :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real^4) upred" ("G")
  where "G T\<^sub>l T\<^sub>h a L \<equiv> \<^U>(t \<le> - (ln ((L-(if L=0 then T\<^sub>l else T\<^sub>h))/(L-T\<^sub>0)))/a)"

no_utp_lift "therm_guard" (0 1 2 3)

abbreviation therm_loop_inv :: "real \<Rightarrow> real \<Rightarrow> (real^4) upred" ("I")
  where "I T\<^sub>l T\<^sub>h \<equiv> \<^U>(T\<^sub>l \<le> T \<and> T \<le> T\<^sub>h \<and> (\<theta> = 0 \<or> \<theta> = 1))"

no_utp_lift "therm_loop_inv" (0 1)

abbreviation therm_flow :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real^4) usubst" ("\<phi>") 
  where "\<phi> a c \<tau> \<equiv> [T \<mapsto>\<^sub>s - exp(-a * \<tau>) * (c - T) + c, t \<mapsto>\<^sub>s \<tau> + t, T\<^sub>0 \<mapsto>\<^sub>s T\<^sub>0, \<theta> \<mapsto>\<^sub>s \<theta>]"

abbreviation therm_ctrl :: "real \<Rightarrow> real \<Rightarrow> (real^4) nd_fun" ("ctrl")
  where "ctrl T\<^sub>l T\<^sub>h \<equiv> 
  (t ::= 0); (T\<^sub>0 ::= T);
  (IF (\<theta> = 0 \<and> T\<^sub>0 \<le> T\<^sub>l + 1) THEN (\<theta> ::= 1) ELSE 
   IF (\<theta> = 1 \<and> T\<^sub>0 \<ge> T\<^sub>h - 1) THEN (\<theta> ::= 0) ELSE skip)"

abbreviation therm_dyn :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real^4) nd_fun" ("dyn")
  where "dyn T\<^sub>l T\<^sub>h a T\<^sub>u \<tau> \<equiv> 
  IF (\<theta> = 0) THEN x\<acute>= f a 0 & G T\<^sub>l T\<^sub>h a 0 on {0..\<tau>} UNIV @ 0 
   ELSE x\<acute>= f a T\<^sub>u & G T\<^sub>l T\<^sub>h a T\<^sub>u on {0..\<tau>} UNIV @ 0"

abbreviation "therm T\<^sub>l T\<^sub>h a L \<tau> \<equiv> LOOP (ctrl T\<^sub>l T\<^sub>h ; dyn T\<^sub>l T\<^sub>h a L \<tau>) INV (I T\<^sub>l T\<^sub>h)"

\<comment> \<open>Verified by providing solutions \<close>

lemma norm_diff_therm_dyn: "0 < (a::real) \<Longrightarrow> (a \<cdot> (s\<^sub>2\<exclamdown>0 - T\<^sub>u) - a \<cdot> (s\<^sub>1\<exclamdown>0 - T\<^sub>u))\<^sup>2
       \<le> (a \<cdot> sqrt ((s\<^sub>1\<exclamdown>1 - s\<^sub>2\<exclamdown>1)\<^sup>2 + ((s\<^sub>1\<exclamdown>2 - s\<^sub>2\<exclamdown>2)\<^sup>2 + ((s\<^sub>1\<exclamdown>3 - s\<^sub>2\<exclamdown>3)\<^sup>2 + (s\<^sub>1\<exclamdown>0 - s\<^sub>2\<exclamdown>0)\<^sup>2))))\<^sup>2"
proof(simp add: field_simps)
  assume a1: "0 < a"
  have "(a \<cdot> s\<^sub>2\<exclamdown>0 - a \<cdot> s\<^sub>1\<exclamdown>0)\<^sup>2 = a\<^sup>2 \<cdot> (s\<^sub>2\<exclamdown>0 - s\<^sub>1\<exclamdown>0)\<^sup>2"
    by (metis (mono_tags, hide_lams) Rings.ring_distribs(4) mult.left_commute 
        semiring_normalization_rules(18) semiring_normalization_rules(29))
  moreover have "(s\<^sub>2\<exclamdown>0 - s\<^sub>1\<exclamdown>0)\<^sup>2 \<le> (s\<^sub>1\<exclamdown>0 - s\<^sub>2\<exclamdown>0)\<^sup>2 + ((s\<^sub>1\<exclamdown>1 - s\<^sub>2\<exclamdown>1)\<^sup>2 + ((s\<^sub>1\<exclamdown>2 - s\<^sub>2\<exclamdown>2)\<^sup>2 + (s\<^sub>1\<exclamdown>3 - s\<^sub>2\<exclamdown>3)\<^sup>2))"
    using zero_le_power2 by (simp add: power2_commute) 
  thus "(a \<cdot> s\<^sub>2\<exclamdown>0 - a \<cdot> s\<^sub>1\<exclamdown>0)\<^sup>2 \<le> a\<^sup>2 \<cdot> (s\<^sub>1\<exclamdown>1 - s\<^sub>2\<exclamdown>1)\<^sup>2 + 
  (a\<^sup>2 \<cdot> (s\<^sub>1\<exclamdown>0 - s\<^sub>2\<exclamdown>0)\<^sup>2 + (a\<^sup>2 \<cdot> (s\<^sub>1\<exclamdown>2 - s\<^sub>2\<exclamdown>2)\<^sup>2 + a\<^sup>2 \<cdot> (s\<^sub>1\<exclamdown>3 - s\<^sub>2\<exclamdown>3)\<^sup>2))"
    using a1 by (simp add: Groups.algebra_simps(18)[symmetric] calculation)
qed

lemma local_lipschitz_therm_dyn:
  assumes "0 < (a::real)"
  shows "local_lipschitz UNIV UNIV (\<lambda>t::real. f a T\<^sub>u)"
  apply(unfold local_lipschitz_def lipschitz_on_def dist_norm)
  apply(clarsimp, rule_tac x=1 in exI, clarsimp, rule_tac x=a in exI)
  using assms apply(simp add: norm_vec_def L2_set_def, unfold UNIV_4, pred_simp)
  unfolding real_sqrt_abs[symmetric] apply (rule real_le_lsqrt)
  by (simp_all add: norm_diff_therm_dyn )

lemma local_flow_therm: "a > 0 \<Longrightarrow> local_flow (f a T\<^sub>u) UNIV UNIV (\<phi> a T\<^sub>u)"
  apply (unfold_locales, simp_all)
  using local_lipschitz_therm_dyn apply pred_simp
   apply(pred_simp, force simp: eucl_nth_def intro!: poly_derivatives)
  using exhaust_4 by (rel_auto' simp: vec_eq_iff eucl_nth_def)

lemma therm_dyn_down:
  fixes T::real
  assumes "a > 0" and Thyps: "0 < T\<^sub>l" "T\<^sub>l \<le> T" "T \<le> T\<^sub>h"
    and thyps: "0 \<le> (\<tau>::real)" "\<forall>\<tau>\<in>{0..\<tau>}. \<tau> \<le> - (ln (T\<^sub>l / T) / a) "
  shows "T\<^sub>l \<le> exp (-a * \<tau>) * T" and "exp (-a * \<tau>) * T \<le> T\<^sub>h"
proof-
  have "0 \<le> \<tau> \<and> \<tau> \<le> - (ln (T\<^sub>l / T) / a)"
    using thyps by auto
  hence "ln (T\<^sub>l / T) \<le> - a * \<tau> \<and> - a * \<tau> \<le> 0"
    using assms(1) divide_le_cancel by fastforce
  also have "T\<^sub>l / T > 0"
    using Thyps by auto
  ultimately have obs: "T\<^sub>l / T \<le> exp (-a * \<tau>)" "exp (-a * \<tau>) \<le> 1"
    using exp_ln exp_le_one_iff by (metis exp_less_cancel_iff not_less, simp)
  thus "T\<^sub>l \<le> exp (-a * \<tau>) * T"
    using Thyps by (simp add: pos_divide_le_eq)
  show "exp (-a * \<tau>) * T \<le> T\<^sub>h"
    using Thyps mult_left_le_one_le[OF _ exp_ge_zero obs(2), of T] 
      less_eq_real_def order_trans_rules(23) by blast
qed

lemma therm_dyn_up:
  fixes T::real
  assumes "a > 0" and Thyps: "T\<^sub>l \<le> T" "T \<le> T\<^sub>h" "T\<^sub>h < (T\<^sub>u::real)"
    and thyps: "0 \<le> \<tau>" "\<forall>\<tau>\<in>{0..\<tau>}. \<tau> \<le> - (ln ((T\<^sub>u - T\<^sub>h) / (T\<^sub>u - T)) / a) "
  shows "T\<^sub>u - T\<^sub>h \<le> exp (-(a * \<tau>)) * (T\<^sub>u - T)" 
    and "T\<^sub>u - exp (-(a * \<tau>)) * (T\<^sub>u - T) \<le> T\<^sub>h" 
    and "T\<^sub>l \<le> T\<^sub>u - exp (-(a * \<tau>)) * (T\<^sub>u - T)"
proof-
  have "0 \<le> \<tau> \<and> \<tau> \<le> - (ln ((T\<^sub>u - T\<^sub>h) / (T\<^sub>u - T)) / a)"
    using thyps by auto
  hence "ln ((T\<^sub>u - T\<^sub>h) / (T\<^sub>u - T)) \<le> - a * \<tau> \<and> - a * \<tau> \<le> 0"
    using assms(1) divide_le_cancel by fastforce
  also have "(T\<^sub>u - T\<^sub>h) / (T\<^sub>u - T) > 0"
    using Thyps by auto
  ultimately have "(T\<^sub>u - T\<^sub>h) / (T\<^sub>u - T) \<le> exp (-a * \<tau>) \<and> exp (-a * \<tau>) \<le> 1"
    using exp_ln exp_le_one_iff by (metis exp_less_cancel_iff not_less)
  moreover have "T\<^sub>u - T > 0"
    using Thyps by auto
  ultimately have obs: "(T\<^sub>u - T\<^sub>h) \<le> exp (-a * \<tau>) * (T\<^sub>u - T) \<and> exp (-a * \<tau>) * (T\<^sub>u - T) \<le> (T\<^sub>u - T)"
    by (simp add: pos_divide_le_eq)
  thus "(T\<^sub>u - T\<^sub>h) \<le> exp (-(a * \<tau>)) * (T\<^sub>u - T)"
    by auto
  thus "T\<^sub>u - exp (-(a * \<tau>)) * (T\<^sub>u - T) \<le> T\<^sub>h"
    by auto
  show "T\<^sub>l \<le> T\<^sub>u - exp (-(a * \<tau>)) * (T\<^sub>u - T)"
    using Thyps and obs by auto
qed

lemmas H_g_ode_therm = local_flow.sH_g_ode_ivl[OF local_flow_therm _ UNIV_I]

lemma thermostat_flow: 
  assumes "0 < a" and "0 \<le> \<tau>" and "0 < T\<^sub>l" and "T\<^sub>h < T\<^sub>u"
  shows "\<^bold>{I T\<^sub>l T\<^sub>h\<^bold>} therm T\<^sub>l T\<^sub>h a T\<^sub>u \<tau> \<^bold>{I T\<^sub>l T\<^sub>h\<^bold>}"
  apply(hyb_hoare "\<^U>(I T\<^sub>l T\<^sub>h \<and> t=0 \<and> T\<^sub>0 = T)")
              prefer 4 prefer 8 using local_flow_therm assms apply force+
  using assms therm_dyn_up therm_dyn_down by rel_auto'

\<comment> \<open>Refined by providing solutions \<close>

lemma R_therm_down: 
  assumes "a > 0" and "0 \<le> \<tau>" and "0 < T\<^sub>l" and "T\<^sub>h < T\<^sub>u"
  shows "\<^bold>[\<theta> = 0 \<and> I T\<^sub>l T\<^sub>h \<and> t = 0 \<and> T\<^sub>0 = T, I T\<^sub>l T\<^sub>h\<^bold>] \<ge> 
  (x\<acute>= f a 0 & G T\<^sub>l T\<^sub>h a 0 on {0..\<tau>} UNIV @ 0)"
  apply(rule local_flow.R_g_ode_ivl[OF local_flow_therm])
  using therm_dyn_down[OF assms(1,3), of _ T\<^sub>h] assms by (rel_auto' simp: eucl_nth_def)

lemma R_therm_up: 
  assumes "a > 0" and "0 \<le> \<tau>" and "0 < T\<^sub>l" and "T\<^sub>h < T\<^sub>u"
  shows "\<^bold>[\<not> \<theta> = 0 \<and> I T\<^sub>l T\<^sub>h \<and> t = 0 \<and> T\<^sub>0 = T, I T\<^sub>l T\<^sub>h\<^bold>] \<ge> 
  (x\<acute>= f a T\<^sub>u & G T\<^sub>l T\<^sub>h a T\<^sub>u on {0..\<tau>} UNIV @ 0)"
  apply(rule local_flow.R_g_ode_ivl[OF local_flow_therm])
  using therm_dyn_up[OF assms(1) _ _ assms(4), of T\<^sub>l] assms by (rel_auto' simp: eucl_nth_def)

lemma R_therm_time: "\<^bold>[I T\<^sub>l T\<^sub>h, I T\<^sub>l T\<^sub>h \<and> t = 0\<^bold>] \<ge> (t ::= 0)"
  by (rule R_assign_law, pred_simp)

lemma R_therm_temp: "\<^bold>[I T\<^sub>l T\<^sub>h \<and> t = 0, I T\<^sub>l T\<^sub>h \<and> t = 0 \<and> T\<^sub>0 = T\<^bold>] \<ge> (T\<^sub>0 ::= T)"
  by (rule R_assign_law, pred_simp)

lemma R_thermostat_flow:
  assumes "a > 0" and "0 \<le> \<tau>" and "0 < T\<^sub>l" and "T\<^sub>h < T\<^sub>u"
  shows "\<^bold>[I T\<^sub>l T\<^sub>h, I T\<^sub>l T\<^sub>h\<^bold>] \<ge> therm T\<^sub>l T\<^sub>h a T\<^sub>u \<tau>"
  by (refinement; (rule R_therm_time)?, (rule R_therm_temp)?, (rule R_assign_law)?, 
      (rule R_therm_up[OF assms])?, (rule R_therm_down[OF assms])?) rel_auto'

no_notation ftherm ("f")
        and therm_flow ("\<phi>")
        and therm_guard ("G")
        and therm_loop_inv ("I")
        and therm_ctrl ("ctrl")
        and therm_dyn ("dyn")


subsubsection \<open> Water tank \<close>  \<comment> \<open>Variation of Hespanha and \cite{AlurCHHHNOSY95}\<close>

abbreviation h :: "real \<Longrightarrow> real^4" where "h \<equiv> \<Pi>[0]"
abbreviation h\<^sub>0 :: "real \<Longrightarrow> real^4" where "h\<^sub>0 \<equiv> \<Pi>[2]"
abbreviation \<pi> :: "real \<Longrightarrow> real^4" where "\<pi> \<equiv> \<Pi>[3]"

abbreviation ftank :: "real \<Rightarrow> (real, 4) vec \<Rightarrow> (real, 4) vec" ("f")
  where "f k \<equiv> [\<pi> \<mapsto>\<^sub>s 0, h \<mapsto>\<^sub>s k, h\<^sub>0 \<mapsto>\<^sub>s 0, t \<mapsto>\<^sub>s 1]"

abbreviation tank_flow :: "real \<Rightarrow> real \<Rightarrow> (real^4) usubst" ("\<phi>") 
  where "\<phi> k \<tau> \<equiv> [h \<mapsto>\<^sub>s k * \<tau> + h, t \<mapsto>\<^sub>s \<tau> + t, h\<^sub>0 \<mapsto>\<^sub>s h\<^sub>0, \<pi> \<mapsto>\<^sub>s \<pi>]"

abbreviation tank_guard :: "real \<Rightarrow> real \<Rightarrow> (real^4) upred" ("G")
  where "G h\<^sub>x k \<equiv> \<^U>(t \<le> (h\<^sub>x - h\<^sub>0)/k)"

no_utp_lift "tank_guard" (0 1)

abbreviation tank_loop_inv :: "real \<Rightarrow> real \<Rightarrow> (real^4) upred" ("I")
  where "I h\<^sub>l h\<^sub>h \<equiv> \<^U>(h\<^sub>l \<le> h \<and> h \<le> h\<^sub>h \<and> (\<pi> = 0 \<or> \<pi> = 1))"

no_utp_lift "tank_loop_inv" (0 1)

abbreviation tank_diff_inv :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real^4) upred" ("dI")
  where "dI h\<^sub>l h\<^sub>h k \<equiv> \<^U>(h = k \<cdot> t + h\<^sub>0 \<and> 0 \<le> t \<and> h\<^sub>l \<le> h\<^sub>0 \<and> h\<^sub>0 \<le> h\<^sub>h \<and> (\<pi> = 0 \<or> \<pi> = 1))"

no_utp_lift "tank_diff_inv" (0 1 2)

\<comment> \<open>Verified by providing solutions \<close>

lemma local_flow_tank: "local_flow (f k) UNIV UNIV (\<phi> k)"
  apply(unfold_locales, unfold local_lipschitz_def lipschitz_on_def, simp_all, clarsimp)
  apply(rule_tac x="1/2" in exI, clarsimp, rule_tac x=1 in exI)
    apply(simp add: dist_norm norm_vec_def L2_set_def, unfold UNIV_4, pred_simp)
   apply(pred_simp, force intro!: poly_derivatives)
  using exhaust_4 by (rel_auto' simp: vec_eq_iff)

lemma tank_arith:
  fixes y::real
  assumes "0 \<le> (\<tau>::real)" and "0 < c\<^sub>o" and "c\<^sub>o < c\<^sub>i"
  shows "\<forall>\<tau>\<in>{0..\<tau>}. \<tau> \<le> - ((h\<^sub>l - y) / c\<^sub>o) \<Longrightarrow>  h\<^sub>l \<le> y - c\<^sub>o * \<tau>"
    and "\<forall>\<tau>\<in>{0..\<tau>}. \<tau> \<le> (h\<^sub>h - y) / (c\<^sub>i - c\<^sub>o) \<Longrightarrow>  (c\<^sub>i - c\<^sub>o) * \<tau> + y \<le> h\<^sub>h"
    and "h\<^sub>l \<le> y \<Longrightarrow> h\<^sub>l \<le> (c\<^sub>i - c\<^sub>o) \<cdot> \<tau> + y"
    and "y \<le> h\<^sub>h \<Longrightarrow> y - c\<^sub>o \<cdot> \<tau> \<le> h\<^sub>h"
  apply(simp_all add: field_simps le_divide_eq assms)
  using assms apply (meson add_mono less_eq_real_def mult_left_mono)
  using assms by (meson add_increasing2 less_eq_real_def mult_nonneg_nonneg) 

abbreviation tank_ctrl :: "real \<Rightarrow> real \<Rightarrow> (real^4) nd_fun" ("ctrl")
  where "ctrl h\<^sub>l h\<^sub>h \<equiv> (t ::=0);(h\<^sub>0 ::= h);
  (IF (\<pi> = 0 \<and> h\<^sub>0 \<le> h\<^sub>l + 1) THEN (\<pi> ::= 1) ELSE
  (IF (\<pi> = 1 \<and> h\<^sub>0 \<ge> h\<^sub>h - 1) THEN (\<pi> ::= 0) ELSE skip))"

abbreviation tank_dyn_sol :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real^4) nd_fun" ("dyn")
  where "dyn c\<^sub>i c\<^sub>o h\<^sub>l h\<^sub>h \<tau> \<equiv> (IF (\<pi> = 0) THEN 
    (x\<acute>= f (c\<^sub>i-c\<^sub>o) & G h\<^sub>h (c\<^sub>i-c\<^sub>o) on {0..\<tau>} UNIV @ 0)
  ELSE (x\<acute>= f (-c\<^sub>o) & G h\<^sub>l (-c\<^sub>o) on {0..\<tau>} UNIV @ 0))"

abbreviation "tank_sol c\<^sub>i c\<^sub>o h\<^sub>l h\<^sub>h \<tau> \<equiv> LOOP (ctrl h\<^sub>l h\<^sub>h ; dyn c\<^sub>i c\<^sub>o h\<^sub>l h\<^sub>h \<tau>) INV (I h\<^sub>l h\<^sub>h)"

lemmas H_g_ode_tank = local_flow.sH_g_ode_ivl[OF local_flow_tank _ UNIV_I]

lemma tank_flow:
  assumes "0 \<le> \<tau>" and "0 < c\<^sub>o" and "c\<^sub>o < c\<^sub>i"
  shows "\<^bold>{I h\<^sub>l h\<^sub>h\<^bold>} tank_sol c\<^sub>i c\<^sub>o h\<^sub>l h\<^sub>h \<tau> \<^bold>{I h\<^sub>l h\<^sub>h\<^bold>}"
  apply(hyb_hoare "\<^U>(I h\<^sub>l h\<^sub>h \<and> t = 0 \<and> h\<^sub>0 = h)")
              prefer 4 prefer 8 using assms local_flow_tank apply force+
  using assms tank_arith by rel_auto'

no_notation tank_dyn_sol ("dyn")

\<comment> \<open>Verified with invariants \<close>

lemma tank_diff_inv:
  "0 \<le> \<tau> \<Longrightarrow> diff_invariant (dI h\<^sub>l h\<^sub>h k) (f k) {0..\<tau>} UNIV 0 Guard"
  apply(pred_simp, intro diff_invariant_conj_rule)
      apply(force intro!: poly_derivatives diff_invariant_rules)
     apply(rule_tac \<nu>'="\<lambda>t. 0" and \<mu>'="\<lambda>t. 1" in diff_invariant_leq_rule, simp_all)
    apply(rule_tac \<nu>'="\<lambda>t. 0" and \<mu>'="\<lambda>t. 0" in diff_invariant_leq_rule, simp_all)
  by (auto intro!: poly_derivatives diff_invariant_rules)

lemma tank_inv_arith1:
  assumes "0 \<le> (\<tau>::real)" and "c\<^sub>o < c\<^sub>i" and b: "h\<^sub>l \<le> y\<^sub>0" and g: "\<tau> \<le> (h\<^sub>h - y\<^sub>0) / (c\<^sub>i - c\<^sub>o)"
  shows "h\<^sub>l \<le> (c\<^sub>i - c\<^sub>o) \<cdot> \<tau> + y\<^sub>0" and "(c\<^sub>i - c\<^sub>o) \<cdot> \<tau> + y\<^sub>0 \<le> h\<^sub>h"
proof-
  have "(c\<^sub>i - c\<^sub>o) \<cdot> \<tau> \<le> (h\<^sub>h - y\<^sub>0)"
    using g assms(2,3) by (metis diff_gt_0_iff_gt mult.commute pos_le_divide_eq) 
  thus "(c\<^sub>i - c\<^sub>o) \<cdot> \<tau> + y\<^sub>0 \<le> h\<^sub>h"
    by auto
  show "h\<^sub>l \<le> (c\<^sub>i - c\<^sub>o) \<cdot> \<tau> + y\<^sub>0"
    using b assms(1,2) by (metis add.commute add_increasing2 diff_ge_0_iff_ge 
        less_eq_real_def mult_nonneg_nonneg) 
qed

lemma tank_inv_arith2:
  assumes "0 \<le> (\<tau>::real)" and "0 < c\<^sub>o" and b: "y\<^sub>0 \<le> h\<^sub>h" and g: "\<tau> \<le> - ((h\<^sub>l - y\<^sub>0) / c\<^sub>o)"
  shows "h\<^sub>l \<le> y\<^sub>0 - c\<^sub>o \<cdot> \<tau>" and "y\<^sub>0 - c\<^sub>o \<cdot> \<tau> \<le> h\<^sub>h"
proof-
  have "\<tau> \<cdot> c\<^sub>o \<le> y\<^sub>0 - h\<^sub>l"
    using g \<open>0 < c\<^sub>o\<close> pos_le_minus_divide_eq by fastforce 
  thus "h\<^sub>l \<le> y\<^sub>0 - c\<^sub>o \<cdot> \<tau>"
    by (auto simp: mult.commute)
  show "y\<^sub>0 - c\<^sub>o \<cdot> \<tau> \<le> h\<^sub>h" 
    using b assms(1,2) by (smt linordered_field_class.sign_simps(39) mult_less_cancel_right) 
qed

abbreviation tank_dyn_dinv :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real^4) nd_fun" ("dyn")
  where "dyn c\<^sub>i c\<^sub>o h\<^sub>l h\<^sub>h \<tau> \<equiv> IF (\<pi> = 0) THEN 
    x\<acute>= f (c\<^sub>i-c\<^sub>o) & G h\<^sub>h (c\<^sub>i-c\<^sub>o) on {0..\<tau>} UNIV @ 0 DINV (dI h\<^sub>l h\<^sub>h (c\<^sub>i-c\<^sub>o))
  ELSE x\<acute>= f (-c\<^sub>o) & G h\<^sub>l (-c\<^sub>o) on {0..\<tau>} UNIV @ 0 DINV (dI h\<^sub>l h\<^sub>h (-c\<^sub>o))"

abbreviation "tank_dinv c\<^sub>i c\<^sub>o h\<^sub>l h\<^sub>h \<tau> \<equiv> LOOP (ctrl h\<^sub>l h\<^sub>h ; dyn c\<^sub>i c\<^sub>o h\<^sub>l h\<^sub>h \<tau>) INV (I h\<^sub>l h\<^sub>h)"

lemma tank_inv:
  assumes "0 \<le> \<tau>" and "0 < c\<^sub>o" and "c\<^sub>o < c\<^sub>i"
  shows "\<^bold>{I h\<^sub>l h\<^sub>h\<^bold>} tank_dinv c\<^sub>i c\<^sub>o h\<^sub>l h\<^sub>h \<tau> \<^bold>{I h\<^sub>l h\<^sub>h\<^bold>}"
  apply(hyb_hoare "\<^U>(I h\<^sub>l h\<^sub>h \<and> t = 0 \<and> h\<^sub>0 = h)")
            prefer 4 prefer 7 using tank_diff_inv assms apply force+
  using assms tank_inv_arith1 tank_inv_arith2 by rel_auto'

\<comment> \<open>Refined with invariants \<close>

lemma R_tank_inv:
  assumes "0 \<le> \<tau>" and "0 < c\<^sub>o" and "c\<^sub>o < c\<^sub>i"
  shows "\<^bold>[I h\<^sub>l h\<^sub>h, I h\<^sub>l h\<^sub>h\<^bold>] \<ge> tank_dinv c\<^sub>i c\<^sub>o h\<^sub>l h\<^sub>h \<tau>"
proof-
  have "\<^bold>[I h\<^sub>l h\<^sub>h, I h\<^sub>l h\<^sub>h\<^bold>] \<ge> LOOP ((t ::= 0);\<^bold>[I h\<^sub>l h\<^sub>h \<and> t = 0, I h\<^sub>l h\<^sub>h\<^bold>]) INV I h\<^sub>l h\<^sub>h" (is "_ \<ge> ?R")
    by (refinement, rel_auto')
  moreover have 
    "?R \<ge> LOOP ((t ::= 0);(h\<^sub>0 ::= h);\<^bold>[I h\<^sub>l h\<^sub>h \<and> t = 0 \<and> h\<^sub>0 = h, I h\<^sub>l h\<^sub>h\<^bold>]) INV I h\<^sub>l h\<^sub>h" (is "_ \<ge> ?R")
    by (refinement, rel_auto')
  moreover have 
    "?R \<ge> LOOP (ctrl h\<^sub>l h\<^sub>h;\<^bold>[I h\<^sub>l h\<^sub>h \<and> t = 0 \<and> h\<^sub>0 = h, I h\<^sub>l h\<^sub>h\<^bold>]) INV I h\<^sub>l h\<^sub>h" (is "_ \<ge> ?R")
    by (simp only: mult.assoc, refinement; (force)?, (rule R_assign_law)?) rel_auto'
  moreover have 
    "?R \<ge> LOOP (ctrl h\<^sub>l h\<^sub>h; dyn c\<^sub>i c\<^sub>o h\<^sub>l h\<^sub>h \<tau>) INV I h\<^sub>l h\<^sub>h"
    apply(simp only: mult.assoc, refinement; (simp)?)
         prefer 4 using tank_diff_inv assms apply force+
    using tank_inv_arith1 tank_inv_arith2 assms by rel_auto'
  ultimately show "\<^bold>[I h\<^sub>l h\<^sub>h, I h\<^sub>l h\<^sub>h\<^bold>] \<ge> tank_dinv c\<^sub>i c\<^sub>o h\<^sub>l h\<^sub>h \<tau>"
    by auto
qed

no_notation ftank ("f")
        and tank_flow ("\<phi>")
        and tank_guard ("G")
        and tank_loop_inv ("I")
        and tank_diff_inv ("dI")
        and tank_ctrl ("ctrl")
        and tank_dyn_dinv ("dyn")

end