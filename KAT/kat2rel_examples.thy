theory kat2rel_examples
  imports "../hs_prelims_matrices" kat2rel

begin


subsection \<open> Examples \<close>

text\<open> Preliminary preparation for the examples.\<close>

no_notation Archimedean_Field.ceiling ("\<lceil>_\<rceil>")
        and Archimedean_Field.floor_ceiling_class.floor ("\<lfloor>_\<rfloor>")

lemma exhaust_5:
  fixes x :: 5
  shows "x = 1 \<or> x = 2 \<or> x = 3 \<or> x = 4 \<or> x = 5"
proof (induct x)
  case (of_int z)
  hence "0 \<le> z" and "z < 5" 
    by simp_all
  hence "z = 0 \<or> z = 1 \<or> z = 2 \<or> z = 3 \<or> z = 4" 
    by arith
  thus ?case 
    by auto
qed

lemma UNIV_5: "(UNIV::5 set) = {1, 2, 3, 4, 5}"
  using exhaust_5 by auto

lemma forall_5: "(\<forall>i::5. P i) \<longleftrightarrow> P 1 \<and> P 2 \<and> P 3 \<and> P 4 \<and> P 5"
  by (metis exhaust_5)

lemma exhaust_6:
  fixes x :: 6
  shows "x = 1 \<or> x = 2 \<or> x = 3 \<or> x = 4 \<or> x = 5 \<or> x = 6"
proof (induct x)
  case (of_int z)
  hence "0 \<le> z" and "z < 6" 
    by simp_all
  hence "z = 0 \<or> z = 1 \<or> z = 2 \<or> z = 3 \<or> z = 4 \<or> z = 5" 
    by arith
  thus ?case 
    by auto
qed

lemma UNIV_6: "(UNIV::6 set) = {1, 2, 3, 4, 5, 6}"
  using exhaust_6 by auto

lemma forall_6: "(\<forall>i::6. P i) \<longleftrightarrow> P 1 \<and> P 2 \<and> P 3 \<and> P 4 \<and> P 5 \<and> P 6"
  by (metis exhaust_6)

subsubsection \<open>Pendulum\<close>

text \<open> The ODEs @{text "x' t = y t"} and {text "y' t = - x t"} describe the circular motion of 
a mass attached to a string looked from above. We use @{text "s$1"} to represent the x-coordinate
and @{text "s$2"} for the y-coordinate. We prove that this motion remains circular. \<close>

\<comment> \<open>Verified with differential invariants. \<close>

abbreviation fpend :: "real^2 \<Rightarrow> real^2" ("f")
  where "f s \<equiv> (\<chi> i. if i=1 then s$2 else -s$1)"

lemma pendulum_inv: "rel_kat.Hoare
  \<lceil>\<lambda>s. r\<^sup>2 = (s$1)\<^sup>2 + (s$2)\<^sup>2\<rceil> (x\<acute>=f & G) \<lceil>\<lambda>s. r\<^sup>2 = (s$1)\<^sup>2 + (s$2)\<^sup>2\<rceil>"
  by (auto intro!: diff_invariant_rules poly_derivatives)

\<comment> \<open>Verified with the flow. \<close>

abbreviation pend_flow :: "real \<Rightarrow> real^2 \<Rightarrow> real^2" ("\<phi>")
  where "\<phi> \<tau> s \<equiv> (\<chi> i. if i = 1 then s$1 \<cdot> cos \<tau> + s$2 \<cdot> sin \<tau> 
  else - s$1 \<cdot> sin \<tau> + s$2 \<cdot> cos \<tau>)"

lemma local_flow_pend: "local_flow f UNIV UNIV \<phi>"
  apply(unfold_locales, simp_all add: local_lipschitz_def lipschitz_on_def vec_eq_iff, clarsimp)
  apply(rule_tac x="1" in exI, clarsimp, rule_tac x=1 in exI)
    apply(simp add: dist_norm norm_vec_def L2_set_def power2_commute UNIV_2)
  by (auto simp: forall_2 intro!: poly_derivatives)

lemma pendulum_flow: "rel_kat.Hoare
  \<lceil>\<lambda>s. r\<^sup>2 = (s$1)\<^sup>2 + (s$2)\<^sup>2\<rceil> (x\<acute>=f & G) \<lceil>\<lambda>s. r\<^sup>2 = (s$1)\<^sup>2 + (s$2)\<^sup>2\<rceil>"
  by (simp only: local_flow.sH_g_ode[OF local_flow_pend], simp)

\<comment> \<open>Verified by providing dynamics. \<close>

lemma pendulum_dyn: "rel_kat.Hoare
  \<lceil>\<lambda>s. r\<^sup>2 = (s$1)\<^sup>2 + (s$2)\<^sup>2\<rceil> (EVOL \<phi> G T) \<lceil>\<lambda>s. r\<^sup>2 = (s$1)\<^sup>2 + (s$2)\<^sup>2\<rceil>"
  by simp

\<comment> \<open>Verified as a linear system (using uniqueness). \<close>

abbreviation pend_sq_mtx :: "2 sq_mtx" ("A")
  where "A \<equiv> sq_mtx_chi (\<chi> i. if i=1 then \<e> 2 else - \<e> 1)"

lemma pend_sq_mtx_exp_eq_flow: "exp (\<tau> *\<^sub>R A) *\<^sub>V s = \<phi> \<tau> s"
  apply(rule local_flow.eq_solution[OF local_flow_exp, symmetric], rule ivp_solsI)
  apply(clarsimp simp: sq_mtx_vec_prod_def matrix_vector_mult_def)
  apply(force intro!: poly_derivatives)
  using exhaust_2 by (auto simp: vec_eq_iff)

lemma pendulum_sq_mtx: "rel_kat.Hoare
  \<lceil>\<lambda>s. r\<^sup>2 = (s$1)\<^sup>2 + (s$2)\<^sup>2\<rceil> (x\<acute>= ((*\<^sub>V) A) & G) \<lceil>\<lambda>s. r\<^sup>2 = (s$1)\<^sup>2 + (s$2)\<^sup>2\<rceil>"
  apply(subst local_flow.sH_g_ode[OF local_flow_exp])
  unfolding pend_sq_mtx_exp_eq_flow by auto

no_notation fpend ("f")
        and pend_sq_mtx ("A")
        and pend_flow ("\<phi>")


subsubsection \<open> Bouncing Ball \<close>

text \<open> A ball is dropped from rest at an initial height @{text "h"}. The motion is described with 
the free-fall equations @{text "x' t = v t"} and @{text "v' t = g"} where @{text "g"} is the 
constant acceleration due to gravity. The bounce is modelled with a variable assigntment that 
flips the velocity, thus it is a completely elastic collision with the ground. We use @{text "s$1"} 
to ball's height and @{text "s$2"} for its velocity. We prove that the ball remains above ground
and below its initial resting position. \<close>

\<comment> \<open>Verified with differential invariants. \<close>

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

abbreviation fball :: "real \<Rightarrow> real^2 \<Rightarrow> real^2" ("f") 
  where "f g s \<equiv> (\<chi> i. if i=1 then s$2 else g)"

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
    apply(rule H_comp[where R="\<lambda>s. 0 \<le> s$1 \<and> 2 \<cdot> g \<cdot> s$1 = 2 \<cdot> g \<cdot> h + s$2 \<cdot> s$2"])
     apply(rule H_g_ode_inv)
  by (auto simp: bb_real_arith intro!: poly_derivatives diff_invariant_rules)

\<comment> \<open>Verified with the flow. \<close>

abbreviation ball_flow :: "real \<Rightarrow> real \<Rightarrow> real^2 \<Rightarrow> real^2" ("\<phi>") 
  where "\<phi> g \<tau> s \<equiv> (\<chi> i. if i=1 then g \<cdot> \<tau> ^ 2/2 + s$2 \<cdot> \<tau> + s$1 else g \<cdot> \<tau> + s$2)"

lemma local_flow_ball: "local_flow (f g) UNIV UNIV (\<phi> g)"
  apply(unfold_locales, simp_all add: local_lipschitz_def lipschitz_on_def vec_eq_iff, clarsimp)
  apply(rule_tac x="1/2" in exI, clarsimp, rule_tac x=1 in exI)
    apply(simp add: dist_norm norm_vec_def L2_set_def UNIV_2)
  by (auto simp: forall_2 intro!: poly_derivatives)

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

lemma bouncing_ball_flow: "g < 0 \<Longrightarrow> h \<ge> 0 \<Longrightarrow> rel_kat.Hoare
  \<lceil>\<lambda>s. s$1 = h \<and> s$2 = 0\<rceil>
  (LOOP 
      ((x\<acute>= f g & (\<lambda> s. s$1 \<ge> 0));
       (IF (\<lambda> s. s$1 = 0) THEN (2 ::= (\<lambda>s. - s$2)) ELSE skip)) 
    INV (\<lambda>s. 0 \<le> s$1 \<and> 2 \<cdot> g \<cdot> s$1 = 2 \<cdot> g \<cdot> h + s$2 \<cdot> s$2)
  ) \<lceil>\<lambda>s. 0 \<le> s$1 \<and> s$1 \<le> h\<rceil>"
  apply(rule H_loopI)
    apply(rule H_comp[where R="\<lambda>s. 0 \<le> s$1 \<and> 2 \<cdot> g \<cdot> s$1 = 2 \<cdot> g \<cdot> h + s$2 \<cdot> s$2"])
     apply(subst local_flow.sH_g_ode[OF local_flow_ball])
     apply(force simp: bb_real_arith)
  by (rule H_cond) (auto simp: bb_real_arith)

\<comment> \<open>Verified as a linear system (computing exponential). \<close>

abbreviation ball_sq_mtx :: "3 sq_mtx" ("A")
  where "ball_sq_mtx \<equiv> sq_mtx_chi (\<chi> i. if i=1 then \<e> 2 else if i=2 then \<e> 3 else 0)"

lemma ball_sq_mtx_pow2: "A\<^sup>2 = sq_mtx_chi (\<chi> i. if i=1 then \<e> 3 else 0)"
  unfolding monoid_mult_class.power2_eq_square times_sq_mtx_def
  by (simp add: sq_mtx_chi_inject vec_eq_iff matrix_matrix_mult_def)

lemma ball_sq_mtx_powN: "m > 2 \<Longrightarrow> (\<tau> *\<^sub>R A)^m = 0"
  apply(induct m, simp, case_tac "m \<le> 2")
   apply(simp only: le_less_Suc_eq power_class.power.simps(2), simp)
  by (auto simp: ball_sq_mtx_pow2 sq_mtx_chi_inject vec_eq_iff 
      times_sq_mtx_def zero_sq_mtx_def matrix_matrix_mult_def)

lemma exp_ball_sq_mtx: "exp (\<tau> *\<^sub>R A) = ((\<tau> *\<^sub>R A)\<^sup>2/\<^sub>R 2) + (\<tau> *\<^sub>R A) + 1"
  unfolding exp_def apply(subst suminf_eq_sum[of 2])
  using ball_sq_mtx_powN by (simp_all add: numeral_2_eq_2)
 
lemma exp_ball_sq_mtx_simps:
  "exp (\<tau> *\<^sub>R A) $$ 1 $ 1 = 1" "exp (\<tau> *\<^sub>R A) $$ 1 $ 2 = \<tau>" "exp (\<tau> *\<^sub>R A) $$ 1 $ 3 = \<tau>^2/2"
  "exp (\<tau> *\<^sub>R A) $$ 2 $ 1 = 0" "exp (\<tau> *\<^sub>R A) $$ 2 $ 2 = 1" "exp (\<tau> *\<^sub>R A) $$ 2 $ 3 = \<tau>"
  "exp (\<tau> *\<^sub>R A) $$ 3 $ 1 = 0" "exp (\<tau> *\<^sub>R A) $$ 3 $ 2 = 0" "exp (\<tau> *\<^sub>R A) $$ 3 $ 3 = 1"
  unfolding exp_ball_sq_mtx scaleR_power ball_sq_mtx_pow2
  by (auto simp: plus_sq_mtx_def scaleR_sq_mtx_def one_sq_mtx_def 
      mat_def scaleR_vec_def axis_def plus_vec_def)

lemma bouncing_ball_sq_mtx: "rel_kat.Hoare
  \<lceil>\<lambda>s. 0 \<le> s$1 \<and> s$1 = h \<and> s$2 = 0 \<and> 0 > s$3\<rceil>
    (LOOP 
      ((x\<acute>=(*\<^sub>V) A & (\<lambda> s. s$1 \<ge> 0));
      (IF (\<lambda>s. s$1 = 0) THEN (2 ::= (\<lambda>s. - s$2)) ELSE skip))
    INV (\<lambda>s. 0 \<le> s$1 \<and> 0 > s$3 \<and>  2 \<cdot> s$3 \<cdot> s$1 = 2 \<cdot> s$3 \<cdot> h + (s$2 \<cdot> s$2)))
  \<lceil>\<lambda>s. 0 \<le> s$1 \<and> s$1 \<le> h\<rceil>"
  apply(rule H_loopI)
    apply(rule H_comp[where R="\<lambda>s. 0 \<le> s$1 \<and> 0 > s$3 \<and>  2 \<cdot> s$3 \<cdot> s$1 = 2 \<cdot> s$3 \<cdot> h + (s$2 \<cdot> s$2)"])
  apply(subst local_flow.sH_g_ode[OF local_flow_exp])
     apply(simp add: sq_mtx_vec_prod_eq, unfold UNIV_3)
     apply(simp add: exp_ball_sq_mtx_simps field_simps monoid_mult_class.power2_eq_square)
  by (rule H_cond) (auto simp: bb_real_arith)

no_notation fball ("f")
        and ball_flow ("\<phi>")
        and ball_sq_mtx ("A")


subsubsection \<open> Thermostat \<close>

text \<open> A thermostat has a chronometer, a thermometer and a switch to turn on and off a heater. 
At most every @{text "t"} minutes, it sets its chronometer to @{term "0::real"}, it registers 
the room temperature, and it turns the heater on (or off) based on this reading. The temperature 
follows the ODE @{text "T' = - a * (T - U)"} where @{text "U"} is @{text "L \<ge> 0"} when the heater 
is on, and @{text "U = 0"} when it is off. We use @{term "1::5"} to denote the room's temperature, 
@{term "2::5"} is time as measured by the thermostat's chronometer, @{term "3::5"} is a variable
to save tempreature measurements while @{term "4::5"} does the same for time measurements. Finally,
@{term "5::5"} states whether the heater is on (@{text "s$5 = 1"}) or off (@{text "s$5 = 0"}). 
We prove that the thermostat keeps the room's temperature between @{text "Tmin"} and @{text "Tmax"}. \<close>

abbreviation temp_vec_field :: "real \<Rightarrow> real \<Rightarrow> real^5 \<Rightarrow> real^5" ("f")
  where "f a L s \<equiv> (\<chi> i. if i = 2 then 1 else (if i = 1 then - a * (s$1 - L) else 0))"

abbreviation temp_flow :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real^5 \<Rightarrow> real^5" ("\<phi>")
  where "\<phi> a L \<tau> s \<equiv> (\<chi> i. if i = 1 then - exp(-a * \<tau>) * (L - s$1) + L else 
  (if i = 2 then \<tau> + s$2 else s$i))"

\<comment> \<open>Verified with the flow. \<close>

lemma norm_diff_temp_dyn: "0 < a \<Longrightarrow> \<parallel>f a L s\<^sub>1 - f a L s\<^sub>2\<parallel> = \<bar>a\<bar> * \<bar>s\<^sub>1$1 - s\<^sub>2$1\<bar>"
proof(simp add: norm_vec_def L2_set_def, unfold UNIV_5, simp)
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
  apply(simp add: norm_vec_def L2_set_def, unfold UNIV_5, clarsimp)
  unfolding real_sqrt_abs[symmetric] by (rule real_le_lsqrt) auto

lemma local_flow_temp: "a > 0 \<Longrightarrow> local_flow (f a L) UNIV UNIV (\<phi> a L)"
  by (unfold_locales, auto intro!: poly_derivatives local_lipschitz_temp_dyn 
      simp: forall_5 vec_eq_iff)

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

lemmas Hoare_temp_dyn = local_flow.sH_g_ode_ivl[OF local_flow_temp _ UNIV_I]

lemma thermostat_flow: 
  assumes "0 < a" and "0 \<le> \<tau>" and "0 < Tmin" and "Tmax < L"
  shows "rel_kat.Hoare 
  \<lceil>\<lambda>s. Tmin \<le> s$1 \<and> s$1 \<le> Tmax \<and> s$5 = 0\<rceil>
  (LOOP 
    \<comment> \<open>control\<close>
    ((2 ::= (\<lambda>s. 0));(3 ::= (\<lambda>s. s$1));
    (IF (\<lambda>s. s$5 = 0 \<and> s$3 \<le> Tmin + 1) THEN (5 ::= (\<lambda>s.1)) ELSE 
    (IF (\<lambda>s. s$5 = 1 \<and> s$3 \<ge> Tmax - 1) THEN (5 ::= (\<lambda>s.0)) ELSE skip));
    \<comment> \<open>dynamics\<close>
    (IF (\<lambda>s. s$5 = 0) THEN (x\<acute>=(f a 0) & (\<lambda>s. s$2 \<le> - (ln (Tmin/s$3))/a) on {0..\<tau>} UNIV @ 0) 
    ELSE (x\<acute>=(f a L) & (\<lambda>s. s$2 \<le> - (ln ((L-Tmax)/(L-s$3)))/a) on {0..\<tau>} UNIV @ 0)) )
  INV (\<lambda>s. Tmin \<le>s$1 \<and> s$1 \<le> Tmax \<and> (s$5 = 0 \<or> s$5 = 1)))
  \<lceil>\<lambda>s. Tmin \<le> s$1 \<and> s$1 \<le> Tmax\<rceil>"
  apply(rule H_loopI)
    apply(rule_tac R="\<lambda>s. Tmin \<le> s$1 \<and> s$1 \<le> Tmax \<and> s$2=0 \<and> s$3 = s$1 \<and> (s$5 = 0 \<or> s$5 = 1)" in H_comp)
     apply(rule_tac R="\<lambda>s. Tmin \<le> s$1 \<and> s$1 \<le> Tmax \<and> s$2=0 \<and> s$3 = s$1 \<and> (s$5 = 0 \<or> s$5 = 1)" in H_comp)
      apply(rule_tac R="\<lambda>s. Tmin \<le> s$1 \<and> s$1 \<le> Tmax \<and> s$2=0 \<and> (s$5 = 0 \<or> s$5 = 1)" in H_comp, simp, simp)
      apply(rule H_cond, simp_all add: Hoare_temp_dyn[OF assms(1,2)])+
  using temp_dyn_up_real_arith[OF assms(1) _ _ assms(4), of Tmin]
    and temp_dyn_down_real_arith[OF assms(1,3), of _ Tmax] by auto

no_notation temp_vec_field ("f")
        and temp_flow ("\<phi>")


subsubsection \<open> Water tank \<close>  \<comment> \<open>As generalized by Hespanha from \cite{Alur et. all, 1995}\<close>

abbreviation water_vec_field :: "real \<Rightarrow> real \<Rightarrow> real^5 \<Rightarrow> real^5" ("f")
  where "f c\<^sub>i c\<^sub>o s \<equiv> (\<chi> i. if i = 2 then 1 else (if i = 1 then c\<^sub>i - c\<^sub>o else 0))"

abbreviation water_flow :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real^5 \<Rightarrow> real^5" ("\<phi>")
  where "\<phi> c\<^sub>i c\<^sub>o \<tau> s \<equiv> (\<chi> i. if i = 1 then (c\<^sub>i - c\<^sub>o) * \<tau> + s$1 else 
  (if i = 2 then \<tau> + s$2 else s$i))"

lemma local_flow_water: "local_flow (f c\<^sub>i c\<^sub>o) UNIV UNIV (\<phi> c\<^sub>i c\<^sub>o)"
  apply (unfold_locales, unfold local_lipschitz_def lipschitz_on_def, simp_all, clarsimp)
  apply(rule_tac x="1/2" in exI, clarsimp, rule_tac x=1 in exI)
  apply(simp add: dist_norm norm_vec_def L2_set_def, unfold UNIV_5)
  by (auto intro!: poly_derivatives simp: vec_eq_iff)

lemma water_tank_arith:
  assumes "0 \<le> (\<tau>::real)" and "0 < c\<^sub>o" and "c\<^sub>o < c\<^sub>i"
  shows "\<forall>\<tau>\<in>{0..\<tau>}. \<tau> \<le> (y - Hmin) / c\<^sub>o \<Longrightarrow>  Hmin \<le> y - c\<^sub>o * \<tau>"
    and "\<forall>\<tau>\<in>{0..\<tau>}. \<tau> \<le> (Hmax - y) / (c\<^sub>i - c\<^sub>o) \<Longrightarrow>  (c\<^sub>i - c\<^sub>o) * \<tau> + y \<le> Hmax"
  apply (erule_tac x=\<tau> in ballE, simp_all add: le_divide_eq mult.commute assms)
  by (erule_tac x=\<tau> in ballE, simp_all add: le_divide_eq[where c="c\<^sub>i - c\<^sub>o"] assms)

lemma water_tank_flow:
  assumes "0 \<le> \<tau>" and "0 < c\<^sub>o" and "c\<^sub>o < c\<^sub>i"
  shows "rel_kat.Hoare 
  \<lceil>\<lambda>s. Hmin < s$1 \<and> s$1 < Hmax \<and> s$3 = 1\<rceil>
  (LOOP 
    \<comment> \<open>control\<close>
    ((2 ::=(\<lambda>s.0));(4 ::=(\<lambda>s. s$1));
    (IF (\<lambda>s. s$3 = 0 \<and> s$4 \<le> Hmin + 1) THEN (3 ::= (\<lambda>s.1)) ELSE 
    (IF (\<lambda>s. s$3 = 1 \<and> s$4 \<ge> Hmax - 1) THEN (3 ::= (\<lambda>s.0)) ELSE skip));
    \<comment> \<open>dynamics\<close>
    (IF (\<lambda>s. s$3 = 0) THEN (x\<acute>=(f c\<^sub>i c\<^sub>o) & (\<lambda>s. s$2 \<le> (Hmax - s$4)/(c\<^sub>i - c\<^sub>o)) on {0..\<tau>} UNIV @ 0) 
     ELSE (x\<acute>=(f 0 c\<^sub>o) & (\<lambda>s. s$2 \<le> (s$4 - Hmin)/c\<^sub>o) on {0..\<tau>} UNIV @ 0)) )
  INV (\<lambda>s. Hmin \<le> s$1 \<and> s$1 \<le>Hmax \<and> (s$3 =0 \<or> s$3 = 1)))
  \<lceil>\<lambda>s. Hmin \<le> s$1 \<and> s$1 \<le> Hmax\<rceil>"
  apply(rule H_loopI)
    apply(rule_tac R="\<lambda>s. Hmin \<le> s$1 \<and> s$1 \<le> Hmax \<and> s$2=0 \<and> s$4 = s$1 \<and> (s$3 =0 \<or> s$3 = 1)" in H_comp)
     apply(rule_tac R="\<lambda>s. Hmin \<le> s$1 \<and> s$1 \<le> Hmax \<and> s$2=0 \<and> s$4 = s$1 \<and> (s$3 =0 \<or> s$3 = 1)" in H_comp)
      apply(rule_tac R="\<lambda>s. Hmin \<le> s$1 \<and> s$1 \<le> Hmax \<and> s$2=0 \<and> (s$3 =0 \<or> s$3 = 1)" in H_comp, simp, simp)
     apply(rule H_cond, simp_all add: local_flow.sH_g_ode_ivl[OF local_flow_water assms(1) UNIV_I])
  using assms water_tank_arith[OF _ assms(2,3)] by auto (smt mult_nonneg_nonneg)+

lemma water_tank_diff_inv:
  "0 \<le> \<tau> \<Longrightarrow> diff_invariant (\<lambda>s. s $ 1 = (c\<^sub>i - (c\<^sub>o::real)) \<cdot> s $ 2 + s $ 4 \<and> 0 \<le> s $ 2 \<and> 
    Hmin \<le> s$4 \<and> s$4 \<le> Hmax \<and> (s$3 =0 \<or> s$3 = 1)) (f c\<^sub>i c\<^sub>o) {0..\<tau>} UNIV 0 G"
  apply(intro diff_invariant_conj_rule)
  apply(force simp: forall_5 intro!: poly_derivatives diff_invariant_rules)
     apply(rule_tac \<nu>'="\<lambda>t. 0" and \<mu>'="\<lambda>t. 1" in diff_invariant_leq_rule, simp_all add: forall_5)
    apply(rule_tac \<nu>'="\<lambda>t. 0" and \<mu>'="\<lambda>t. 0" in diff_invariant_leq_rule, 
      simp_all add: forall_5, force intro!: poly_derivatives)+
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
  shows "rel_kat.Hoare 
  \<lceil>\<lambda>s. Hmin < s$1 \<and> s$1 < Hmax \<and> s$3 = 1\<rceil>
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
  INV (\<lambda>s. Hmin \<le> s$1 \<and> s$1 \<le> Hmax \<and> (s$3 =0 \<or> s$3 = 1)))
  \<lceil>\<lambda>s. Hmin \<le> s$1 \<and> s$1 \<le> Hmax\<rceil>"
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

(**************************************************************************************************)

(* NEED MORE DIMENSIONS TO WORK WITH OBVIOUS INVARIANTS (ORBITS). *)

lemma "a > 0 \<Longrightarrow> 0 \<le> \<tau> \<Longrightarrow> diff_invariant (\<lambda>s. (s$3 = 0 \<or> s$3 = 1)) (f a L) {0..\<tau>} UNIV 0 G"
  by (auto intro!: diff_invariant_rules poly_derivatives)

lemma "a > 0 \<Longrightarrow> 0 \<le> \<tau> \<Longrightarrow> diff_invariant (\<lambda>s. s$0 = - exp(-a * s$1) * (L - s$2) + L) (f a L) {0..\<tau>} UNIV 0 G"
  apply(rule diff_invariant_rules(1), simp, simp, clarify)
  apply(rule poly_derivatives, simp)
    apply(erule_tac x=0 in allE, simp)
   apply(rule poly_derivatives) defer
   apply(rule poly_derivatives, force, force)
   apply(intro poly_derivatives)
              apply(rule poly_derivatives, force, simp)
    apply(erule_tac x=1 in allE, simp)
           apply force
          apply force
         apply force
        apply(rule poly_derivatives, simp)
    apply(erule_tac x=2 in allE, simp, simp)
     apply force
    apply(rule poly_derivatives)
   apply force
  apply auto
  apply (auto intro!: diff_invariant_rules poly_derivatives)
   apply force defer
  apply(frule_tac x=1 in spec)


lemma thermostat_inv: 
  assumes "a > 0" and "0 \<le> \<tau>" and "0 < Tmin" and "Tmax < L"
  shows "rel_kat.Hoare 
  \<lceil>\<lambda>s. Tmin \<le> s$1 \<and> s$1 \<le> Tmax \<and> s$3 = 0\<rceil>
  (LOOP 
    \<comment> \<open>control\<close>
    ((1 ::= (\<lambda>s. 0));(2 ::= (\<lambda>s. s$0));
    (IF (\<lambda>s. s$3 = 0 \<and> s$2 \<le> Tmin + 1) THEN (3 ::= (\<lambda>s.1)) ELSE 
    (IF (\<lambda>s. s$3 = 1 \<and> s$2 \<ge> Tmax - 1) THEN (3 ::= (\<lambda>s.0)) ELSE skip));
    \<comment> \<open>dynamics\<close>
    (IF (\<lambda>s. s$3 = 0) THEN 
      (x\<acute>=(f a 0) & (\<lambda>s. s$1 \<le> - (ln (Tmin/s$2))/a) on {0..\<tau>} UNIV @ 0 
      DINV (\<lambda>s. Tmin \<le>s$0 \<and> s$0 \<le> Tmax \<and> s$2 = s$0 \<and> (s$3 = 0 \<or> s$3 = 1)))
    ELSE 
      (x\<acute>=(f a L) & (\<lambda>s. s$1 \<le> - (ln ((L-Tmax)/(L-s$2)))/a) on {0..\<tau>} UNIV @ 0 
      DINV (\<lambda>s. Tmin \<le>s$0 \<and> s$0 \<le> Tmax \<and> s$2 = s$0 \<and> (s$3 = 0 \<or> s$3 = 1)))))
  INV (\<lambda>s. Tmin \<le>s$0 \<and> s$0 \<le> Tmax \<and> (s$3 = 0 \<or> s$3 = 1)))
  \<lceil>\<lambda>s. Tmin \<le> s$1 \<and> s$1 \<le> Tmax\<rceil>"
  apply(rule H_loopI)
    apply(rule_tac R="\<lambda>s. Tmin \<le> s$1 \<and> s$1 \<le> Tmax \<and> s$1=0 \<and> s$2 = s$0 \<and> (s$3 = 0 \<or> s$3 = 1)" in H_comp)
     apply(rule_tac R="\<lambda>s. Tmin \<le> s$1 \<and> s$1 \<le> Tmax \<and> s$1=0 \<and> s$2 = s$0 \<and> (s$3 = 0 \<or> s$3 = 1)" in H_comp)
      apply(rule_tac R="\<lambda>s. Tmin \<le> s$1 \<and> s$1 \<le> Tmax \<and> s$1=0 \<and> (s$3 = 0 \<or> s$3 = 1)" in H_comp, simp, simp)
     apply(rule H_cond, simp)
  apply(rule H_cond, simp, simp)
    apply(rule H_cond)
     apply(rule H_g_ode_inv)
       apply simp
  oops

no_notation temp_vec_field ("f")
        and temp_flow ("\<phi>")

end