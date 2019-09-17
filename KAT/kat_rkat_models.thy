(*  Title:       KAT Models 
    Author:      Jonathan Julián Huerta y Munive, 2019
    Maintainer:  Jonathan Julián Huerta y Munive <jjhuertaymunive1@sheffield.ac.uk>
*)

section \<open> KAT Models \<close>

text \<open> We show that relations and non-deterministic functions form Kleene algebras with tests. \<close>

theory kat_rkat_models
  imports kat_rkat_prelims

begin

subsection \<open> Relational model \<close>

interpretation rel_uq: unital_quantale Id "(O)" "\<Inter>" "\<Union>" "(\<inter>)" "(\<subseteq>)" "(\<subset>)" "(\<union>)" "{}" UNIV
  by (unfold_locales, auto)

lemma power_is_relpow: "rel_uq.power X m = X ^^ m" for X::"'a rel"
proof (induct m)
  case 0 show ?case
    by (metis rel_uq.power_0 relpow.simps(1))
  case Suc thus ?case
    by (metis rel_uq.power_Suc2 relpow.simps(2))
qed

lemma rel_star_def: "X^* = (\<Union>m. rel_uq.power X m)"
  by (simp add: power_is_relpow rtrancl_is_UN_relpow)

lemma rel_star_contl: "X O Y^* = (\<Union>m. X O rel_uq.power Y m)"
by (metis rel_star_def relcomp_UNION_distrib)

lemma rel_star_contr: "X^* O Y = (\<Union>m. (rel_uq.power X m) O Y)"
  by (metis rel_star_def relcomp_UNION_distrib2)
         
interpretation rel_ka: kleene_algebra "(\<union>)" "(O)" Id "{}" "(\<subseteq>)" "(\<subset>)" rtrancl
proof
  fix x y z :: "'a rel"
  show "Id \<union> x O x\<^sup>* \<subseteq> x\<^sup>*"
    by (metis order_refl r_comp_rtrancl_eq rtrancl_unfold)
next
  fix x y z :: "'a rel"
  assume "z \<union> x O y \<subseteq> y"
  thus "x\<^sup>* O z \<subseteq> y"
    by (simp only: rel_star_contr, metis (lifting) SUP_le_iff rel_uq.power_inductl)
next
  fix x y z :: "'a rel"
  assume "z \<union> y O x \<subseteq> y"
  thus "z O x\<^sup>* \<subseteq> y"
    by (simp only: rel_star_contl, metis (lifting) SUP_le_iff rel_uq.power_inductr)
qed

interpretation rel_tests: test_semiring "(\<union>)" "(O)" Id "{}" "(\<subseteq>)" "(\<subset>)" "\<lambda>x. Id \<inter> ( - x)"
  by (standard, auto)

interpretation rel_kat: kat "(\<union>)" "(O)" Id "{}" "(\<subseteq>)" "(\<subset>)" rtrancl "\<lambda>x. Id \<inter> ( - x)"
  by (unfold_locales)

definition rel_R :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where 
  "rel_R P Q = \<Union>{X. rel_kat.Hoare P X Q}"

interpretation rel_rkat: rkat "(\<union>)" "(;)" Id "{}" "(\<subseteq>)" "(\<subset>)" rtrancl "(\<lambda>X. Id \<inter> - X)" rel_R
  by (standard, auto simp: rel_R_def rel_kat.Hoare_def)

lemma RdL_is_rRKAT: "(\<forall>x. {(x,x)}; R1 \<subseteq> {(x,x)}; R2) = (R1 \<subseteq> R2)" (* Refinement in dL is that of rKAT *)
  by auto


subsection \<open> State transformer model \<close>

notation Abs_nd_fun ("_\<^sup>\<bullet>" [101] 100) 
     and Rep_nd_fun ("_\<^sub>\<bullet>" [101] 100)

declare Abs_nd_fun_inverse [simp]

lemma nd_fun_ext: "(\<And>x. (f\<^sub>\<bullet>) x = (g\<^sub>\<bullet>) x) \<Longrightarrow> f = g"
  apply(subgoal_tac "Rep_nd_fun f = Rep_nd_fun g")
  using Rep_nd_fun_inject 
   apply blast
  by(rule ext, simp)

lemma nd_fun_eq_iff: "(f = g) = (\<forall>x. (f\<^sub>\<bullet>) x = (g\<^sub>\<bullet>) x)"
  by (auto simp: nd_fun_ext)

instantiation nd_fun :: (type) kleene_algebra
begin

definition "0 = \<zeta>\<^sup>\<bullet>"

definition "star_nd_fun f = qstar f" for f::"'a nd_fun"

definition "f + g = ((f\<^sub>\<bullet>) \<squnion> (g\<^sub>\<bullet>))\<^sup>\<bullet>"

named_theorems nd_fun_aka "antidomain kleene algebra properties for nondeterministic functions."

lemma nd_fun_plus_assoc[nd_fun_aka]: "x + y + z = x + (y + z)"
  and nd_fun_plus_comm[nd_fun_aka]: "x + y = y + x"
  and nd_fun_plus_idem[nd_fun_aka]: "x + x = x" for x::"'a nd_fun"
  unfolding plus_nd_fun_def by (simp add: ksup_assoc, simp_all add: ksup_comm)

lemma nd_fun_distr[nd_fun_aka]: "(x + y) \<cdot> z = x \<cdot> z + y \<cdot> z"
  and nd_fun_distl[nd_fun_aka]: "x \<cdot> (y + z) = x \<cdot> y + x \<cdot> z" for x::"'a nd_fun"
  unfolding plus_nd_fun_def times_nd_fun_def by (simp_all add: kcomp_distr kcomp_distl)

lemma nd_fun_plus_zerol[nd_fun_aka]: "0 + x = x" 
  and nd_fun_mult_zerol[nd_fun_aka]: "0 \<cdot> x = 0"
  and nd_fun_mult_zeror[nd_fun_aka]: "x \<cdot> 0 = 0" for x::"'a nd_fun"
  unfolding plus_nd_fun_def zero_nd_fun_def times_nd_fun_def by auto

lemma nd_fun_leq[nd_fun_aka]: "(x \<le> y) = (x + y = y)"
  and nd_fun_less[nd_fun_aka]: "(x < y) = (x + y = y \<and> x \<noteq> y)"
  and nd_fun_leq_add[nd_fun_aka]: "z \<cdot> x \<le> z \<cdot> (x + y)" for x::"'a nd_fun"
  unfolding less_eq_nd_fun_def less_nd_fun_def plus_nd_fun_def times_nd_fun_def sup_fun_def
  by (unfold nd_fun_eq_iff le_fun_def, auto simp: kcomp_def)

lemma nd_star_one[nd_fun_aka]: "1 + x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
  and nd_star_unfoldl[nd_fun_aka]: "z + x \<cdot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<cdot> z \<le> y"
  and nd_star_unfoldr[nd_fun_aka]: "z + y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> x\<^sup>\<star> \<le> y" for x::"'a nd_fun"
  unfolding plus_nd_fun_def star_nd_fun_def
    apply(simp_all add: fun_star_inductl sup_nd_fun.rep_eq fun_star_inductr)
  by (metis order_refl sup_nd_fun.rep_eq uwqlka.conway.dagger_unfoldl_eq)

instance
  apply intro_classes
  using nd_fun_aka by simp_all

end

instantiation nd_fun :: (type) kat
begin

definition "n f = (\<lambda>x. if ((f\<^sub>\<bullet>) x = {}) then {x} else {})\<^sup>\<bullet>"

lemma nd_fun_n_op_one[nd_fun_aka]: "n (n (1::'a nd_fun)) = 1"
  and nd_fun_n_op_mult[nd_fun_aka]: "n (n (n x \<cdot> n y)) = n x \<cdot> n y"
  and nd_fun_n_op_mult_comp[nd_fun_aka]: "n x \<cdot> n (n x) = 0" 
  and nd_fun_n_op_de_morgan[nd_fun_aka]: "n (n (n x) \<cdot> n (n y)) = n x + n y" for x::"'a nd_fun"
  unfolding n_op_nd_fun_def one_nd_fun_def times_nd_fun_def plus_nd_fun_def zero_nd_fun_def 
  by (auto simp: nd_fun_eq_iff kcomp_def)

instance
  by (intro_classes, auto simp: nd_fun_aka)

end

instantiation nd_fun :: (type) rkat
begin

definition "Ref_nd_fun P Q \<equiv> (\<lambda>s. \<Union>{(f\<^sub>\<bullet>) s|f. Hoare P f Q})\<^sup>\<bullet>"

instance
  apply(intro_classes)
  by (unfold Hoare_def n_op_nd_fun_def Ref_nd_fun_def times_nd_fun_def)
    (auto simp: kcomp_def le_fun_def less_eq_nd_fun_def)

end

end