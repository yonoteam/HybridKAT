(*  Title:       Verification components with relational MKA 
    Author:      Jonathan Julián Huerta y Munive, 2019
    Maintainer:  Jonathan Julián Huerta y Munive <jjhuertaymunive1@sheffield.ac.uk>
*)

section \<open> Verification components with relational KAT \<close>

text \<open> We derive the rules of Hoare Logic in KAT. We instantiate to our relational model and 
derive rules for evolution statements with our three methods for verifying correctness 
specifications of continuous dynamics: flows, solutions and invariants. \<close>

theory kat2rel
  imports
  "../hs_prelims_dyn_sys"
  KAT_and_DRA.PHL_KAT 
  (*"../../../../Georgs/Algebraic_VCs/AVC_KAT/VC_KAT"*)
  (*"../../../afpModified/VC_KAT"*)

begin

subsection \<open> Kleene algebra preparation \<close> 

no_notation if_then_else ("if _ then _ else _ fi" [64,64,64] 63)
        and while ("while _ do _ od" [64,64] 63)

context dioid_one_zero (* by Victor Gomes, Georg Struth *)
begin

lemma power_inductl: "z + x \<cdot> y \<le> y \<Longrightarrow> (x ^ m) \<cdot> z \<le> y"
  by(induct m, auto, metis mult.assoc mult_isol order_trans)

lemma power_inductr: "z + y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> (x ^ m) \<le> y"
proof (induct m)
  case 0 show ?case
    using "0.prems" by auto
  case Suc
  {
    fix m
    assume "z + y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> x ^ m \<le> y"
      and "z + y \<cdot> x \<le> y"
    hence "z \<cdot> x ^ m \<le> y"
      by auto
    also have "z \<cdot> x ^ Suc m = z \<cdot> x \<cdot> x ^ m"
      by (metis mult.assoc power_Suc)
    moreover have "... = (z \<cdot> x ^ m) \<cdot> x"
      by (metis mult.assoc power_commutes)
    moreover have "... \<le> y \<cdot> x"
      by (metis calculation(1) mult_isor)
    moreover have "... \<le> y"
      using \<open>z + y \<cdot> x \<le> y\<close> by auto
    ultimately have "z \<cdot> x ^ Suc m \<le> y" by auto
  }
  thus ?case
    by (metis Suc)
qed

end

context kat (* mostly by Victor Gomes, Georg Struth *)
begin

\<comment> \<open> Definitions of Hoare Triple \<close>

definition Hoare :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("H") where
  "H p x q \<longleftrightarrow> t p \<cdot> x \<le> x \<cdot> t q" 

lemma H_consl: "t p \<le> t p' \<Longrightarrow> H p' x q \<Longrightarrow> H p x q"
  using Hoare_def phl_cons1 by blast

lemma H_consr: "t q' \<le> t q \<Longrightarrow> H p x q' \<Longrightarrow> H p x q"
  using Hoare_def phl_cons2 by blast          

lemma H_cons: "t p \<le> t p' \<Longrightarrow> t q' \<le> t q \<Longrightarrow> H p' x q' \<Longrightarrow> H p x q"
  by (simp add: H_consl H_consr)

\<comment> \<open> Skip program \<close>

lemma H_skip:  "H p 1 p"
  by (simp add: Hoare_def)

\<comment> \<open> Sequential composition \<close>

lemma H_seq: "H p x r \<Longrightarrow> H r y q \<Longrightarrow> H p (x \<cdot> y) q"
  by (simp add: Hoare_def phl_seq)

\<comment> \<open> Conditional statement \<close>

definition ifthenelse :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" ("if _ then _ else _ fi" [64,64,64] 63) where
  "if p then x else y fi = (t p \<cdot> x + n p \<cdot> y)"

lemma H_var: "H p x q \<longleftrightarrow> t p \<cdot> x \<cdot> n q = 0"
  by (metis Hoare_def n_kat_3 t_n_closed)

lemma H_cond_iff: "H p (if r then x else y fi) q \<longleftrightarrow> H (t p \<cdot> t r) x q \<and> H (t p \<cdot> n r) y q"
proof -
  have "H p (if r then x else y fi) q \<longleftrightarrow> t p \<cdot> (t r \<cdot> x + n r \<cdot> y) \<cdot> n q = 0"
    by (simp add: H_var ifthenelse_def)
  also have "... \<longleftrightarrow> t p \<cdot> t r \<cdot> x \<cdot> n q + t p \<cdot> n r \<cdot> y \<cdot> n q = 0"
    by (simp add: distrib_left mult_assoc)
  also have "... \<longleftrightarrow> t p \<cdot> t r \<cdot> x \<cdot> n q = 0 \<and> t p \<cdot> n r \<cdot> y \<cdot> n q = 0"
    by (metis add_0_left no_trivial_inverse)
  finally show ?thesis
    by (metis H_var test_mult)
qed

lemma H_cond: "H (t p \<cdot> t r) x q \<Longrightarrow> H (t p \<cdot> n r) y q \<Longrightarrow> H p (if r then x else y fi) q"
  by (simp add: H_cond_iff)

\<comment> \<open> While loop \<close>

definition while :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("while _ do _ od" [64,64] 63) where
  "while b do x od = (t b \<cdot> x)\<^sup>\<star> \<cdot> n b"

definition while_inv :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" ("while _ inv _ do _ od" [64,64,64] 63) where
  "while p inv i do x od = while p do x od"

lemma H_exp1: "H (t p \<cdot> t r) x q \<Longrightarrow> H p (t r \<cdot> x) q"
  using Hoare_def n_de_morgan_var2 phl.ht_at_phl_export1 by auto

lemma H_while: "H (t p \<cdot> t r) x p \<Longrightarrow> H p (while r do x od) (t p \<cdot> n r)"
proof -
  assume a1: "H (t p \<cdot> t r) x p"
  have "t (t p \<cdot> n r) = n r \<cdot> t p \<cdot> n r"
    using n_preserve test_mult by presburger
  then show ?thesis
    using a1 Hoare_def H_exp1 conway.phl.it_simr phl_export2 while_def by auto
qed

lemma H_while_inv: "t p \<le> t i \<Longrightarrow> t i \<cdot> n r \<le> t q \<Longrightarrow> H (t i \<cdot> t r) x i \<Longrightarrow> H p (while r inv i do x od) q"
  by (metis H_cons H_while test_mult while_inv_def)

\<comment> \<open> Finite iteration \<close>

lemma H_star: "H i x i \<Longrightarrow> H i (x\<^sup>\<star>) i"
  unfolding Hoare_def using star_sim2 by blast

lemma H_star_inv: 
  assumes "t p \<le> t i" and "H i x i" and "(t i) \<le> (t q)"
  shows "H p (x\<^sup>\<star>) q"
proof-
  have "H i (x\<^sup>\<star>) i"
    using assms(2) H_star by blast
  hence "H p (x\<^sup>\<star>) i"
    unfolding Hoare_def using assms(1) phl_cons1 by blast 
  thus ?thesis 
    unfolding Hoare_def using assms(3) phl_cons2 by blast 
qed

definition loopi :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("loop _ inv _ " [64,64] 63)
  where "loop x inv i = x\<^sup>\<star>"

lemma H_loop: "H p x p \<Longrightarrow> H p (loop x inv i) p"
  unfolding loopi_def by (rule H_star)

lemma H_loop_inv: "t p \<le> t i \<Longrightarrow> H i x i \<Longrightarrow> t i \<le> t q \<Longrightarrow> H p (loop x inv i) q"
  unfolding loopi_def using H_star_inv by blast

\<comment> \<open> Invariants \<close>

lemma H_inv: "t p \<le> t i \<Longrightarrow> t i \<le> t q \<Longrightarrow> H i x i \<Longrightarrow> H p x q"
  by (rule_tac p'=i and q'=i in H_cons)

end


subsection \<open> Relational model \<close> (* by Alasdair Armstrong, Victor B. F. Gomes, Georg Struth, Tjark Weber *)

interpretation rel_dioid: dioid_one_zero "(\<union>)" "(O)" Id "{}" "(\<subseteq>)" "(\<subset>)"
  by (unfold_locales, auto)

lemma power_is_relpow: "rel_dioid.power X m = X ^^ m"
proof (induct m)
  case 0 show ?case
    by (metis rel_dioid.power_0 relpow.simps(1))
  case Suc thus ?case
    by (metis rel_dioid.power_Suc2 relpow.simps(2))
qed

lemma rel_star_def: "X^* = (\<Union>m. rel_dioid.power X m)"
  by (simp add: power_is_relpow rtrancl_is_UN_relpow)

lemma rel_star_contl: "X O Y^* = (\<Union>m. X O rel_dioid.power Y m)"
by (metis rel_star_def relcomp_UNION_distrib)

lemma rel_star_contr: "X^* O Y = (\<Union>m. (rel_dioid.power X m) O Y)"
by (metis rel_star_def relcomp_UNION_distrib2)

interpretation rel_kleene_algebra: kleene_algebra "(\<union>)" "(O)" Id "{}" "(\<subseteq>)" "(\<subset>)" rtrancl
proof
  fix x y z :: "'a rel"
  show "Id \<union> x O x\<^sup>* \<subseteq> x\<^sup>*"
    by (metis order_refl r_comp_rtrancl_eq rtrancl_unfold)
next
  fix x y z :: "'a rel"
  assume "z \<union> x O y \<subseteq> y"
  thus "x\<^sup>* O z \<subseteq> y"
    by (simp only: rel_star_contr, metis (lifting) SUP_le_iff rel_dioid.power_inductl)
next
  fix x y z :: "'a rel"
  assume "z \<union> y O x \<subseteq> y"
  thus "z O x\<^sup>* \<subseteq> y"
    by (simp only: rel_star_contl, metis (lifting) SUP_le_iff rel_dioid.power_inductr)
qed

interpretation rel_dioid_tests: test_semiring "(\<union>)" "(O)" Id "{}" "(\<subseteq>)" "(\<subset>)" "\<lambda>x. Id \<inter> ( - x)"
  by (standard, auto)

interpretation rel_kat: kat "(\<union>)" "(O)" Id "{}" "(\<subseteq>)" "(\<subset>)" rtrancl "\<lambda>x. Id \<inter> ( - x)"
  by (unfold_locales)


subsection \<open> Store and Hoare triples \<close>

type_synonym 'a pred = "'a \<Rightarrow> bool"

\<comment> \<open>We start by deleting some conflicting notation.\<close>

no_notation Archimedean_Field.ceiling ("\<lceil>_\<rceil>")
        and Archimedean_Field.floor_ceiling_class.floor ("\<lfloor>_\<rfloor>")
        and Relation.Domain ("r2s")
        and tau ("\<tau>")

notation Id ("skip")
     and relcomp (infixl ";" 70) 
     and inf (infixl "\<sqinter>" 70)  
     and sup (infixl "\<squnion>" 65)

\<comment> \<open>Canonical lifting from predicates to relations and its simplification rules\<close>

definition p2r :: "'a pred \<Rightarrow> 'a rel" ("\<lceil>_\<rceil>") where
  "\<lceil>P\<rceil> = {(s,s) |s. P s}"

lemma p2r_simps[simp]: 
  "\<lceil>P\<rceil> \<le> \<lceil>Q\<rceil> = (\<forall>s. P s \<longrightarrow> Q s)"
  "(\<lceil>P\<rceil> = \<lceil>Q\<rceil>) = (\<forall>s. P s = Q s)"
  "(\<lceil>P\<rceil> ; \<lceil>Q\<rceil>) = \<lceil>\<lambda> s. P s \<and> Q s\<rceil>"
  "(\<lceil>P\<rceil> \<union> \<lceil>Q\<rceil>) = \<lceil>\<lambda> s. P s \<or> Q s\<rceil>"
  "rel_dioid_tests.t \<lceil>P\<rceil> = \<lceil>P\<rceil>"
  "(- Id) \<union> \<lceil>P\<rceil> = - \<lceil>\<lambda>s. \<not> P s\<rceil>"
  "Id \<inter> (- \<lceil>P\<rceil>) = \<lceil>\<lambda>s. \<not> P s\<rceil>"
  unfolding p2r_def by auto

\<comment> \<open> Meaning of the relational hoare triple \<close>

lemma rel_kat_H: "rel_kat.Hoare \<lceil>P\<rceil> X \<lceil>Q\<rceil> \<longleftrightarrow> (\<forall>s s'. P s \<longrightarrow> (s,s') \<in> X \<longrightarrow> Q s')"
  by (simp add: rel_kat.Hoare_def, auto simp add: p2r_def)

lemma rel_dioid_H: "rel_dioid.ht \<lceil>P\<rceil> X \<lceil>Q\<rceil> = (\<forall>s s'. P s \<longrightarrow> (s,s') \<in> X \<longrightarrow> Q s')"
  by (auto simp: p2r_def subset_eq)

\<comment> \<open> Hoare triple for skip and simp-rule \<close>

lemma H_skip: "rel_kat.Hoare \<lceil>P\<rceil> skip \<lceil>P\<rceil>"
  using rel_kat.H_skip by blast

lemma sH_skip[simp]: "rel_kat.Hoare \<lceil>P\<rceil> skip \<lceil>Q\<rceil> \<longleftrightarrow> \<lceil>P\<rceil> \<le> \<lceil>Q\<rceil>"
  unfolding rel_kat_H by simp

\<comment> \<open> We introduce assignments and compute their Hoare triple. \<close>

definition vec_upd :: "('a^'b) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'a^'b"
  where "vec_upd s i a \<equiv> (\<chi> j. ((($) s)(i := a)) j)"

definition assign :: "'b \<Rightarrow> ('a^'b \<Rightarrow> 'a) \<Rightarrow> ('a^'b) rel" ("(2_ ::= _)" [70, 65] 61) 
  where "(x ::= e) \<equiv> {(s, vec_upd s x (e s))| s. True}" 

lemma H_assign: "P = (\<lambda>s. Q (\<chi> j. ((($) s)(x := (e s))) j)) \<Longrightarrow> rel_kat.Hoare \<lceil>P\<rceil> (x ::= e) \<lceil>Q\<rceil>"
  unfolding rel_kat_H assign_def vec_upd_def by force

lemma sH_assign[simp]: "rel_kat.Hoare \<lceil>P\<rceil> (x ::= e) \<lceil>Q\<rceil> \<longleftrightarrow> (\<forall>s. P s \<longrightarrow> Q (\<chi> j. ((($) s)(x := (e s))) j))"
  unfolding rel_kat_H vec_upd_def assign_def by (auto simp: fun_upd_def)

\<comment> \<open> Next, the Hoare rule of the composition \<close>

lemma H_comp: "rel_kat.Hoare \<lceil>P\<rceil> X \<lceil>R\<rceil> \<Longrightarrow> rel_kat.Hoare \<lceil>R\<rceil> Y \<lceil>Q\<rceil> \<Longrightarrow> rel_kat.Hoare \<lceil>P\<rceil> (X ; Y) \<lceil>Q\<rceil>"
  by (auto intro: rel_kat.H_seq)

lemma sH_comp: 
  "rel_kat.Hoare \<lceil>P\<rceil> (X ; Y) \<lceil>Q\<rceil> = rel_kat.Hoare \<lceil>P\<rceil> (X) \<lceil>\<lambda>s. \<forall>s'. (s, s') \<in> Y \<longrightarrow> Q s'\<rceil>"
  unfolding rel_kat_H by auto

\<comment> \<open> Rewriting the Hoare rule for the conditional statement \<close>

abbreviation cond_sugar :: "'a pred \<Rightarrow> 'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a rel" ("IF _ THEN _ ELSE _" [64,64] 63) 
  where "IF B THEN X ELSE Y \<equiv> rel_kat.ifthenelse \<lceil>B\<rceil> X Y"

lemma H_cond: "rel_kat.Hoare \<lceil>P \<sqinter> B\<rceil> X \<lceil>Q\<rceil> \<Longrightarrow> rel_kat.Hoare \<lceil>P \<sqinter> - B\<rceil> Y \<lceil>Q\<rceil> \<Longrightarrow> 
  rel_kat.Hoare \<lceil>P\<rceil> (IF B THEN X ELSE Y) \<lceil>Q\<rceil>"
  by (rule rel_kat.H_cond, auto simp: rel_kat_H)

lemma sH_cond[simp]: "rel_kat.Hoare \<lceil>P\<rceil> (IF B THEN X ELSE Y) \<lceil>Q\<rceil> \<longleftrightarrow> 
  (rel_kat.Hoare \<lceil>P \<sqinter> B\<rceil> X \<lceil>Q\<rceil> \<and> rel_kat.Hoare \<lceil>P \<sqinter> - B\<rceil> Y \<lceil>Q\<rceil>)"
  by (auto simp: rel_kat.H_cond_iff rel_kat_H)

\<comment> \<open> Rewriting the Hoare rule for the while loop \<close>

abbreviation while_inv_sugar :: "'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a rel \<Rightarrow> 'a rel" ("WHILE _ INV _ DO _" [64,64,64] 63) 
  where "WHILE B INV I DO X \<equiv> rel_kat.while_inv \<lceil>B\<rceil> \<lceil>I\<rceil> X"

lemma sH_while_inv: "\<forall>s. P s \<longrightarrow> I s \<Longrightarrow> \<forall>s. I s \<and> \<not> B s \<longrightarrow> Q s \<Longrightarrow> rel_kat.Hoare \<lceil>I \<sqinter> B\<rceil> X \<lceil>I\<rceil> 
  \<Longrightarrow> rel_kat.Hoare \<lceil>P\<rceil> (WHILE B INV I DO X) \<lceil>Q\<rceil>"
  by (rule rel_kat.H_while_inv, auto simp: p2r_def rel_kat.Hoare_def, fastforce)

\<comment> \<open> Finally, we add a Hoare triple rule for finite iterations. \<close>

abbreviation loopi_sugar :: "'a rel \<Rightarrow> 'a pred \<Rightarrow> 'a rel" ("LOOP _ INV _ " [64,64] 63)
  where "LOOP X INV I \<equiv> rel_kat.loopi X \<lceil>I\<rceil>"

lemma H_loop: "rel_kat.Hoare \<lceil>P\<rceil> X \<lceil>P\<rceil> \<Longrightarrow> rel_kat.Hoare \<lceil>P\<rceil> (LOOP X INV I) \<lceil>P\<rceil>"
  by (auto intro: rel_kat.H_loop)

lemma H_loopI: "rel_kat.Hoare \<lceil>I\<rceil> X \<lceil>I\<rceil> \<Longrightarrow> \<lceil>P\<rceil> \<subseteq> \<lceil>I\<rceil> \<Longrightarrow> \<lceil>I\<rceil> \<subseteq> \<lceil>Q\<rceil> \<Longrightarrow> rel_kat.Hoare \<lceil>P\<rceil> (LOOP X INV I) \<lceil>Q\<rceil>"
  using rel_kat.H_loop_inv[of "\<lceil>P\<rceil>" "\<lceil>I\<rceil>" X "\<lceil>Q\<rceil>"] by auto


subsection\<open> Verification of hybrid programs \<close>

\<comment> \<open>Verification by providing evolution\<close>

definition g_evol :: "(('a::ord) \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b pred \<Rightarrow> 'a set \<Rightarrow> 'b rel" ("EVOL")
  where "EVOL \<phi> G T = {(s,s') |s s'. s' \<in> g_orbit (\<lambda>t. \<phi> t s) G T}"

lemma H_g_evol: 
  fixes \<phi> :: "('a::preorder) \<Rightarrow> 'b \<Rightarrow> 'b"
  assumes "P = (\<lambda>s. (\<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)))"
  shows "rel_kat.Hoare \<lceil>P\<rceil> (EVOL \<phi> G T) \<lceil>Q\<rceil>"
  unfolding rel_kat_H g_evol_def g_orbit_eq using assms by clarsimp

lemma sH_g_evol[simp]:  
  fixes \<phi> :: "('a::preorder) \<Rightarrow> 'b \<Rightarrow> 'b"
  shows "rel_kat.Hoare \<lceil>P\<rceil> (EVOL \<phi> G T) \<lceil>Q\<rceil> = (\<forall>s. P s \<longrightarrow> (\<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)))"
  unfolding rel_kat_H g_evol_def g_orbit_eq by auto

\<comment> \<open>Verification by providing solutions\<close>

definition g_ode :: "(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> real set \<Rightarrow> 'a set \<Rightarrow> real \<Rightarrow> 
  'a rel" ("(1x\<acute>=_ & _ on _ _ @ _)") 
  where "(x\<acute>= f & G on T S @ t\<^sub>0) = {(s,s') |s s'. s' \<in> g_orbital f G T S t\<^sub>0 s}"

lemma H_g_orbital: 
  "P = (\<lambda>s. (\<forall>X\<in>ivp_sols (\<lambda>t. f) T S t\<^sub>0 s. \<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (X \<tau>)) \<longrightarrow> Q (X t))) \<Longrightarrow> 
  rel_kat.Hoare \<lceil>P\<rceil> (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
  unfolding rel_kat_H g_ode_def g_orbital_eq by clarsimp

lemma sH_g_orbital: "rel_kat.Hoare \<lceil>P\<rceil> (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil> = 
  (\<forall>s. P s \<longrightarrow> (\<forall>X\<in>ivp_sols (\<lambda>t. f) T S t\<^sub>0 s. \<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (X \<tau>)) \<longrightarrow> Q (X t)))"
  unfolding g_orbital_eq g_ode_def rel_kat_H by auto

context local_flow
begin

lemma H_g_ode:
  assumes "P = (\<lambda>s. s \<in> S \<longrightarrow> (\<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)))" 
  shows "rel_kat.Hoare \<lceil>P\<rceil> (x\<acute>= f & G on T S @ 0) \<lceil>Q\<rceil>"
proof(unfold rel_kat_H g_ode_def g_orbital_eq assms, clarsimp)
  fix s t X
  assume hyps: "t \<in> T" "\<forall>x. x \<in> T \<and> x \<le> t \<longrightarrow> G (X x)" "X \<in> Sols (\<lambda>t. f) T S 0 s"
     and main: "s \<in> S \<longrightarrow> (\<forall>t\<in>T. (\<forall>\<tau>. \<tau> \<in> T \<and> \<tau> \<le> t \<longrightarrow> G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s))"
  have "s \<in> S"
    using ivp_solsD[OF hyps(3)] init_time by auto
  hence "\<forall>\<tau>\<in>down T t. X \<tau> = \<phi> \<tau> s"
    using eq_solution hyps by blast
  thus "Q (X t)"
    using main \<open>s \<in> S\<close> hyps by fastforce
qed

lemma sH_g_ode: "rel_kat.Hoare \<lceil>P\<rceil> (x\<acute>= f & G on T S @ 0) \<lceil>Q\<rceil> = 
  (\<forall>s\<in>S. P s \<longrightarrow> (\<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)))"
proof(unfold sH_g_orbital, clarsimp, safe)
  fix s t
  assume hyps: "s \<in> S" "P s" "t\<in>T" "\<forall>\<tau>. \<tau> \<in> T \<and> \<tau> \<le> t \<longrightarrow> G (\<phi> \<tau> s)"
    and main: "\<forall>s. P s \<longrightarrow> (\<forall>X\<in>Sols (\<lambda>t. f) T S 0 s. \<forall>t\<in>T. (\<forall>\<tau>. \<tau> \<in> T \<and> \<tau> \<le> t \<longrightarrow> G (X \<tau>)) \<longrightarrow> Q (X t))"
  hence "(\<lambda>t. \<phi> t s) \<in> Sols (\<lambda>t. f) T S 0 s"
    using in_ivp_sols by blast
  thus "Q (\<phi> t s)"
    using main hyps by fastforce
next
  fix s X t
  assume hyps: "P s" "X \<in> Sols (\<lambda>t. f) T S 0 s" "t \<in> T"  "\<forall>\<tau>. \<tau> \<in> T \<and> \<tau> \<le> t \<longrightarrow> G (X \<tau>)"
    and main: "\<forall>s\<in>S. P s \<longrightarrow> (\<forall>t\<in>T. (\<forall>\<tau>. \<tau> \<in> T \<and> \<tau> \<le> t \<longrightarrow> G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s))"
  hence obs: "s \<in> S"
    using ivp_sols_def[of "\<lambda>t. f"] init_time by auto
  hence "\<forall>\<tau>\<in>down T t. X \<tau> = \<phi> \<tau> s"
    using eq_solution hyps by blast
  thus "Q (X t)"
    using hyps main obs by auto
qed

lemma sH_g_ode_ivl: "\<tau> \<ge> 0 \<Longrightarrow> \<tau> \<in> T \<Longrightarrow> rel_kat.Hoare \<lceil>P\<rceil> (x\<acute>= f & G on {0..\<tau>} S @ 0) \<lceil>Q\<rceil> = 
  (\<forall>s\<in>S. P s \<longrightarrow> (\<forall>t\<in>{0..\<tau>}. (\<forall>\<tau>\<in>{0..t}. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)))"
proof(unfold sH_g_orbital, clarsimp, safe)
  fix s t
  assume hyps: "0 \<le> \<tau>" "\<tau> \<in> T" "s \<in> S" "P s" "t \<in> {0..\<tau>}" "\<forall>\<tau>\<in>{0..t}. G (\<phi> \<tau> s)"
    and main: "\<forall>s. P s \<longrightarrow> (\<forall>X\<in>Sols (\<lambda>t. f) {0..\<tau>} S 0 s. \<forall>t\<in>{0..\<tau>}. 
  (\<forall>\<tau>'. 0 \<le> \<tau>' \<and> \<tau>' \<le> \<tau> \<and> \<tau>' \<le> t \<longrightarrow> G (X \<tau>')) \<longrightarrow> Q (X t))"
  hence "(\<lambda>t. \<phi> t s) \<in> Sols (\<lambda>t. f) {0..\<tau>} S 0 s"
    using in_ivp_sols_ivl closed_segment_eq_real_ivl[of 0 \<tau>] by force
  thus "Q (\<phi> t s)"
    using main hyps by fastforce
next
  fix s X t
  assume hyps: "0 \<le> \<tau>" "\<tau> \<in> T" "P s" "X \<in> Sols (\<lambda>t. f) {0..\<tau>} S 0 s" "t \<in> {0..\<tau>}"  
    "\<forall>\<tau>'. 0 \<le> \<tau>' \<and> \<tau>' \<le> \<tau> \<and> \<tau>' \<le> t \<longrightarrow> G (X \<tau>')"
    and main: "\<forall>s\<in>S. P s \<longrightarrow> (\<forall>t\<in>{0..\<tau>}. (\<forall>\<tau>\<in>{0..t}. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s))"
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
  thus "Q (X t)"
    using hyps main \<open>s \<in> S\<close> by auto
qed

lemma sH_orbit: 
  "rel_kat.Hoare \<lceil>P\<rceil> ({(s,s') | s s'. s' \<in> \<gamma>\<^sup>\<phi> s}) \<lceil>Q\<rceil> = (\<forall>s \<in> S. P s \<longrightarrow> (\<forall> t \<in> T. Q (\<phi> t s)))"
  using sH_g_ode unfolding orbit_def g_ode_def by auto

end

\<comment> \<open> Verification with differential invariants \<close>

definition g_ode_inv :: "(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> real set \<Rightarrow> 'a set \<Rightarrow> 
  real \<Rightarrow> 'a pred \<Rightarrow> 'a rel" ("(1x\<acute>=_ & _ on _ _ @ _ DINV _ )") 
  where "(x\<acute>= f & G on T S @ t\<^sub>0 DINV I) = (x\<acute>= f & G on T S @ t\<^sub>0)"

lemma sH_g_orbital_guard: 
  assumes "R = (\<lambda>s. G s \<and> Q s)"
  shows "rel_kat.Hoare \<lceil>P\<rceil> (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil> = rel_kat.Hoare \<lceil>P\<rceil> (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>R\<rceil>" 
  using assms unfolding g_orbital_eq rel_kat_H ivp_sols_def g_ode_def by auto

lemma sH_g_orbital_inv:
  assumes "\<lceil>P\<rceil> \<le> \<lceil>I\<rceil>" and "rel_kat.Hoare \<lceil>I\<rceil> (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>I\<rceil>" and "\<lceil>I\<rceil> \<le> \<lceil>Q\<rceil>"
  shows "rel_kat.Hoare \<lceil>P\<rceil> (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
  using assms(1) apply(rule_tac p'="\<lceil>I\<rceil>" in rel_kat.H_consl, simp)
  using assms(3) apply(rule_tac q'="\<lceil>I\<rceil>" in rel_kat.H_consr, simp)
  using assms(2) by simp

lemma sH_diff_inv[simp]: "rel_kat.Hoare \<lceil>I\<rceil> (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>I\<rceil> = diff_invariant I f T S t\<^sub>0 G"
  unfolding diff_invariant_eq rel_kat_H g_orbital_eq g_ode_def by auto

lemma H_g_ode_inv: "rel_kat.Hoare \<lceil>I\<rceil> (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>I\<rceil> \<Longrightarrow> \<lceil>P\<rceil> \<le> \<lceil>I\<rceil> \<Longrightarrow> 
  \<lceil>\<lambda>s. I s \<and> G s\<rceil> \<le> \<lceil>Q\<rceil> \<Longrightarrow> rel_kat.Hoare \<lceil>P\<rceil> (x\<acute>= f & G on T S @ t\<^sub>0 DINV I) \<lceil>Q\<rceil>"
  unfolding g_ode_inv_def apply(rule_tac q'="\<lceil>\<lambda>s. I s \<and> G s\<rceil>" in rel_kat.H_consr, simp)
  apply(subst sH_g_orbital_guard[symmetric], force)
  by (rule_tac I="I" in sH_g_orbital_inv, simp_all)

subsection \<open> Derivation of the rules of dL \<close>

text \<open> We derive domain specific rules of differential dynamic logic (dL). First we present a 
generalised version, then we show the rules as instances of the general ones.\<close>

lemma diff_solve_axiom: 
  fixes c::"'a::{heine_borel, banach}"
  assumes "0 \<in> T" and "is_interval T" "open T"
    and "\<forall>s. P s \<longrightarrow> (\<forall>t\<in>T. (\<P> (\<lambda> t. s + t *\<^sub>R c) (down T t) \<subseteq> {s. G s}) \<longrightarrow> Q (s + t *\<^sub>R c))"
  shows "rel_kat.Hoare \<lceil>P\<rceil> (x\<acute>=(\<lambda>s. c) & G on T UNIV @ 0) \<lceil>Q\<rceil>"
  apply(subst local_flow.sH_g_ode[where f="\<lambda>s. c" and \<phi>="(\<lambda> t x. x + t *\<^sub>R c)"])
  using line_is_local_flow assms by auto

lemma diff_solve_rule:
  assumes "local_flow f T UNIV \<phi>"
    and "\<forall>s. P s \<longrightarrow> (\<forall> t\<in>T. (\<P> (\<lambda>t. \<phi> t s) (down T t) \<subseteq> {s. G s}) \<longrightarrow> Q (\<phi> t s))"
  shows "rel_kat.Hoare \<lceil>P\<rceil> (x\<acute>= f & G on T UNIV @ 0) \<lceil>Q\<rceil>"
  using assms by(subst local_flow.sH_g_ode, auto)

lemma diff_weak_rule: 
  assumes "\<lceil>G\<rceil> \<le> \<lceil>Q\<rceil>"
  shows "rel_kat.Hoare \<lceil>P\<rceil> (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
  using assms unfolding g_orbital_eq rel_kat_H ivp_sols_def g_ode_def by auto

lemma diff_cut_rule:
  assumes Thyp: "is_interval T" "t\<^sub>0 \<in> T"
    and wp_C:"rel_kat.Hoare \<lceil>P\<rceil> (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>C\<rceil>"
    and wp_Q:"rel_kat.Hoare \<lceil>P\<rceil> (x\<acute>= f & (\<lambda> s. G s \<and> C s) on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
  shows "rel_kat.Hoare \<lceil>P\<rceil> (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil>"
proof(subst rel_kat_H, simp add: g_orbital_eq p2r_def g_ode_def, clarsimp)
  fix t::real and X::"real \<Rightarrow> 'a" and s assume "P s" and "t \<in> T"
    and x_ivp:"X \<in> ivp_sols (\<lambda>t. f) T S t\<^sub>0 s" 
    and guard_x:"\<forall>x. x \<in> T \<and> x \<le> t \<longrightarrow> G (X x)"
  have "\<forall>t\<in>(down T t). X t \<in> g_orbital f G T S t\<^sub>0 s"
    using g_orbitalI[OF x_ivp] guard_x by auto
  hence "\<forall>t\<in>(down T t). C (X t)" 
    using wp_C \<open>P s\<close> by (subst (asm) rel_kat_H, auto simp: g_ode_def)
  hence "X t \<in> g_orbital f (\<lambda>s. G s \<and> C s) T S t\<^sub>0 s"
    using guard_x \<open>t \<in> T\<close> by (auto intro!: g_orbitalI x_ivp)
  thus "Q (X t)"
    using \<open>P s\<close> wp_Q by (subst (asm) rel_kat_H) (auto simp: g_ode_def)
qed

abbreviation g_global_ode ::"(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> 'a rel" ("(1x\<acute>=_ & _)") 
  where "(x\<acute>= f & G) \<equiv> (x\<acute>= f & G on UNIV UNIV @ 0)"

abbreviation g_global_ode_inv :: "(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a rel" 
  ("(1x\<acute>=_ & _ DINV _)") where "(x\<acute>= f & G DINV I) \<equiv> (x\<acute>= f & G on UNIV UNIV @ 0 DINV I)"

end