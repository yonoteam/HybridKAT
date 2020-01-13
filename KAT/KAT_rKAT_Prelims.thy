(*  Title:       Verification components with KAT 
    Author:      Jonathan Julián Huerta y Munive, 2019
    Maintainer:  Jonathan Julián Huerta y Munive <jjhuertaymunive1@sheffield.ac.uk>
*)

section \<open> Verification components with KAT \<close>

text \<open> In this section we derive the rules of Hoare Logic and a refinement calculus in KAT. \<close>

theory KAT_rKAT_Prelims
  imports
  "KAT_and_DRA.PHL_KAT"
  "Transformer_Semantics.Kleisli_Quantale"
  "UTP.utp_pred_laws"
  "UTP.utp_lift_parser"
  "UTP.utp_lift_pretty"
begin recall_syntax

purge_notation Lattices.inf (infixl "\<squnion>" 70)
notation Lattices.inf (infixl "\<sqinter>" 70)
purge_notation Lattices.sup (infixl "\<sqinter>" 65)
notation Lattices.sup (infixl "\<squnion>" 65)

subsection \<open> Hoare logic derivation \<close> 

no_notation if_then_else ("if _ then _ else _ fi" [64,64,64] 63)
        and while ("while _ do _ od" [64,64] 63)

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

lemma H_inv_plus: "t i = i \<Longrightarrow> t j = j \<Longrightarrow> H i x i \<Longrightarrow>  H j x j \<Longrightarrow>  H (i + j) x (i + j)"
  unfolding Hoare_def using combine_common_factor
  by (smt add_commute add.left_commute distrib_left join.sup.absorb_iff1 t_add_closed)

lemma H_inv_mult: "t i = i \<Longrightarrow> t j = j \<Longrightarrow> H i x i \<Longrightarrow>  H j x j \<Longrightarrow>  H (i \<cdot> j) x (i \<cdot> j)"
  unfolding Hoare_def by (smt n_kat_2 n_mult_comm t_mult_closure mult_assoc)

end


subsection \<open> refinement KAT \<close> 

class rkat = kat +
  fixes Ref :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes spec_def:  "x \<le> Ref p q \<longleftrightarrow> H p x q"

begin (* mostly by Victor Gomes, Georg Struth *)

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

end