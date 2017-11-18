(*  Title:      HOL/Import/HOL_Light_Maps.thy
    Author:     Cezary Kaliszyk, University of Innsbruck
    Author:     Alexander Krauss, QAware GmbH

Based on earlier code by Steven Obua and Sebastian Skalberg
*)

header {* Type and constant mappings of HOL Light importer *}

theory HOL_Light_Maps
imports Import_Setup Real
begin

lemma [import_const T]:
  "True = ((\<lambda>p :: bool. p) = (\<lambda>p. p))"
  by simp

lemma [import_const "/\\"]:
  "(op \<and>) = (\<lambda>p q. (\<lambda>f. f p q \<Colon> bool) = (\<lambda>f. f True True))"
  by metis

lemma [import_const "==>"]:
  "(op \<longrightarrow>) = (\<lambda>(p\<Colon>bool) q\<Colon>bool. (p \<and> q) = p)"
  by auto

lemma [import_const "!"]:
  "All = (\<lambda>P\<Colon>'A \<Rightarrow> bool. P = (\<lambda>x\<Colon>'A. True))"
  by auto

lemma [import_const "?"]:
  "Ex = (\<lambda>P\<Colon>'A \<Rightarrow> bool. All (\<lambda>q\<Colon>bool. (All (\<lambda>x\<Colon>'A\<Colon>type. (P x) \<longrightarrow> q)) \<longrightarrow> q))"
  by auto

lemma [import_const "\\/"]:
  "(op \<or>) = (\<lambda>p q. \<forall>r. (p \<longrightarrow> r) \<longrightarrow> (q \<longrightarrow> r) \<longrightarrow> r)"
  by auto

lemma [import_const F]:
  "False = (\<forall>p. p)"
  by auto

lemma [import_const "~"]:
  "Not = (\<lambda>p. p \<longrightarrow> False)"
  by simp

lemma [import_const "?!"]:
  "Ex1 = (\<lambda>P\<Colon>'A \<Rightarrow> bool. Ex P \<and> (\<forall>x y. P x \<and> P y \<longrightarrow> x = y))"
  by auto

lemma [import_const "_FALSITY_"]: "False = False"
  by simp

lemma hl_ax1: "\<forall>t\<Colon>'A \<Rightarrow> 'B. (\<lambda>x. t x) = t"
  by metis

lemma hl_ax2: "\<forall>P x\<Colon>'A. P x \<longrightarrow> P (Eps P)"
  by (auto intro: someI)

lemma [import_const COND]:
  "If = (\<lambda>t (t1 :: 'A) t2. SOME x. (t = True \<longrightarrow> x = t1) \<and> (t = False \<longrightarrow> x = t2))"
  unfolding fun_eq_iff by auto

lemma [import_const o]:
  "(op \<circ>) = (\<lambda>(f\<Colon>'B \<Rightarrow> 'C) g x\<Colon>'A. f (g x))"
  unfolding fun_eq_iff by simp

lemma [import_const I]: "id = (\<lambda>x\<Colon>'A. x)"
  by auto

lemma [import_type 1 one_ABS one_REP]:
  "type_definition Rep_unit Abs_unit (Collect (\<lambda>b. b))"
  by (metis (full_types) Collect_cong singleton_conv2 type_definition_unit)

lemma [import_const one]: "() = (SOME x\<Colon>unit. True)"
  by auto

lemma [import_const mk_pair]:
  "Pair_Rep = (\<lambda>(x\<Colon>'A) (y\<Colon>'B) (a\<Colon>'A) b\<Colon>'B. a = x \<and> b = y)"
  by (simp add: Pair_Rep_def fun_eq_iff)

lemma [import_type prod ABS_prod REP_prod]:
  "type_definition Rep_prod Abs_prod (Collect (\<lambda>x\<Colon>'A \<Rightarrow> 'B \<Rightarrow> bool. \<exists>a b. x = Pair_Rep a b))"
  using type_definition_prod[unfolded Product_Type.prod_def] by simp

lemma [import_const ","]: "Pair = (\<lambda>(x\<Colon>'A) y\<Colon>'B. Abs_prod (Pair_Rep x y))"
  by (metis Pair_def)

lemma [import_const FST]:
  "fst = (\<lambda>p\<Colon>'A \<times> 'B. SOME x\<Colon>'A. \<exists>y\<Colon>'B. p = (x, y))"
  by auto

lemma [import_const SND]:
  "snd = (\<lambda>p\<Colon>'A \<times> 'B. SOME y\<Colon>'B. \<exists>x\<Colon>'A. p = (x, y))"
  by auto

lemma CURRY_DEF[import_const CURRY]:
  "curry = (\<lambda>(f\<Colon>'A \<times> 'B \<Rightarrow> 'C) x y. f (x, y))"
  using curry_def .

definition [import_const ONE_ONE, simp]:
  "ONE_ONE = (\<lambda>(f\<Colon>'A \<Rightarrow> 'B). \<forall>x1 x2. f x1 = f x2 \<longrightarrow> x1 = x2)"

lemma [import_rewrite]: "ONE_ONE = inj"
  by (auto simp add: fun_eq_iff inj_on_def)

definition [import_const ONTO, simp]:
  "ONTO = (\<lambda>(f\<Colon>'A \<Rightarrow> 'B). \<forall>y. \<exists>x. y = f x)"

lemma [import_rewrite]: "ONTO = surj"
  by (auto simp add: fun_eq_iff)

lemma hl_ax3: "\<exists>f\<Colon>ind \<Rightarrow> ind. ONE_ONE f \<and> \<not> ONTO f"
  by (rule_tac x="Suc_Rep" in exI)
     (metis Suc_Rep_inject' Suc_Rep_not_Zero_Rep ONTO_def ONE_ONE_def)

import_type_map num : Nat.nat
import_const_map "_0" : Groups.zero_class.zero
import_const_map SUC : Nat.Suc

definition [import_const NUMERAL, simp]: "NUM = (\<lambda>x :: nat. x)"

lemma NOT_SUC: "\<forall>n. Suc n \<noteq> NUM 0"
  by simp

lemma SUC_INJ: "\<forall>m n. (Suc m = Suc n) = (m = n)"
  by simp

lemma num_INDUCTION:
  "\<forall>P. P (NUM 0) \<and> (\<forall>n. P n \<longrightarrow> P (Suc n)) \<longrightarrow> (\<forall>n. P n)"
  by (auto intro: nat.induct)

lemma num_Axiom:
  "\<forall>(e\<Colon>'A\<Colon>type) f. \<exists>!fn. fn (NUM 0) = e \<and> (\<forall>n. fn (Suc n) = f (fn n) n)"
  apply (intro allI)
  apply (rule_tac a="nat_rec e (\<lambda>a b. f b a)" in ex1I)
  apply (simp_all add: fun_eq_iff)
  apply rule
  apply (induct_tac xa)
  apply simp_all
  done

definition [simp]: "bit0 n = 2 * n"

lemma [import_const BIT0]:
  "bit0 = (SOME fn. fn (NUM 0) = NUM 0 \<and> (\<forall>n. fn (Suc n) = Suc (Suc (fn n))))"
  apply (auto intro!: some_equality[symmetric])
  apply (auto simp add: fun_eq_iff)
  apply (induct_tac x)
  apply auto
  done

definition [import_const BIT1, simp]:
  "bit1 = (\<lambda>x. Suc (bit0 x))"

definition [simp]: "pred n = n - 1"

lemma PRE[import_const PRE : HOL_Light_Maps.pred]:
  "pred (NUM 0) = NUM 0"
  "\<forall>n. pred (Suc n) = n"
  by simp_all

lemma ADD[import_const "+" : Groups.plus_class.plus]:
  "\<forall>n :: nat. (NUM 0) + n = n"
  "\<forall>m n. (Suc m) + n = Suc (m + n)"
  by simp_all

lemma MULT[import_const "*" : Groups.times_class.times]:
  "\<forall>n :: nat. (NUM 0) * n = NUM 0"
  "\<forall>m n. (Suc m) * n = (m * n) + n"
  by simp_all

lemma EXP[import_const EXP : Power.power_class.power]:
  "\<forall>m. m ^ (NUM 0) = NUM (bit1 0)"
  "\<forall>(m :: nat) n. m ^ (Suc n) = m * (m ^ n)"
  by simp_all

lemma LE[import_const "<=" : Orderings.ord_class.less_eq]:
  "\<forall>m :: nat. m \<le> (NUM 0) = (m = NUM 0)"
  "\<forall>m n. m \<le> (Suc n) = (m = Suc n \<or> m \<le> n)"
  by auto

lemma LT[import_const "<" : Orderings.ord_class.less]:
  "\<forall>m :: nat. m < (NUM 0) = False"
  "\<forall>m n. m < (Suc n) = (m = n \<or> m < n)"
  by auto

lemma DEF_GE[import_const ">=" : "Orderings.ord_class.greater_eq"]:
  "(op \<ge>) = (\<lambda>x y :: nat. y \<le> x)"
  by simp

lemma DEF_GT[import_const ">" : "Orderings.ord_class.greater"]:
  "(op >) = (\<lambda>x y :: nat. y < x)"
  by simp

lemma DEF_MAX[import_const "MAX"]:
  "max = (\<lambda>x y :: nat. if x \<le> y then y else x)"
  by (auto simp add: min_max.le_iff_sup fun_eq_iff)

lemma DEF_MIN[import_const "MIN"]:
  "min = (\<lambda>x y :: nat. if x \<le> y then x else y)"
  by (auto simp add: min_max.le_iff_inf fun_eq_iff)

lemma EVEN[import_const "EVEN" : "Parity.even_odd_class.even"]:
  "even (NUM 0) = True"
  "\<forall>n. even (Suc n) = (\<not> even n)"
  by simp_all

lemma SUB[import_const "-" : "Groups.minus_class.minus"]:
  "\<forall>m\<Colon>nat. m - (NUM 0) = m"
  "\<forall>m n. m - (Suc n) = pred (m - n)"
  by simp_all

lemma FACT[import_const "FACT" : "Fact.fact_class.fact"]:
  "fact (NUM 0) = NUM (bit1 0)"
  "\<forall>n. fact (Suc n) = Suc n * fact n"
  by simp_all

import_const_map MOD : Divides.div_class.mod
import_const_map DIV : Divides.div_class.div

lemma DIVISION_0:
  "\<forall>m n\<Colon>nat. if n = NUM 0 then m div n = NUM 0 \<and> m mod n = m else m = m div n * n + m mod n \<and> m mod n < n"
  by simp

(*
lemma WF[import_const WF : Wellfounded.wfP]:
  "\<forall>u. wfP u \<longleftrightarrow> (\<forall>P. (\<exists>x :: 'A. P x) \<longrightarrow> (\<exists>x. P x \<and> (\<forall>y. u y x \<longrightarrow> \<not> P y)))"
proof (intro allI iffI impI wfI_min[to_pred], elim exE wfE_min[to_pred])
  fix x :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and xa :: "'a" and Q
  assume a: "xa \<in> Q"
  assume "\<forall>P. Ex P \<longrightarrow> (\<exists>xa. P xa \<and> (\<forall>y. x y xa \<longrightarrow> \<not> P y))"
  then have "Ex (\<lambda>x. x \<in> Q) \<longrightarrow> (\<exists>xa. (\<lambda>x. x \<in> Q) xa \<and> (\<forall>y. x y xa \<longrightarrow> \<not> (\<lambda>x. x \<in> Q) y))" by auto
  then show "\<exists>z\<in>Q. \<forall>y. x y z \<longrightarrow> y \<notin> Q" using a by auto
next
  fix x P and xa :: 'A and z
  assume "P xa" "z \<in> {a. P a}" "\<And>y. x y z \<Longrightarrow> y \<notin> {a. P a}"
  then show "\<exists>xa. P xa \<and> (\<forall>y. x y xa \<longrightarrow> \<not> P y)" by auto
qed auto
*)

lemmas [import_type sum "_dest_sum" "_mk_sum"] = type_definition_sum[where 'a="'A" and 'b="'B"]
import_const_map INL : Sum_Type.Inl
import_const_map INR : Sum_Type.Inr

lemma sum_INDUCT:
  "\<forall>P. (\<forall>a :: 'A. P (Inl a)) \<and> (\<forall>a :: 'B. P (Inr a)) \<longrightarrow> (\<forall>x. P x)"
  by (auto intro: sum.induct)

lemma sum_RECURSION:
  "\<forall>Inl' Inr'. \<exists>fn. (\<forall>a :: 'A. fn (Inl a) = (Inl' a :: 'Z)) \<and> (\<forall>a :: 'B. fn (Inr a) = Inr' a)"
  by (intro allI, rule_tac x="sum_case Inl' Inr'" in exI) auto

lemma OUTL[import_const "OUTL" : "Sum_Type.Projl"]:
  "Sum_Type.Projl (Inl x) = x"
  by simp

lemma OUTR[import_const "OUTR" : "Sum_Type.Projr"]:
  "Sum_Type.Projr (Inr y) = y"
  by simp

import_type_map list : List.list
import_const_map NIL : List.list.Nil
import_const_map CONS : List.list.Cons

lemma list_INDUCT:
  "\<forall>P\<Colon>'A list \<Rightarrow> bool. P [] \<and> (\<forall>a0 a1. P a1 \<longrightarrow> P (a0 # a1)) \<longrightarrow> (\<forall>x. P x)"
  using list.induct by auto

lemma list_RECURSION:
 "\<forall>nil' cons'. \<exists>fn\<Colon>'A list \<Rightarrow> 'Z. fn [] = nil' \<and> (\<forall>(a0\<Colon>'A) a1\<Colon>'A list. fn (a0 # a1) = cons' a0 a1 (fn a1))"
  by (intro allI, rule_tac x="list_rec nil' cons'" in exI) auto


lemma HD[import_const HD : List.hd]:
  "hd ((h\<Colon>'A) # t) = h"
  by simp

lemma TL[import_const TL : List.tl]:
  "tl ((h\<Colon>'A) # t) = t"
  by simp

lemma APPEND[import_const APPEND : List.append]:
  "\<forall>l\<Colon>'A list. [] @ l = l"
  "\<forall>(h\<Colon>'A) t l. (h # t) @ l = h # t @ l"
  by simp_all

lemma REVERSE[import_const REVERSE : List.rev]:
  "rev [] = ([] :: 'A list)"
  "rev ((x\<Colon>'A) # l) = rev l @ [x]"
  by simp_all

lemma LENGTH[import_const LENGTH : List.length]:
  "length ([] :: 'A list) = NUM 0"
  "\<forall>(h\<Colon>'A) t. length (h # t) = Suc (length t)"
  by simp_all

lemma MAP[import_const MAP : List.map]:
  "\<forall>f\<Colon>'A \<Rightarrow> 'B. map f [] = []"
  "\<forall>(f\<Colon>'A \<Rightarrow> 'B) h t. map f (h # t) = f h # map f t"
  by simp_all

lemma LAST[import_const LAST : List.last]:
  "last ((h\<Colon>'A) # t) = (if t = [] then h else last t)"
  by simp

lemma BUTLAST[import_const BUTLAST : List.butlast]:
  "butlast [] = ([] :: 't18547 list)"
  "butlast ((h :: 't18547) # t) = (if t = [] then [] else h # butlast t)"
  by simp_all

lemma REPLICATE [import_const REPLICATE : List.replicate]:
  "replicate (NUM (0\<Colon>nat)) (x\<Colon>'t18568) = []"
  "replicate (Suc n) x = (x\<Colon>'t18568) # replicate n x"
  by simp_all

lemma NULL[import_const NULL : List.null]:
  "List.null ([]\<Colon>'t18583 list) = True"
  "List.null ((h\<Colon>'t18583) # t) = False"
  unfolding null_def by simp_all

lemma ALL[import_const ALL : List.list_all]:
  "list_all (P\<Colon>'t18603 \<Rightarrow> bool) [] = True"
  "list_all (P\<Colon>'t18603 \<Rightarrow> bool) (h # t) = (P h \<and> list_all P t)"
  by simp_all

lemma EX[import_const EX : List.list_ex]:
  "list_ex (P\<Colon>'t18624 \<Rightarrow> bool) [] = False"
  "list_ex (P\<Colon>'t18624 \<Rightarrow> bool) (h # t) = (P h \<or> list_ex P t)"
  by simp_all

lemma ITLIST[import_const ITLIST : List.foldr]:
  "foldr (f\<Colon>'t18647 \<Rightarrow> 't18646 \<Rightarrow> 't18646) [] b = b"
  "foldr (f\<Colon>'t18647 \<Rightarrow> 't18646 \<Rightarrow> 't18646) (h # t) b = f h (foldr f t b)"
  by simp_all

lemma ALL2_DEF[import_const ALL2 : List.list_all2]:
  "list_all2 (P\<Colon>'t18705 \<Rightarrow> 't18712 \<Rightarrow> bool) [] l2 = (l2 = [])"
  "list_all2 (P\<Colon>'t18705\<Colon>type \<Rightarrow> 't18712\<Colon>type \<Rightarrow> bool) (h1 # t1) l2 =
  (if l2 = [] then False else P h1 (hd l2) \<and> list_all2 P t1 (tl l2))"
  by (induct_tac [!] l2, simp_all)

lemma FILTER[import_const FILTER : List.filter]:
  "filter (P\<Colon>'t18890 \<Rightarrow> bool) [] = []"
  "filter P ((h\<Colon>'t18890) # t) = (if P h then h # filter P t else filter P t)"
  by simp_all

lemma ZIP[import_const ZIP : List.zip]:
  "zip [] [] = ([] :: ('t19034 \<times> 't19035) list)"
  "zip ((h1\<Colon>'t19059) # t1) ((h2\<Colon>'t19060) # t2) = (h1, h2) # zip t1 t2"
  by simp_all

lemma [import_rewrite]:
  "NUM x = 1 \<Longrightarrow> NUM (bit0 x) = numeral (num.Bit0 num.One)"
  "NUM x = 1 \<Longrightarrow> NUM (bit1 x) = numeral (num.Bit1 num.One)"
  "NUM x = numeral y \<Longrightarrow> NUM (bit0 x) = numeral (num.Bit0 y)"
  "NUM x = numeral y \<Longrightarrow> NUM (bit1 x) = numeral (num.Bit1 y)"
  "NUM (bit1 0) = 1"
  "NUM 0 = 0"
  by (simp_all add: numeral_Bit1 numeral_Bit0)

lemma REAL_ADD_SYM:
  "\<forall>(x\<Colon>real) y\<Colon>real. x + y = y + x"
  by simp
lemma REAL_ADD_ASSOC:
  "\<forall>(x\<Colon>real) (y\<Colon>real) z\<Colon>real. x + (y + z) = (x + y) + z"
  by simp
lemma REAL_ADD_LID:
  "\<forall>x\<Colon>real. (real_of_nat (NUM (0\<Colon>nat))) + x = x"
  by simp
lemma REAL_ADD_LINV:
  "\<forall>x\<Colon>real. (- x) + x = real_of_nat (NUM (0\<Colon>nat))"
  by simp
lemma REAL_MUL_SYM:
  "\<forall>(x\<Colon>real) y\<Colon>real. x * y = y * x"
  by simp
lemma REAL_MUL_ASSOC:
  "\<forall>(x\<Colon>real) (y\<Colon>real) z\<Colon>real. x * (y * z) = (x * y) * z"
  by simp
lemma REAL_MUL_LID:
  "\<forall>x\<Colon>real. (real_of_nat (NUM (bit1 (0\<Colon>nat)))) * x = x"
  by simp
lemma REAL_ADD_LDISTRIB:
  "\<forall>(x\<Colon>real) (y\<Colon>real) z\<Colon>real. x * (y + z) = (x * y) + (x * z)"
  by (metis REAL_MUL_SYM comm_semiring_class.distrib)
lemma REAL_LE_REFL:
  "\<forall>x\<Colon>real. x \<le> x"
  by simp
lemma REAL_COMPLETE_SOMEPOS:
  "\<forall>P\<Colon>real \<Rightarrow> bool.
  (\<exists>x. P x \<and> (real_of_nat (NUM (0\<Colon>nat))) \<le> x) \<and> (\<exists>M. \<forall>x. P x \<longrightarrow> x \<le> M) \<longrightarrow>
  (\<exists>M. (\<forall>x. P x \<longrightarrow> x \<le> M) \<and> (\<forall>M'. (\<forall>x. P x \<longrightarrow> x \<le> M') \<longrightarrow> M \<le> M'))"
proof fix P :: "real \<Rightarrow> bool"
  show "(\<exists>x. P x \<and> (real_of_nat (NUM (0\<Colon>nat))) \<le> x) \<and> (\<exists>M. \<forall>x. P x \<longrightarrow> x \<le> M) \<longrightarrow>
    (\<exists>M. (\<forall>x. P x \<longrightarrow> x \<le> M) \<and> (\<forall>M'. (\<forall>x. P x \<longrightarrow> x \<le> M') \<longrightarrow> M \<le> M'))"
    using complete_real[unfolded Ball_def, of "Collect P"] by auto
qed
lemma REAL_LE_ANTISYM:
  "\<forall>(x\<Colon>real) y\<Colon>real. (x \<le> y \<and> y \<le> x) = (x = y)"
  by (simp add: order_eq_iff)
lemma REAL_LE_TRANS:
  "\<forall>(x\<Colon>real) (y\<Colon>real) z\<Colon>real. x \<le> y \<and> y \<le> z \<longrightarrow> x \<le> z"
  by simp
lemma REAL_LE_TOTAL:
  "\<forall>(x\<Colon>real) y\<Colon>real. x \<le> y \<or> y \<le> x"
  by (simp add: linorder_linear)
lemma REAL_LE_LADD_IMP:
  "\<forall>(x\<Colon>real) (y\<Colon>real) z\<Colon>real. y \<le> z \<longrightarrow> (x + y) \<le> (x + z)"
  by simp
lemma REAL_LE_MUL:
  "\<forall>(x\<Colon>real) y\<Colon>real.
   (real_of_nat (NUM (0\<Colon>nat))) \<le> x \<and> (real_of_nat (NUM (0\<Colon>nat))) \<le> y \<longrightarrow>
   (real_of_nat (NUM (0\<Colon>nat))) \<le> (x * y)"
  by (simp add: zero_le_mult_iff)
lemma REAL_OF_NUM_LE:
  "\<forall>(m\<Colon>nat) n\<Colon>nat. (real_of_nat m) \<le> (real_of_nat n) = (m \<le> n)"
  by simp
lemma real_sub:
  "\<forall>(x\<Colon>real) y\<Colon>real. x - y = x + (- y)"
  by simp
lemma real_lt:
  "\<forall>(y\<Colon>real) x\<Colon>real. x < y = (\<not> y \<le> x)"
  by (metis linorder_not_less)
definition real_ge:
  "\<forall>(y\<Colon>real) x\<Colon>real. real_ge x y \<longleftrightarrow> y \<le> x"
definition real_gt:
  "\<forall>(y\<Colon>real) x\<Colon>real. real_gt x y \<longleftrightarrow> y < x"
lemma real_abs:
  "\<forall>x\<Colon>real. abs x = (if (real_of_nat (NUM (0\<Colon>nat))) \<le> x then x else - x)"
  by simp
lemma REAL_POLY_CLAUSES_conjunct8:
  "\<forall>x\<Colon>real. x ^ (NUM (0\<Colon>nat)) = real_of_nat (NUM (bit1 (0\<Colon>nat)))"
  by simp
lemma REAL_POLY_CLAUSES_conjunct9:
  "\<forall>(x\<Colon>real) n\<Colon>nat. x ^ (Suc n) = x * (x ^ n)"
  by simp
lemma real_div:
  "\<forall>(x\<Colon>real) y\<Colon>real. x / y = x * (inverse y)"
  by (simp add: divide_real_def)
lemma real_max:
  "\<forall>(n\<Colon>real) m\<Colon>real. max m n = (if m \<le> n then n else m)"
  by (metis le_iff_sup linorder_linear sup_absorb1 sup_real_def)
lemma real_min:
  "\<forall>(m\<Colon>real) n\<Colon>real. min m n = (if m \<le> n then m else n)"
  by (metis inf.commute inf_min le_maxI2 min_max.inf_absorb2 real_max)
lemma REAL_OF_NUM_MUL:
  "\<forall>(m\<Colon>nat) n\<Colon>nat. (real_of_nat m) * (real_of_nat n) = real_of_nat (m * n)"
  by (metis of_nat_mult)
lemma REAL_OF_NUM_ADD:
  "\<forall>(m\<Colon>nat) n\<Colon>nat. (real_of_nat m) + (real_of_nat n) = real_of_nat (m + n)"
  by (metis of_nat_add)
lemma REAL_OF_NUM_EQ:
  "\<forall>(m\<Colon>nat) n\<Colon>nat. (real_of_nat m = real_of_nat n) = (m = n)"
  by simp
lemma REAL_INV_0:
  "inverse (real_of_nat (NUM (0\<Colon>nat))) = real_of_nat (NUM (0\<Colon>nat))"
  by simp
lemma REAL_MUL_LINV:
  "\<forall>x\<Colon>real. x \<noteq> real_of_nat (NUM (0\<Colon>nat)) \<longrightarrow> (inverse x) * x = real_of_nat (NUM (bit1 (0\<Colon>nat)))"
  by simp
lemma real_sgn:
  "\<forall>x\<Colon>real. sgn x =
   (if (real_of_nat (NUM (0\<Colon>nat))) < x then real_of_nat (NUM (bit1 (0\<Colon>nat)))
    else if x < (real_of_nat (NUM (0\<Colon>nat))) then - (real_of_nat (NUM (bit1 (0\<Colon>nat))))
         else real_of_nat (NUM (0\<Colon>nat)))"
  by simp

import_type_map real : RealDef.real
import_const_map real_of_num : Nat.semiring_1_class.of_nat
import_const_map real_neg : Groups.uminus_class.uminus
import_const_map real_add : Groups.plus_class.plus
import_const_map real_mul : Groups.times_class.times
import_const_map real_le : Orderings.ord_class.less_eq
import_const_map real_inv : Fields.inverse_class.inverse
import_const_map real_sub : Groups.minus_class.minus
import_const_map real_lt : Orderings.ord_class.less
import_const_map real_ge : HOL_Light_Maps.real_ge
import_const_map real_gt : HOL_Light_Maps.real_gt
import_const_map real_abs : Groups.abs_class.abs
import_const_map real_pow : Power.power_class.power
import_const_map real_div : Fields.inverse_class.divide
import_const_map real_max : Orderings.ord_class.max
import_const_map real_min : Orderings.ord_class.min
import_const_map real_sgn : Groups.sgn_class.sgn

lemma [import_rewrite]:
  "real_of_nat 0 = 0"
  "real_of_nat 1 = 1"
  by simp_all

definition integer: "\<forall>x::real. integer x = (\<exists>n::nat. abs x = real_of_nat n)"
lemma int_rep: "integer r \<longleftrightarrow> real_of_int (floor r) = r"
  apply rule
  apply (auto simp add: integer)
  apply (case_tac "r >= 0")
  apply simp_all
apply (metis (hide_lams, mono_tags) REAL_LE_ANTISYM le_floor_iff minus_minus of_int_le_iff of_int_minus of_int_of_nat_eq)
  apply (case_tac "r >= 0")
apply simp_all
apply (metis ceiling_mono ceiling_of_int ceiling_zero of_nat_nat)
 by (metis REAL_LE_TOTAL floor_mono floor_of_int le_minus_iff minus_zero of_int_0 of_int_minus of_nat_nat)

lemma int_abstr:
  "floor (real_of_int a :: real) = a"
  by simp
lemma int_eq:
  "\<forall>x y. x = y \<longleftrightarrow> real_of_int x = real_of_int y"
  by simp
lemma dest_int_rep:
  "\<forall>i. \<exists>n. real_of_int i = real_of_nat n \<or> real_of_int i = - real_of_nat n"
  by (auto simp add: of_int_of_nat)
lemma int_le:
  "\<forall>x y. x \<le> y \<longleftrightarrow> real_of_int x \<le> real_of_int y"
  by simp
lemma int_lt:
  "\<forall>x y. x < y \<longleftrightarrow> real_of_int x < real_of_int y"
  by simp
definition [import_rewrite]: "\<forall>(y\<Colon>int) x\<Colon>int. int_ge x y \<longleftrightarrow> y \<le> x"
definition [import_rewrite]: "\<forall>(y\<Colon>int) x\<Colon>int. int_gt x y \<longleftrightarrow> y < x"
lemma int_ge:
  "\<forall>x y. int_ge x y \<longleftrightarrow> real_ge (real_of_int x) (real_of_int y)"
  by (simp add: int_ge_def real_ge)
lemma int_gt:
  "\<forall>x y. int_gt x y \<longleftrightarrow> real_gt (real_of_int x) (real_of_int y)"
  by (simp add: int_gt_def real_gt)
lemma int_of_num: "\<forall>n. int n = floor (real_of_nat n)"
  by simp
lemma int_of_num_th: "\<forall>n. real_of_int (int n) = real_of_nat n"
  by simp
lemma int_neg_th: "\<forall>x. real_of_int (- x) = - real_of_int x"
  by simp
lemma int_add_th: "\<forall>x y. real_of_int (x + y) = real_of_int x + real_of_int y"
  by simp
lemma int_sub_th: "\<forall>x y. real_of_int (x - y) = real_of_int x - real_of_int y"
  by simp
lemma int_mul_th: "\<forall>x y. real_of_int (x * y) = real_of_int x * real_of_int y"
  by simp
lemma int_abs_th: "\<forall>x. real_of_int \<bar>x\<bar> = \<bar>real_of_int x\<bar>"
  by (metis real_of_int_abs real_of_int_def)
lemma int_sgn_th: "\<forall>x. real_of_int (sgn x) = sgn (real_of_int x)"
  apply (rule allI)
  apply (case_tac "x \<le> 0")
  apply (case_tac "x < 0")
  apply simp_all
  done
lemma int_max_th:
  "\<forall>x y. real_of_int (max x y) = max (real_of_int x) (real_of_int y)"
  by (metis le_iff_sup linorder_linear of_int_le_iff sup_absorb1 sup_int_def sup_real_def)
lemma int_min_th:
  "\<forall>x y. real_of_int (min x y) = min (real_of_int x) (real_of_int y)"
  by (metis inf_absorb2 inf_int_def inf_real_def le_iff_inf linorder_linear of_int_le_iff)
lemma int_pow_th:
  "\<forall>x n. real_of_int (x ^ n) = real_of_int x ^ n"
  by (simp add: of_int_power)
lemma INT_IMAGE:
  "\<forall>x. (\<exists>n. x = int n) \<or> (\<exists>n. x = - (int n))"
  by (metis int_cases)

import_type_map int : Int.int
import_const_map real_of_int : Int.ring_1_class.of_int
import_const_map int_of_real : Archimedean_Field.floor_ceiling_class.floor
import_const_map int_add : Groups.plus_class.plus
import_const_map int_mul : Groups.times_class.times
import_const_map int_neg : Groups.uminus_class.uminus
import_const_map int_of_num : Nat.semiring_1_class.of_nat
import_const_map int_sub : Groups.minus_class.minus
import_const_map int_abs : Groups.abs_class.abs
import_const_map int_max : Orderings.ord_class.max
import_const_map int_min : Orderings.ord_class.min
import_const_map int_sgn : Groups.sgn_class.sgn
import_const_map int_le : Orderings.ord_class.less_eq
import_const_map int_lt : Orderings.ord_class.less
import_const_map int_ge : HOL_Light_Maps.int_ge
import_const_map int_gt : HOL_Light_Maps.int_gt
import_const_map int_pow : Power.power_class.power
import_const_map integer : HOL_Light_Maps.integer


lemmas [import_rewrite] = real_gt real_ge

end

