theory P02
imports Main 
begin 
(*from now on I will mix isar and apply-script proofs and I will also mix step-by-step solving with automation*)
(*find the last but one element of a list*)


(*using a default element in case the list is too small*)
fun p02_1 :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a" where
"p02_1 [] def = def"|
"p02_1 (x#xs) def = (case xs of  [y] \<Rightarrow> x | _  \<Rightarrow>  p02_1 xs def) "


value "p02_1 [] 5 :: int"
value "p02_1 [1] 7 :: int"
value "p02_1 [1,2,3,4,5] 6 :: int"


theorem tp02_1_1 : "p02_1 [] a = a" by auto

theorem tp02_1_2 : "p02_1 [] a = a"
using [[simp_trace_new mode=full]]
apply (subst p02_1.simps)
apply (rule refl)
done 

theorem isar_tp02_1_1 : "p02_1 [x] a = a" 
proof - 
have 