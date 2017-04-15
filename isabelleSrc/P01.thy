theory P01 
imports Main 
begin

(*using a default value*)
fun p01_1 ::  "'a list \<Rightarrow> 'a \<Rightarrow> 'a" where 
"p01_1 [] def = def"|
"p01_1 [x] _ = x"|
"p01_1 (x#xs) def = p01_1 xs def" 

(*evaluate an expression*)
value "p01_1 [1,2,3,4] 5 :: int" 
value "p01_1 [] 5 :: int"

(*show the type of an expression*)
term p01_1

(*show the definition of a theorem*)
thm p01_1.simps(1)

theorem tp01_1 : "p01_1 [] a = a"
apply (rule p01_1.simps(1)) 
done 

theorem isar_tp01_1 :"p01_1 [] a = a"
proof - 
  show ?thesis by (rule p01_1.simps(1))
qed 

theorem tp01_2 : "p01_1 ( ls @ [a]) b = a "
apply (induct "ls")
apply simp
apply (cases "ls @ [a]")
apply auto



fun p01_2 :: "'a list \<Rightarrow> 'a option" where
"p01_2 [] = None"|
"p01_2 [x] = Some x"|
"p01_2 (x#xs) = p01_2 xs"

  