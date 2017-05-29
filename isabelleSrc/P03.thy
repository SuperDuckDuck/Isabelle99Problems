theory P03
imports Main 
begin 



fun p03_1 :: "'a list \<Rightarrow> nat \<Rightarrow> 'a option" where
"p03_1 [] _ = None"|
"p03_1 (x#xs) n = (case n of  0 \<Rightarrow> None| (Suc 0) \<Rightarrow> Some x | _ \<Rightarrow>  p03_1 xs (n - 1))"

value "p03_1 [1,2 ,3,4] 4 :: int option"

value "p03_1 [] 4"

value "p03_1 [1,2,3,4] 0"


lemma "p03_1 ls n "


