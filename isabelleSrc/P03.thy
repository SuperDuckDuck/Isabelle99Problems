theory P03
imports Main 
begin 



fun p03_1 :: "'a list \<Rightarrow> nat \<Rightarrow> 'a option" where
"p03_1 [] _ = None"|
"p03_1 (x#xs) n = (if n = 1 then Some x else  p03_1 xs (n - 1))"

value "p03_1 [1,2 ,3,4] 3 :: int option"