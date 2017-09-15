theory P07
imports Main 
begin 


datatype 'a NestedList  =  Elem 'a | List "('a NestedList) list"

fun p07_1 :: "'a NestedList \<Rightarrow> 'a list" where
"p07_1 (Elem val) =  [val]"|
"p07_1 (List ls) = concat (map p07_1 ls)"


lemma ""