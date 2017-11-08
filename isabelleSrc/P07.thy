theory P07
imports Main 
begin 


datatype 'a NestedList  =  Elem 'a | List "('a NestedList) list"

fun p07_1 :: "'a NestedList \<Rightarrow> 'a list" where
"p07_1 (Elem val) =  [val]"|
"p07_1 (List ls) = concat (map p07_1 ls)"


lemma "p07_1 (Elem (5::nat)) = [5]" by simp
    
lemma "p07_1 (List [List [List [Elem (4::nat), Elem 5 , Elem 6] , List [Elem 3]  , Elem 1] , Elem 7 , List [Elem 8]])
      = [4,5,6,3,1,7,8]" by simp

theorem "p07_1 "