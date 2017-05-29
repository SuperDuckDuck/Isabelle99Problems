theory P05 
imports Main 
begin 


primrec p05_1 :: "'a list \<Rightarrow> 'a list" where 
"p05_1 [] = []"|
"p05_1 (x#xs) = p05_1 xs @ [x]"


value "p05_1 [1,2,3,4] :: int list"


lemma [simp] : "p05_1 (ls @ [b]) = b # p05_1 ls " 
apply (induct ls)
apply auto
done 

lemma "p05_1 (p05_1 xs)  = xs" 
proof (induct xs)
  case Nil 
  show ?case by simp
 next 
  fix a xs ls b
  case (Cons a xs)
  assume "p05_1 (p05_1 xs) = xs"
  thus "p05_1 (p05_1 (a # xs)) = a # xs " by simp
qed

lemma "p05_1 ls = rev ls"
apply (induct ls)
apply simp_all
done

 
