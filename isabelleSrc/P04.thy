theory P04 
imports Main 
begin 


primrec p04_1 :: "'a list \<Rightarrow> int" where 
"p04_1 [] = 0"|
"p04_1 (x#xs) = 1 + p04_1 xs"


value "p04_1[1,2,3,4,5]"

value "p04_1 []"

lemma "p04_1 [] = 0" by simp
    
lemma "p04_1 ls = int (length ls)"
proof (induct ls)
  case Nil 
  show ?case by simp
 next 
  fix a ls 
  case (Cons a ls)
  assume " p04_1 ls = int (length ls)"
  thus " p04_1 (a # ls) = int (length (a # ls))" by simp
qed
  
lemma "p04_1 (ls @ xs) = p04_1 ls + p04_1 xs" 
apply (induction ls  arbitrary : xs)
apply auto
done 

lemma " p04_1 ls + 1 = p04_1 (h#ls)" by simp
    
lemma "int(card (set ls)) \<le> p04_1 ls" 
proof (induct ls)
  case Nil
  then show ?case by simp
next
  case (Cons a ls)
  assume a:"int (card (set ls)) \<le> p04_1 ls"
  show ?case 
  proof (cases "a \<in> set ls")
    case True
    assume "a \<in> set ls"
    with a show ?thesis 
      
  next
    case False
    then show ?thesis sorry
  qed
qed
  