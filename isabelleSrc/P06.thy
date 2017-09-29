theory P06
imports Main
begin 

definition  p06_1  :: "'a list \<Rightarrow> bool"where
"p06_1 ls = (ls = rev ls)"

declare p06_1_def [simp]

corollary "p06_1 [1,2,1]" by simp

corollary "p06_1 []" by simp

corollary "p06_1 [1]" by simp
(*
value "p06_1 ([1,2,3,4,5] :: int list) "

value "p06_1 ([1,2,3,4,4,3,2,1]::int list)"

lemma "p06_1 [] = True" by simp

lemma "p06_1 [x] = True" by simp
*)
corollary "p06_1 [1,2,3,4,(5::int)] = False" by simp    
    
theorem "p06_1 []" by simp
    
theorem "p06_1 [x]" by simp
  
theorem "p06_1  (ls @ rev ls)"  by simp
    
theorem "p06_1 (ls @ [val] @ rev ls)" by simp
    
theorem "ls = rev ls \<Longrightarrow>  p06_1 ls" by simp
    
theorem "ls \<noteq> rev ls \<Longrightarrow> p06_1 ls = False" by simp
  
(*lemma "let len = length ls in if odd len then  else "*) 


definition  p06_2 :: "'a list \<Rightarrow> bool" where
"p06_2 ls =  (let len = length ls; firstHalf = take (len div 2) ls ; secondHalf =rev (drop (len div 2) ls) in 
  if odd len then firstHalf = butlast secondHalf  else firstHalf = secondHalf) "

declare p06_2_def [simp]

(*
value "p06_2 []"

value "p06_2 [1]"

value "p06_2 [1,1]"

value "p06_2 [(1::int),2]"

value "p06_2 [(1::int),2,1]"

value "p06_2 [1,2,2,1]"

value "p06_2 [(1::int),2,3,3,1]"

value "p06_2 [(1::int),2,3,4,1]"


*)
  
corollary "p06_2 [1,2,3,4,(5::int)] = False" by simp
  
theorem "p06_2 []" by simp
    
theorem "p06_2 [1]" by simp
    
theorem "p06_2 (ls @ rev ls)" by simp
    
theorem "p06_2 (ls @ [val] @ rev ls)" by simp   
    
    
lemma helper3: "even (length ls) \<Longrightarrow> length (drop (length ls div 2) ls) = length ls div 2"
proof (induction ls)
  case Nil
  then show ?case by simp
next
  case (Cons a ls)
  assume hyp1:"even (length ls) \<Longrightarrow> length (drop (length ls div 2) ls) = length ls div 2" 
    and hyp2:" even (length (a # ls))"
  then show ?case  
  proof (cases ls)
    case Nil
    then show ?thesis using hyp by simp
  next
    case (Cons aa list)
    then show ?thesis 
  qed
    
qed
  
  
  
  (*
lemma helper4:"ls = rev ls \<Longrightarrow>  even (length ls) \<Longrightarrow> take (length ls div 2) ls =  (rev (drop (length ls div 2) ls))"      
proof (induction ls)
  case Nil
  then show ?case by simp
next
  case (Cons a ls)
  let ?tmp = "take (length (a # ls) div 2) (a # ls)"
  let ?tmp2 = "drop (length (a # ls) div 2) (a # ls)"
  assume hyp1:"ls = rev ls \<Longrightarrow> even (length ls) \<Longrightarrow> take (length ls div 2) ls = rev (drop (length ls div 2) ls)"
    and hyp2:"a # ls = rev (a # ls)"
    and hyp3:" even (length (a # ls))"
  have tmp1:"a # ls = ?tmp @ ?tmp2" by simp
  then have tmp2:"rev (a # ls) = rev (?tmp @ ?tmp2)" by simp
  with tmp1 hyp2 have "?tmp @ ?tmp2 = rev (?tmp @ ?tmp2)" by simp
  have tmp3:"length ?tmp = length (a #ls) div 2" by simp
  from hyp3 tmp3 have tmp4:"length ?tmp2  = length (a #ls) div 2" 
    
      have "length ?tmp = length ?tmp2" using 
  then show ?case 
qed
  
    
theorem "ls = rev ls \<Longrightarrow>  p06_2 ls" 
proof (induction ls)
  case Nil
  then show ?case by simp
next
  case (Cons a ls)
  assume hyp1:"ls = rev ls \<Longrightarrow> p06_2 ls"
    and hyp2:"a # ls = rev (a # ls)"
  then show  "p06_2 (a # ls)"
  proof (cases "odd (length ls)")
    case True
    assume "odd (length ls)"
    hence "even (length (a # ls))" by simp
        
    have "p06_2 (a # ls) = 
  (let len = length ls; firstHalf = take (len div 2) ls ; secondHalf =rev (drop (len div 2) ls) in 
  if odd len then firstHalf = butlast secondHalf  else firstHalf = secondHalf) "
        
    show "p06_2 (a # ls)"
  next
    case False
    then show ?thesis sorry
  qed
    
qed
*)  
     
theorem "ls \<noteq> rev ls \<Longrightarrow> p06_2 ls = False" by simp  
(*
lemma "p06_1 ls = p06_2 ls"
proof (induct ls)
  case Nil 
  show ?case by simp
 next 
  fix a ls 
  case (Cons a ls)
  assume a:"p06_1 ls = p06_2 ls"
  show " p06_1 (a # ls) = p06_2 (a # ls) "
  proof (cases  ls)
    show "ls = [] \<Longrightarrow> p06_1 (a # ls) = p06_2 (a # ls)" by  simp
   next
    fix aa list
    assume b:"ls = aa # list"
    show "p06_1 (a # ls) = p06_2 (a # ls)" 
    proof (rule case_split[where ?P = "even (length ls)"])
      assume "even (length ls)"
      "p06_1 (a # ls) = p06_2 (a # ls)" 
*)

(*lemma evenlist_plus_one_is_odd [simp] : "even (length ls) \<Longrightarrow> odd (length (x # ls)) " by simp*)


lemma "p06_1 ls = p06_2 ls" 
proof -
  let ?len="length ls"
  let ?half= "length ls div 2"
  let ?fh =  "take ?half ls"   
  let ?sh = "drop ?half ls"
  
  
  (*
proof (rule case_split[where ?P = "even (length ls)"])
  assume a:"even (length ls)"
  show " p06_1 ls = p06_2 ls"
  proof (induction ls)
    case Nil
    show ?case by simp 
   next   
    fix a ls 
    case (Cons a ls)
    assume b:"p06_1 ls = p06_2 ls"
    show "p06_1 (a # ls) = p06_2 (a # ls)"
    *)

    

    
     
     
  