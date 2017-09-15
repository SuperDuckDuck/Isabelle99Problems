theory P06
imports Main
begin 

definition  p06_1  :: "'a list \<Rightarrow> bool"where
"p06_1 ls = (ls = rev ls)"

declare p06_1_def [simp]
(*
value "p06_1 [1,2,1]"

value "p06_1 []"

value "p06_1 [1]"

value "p06_1 ([1,2,3,4,5] :: int list) "

value "p06_1 ([1,2,3,4,4,3,2,1]::int list)"

lemma "p06_1 [] = True" by simp

lemma "p06_1 [x] = True" by simp
*)
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

find_theorems "(?P  \<Longrightarrow> ?R) \<Longrightarrow> (\<not>?P  \<Longrightarrow> ?R) \<Longrightarrow> ?R  "

*)
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
    

    

    
     
     
  