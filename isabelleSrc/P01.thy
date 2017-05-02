theory P01 
imports Main 
begin


(*
useful commands
using [[simp_trace]] shows the used rewrite rules and what has been rewritten in the output tab
using [[simp_trace_new]] only shows the rewrites in a new window
using [[simp_trace_new mode=full]] shows the used rewrite rules and what has been rewritten
simp only: <rule name> only uses one simplification rule and some trivial simplifications
subst really only uses one simplification rule
*)


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
thm append_Nil

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
apply (case_tac "ls @ [a]")
apply simp
apply simp
done


(*step by step rewriting*)
theorem tp01_4 : "p01_1 (ls @ [a]) b = a"
apply (induct "ls")
  apply (subst append.append_Nil)
  apply (subst p01_1.simps(2))
  apply (rule refl)
apply (case_tac ls)
(*case ls = []*)
  apply (erule_tac ?t = ls and ?s = "[]" in  ssubst)
  apply (subst append.append_Cons)
  apply (subst append.append_Nil)
  apply (subst  p01_1.simps(3))
  apply (subst p01_1.simps(2))
  apply (rule refl)
(*case ls = aaa # list*)
  apply (rule_tac ?t = ls and ?s = "aaa # list" in ssubst)
  apply assumption
  apply (rule_tac ?t = ls and ?s = "aaa # list" in ssubst)
  apply assumption
  apply (subst  append.append_Cons)+ (*the "+" means that we apply the same rule as often as possible*)
  apply (subst p01_1.simps(3))
  apply hypsubst
  apply (subst (asm) append.append_Cons)
  apply (assumption)
done
 


(*isar proof using automation*)
theorem isar_tp01_2 : "p01_1 ( ls @ [a]) b = a "
proof (induction ls)
{
  show " p01_1 ([] @ [a]) b = a" by simp
}
{
  fix aa ls
  show " p01_1 (ls @ [a]) b = a \<Longrightarrow> p01_1 ((aa # ls) @ [a]) b = a " 
  proof (cases ls)
  {
    show " p01_1 (ls @ [a]) b = a \<Longrightarrow> ls = [] \<Longrightarrow> p01_1 ((aa # ls) @ [a]) b = a" by simp
    fix ab list
    show "p01_1 (ls @ [a]) b = a \<Longrightarrow> ls = ab # list \<Longrightarrow> p01_1 ((aa # ls) @ [a]) b = a " by simp
  }
  qed
}
qed




(*step by step syntactical replacement with Isar*)
theorem isar_tp01_3 : fixes ls a b  shows "p01_1 ( ls @ [a]) b = a " 
proof (induct ls)
 case Nil
  have "p01_1 ([] @ [a]) b =  p01_1 [a] b" unfolding append_Nil ..  (*instead of   the two dots ".." one could write "by (rule refl)" *)(*instead of unfolding \<rightarrow> "by (subst append_Nil[where ?ys = "[a]"]; rule refl)" *)
  also have "\<dots> = a" unfolding p01_1.simps(2) ..
  finally show "p01_1 ([] @ [a]) b = a" . 
next
 case (Cons  aa ls)
  show " p01_1 (ls @ [a]) b = a \<Longrightarrow>  p01_1 ((aa # ls) @ [a]) b = a "
  proof (cases ls)
   case Nil
    assume "ls = []" 
    assume "p01_1 (ls @ [a]) b = a"
    have " p01_1 ((aa # ls) @ [a]) b =  p01_1 (aa # ls @ [a]) b " unfolding append_Cons ..
    also have "\<dots> = p01_1 (aa # [] @ [a]) b" unfolding \<open>ls = []\<close> ..
    also have "\<dots> = p01_1 (aa # [a]) b" unfolding append_Nil ..
    also have "\<dots> = p01_1 [a] b" unfolding p01_1.simps(3) ..
    also have "\<dots> = a" unfolding p01_1.simps(2)  ..
    finally show "p01_1 ((aa # ls) @ [a]) b = a" . 
  next  
   case (Cons ab list)
    fix ab list 
    assume IH:"p01_1 (ls @ [a]) b = a"
    assume "ls = ab # list"

    from  \<open>ls= ab # list\<close> and  IH have "p01_1 ((ab # list) @ [a]) b = a"  by (rule subst)
    with append_Cons have  "p01_1 (ab # list @ [a]) b = a" by (rule subst)
    note IH2 = this

    have  "p01_1 ((aa # ls) @ [a]) b = p01_1 ((aa # ab # list)@ [a]) b" unfolding \<open>ls = ab # list\<close> ..
    also have "\<dots> =  p01_1 (aa # (ab # list)@ [a]) b " unfolding append_Cons ..
    also have "\<dots> =  p01_1 (aa # ab # list@ [a]) b" unfolding append_Cons ..
    also have "\<dots> = p01_1 (ab # list @ [a]) b " unfolding p01_1.simps(3) ..
    also have "\<dots> = a " unfolding IH2 ..
    finally show " p01_1 ((aa # ls) @ [a]) b = a" .
  qed
qed


(*on other way to proof this (less readable but probably easier to understand)*)
theorem isar_tp01_4 : fixes ls a b  shows "p01_1 ( ls @ [a]) b = a " 
using [[simp_trace_new mode=full]]
proof (induct ls)
{
  show "p01_1 ([] @ [a]) b = a"
  proof (subst append_Nil)
  {
    show " p01_1 [a] b = a"
    proof (subst p01_1.simps(2))
    {
      show "a = a" by (rule refl)
    }
    qed
  }
  qed
  fix aa ls
  assume "p01_1 (ls @ [a]) b = a"
  show " p01_1 ((aa # ls) @ [a]) b = a "
  proof (cases ls)
  {
    assume "ls = []"
    show "p01_1 ((aa # ls) @ [a]) b = a"
    proof (subst \<open>ls=[]\<close>)
    {
      show "p01_1 ([aa] @ [a]) b = a"
      proof (subst append_Cons)
      {
        show "p01_1 (aa # [] @ [a]) b = a"
        proof (subst append_Nil)
        {
          show " p01_1 [aa, a] b = a"
          proof (subst p01_1.simps(3))
          {
            show "p01_1 [a] b = a" 
            proof (subst p01_1.simps(2))
            {
              show "a = a" by (rule refl)
            }
            qed
          }
          qed
        }
        qed
      }
      qed
    }
    qed
  }
  fix ab list
  assume "ls = ab # list"
  from this and  \<open>p01_1 (ls @ [a]) b = a\<close> have "p01_1 ((ab # list) @ [a]) b = a" by (rule subst) 
  with append_Cons have "p01_1 (ab # list @ [a]) b = a" by (rule subst)
  show "p01_1 ((aa # ls) @ [a]) b = a" 
  proof (subst \<open>ls = ab # list\<close>)
  {
    show " p01_1 ((aa # ab # list) @ [a]) b = a "
    proof (subst  append_Cons)
    {
      show "p01_1 (aa # (ab # list) @ [a]) b = a "
      proof (subst append_Cons )
      {
        show "p01_1 (aa # ab # list @ [a]) b = a "
        proof (subst p01_1.simps(3))
        {
          show "p01_1 (ab # list @ [a]) b = a " by (rule \<open>p01_1 (ab # list @ [a]) b = a\<close>)
        }
        qed
      }
      qed
    }
    qed
  }
  qed
  qed
}
qed



(*
oops

theorem  isar_tp01_3 :  shows "p01_1 ( ls @ [a]) b = a " 
proof (induct ls)
{
  show "p01_1 ([] @ [a]) b = a"
  proof (subst append_Nil)
  {
    show "p01_1 [a] b = a "
    proof 
oops
fun p01_2 :: "'a list \<Rightarrow> 'a option" where
"p01_2 [] = None"|
"p01_2 [x] = Some x"|
"p01_2 (x#xs) = p01_2 xs"
*)

(*
  proof (subst (asm) "List.append_is_Nil_conv"  )
  {
    show " ls = [] \<and> [a] = [] \<Longrightarrow> p01_1 (aa # ls @ [a]) b = a"
    proof (subst (asm) "List.not_Cons_self2" )
    {
      show "ls = [] \<and> False \<Longrightarrow> p01_1 (aa # ls @ [a]) b = a "
      proof (subst  (asm) HOL.simp_thms(23))
      {
         show "False \<Longrightarrow> p01_1 (aa # ls @ [a]) b = a" by (rule FalseE)
       
      }
      qed
    }   
    qed
  }
  qed
*)