theory P09
  imports Main 
begin 


function  p09_1  :: "'a list \<Rightarrow> ('a list) list" where
"p09_1 [] = []"|
"p09_1 (a#xs) = (a #takeWhile (op = a) xs )# p09_1 (dropWhile (op = a) xs)"  by pat_completeness auto 
termination 
  apply (relation "measure (\<lambda> ls . length ls)")
   apply simp
  apply auto
  apply (induct_tac xs)
   apply simp
  apply auto
  done




lemma "(p09_1 [1,2,3::nat]) = [[1],[2],[3::nat]]" by simp

lemma "p09_1 [1,2,1,1,3,2,2,5,5,5::nat] = [[1],[2],[1,1],[3],[2,2],[5,5,5]] " by simp

lemma helper:"length (dropWhile (op = a) xs) \<le> length xs" 
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons aa xs)
  then show ?case by (cases "a = aa" ; auto)
qed


theorem "length (p09_1 ls) \<le> length ls"
proof (induction ls rule : p09_1.induct)
  case 1
  then show ?case by simp
next
  case (2 a xs)
  then show ?case using helper[of a xs] by simp
qed



theorem "ls =  concat (p09_1 ls)" 
proof (induction ls rule : p09_1.induct)
  case 1
  then show ?case by simp
next
  case (2 a xs)
  assume hyp:"dropWhile (op = a) xs = concat (p09_1 (dropWhile (op = a) xs))"
  from hyp show ?case by simp
qed

lemma helper2:"i \<in> set (takeWhile (op = a) xs) \<Longrightarrow> i = a" 
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons aa xs)
  then show ?case by (cases "a = aa"; auto)
qed



theorem "i \<in> set (p09_1 ls) \<Longrightarrow> (\<forall>x y . x \<in> set i \<and> y \<in> set i \<longrightarrow> x = y)" 
proof (induction ls rule : p09_1.induct)
  case 1
  then show ?case by simp
next
  case (2 a xs)
  let ?tmp = "takeWhile (op = a) xs"
  let ?tmp2 = "dropWhile (op = a) xs"
  have "(i \<in> set (p09_1 (a # xs))) = (i \<in> set  ((a # ?tmp) # p09_1 ?tmp2))" by simp
  also have "\<dots> = ((i \<in> set ([a#?tmp])) \<or> (i \<in> set (p09_1 ?tmp2)))" by simp
  finally have tmp:"(i \<in> set (p09_1 (a # xs))) = (i \<in> set [a # ?tmp] \<or> i \<in> set (p09_1 ?tmp2)) " by simp
  show ?case
  proof (cases "i \<in> set ([a#?tmp])")
    case True
    then show ?thesis using helper2[of _ a _] by auto
  next
    case False
    with 2(2) tmp have tmp2:"i \<in> set (p09_1 ?tmp2)" by simp
    with 2(1) show ?thesis by simp
  qed
qed


theorem "length ls = sum_list (map length (p09_1 ls))" 
proof (induction ls rule : p09_1.induct)
  case 1
  then show ?case by simp
next
  case (2 a xs)
  let ?tmp="takeWhile (op = a) xs"
  let ?tmp2="dropWhile (op = a) xs"
  have "sum_list (map length (p09_1 (a # xs))) = sum_list (length (a#?tmp) # map length (p09_1  ?tmp2))" by simp
  also have "\<dots> = length (a#?tmp) + sum_list (map length (p09_1 ?tmp2))" by simp
  also have "\<dots> = 1 + length (?tmp) + length (dropWhile (op = a) xs)" using 2 by simp
  also have "\<dots> = 1 + length xs" using takeWhile_dropWhile_id[of "op = a" xs] length_append[symmetric , of ?tmp ?tmp2] by simp
  finally show ?case by simp
qed

