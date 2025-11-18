theory ACh_equality

imports Main "First_Order_Terms.Term" "Experiments"

begin

context signature

begin

fun app_fun :: "'f \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term" where
  "app_fun f t = Fun f [t]"

fun unordered_pred_all :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> bool" where
  "unordered_pred_all P xs ys = (case xs of
                             [] \<Rightarrow> True |
                             x # xs' \<Rightarrow> let t = find (P x) ys in
                                       (case t of 
                                        None \<Rightarrow> False |
                                        Some _ \<Rightarrow> unordered_pred_all P xs' ys
                                                 )
                                        )"

fun equal :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" where
 "equal t1 t2 = (case (t1, t2) of  
                 (Var x, Var y) \<Rightarrow> x=y |
                 (Var x, Fun _ _) \<Rightarrow> False |
                 (Fun _ _, Var y) \<Rightarrow> False | 
                 (Fun f ts, Fun g ss) \<Rightarrow> (if (label f = Hom \<and> label g = AC \<and> (length ts) = 1) 
                                          then
                                            let s = hd ts in
                                              (case s of 
                                               Fun g xs \<Rightarrow> if length xs = length ss
                                                then
                                                  (let ys = map (app_fun g) xs in
                                                    unordered_pred_all equal ss ys)
                                                else
                                                  False)
                                          else
                                            False)
                  )"


end


end