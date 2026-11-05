module

meta import Lean.Elab.Tactic
import Batteries.Data.String.Lemmas
import Init.Data.List.SplitOn.Lemmas
import all Init.Data.List.SplitOn.Basic
import all Init.Data.String.Legacy
import all Init.Data.String.Search
import all Init.Data.String.Slice

/-! String identities for source-relation certificates. -/

set_option backward.privateInPublic true
set_option maxRecDepth 100000

@[expose] section
namespace KIP126.Computation.Standard

private theorem nativeCoreSplitOnAuxChar (s : String) (c : Char) (b i : String.Pos.Raw)
    (acc : List String) :
    s.splitOnAux (String.singleton c) b i 0 acc = s.splitAux (· == c) b i acc := by
  have hg : String.Pos.Raw.get (String.singleton c) 0 = c := by
    simp only [String.Pos.Raw.get, String.toList_singleton, String.Pos.Raw.utf8GetAux,
      ↓reduceIte]
  have hn : String.Pos.Raw.next (String.singleton c) 0 = ⟨c.utf8Size⟩ := by
    simp [String.Pos.Raw.next, hg, String.Pos.Raw.ext_iff]
  have he : String.Pos.Raw.atEnd (String.singleton c) ⟨c.utf8Size⟩ = true := by
    simp [String.Pos.Raw.atEnd]
  fun_induction String.splitAux s (· == c) b i acc with
  | case1 b i acc h => rw [String.splitOnAux, if_pos h]
  | case2 b i acc h _ h' i' ih =>
    have hi : String.Pos.Raw.get s i = c := by simpa using h'
    have hu : (String.Pos.Raw.next s i).unoffsetBy ⟨c.utf8Size⟩ = i := by
      apply String.Pos.Raw.ext
      change (i.byteIdx+(String.Pos.Raw.get s i).utf8Size)-c.utf8Size=i.byteIdx
      rw [hi]
      exact Nat.add_sub_cancel _ _
    rw [String.splitOnAux, if_neg h, hg, if_pos h', hn, if_pos he, hu]
    exact ih
  | case3 b i acc h _ h' ih =>
    have hu : i.unoffsetBy 0 = i := String.Pos.Raw.unoffsetBy_zero
    rw [String.splitOnAux, if_neg h, hg, if_neg h', hu]
    exact ih
private theorem nativeCoreSplitOnChar (s : String) (c : Char) :
    s.splitOn (String.singleton c) = (s.toList.splitOn c).map String.ofList := by
  have hc : (String.singleton c == "") = false := by simp
  rw [String.splitOn, hc, if_neg Bool.false_ne_true, nativeCoreSplitOnAuxChar]
  change String.splitToList s (· == c) = _
  rw [String.splitToList_of_valid, List.splitOn_eq_splitOnP]
private theorem nativeCoreMiddleMember (s code : String) (a c b : List Char)
    (hs : s=String.ofList (a++'\n'::(c++'\n'::b)))
    (hc : String.ofList c=code) (hn : '\n'∉c) : code∈s.splitOn "\n" := by
  rw [hs,show "\n"=String.singleton '\n' from rfl,nativeCoreSplitOnChar,String.toList_ofList,
    List.splitOn_append_cons_self,List.splitOn_append_cons_self_of_not_mem hn]
  apply List.mem_map.mpr
  exact ⟨c,List.mem_append.mpr (Or.inr (List.mem_cons_self)),hc⟩

end KIP126.Computation.Standard
