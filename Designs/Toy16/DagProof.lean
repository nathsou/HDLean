import Designs.Toy16.DagHardware

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace HDLean.Dag.Build.Word

theorem literal_ensures (s : State d i r) (v : BitVec w) :
    Ensures s (literal v) (fun js t => WordRefines t js (WordExpr.literal v)) := by
  simp only [literal, WordRefines, Fin.getElem_fin, WordExpr.literal, Vector.getElem_ofFn, Vector.getElem_zipWith, Vector.getElem_map]
  apply tabulate_ensures _ (fun k j t => Refines t j (.lit (v.getLsbD k.val)))
    (fun _ _ _ _ he h => h.mono he) s
  intro t _ k
  exact Build.literal_ensures t _

theorem registers_ensures (s : State d i r) (off : Nat) (h : off+w ≤ r) :
    Ensures s (registers off h) (fun js t => WordRefines t js (WordExpr.registers off h)) := by
  simp only [registers, WordRefines, Fin.getElem_fin, WordExpr.registers, Vector.getElem_ofFn, Vector.getElem_zipWith, Vector.getElem_map]
  apply tabulate_ensures _ (fun k j t => Refines t j (.reg ⟨off+k.val,by omega⟩))
    (fun _ _ _ _ he h => h.mono he) s
  intro t _ k
  exact Build.reg_ensures t _

theorem mux_ensures (hc : Refines s c ec) (ha : WordRefines s a ea) (hb : WordRefines s b eb) :
    Ensures s (mux c a b) (fun js t => WordRefines t js (WordExpr.mux ec ea eb)) := by
  simp only [mux, WordRefines, Fin.getElem_fin, WordExpr.mux, Vector.getElem_ofFn, Vector.getElem_zipWith, Vector.getElem_map]
  apply tabulate_ensures _ (fun k j t => Refines t j (.mux ec ea[k] eb[k]))
    (fun _ _ _ _ he h => h.mono he) s
  intro t he k
  exact Build.mux_ensures (hc.mono he) ((ha k).mono he) ((hb k).mono he)

theorem bitAnd_ensures (ha : WordRefines s a ea) (hb : WordRefines s b eb) :
    Ensures s (bitAnd a b) (fun js t => WordRefines t js (WordExpr.bitAnd ea eb)) := by
  simp only [bitAnd, WordRefines, Fin.getElem_fin, WordExpr.bitAnd, Vector.getElem_ofFn, Vector.getElem_zipWith, Vector.getElem_map]
  apply tabulate_ensures _ (fun k j t => Refines t j (.and ea[k] eb[k]))
    (fun _ _ _ _ he h => h.mono he) s
  intro t he k
  exact Build.and_ensures ((ha k).mono he) ((hb k).mono he)

theorem bitOr_ensures (ha : WordRefines s a ea) (hb : WordRefines s b eb) :
    Ensures s (bitOr a b) (fun js t => WordRefines t js (WordExpr.bitOr ea eb)) := by
  simp only [bitOr, WordRefines, Fin.getElem_fin, WordExpr.bitOr, Vector.getElem_ofFn, Vector.getElem_zipWith, Vector.getElem_map]
  apply tabulate_ensures _ (fun k j t => Refines t j (ea[k].or eb[k]))
    (fun _ _ _ _ he h => h.mono he) s
  intro t he k
  exact Build.or_ensures ((ha k).mono he) ((hb k).mono he)

theorem bitXor_ensures (ha : WordRefines s a ea) (hb : WordRefines s b eb) :
    Ensures s (bitXor a b) (fun js t => WordRefines t js (WordExpr.bitXor ea eb)) := by
  simp only [bitXor, WordRefines, Fin.getElem_fin, WordExpr.bitXor, Vector.getElem_ofFn, Vector.getElem_zipWith, Vector.getElem_map]
  apply tabulate_ensures _ (fun k j t => Refines t j (.xor ea[k] eb[k]))
    (fun _ _ _ _ he h => h.mono he) s
  intro t he k
  exact Build.xor_ensures ((ha k).mono he) ((hb k).mono he)

theorem bitNot_ensures (ha : WordRefines s a ea) :
    Ensures s (bitNot a) (fun js t => WordRefines t js (WordExpr.bitNot ea)) := by
  simp only [bitNot, WordRefines, Fin.getElem_fin, WordExpr.bitNot, Vector.getElem_ofFn, Vector.getElem_zipWith, Vector.getElem_map]
  apply tabulate_ensures _ (fun k j t => Refines t j (.inv ea[k]))
    (fun _ _ _ _ he h => h.mono he) s
  intro t he k
  exact Build.inv_ensures ((ha k).mono he)

theorem extract_refines {a : Word w} {ea : WordExpr d i r w} (ha : WordRefines s a ea) (off len : Nat) (h : off+len ≤ w) :
    WordRefines s (extract (w := w) a off len h) (WordExpr.extract ea off len h) := by
  intro k
  simpa only [extract,WordExpr.extract,Fin.getElem_fin,Vector.getElem_ofFn] using ha ⟨off+k.val,by omega⟩

theorem setWidth_refines (hz : Refines s z (.lit false)) (ha : WordRefines s a ea) (size : Nat) :
    WordRefines s (setWidth z a size) (WordExpr.setWidth ea size) := by
  intro k
  simp only [Fin.getElem_fin,setWidth,WordExpr.setWidth,Vector.getElem_ofFn]
  split
  · exact ha ⟨k.val,by assumption⟩
  · exact hz

theorem signExtend_refines {a : Word w} {ea : WordExpr d i r w} (hz : Refines s z (.lit false)) (ha : WordRefines s a ea) (size : Nat) :
    WordRefines s (signExtend z a size) (WordExpr.signExtend ea size) := by
  intro k
  simp only [Fin.getElem_fin,signExtend,WordExpr.signExtend,Vector.getElem_ofFn]
  split
  · exact ha ⟨k.val,by assumption⟩
  · split
    · exact ha ⟨w-1,by omega⟩
    · exact hz

def sumPrefix (a b : WordExpr d i r w) (carry : Expr d i r) (n : Nat) (hn : n ≤ w) : WordExpr d i r n :=
  Vector.ofFn fun k => .xor (.xor a[k.val] b[k.val]) (WordExpr.carryAt a b carry k.val)

theorem addAux_ensures {a b : Word w} {ea eb : WordExpr d i r w}
    (ha : WordRefines s a ea) (hb : WordRefines s b eb) (hc : Refines s carry ec)
    (n : Nat) (hn : n ≤ w) :
    Ensures s (addAux a b carry n hn) (fun p t =>
      WordRefines t p.1 (sumPrefix ea eb ec n hn) ∧ Refines t p.2 (WordExpr.carryAt ea eb ec n)) := by
  induction n generalizing s with
  | zero =>
    apply ensures_pure
    exact ⟨fun k => Fin.elim0 k,hc⟩
  | succ n ih =>
    apply ensures_bind (ih ha hb hc (by omega))
    intro p t he hp
    obtain ⟨hbits,hcarry⟩ := hp
    have hn' : n < w := by omega
    have han := (ha ⟨n,hn'⟩).mono he
    have hbn := (hb ⟨n,hn'⟩).mono he
    apply ensures_bind (Build.xor_ensures han hbn)
    intro x u he1 hx
    apply ensures_bind (Build.xor_ensures hx (hcarry.mono he1))
    intro sum v he2 hsum
    apply ensures_bind (Build.and_ensures ((han.mono he1).mono he2) ((hbn.mono he1).mono he2))
    intro ab v1 he3 hab
    apply ensures_bind (Build.and_ensures ((hx.mono he2).mono he3) (((hcarry.mono he1).mono he2).mono he3))
    intro xc v2 he4 hxc
    apply ensures_bind (Build.or_ensures (hab.mono he4) hxc)
    intro next v3 he5 hnext
    apply ensures_pure
    refine ⟨?_,?_⟩
    · have old := ((((hbits.mono he1).mono he2).mono he3).mono he4).mono he5
      have newest := ((hsum.mono he3).mono he4).mono he5
      intro k
      simp only [sumPrefix,Fin.getElem_fin,Vector.getElem_ofFn]
      by_cases hk : k.val < n
      · simpa only [Fin.getElem_fin,Vector.getElem_push, hk, ↓reduceDIte,
          sumPrefix,Vector.getElem_ofFn] using old ⟨k.val,hk⟩
      · have heq : k.val = n := by have := k.isLt; omega
        simpa only [heq,Vector.getElem_push,Nat.lt_irrefl,↓reduceDIte,Fin.getElem_fin] using newest
    · simpa only [WordExpr.carryAt,hn',↓reduceDIte,Fin.getElem_fin] using hnext

theorem add_ensures {a b : Word w} {ea eb : WordExpr d i r w}
    (hz : Refines s z (.lit false)) (ha : WordRefines s a ea) (hb : WordRefines s b eb) :
    Ensures s (add z a b) (fun js t => WordRefines t js (WordExpr.add ea eb)) := by
  apply ensures_bind (addAux_ensures ha hb hz w (Nat.le_refl w))
  intro p t he hp
  apply ensures_pure
  exact hp.1

theorem sub_ensures {a b : Word w} {ea eb : WordExpr d i r w}
    (ho : Refines s one (.lit true)) (ha : WordRefines s a ea) (hb : WordRefines s b eb) :
    Ensures s (sub one a b) (fun js t => WordRefines t js (WordExpr.sub ea eb)) := by
  apply ensures_bind (bitNot_ensures hb)
  intro nb t he hnb
  apply ensures_bind (addAux_ensures (ha.mono he) hnb (ho.mono he) w (Nat.le_refl w))
  intro p u he' hp
  apply ensures_pure
  exact hp.1

theorem ult_ensures {a b : Word w} {ea eb : WordExpr d i r w}
    (ho : Refines s one (.lit true)) (ha : WordRefines s a ea) (hb : WordRefines s b eb) :
    Ensures s (ult one a b) (fun j t => Refines t j (WordExpr.ult ea eb)) := by
  apply ensures_bind (bitNot_ensures hb)
  intro nb t he hnb
  apply ensures_bind (addAux_ensures (ha.mono he) hnb (ho.mono he) w (Nat.le_refl w))
  intro p u he' hp
  exact Build.inv_ensures hp.2

theorem equalAux_ensures {a b : Word w} {ea eb : WordExpr d i r w}
    (ho : Refines s one (.lit true)) (ha : WordRefines s a ea) (hb : WordRefines s b eb)
    (n : Nat) (hn : n ≤ w) :
    Ensures s (equalAux a b one n hn) (fun j t => Refines t j (WordExpr.equalPrefix ea eb n)) := by
  induction n generalizing s with
  | zero => exact ensures_pure s _ ho
  | succ n ih =>
    apply ensures_bind (ih ho ha hb (by omega))
    intro previous t he hprev
    have hn' : n < w := by omega
    apply ensures_bind (Build.xor_ensures ((ha ⟨n,hn'⟩).mono he) ((hb ⟨n,hn'⟩).mono he))
    intro x u he1 hx
    apply ensures_bind (Build.inv_ensures hx)
    intro nx v he2 hnx
    simpa only [WordExpr.equalPrefix,hn',↓reduceDIte,Fin.getElem_fin] using
      Build.and_ensures ((hprev.mono he1).mono he2) hnx

theorem equal_ensures {a b : Word w} {ea eb : WordExpr d i r w}
    (ho : Refines s one (.lit true)) (ha : WordRefines s a ea) (hb : WordRefines s b eb) :
    Ensures s (equal one a b) (fun j t => Refines t j (WordExpr.equal ea eb)) :=
  equalAux_ensures ho ha hb w (Nat.le_refl w)

theorem selectBalanced_ensures {address : Word a} {ea : WordExpr d i r a}
    {table : Fin (2^a) → Word w} {et : Fin (2^a) → WordExpr d i r w}
    (ha : WordRefines s address ea) (ht : ∀ j, WordRefines s (table j) (et j)) :
    Ensures s (selectBalanced address table) (fun js t => WordRefines t js (WordExpr.selectBalanced ea et)) := by
  induction a generalizing s with
  | zero => exact ensures_pure s _ (ht ⟨0,by decide⟩)
  | succ a ih =>
    simp only [selectBalanced,WordExpr.selectBalanced]
    apply ensures_bind (ih (extract_refines ha 0 a (by omega)) (fun j => ht _))
    intro yes t he hyes
    apply ensures_bind (ih (extract_refines (ha.mono he) 0 a (by omega)) (fun j => (ht _).mono he))
    intro no u he' hno
    exact mux_ensures (((ha ⟨a,by omega⟩).mono he).mono he') (hyes.mono he') hno

end HDLean.Dag.Build.Word
