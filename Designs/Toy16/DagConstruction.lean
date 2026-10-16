import Designs.Toy16.DagProof
import Designs.Toy16.DagPacking
import Lean

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.constructorNameAsVariable false

namespace HDLean.Toy16.DagPhysical
open Dag.Build
open Lean Elab Tactic Meta

/-- Proof automation for sequential allocation. Every prior reference invariant
is transported across the just-proved extension; the kernel checks all terms. -/
elab "dag_bind " rule:term " as " x:ident h:ident : tactic => do
  let oldGoal ← getMainGoal
  let oldContext ← oldGoal.withContext getLCtx
  evalTactic (← `(tactic| apply ensures_bind $rule))
  let stateName := `current
  let extName ← mkFreshUserName `extended
  evalTactic (← `(tactic| intro $x $(mkIdent stateName) $(mkIdent extName) $h))
  let goal ← getMainGoal
  goal.withContext do
    let extExpr ← elabTerm (mkIdent extName) none
    let extType ← instantiateMVars (← inferType extExpr)
    let oldState := extType.getAppArgs[3]!
    for decl in oldContext do
      if decl.isImplementationDetail then continue
      let type ← instantiateMVars decl.type
      let mono? ← withReducible <| forallTelescope type fun params body => do
        let body ← instantiateMVars body
        let rule := if body.isAppOf ``Dag.Build.Refines then some ``Dag.Build.Refines.mono
          else if body.isAppOf ``WordRefines then some ``WordRefines.mono else none
        if rule.isSome then
          let stateIndex := if body.isAppOf ``Dag.Build.Refines then 3 else 4
          if (← whnf body.getAppArgs[stateIndex]!) != (← whnf oldState) then return none
        match rule with
        | none => pure none
        | some rule =>
          try
            let result ← mkAppM rule #[mkAppN decl.toExpr params,extExpr]
            pure (some (← mkLambdaFVars params result))
          catch _ => pure none
      if let some proof := mono? then
        let goal ← getMainGoal
        let (_,goal) ← goal.note decl.userName proof
        replaceMainGoal [goal]

elab "dag_mono " ext:term : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let context ← getLCtx
    let extExpr ← elabTerm ext none
    let extType ← instantiateMVars (← inferType extExpr)
    let oldState := extType.getAppArgs[3]!
    for decl in context do
      if decl.isImplementationDetail then continue
      let type ← instantiateMVars decl.type
      let mono? ← withReducible <| forallTelescope type fun params body => do
        let body ← instantiateMVars body
        let rule := if body.isAppOf ``Dag.Build.Refines then some ``Dag.Build.Refines.mono
          else if body.isAppOf ``WordRefines then some ``WordRefines.mono else none
        if rule.isSome then
          let stateIndex := if body.isAppOf ``Dag.Build.Refines then 3 else 4
          if (← whnf body.getAppArgs[stateIndex]!) != (← whnf oldState) then return none
        match rule with
        | none => pure none
        | some rule =>
          let result ← mkAppM rule #[mkAppN decl.toExpr params,extExpr]
          pure (some (← mkLambdaFVars params result))
      if let some proof := mono? then
        let goal ← getMainGoal
        let (_,goal) ← goal.note decl.userName proof
        replaceMainGoal [goal]


private theorem refines_ofFn (s : State d i r) (f : Fin n → Ref) (g : Fin n → Expr d i r) (k : Fin n) :
    Dag.Build.Refines s (Vector.ofFn f)[k] (Vector.ofFn g)[k] ↔ Dag.Build.Refines s (f k) (g k) := by
  simp only [Fin.getElem_fin,Vector.getElem_ofFn]

private theorem zeroWord_refines (h : Dag.Build.Refines s z (.lit false)) :
    WordRefines s (Vector.replicate w z) (WordExpr.literal (0 : BitVec w)) := by
  intro k
  simpa [WordExpr.literal] using h

private theorem word_registers (j : Fin 268) :
    (WordExpr.registers (j.val*16) (by omega) : WordExpr 0 0 (268*16) 16) = Physical.word j := by
  apply Vector.ext
  intro k hk
  simp [WordExpr.registers,Physical.word,bankWord,flatIndex]

structure Datapath.Spec (a : Datapath) (s : State 0 0 (268*16)) : Prop where
  zero : Dag.Build.Refines s a.zero (.lit false)
  one : Dag.Build.Refines s a.one (.lit true)
  words : ∀ j : Fin 268, WordRefines s a.words[j] (Physical.word j)
  pc : WordRefines s a.pc Physical.pc
  halted : Dag.Build.Refines s a.halted Physical.halted
  execute : Dag.Build.Refines s a.execute Physical.execute
  fetched : WordRefines s a.fetched Physical.fetched
  rd : WordRefines s a.rd Physical.rd
  imm : WordRefines s a.imm Physical.imm
  offset : WordRefines s a.offset Physical.offset
  opcode : WordRefines s a.opcode Physical.opcode
  operandA : WordRefines s a.operandA Physical.operandA
  storeData : WordRefines s a.storeData Physical.storeData
  addedImmediate : WordRefines s a.addedImmediate (WordExpr.add Physical.operandA (WordExpr.signExtend Physical.imm 16))
  ea : WordRefines s a.ea Physical.ea
  opTests : ∀ j : Fin 11, Dag.Build.Refines s a.opTests[j] (Physical.isOp j.val)
  trap : Dag.Build.Refines s a.trap Physical.trap
  flagTrap : WordRefines s a.flagTrap (Physical.flagWord Physical.trap)
  flagExecute : WordRefines s a.flagExecute (Physical.flagWord (.inv Physical.execute))
  result : WordRefines s a.result Physical.result

structure Control.Spec (imem : Addr → Word) (c : Control) (s : State 0 0 (268*16)) : Prop where
  base : c.base.Spec s
  nextPc : WordRefines s c.nextPc Physical.nextPc
  writeEnable : Dag.Build.Refines s c.writeEnable Physical.writeEnable
  active : Dag.Build.Refines s c.active Physical.active
  fetchEnable : Dag.Build.Refines s c.fetchEnable (.and (.inv Physical.halted) (.inv Physical.execute))
  fetchValue : WordRefines s c.fetchValue (WordExpr.selectBalanced Physical.pc (fun a => WordExpr.literal (imem (BitVec.ofNat 8 a.val))))

theorem datapath_ensures (start : State 0 0 (268*16)) :
    Ensures start datapath Datapath.Spec := by
  unfold datapath
  dag_bind (literal_ensures start false) as zero hz
  dag_bind (literal_ensures _ true) as one ho
  have hregs : Ensures current (tabulate fun j : Fin 268 => Dag.Build.Word.registers (j.val*16) (by omega))
      (fun words t => ∀ j : Fin 268, WordRefines t words[j] (Physical.word j)) := by
    apply tabulate_ensures _ (fun j ws t => WordRefines t ws (Physical.word j))
      (fun _ _ _ _ he h => h.mono he)
    intro t he j
    simpa only [← word_registers] using Dag.Build.Word.registers_ensures t (j.val*16) (by omega)
  dag_bind hregs as words hw
  dsimp only
  have hz16 := zeroWord_refines (w := 16) hz
  have hpc := Dag.Build.Word.extract_refines (hw ⟨0,by decide⟩) 0 8 (by decide)
  change WordRefines current _ Physical.pc at hpc
  have hhalt := hw ⟨1,by decide⟩ ⟨0,by decide⟩
  change Dag.Build.Refines current _ Physical.halted at hhalt
  have hexecute := hw ⟨2,by decide⟩ ⟨0,by decide⟩
  change Dag.Build.Refines current _ Physical.execute at hexecute
  have hfetched := hw ⟨3,by decide⟩
  change WordRefines current _ Physical.fetched at hfetched
  have hrd := Dag.Build.Word.extract_refines hfetched 9 3 (by decide)
  change WordRefines current _ Physical.rd at hrd
  have hrs := Dag.Build.Word.extract_refines hfetched 6 3 (by decide)
  change WordRefines current _ Physical.rs at hrs
  have hrt := Dag.Build.Word.extract_refines hfetched 3 3 (by decide)
  change WordRefines current _ Physical.rt at hrt
  have hopcode := Dag.Build.Word.extract_refines hfetched 12 4 (by decide)
  change WordRefines current _ Physical.opcode at hopcode
  have himm := Dag.Build.Word.extract_refines hfetched 0 6 (by decide)
  change WordRefines current _ Physical.imm at himm
  have hoffset := Dag.Build.Word.extract_refines hfetched 0 12 (by decide)
  change WordRefines current _ Physical.offset at hoffset
  have htable (j : Fin 8) : WordRefines current
      (if j.val = 0 then Vector.replicate 16 zero else words[4+j.val]'(by omega))
      (if j.val = 0 then WordExpr.literal 0 else Physical.regWord j) := by
    split
    · exact hz16
    · exact hw ⟨4+j.val,by omega⟩
  dag_bind (Dag.Build.Word.selectBalanced_ensures hrs htable) as operandA ha
  change WordRefines current _ Physical.operandA at ha
  dag_bind (Dag.Build.Word.selectBalanced_ensures hrt htable) as operandB hb
  change WordRefines current _ Physical.operandB at hb
  dag_bind (Dag.Build.Word.selectBalanced_ensures hrd htable) as storeData hstore
  change WordRefines current _ Physical.storeData at hstore
  dag_bind (Dag.Build.Word.add_ensures hz ha (Dag.Build.Word.signExtend_refines hz himm 16)) as addedImmediate hai
  have hea := Dag.Build.Word.setWidth_refines hz hai 8
  change WordRefines current _ Physical.ea at hea
  have hdec : Ensures current
      (tabulate fun j : Fin 11 => do
        let lit ← Dag.Build.Word.literal (BitVec.ofNat 4 j.val)
        Dag.Build.Word.equal one (Dag.Build.Word.extract words[3] 12 4 (by decide)) lit)
      (fun refs t => ∀ j : Fin 11, Dag.Build.Refines t refs[j] (Physical.isOp j.val)) := by
    apply tabulate_ensures _ (fun j ref t => Dag.Build.Refines t ref (Physical.isOp j.val))
      (fun _ _ _ _ he h => h.mono he)
    intro t he j
    apply ensures_bind (Dag.Build.Word.literal_ensures t (BitVec.ofNat 4 j.val))
    intro lit u he' hlit
    exact Dag.Build.Word.equal_ensures ((ho.mono he).mono he') ((hopcode.mono he).mono he') hlit
  dag_bind hdec as opTests hdec
  dag_bind (Dag.Build.Word.literal_ensures current (11 : BitVec 4)) as eleven heleven
  dag_bind (Dag.Build.Word.ult_ensures ho hopcode heleven) as legal hlegal
  dag_bind (inv_ensures hlegal) as trap htrap
  change Dag.Build.Refines current _ Physical.trap at htrap
  dag_bind (Dag.Build.Word.add_ensures hz ha hb) as addResult hadd
  dag_bind (Dag.Build.Word.sub_ensures ho ha hb) as subResult hsub
  dag_bind (Dag.Build.Word.bitAnd_ensures ha hb) as andResult hand
  dag_bind (Dag.Build.Word.bitOr_ensures ha hb) as orResult hor
  dag_bind (Dag.Build.Word.bitXor_ensures ha hb) as xorResult hxor
  dag_bind (Dag.Build.Word.ult_ensures ho ha hb) as less hless
  dag_bind (Dag.Build.Word.literal_ensures current (1 : BitVec 16)) as one16 hone16
  dag_bind (Dag.Build.Word.mux_ensures hless hone16 hz16) as flagLess hflagLess
  dag_bind (Dag.Build.Word.mux_ensures htrap hone16 hz16) as flagTrap hflagTrap
  dag_bind (inv_ensures hexecute) as notExecute hnotExecute
  dag_bind (Dag.Build.Word.mux_ensures hnotExecute hone16 hz16) as flagExecute hflagExecute
  dag_bind (Dag.Build.Word.selectBalanced_ensures hea (fun j : Fin 256 => hw ⟨12+j.val,by omega⟩)) as memResult hmem
  have hresults (j : Fin 16) : WordRefines current
      (match j.val with
       | 0 => addResult
       | 1 => subResult
       | 2 => andResult
       | 3 => orResult
       | 4 => xorResult
       | 5 => flagLess
       | 6 => addedImmediate
       | 7 => memResult
       | _ => Vector.replicate 16 zero)
      (match j.val with
       | 0 => WordExpr.add Physical.operandA Physical.operandB
       | 1 => WordExpr.sub Physical.operandA Physical.operandB
       | 2 => WordExpr.bitAnd Physical.operandA Physical.operandB
       | 3 => WordExpr.bitOr Physical.operandA Physical.operandB
       | 4 => WordExpr.bitXor Physical.operandA Physical.operandB
       | 5 => Physical.flagWord (WordExpr.ult Physical.operandA Physical.operandB)
       | 6 => WordExpr.add Physical.operandA (WordExpr.signExtend Physical.imm 16)
       | 7 => WordExpr.selectBalanced Physical.ea Physical.memWord
       | _ => WordExpr.literal 0) := by
    split <;> first | exact hadd | exact hsub | exact hand | exact hor | exact hxor |
      exact hflagLess | exact hai | exact hmem | exact hz16
  dag_bind (Dag.Build.Word.selectBalanced_ensures hopcode hresults) as result hresult
  change WordRefines current _ Physical.result at hresult
  apply ensures_pure
  exact ⟨hz,ho,hw,hpc,hhalt,hexecute,hfetched,hrd,himm,hoffset,hopcode,ha,hstore,hai,hea,hdec,htrap,hflagTrap,hflagExecute,hresult⟩

theorem control_ensures (imem : Addr → Word) (base : Datapath) (start : State 0 0 (268*16))
    (hbase : base.Spec start) : Ensures start (control imem base) (Control.Spec imem) := by
  rcases base with ⟨zero,one,words,pc,halted,execute,fetched,rd,imm,offset,opcode,operandA,storeData,addedImmediate,ea,opTests,trap,flagTrap,flagExecute,result⟩
  rcases hbase with ⟨hz,ho,hw,hpc,hhalt,hexecute,hfetched,hrd,himm,hoffset,hopcode,ha,hstore,hai,hea,hdec,htrap,hflagTrap,hflagExecute,hresult⟩
  unfold control
  dsimp only
  let current := start
  dag_bind (Dag.Build.Word.literal_ensures current (1 : BitVec 8)) as one8 hone8
  dag_bind (Dag.Build.Word.add_ensures hz hpc hone8) as pc1 hpc1
  dag_bind (Dag.Build.Word.add_ensures hz hpc1 (Dag.Build.Word.setWidth_refines hz hoffset 8)) as jumpPc hjump
  dag_bind (Dag.Build.Word.add_ensures hz hpc1 (Dag.Build.Word.signExtend_refines hz himm 8)) as branchPc hbranchPc
  dag_bind (Dag.Build.Word.equal_ensures ho hstore ha) as beq hbeq
  dag_bind (and_ensures (hdec ⟨9,by decide⟩) hbeq) as branch hbranch
  dag_bind (Dag.Build.Word.mux_ensures hbranch hbranchPc hpc1) as branchOrNext hbranchOrNext
  dag_bind (Dag.Build.Word.mux_ensures (hdec ⟨10,by decide⟩) hjump hbranchOrNext) as jumpOrBranch hjumpOrBranch
  dag_bind (Dag.Build.Word.mux_ensures htrap hpc hjumpOrBranch) as nextPc hnextPc
  change WordRefines current _ Physical.nextPc at hnextPc
  dag_bind (Dag.Build.Word.literal_ensures current (8 : BitVec 4)) as eight heigh
  dag_bind (Dag.Build.Word.ult_ensures ho hopcode heigh) as writing hwriting
  dag_bind (Dag.Build.Word.literal_ensures current (0 : BitVec 3)) as zero3 hzero3
  dag_bind (Dag.Build.Word.equal_ensures ho hrd hzero3) as rdZero hrdZero
  dag_bind (inv_ensures hrdZero) as rdNonzero hrdNonzero
  dag_bind (and_ensures hwriting hrdNonzero) as writeEnable hwrite
  change Dag.Build.Refines current _ Physical.writeEnable at hwrite
  dag_bind (inv_ensures hhalt) as notHalted hnotHalted
  dag_bind (and_ensures hexecute hnotHalted) as active hactive
  change Dag.Build.Refines current _ Physical.active at hactive
  dag_bind (inv_ensures hhalt) as notHalted2 hnotHalted2
  dag_bind (inv_ensures hexecute) as notExecute2 hnotExecute2
  dag_bind (and_ensures hnotHalted2 hnotExecute2) as fetchEnable hfetchEnable

  have hrom : Ensures current
      (tabulate fun a : Fin 256 => Dag.Build.Word.literal (imem (BitVec.ofNat 8 a.val)))
      (fun rom t => ∀ a : Fin 256, WordRefines t rom[a] (WordExpr.literal (imem (BitVec.ofNat 8 a.val)))) := by
    apply tabulate_ensures _ (fun a ws t => WordRefines t ws (WordExpr.literal (imem (BitVec.ofNat 8 a.val))))
      (fun _ _ _ _ he h => h.mono he)
    intro t he a
    exact Dag.Build.Word.literal_ensures t _
  dag_bind hrom as rom hrom
  dag_bind (Dag.Build.Word.selectBalanced_ensures hpc hrom) as fetchValue hfetchValue
  apply ensures_pure
  exact ⟨⟨hz,ho,hw,hpc,hhalt,hexecute,hfetched,hrd,himm,hoffset,hopcode,ha,hstore,hai,hea,hdec,htrap,hflagTrap,hflagExecute,hresult⟩,hnextPc,hwrite,hactive,hfetchEnable,hfetchValue⟩


set_option maxHeartbeats 100000 in
theorem ports_ensures (imem : Addr → Word) (c : Control) (start : State 0 0 (268*16))
    (hc : c.Spec imem start) : Ensures start (ports c) (fun p t =>
      (∀ k : Fin (268*16), Dag.Build.Refines t p.1[k] (Physical.hardware imem).state[k].next) ∧
      WordRefines t p.2 (Physical.hardware imem).output) := by
  rcases c with ⟨base,nextPc,writeEnable,active,fetchEnable,fetchValue⟩
  rcases base with ⟨zero,one,words,pc,halted,execute,fetched,rd,imm,offset,opcode,operandA,storeData,addedImmediate,ea,opTests,trap,flagTrap,flagExecute,result⟩
  rcases hc with ⟨hbase,hnextPc,hwrite,hactive,hfetchEnable,hfetchValue⟩
  rcases hbase with ⟨hz,ho,hw,hpc,hhalt,hexecute,hfetched,hrd,himm,hoffset,hopcode,ha,hstore,hai,hea,hdec,htrap,hflagTrap,hflagExecute,hresult⟩
  unfold ports
  dsimp only
  let current := start
  have hnextWords : Ensures current
      (tabulate fun j : Fin 268 => do
        if j.val = 0 then Dag.Build.Word.mux active (Dag.Build.Word.setWidth zero nextPc 16) words[j]
        else if j.val = 1 then Dag.Build.Word.mux active flagTrap words[j]
        else if j.val = 2 then Dag.Build.Word.mux halted words[j] flagExecute
        else if j.val = 3 then Dag.Build.Word.mux fetchEnable fetchValue words[j]
        else if j.val < 12 then
          Dag.Build.Word.mux (← and active (← and writeEnable (← Dag.Build.Word.equal one
            rd (← Dag.Build.Word.literal (BitVec.ofNat 3 (j.val-4)))))) result words[j]
        else Dag.Build.Word.mux (← and active (← and opTests[8] (← Dag.Build.Word.equal one
          ea (← Dag.Build.Word.literal (BitVec.ofNat 8 (j.val-12)))))) storeData words[j])
      (fun ws t => ∀ j : Fin 268, WordRefines t ws[j] (Physical.nextWord imem j)) := by
    apply tabulate_ensures _ (fun j ws t => WordRefines t ws (Physical.nextWord imem j))
      (fun _ _ _ _ he h => h.mono he)
    intro current he j
    dag_mono he
    by_cases h0 : j.val = 0
    · simp only [h0,↓reduceIte,Physical.nextWord]
      exact Dag.Build.Word.mux_ensures hactive (Dag.Build.Word.setWidth_refines hz hnextPc 16) (hw j)
    · by_cases h1 : j.val = 1
      · simp only [h0,h1,↓reduceIte,Physical.nextWord]
        exact Dag.Build.Word.mux_ensures hactive hflagTrap (hw j)
      · by_cases h2 : j.val = 2
        · simp only [h0,h1,h2,↓reduceIte,Physical.nextWord]
          exact Dag.Build.Word.mux_ensures hhalt (hw j) hflagExecute
        · by_cases h3 : j.val = 3
          · simp only [h0,h1,h2,h3,↓reduceIte,Physical.nextWord]
            exact Dag.Build.Word.mux_ensures hfetchEnable hfetchValue (hw j)
          · by_cases h12 : j.val < 12
            · simp only [h0,h1,h2,h3,h12,↓reduceIte,Physical.nextWord]
              dag_bind (Dag.Build.Word.literal_ensures current (BitVec.ofNat 3 (j.val-4))) as regIndex hregIndex
              dag_bind (Dag.Build.Word.equal_ensures ho hrd hregIndex) as selected hselected
              dag_bind (and_ensures hwrite hselected) as enabled henabled
              dag_bind (and_ensures hactive henabled) as write hwriteBit
              exact Dag.Build.Word.mux_ensures hwriteBit hresult (hw j)
            · simp only [h0,h1,h2,h3,h12,↓reduceIte,Physical.nextWord]
              dag_bind (Dag.Build.Word.literal_ensures current (BitVec.ofNat 8 (j.val-12))) as memIndex hmemIndex
              dag_bind (Dag.Build.Word.equal_ensures ho hea hmemIndex) as selected hselected
              dag_bind (and_ensures (hdec ⟨8,by decide⟩) hselected) as enabled henabled
              dag_bind (and_ensures hactive henabled) as write hwriteBit
              exact Dag.Build.Word.mux_ensures hwriteBit hstore (hw j)
  dag_bind hnextWords as nextWords hnextWords
  apply ensures_pure
  constructor
  · intro k
    have h := hnextWords ⟨k.val/16,by have := k.isLt; omega⟩ ⟨k.val%16,by omega⟩
    simpa only [Physical.hardware,wordBank,Fin.getElem_fin,Vector.getElem_flatten,Vector.getElem_ofFn] using h
  · intro k
    change Dag.Build.Refines current _ Physical.outputBits[k]
    rw [outputBits_pack]
    exact packOutputs_related (Dag.Build.Refines current) _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _ _ _ _ _ hactive hpc hfetched hnextPc hwrite hrd hresult
      (hdec ⟨8,by decide⟩) hea hstore htrap k


/-- Full construction proof, composed from the three separately checked allocation stages. -/
theorem program_ensures (imem : Addr → Word) (start : State 0 0 (268*16)) :
    Ensures start (program imem) (fun p t =>
      (∀ k : Fin (268*16), Dag.Build.Refines t p.1[k] (Physical.hardware imem).state[k].next) ∧
      WordRefines t p.2 (Physical.hardware imem).output) := by
  apply ensures_bind (datapath_ensures start)
  intro data t _ hd
  apply ensures_bind (control_ensures imem data t hd)
  intro c u _ hc
  exact ports_ensures imem c u hc


end HDLean.Toy16.DagPhysical
